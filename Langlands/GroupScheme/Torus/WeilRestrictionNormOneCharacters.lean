import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCocharacters
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Characters of the actual norm-one torus -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Algebra.SeparableTensor
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.characterLattice

variable {S : Scheme.{u}} {G H : CommGroupScheme S}

/-- Restrict actual characters along an actual commutative-group-scheme homomorphism. -/
def precompose (f : G ⟶ H) : characterLattice H →+ characterLattice G where
  toFun χ := f ≫ χ
  map_zero' := by simp
  map_add' χ ψ := Preadditive.comp_add _ _ _ _ _ _

section Naturality

variable {B : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)
  {G H : CommGroupScheme B} (f : G ⟶ H)

/-- Coefficient transport commutes with restriction along an actual descended morphism. -/
theorem transport_precompose
    (χ : characterLattice ((CommGroupScheme.baseChange b).obj H)) :
    transport b a ha G ((CommGroupScheme.baseChange b).map f ≫ χ) =
      (CommGroupScheme.baseChange b).map f ≫ transport b a ha H χ := by
  apply ext_points
  intro U x
  rw [transport_points]
  change Gm.pointsEquiv S ((Over.map a).obj U)
      ((descentPoint b a ha G.toGrp U x ≫
        (CommGroupScheme.groupHom ((CommGroupScheme.baseChange b).map f)).hom.hom) ≫
          (CommGroupScheme.groupHom χ).hom.hom) = _
  rw [comp_groupHom_comp, transport_points]
  change Gm.pointsEquiv S ((Over.map a).obj U)
      ((descentPoint b a ha G.toGrp U x ≫
        ((Over.pullback b).mapGrp.map (CommGroupScheme.groupHom f)).hom.hom) ≫
          (CommGroupScheme.groupHom χ).hom.hom) =
    Gm.pointsEquiv S ((Over.map a).obj U)
      (descentPoint b a ha H.toGrp U
        (x ≫ ((Over.pullback b).mapGrp.map (CommGroupScheme.groupHom f)).hom.hom) ≫
          (CommGroupScheme.groupHom χ).hom.hom)
  rw [descentPoint_comp_baseChange]

end Naturality

/-- The ordinary Galois action commutes with actual character restriction. -/
theorem galoisRepresentation_precompose
    (k Ω : Type u) [CommRing k] [CommRing Ω] [Algebra k Ω]
    {G H : CommGroupScheme (Spec (CommRingCat.of k))} (f : G ⟶ H)
    (σ : Ω ≃ₐ[k] Ω)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj H)) :
    galoisRepresentation k Ω G σ
        ((CommGroupScheme.baseChange (algebraBaseMap k Ω)).map f ≫ χ) =
      (CommGroupScheme.baseChange (algebraBaseMap k Ω)).map f ≫
        galoisRepresentation k Ω H σ χ :=
  transport_precompose (algebraBaseMap k Ω) (galoisBaseMap k Ω σ)
    (galoisBaseMap_over k Ω σ) f χ

end Langlands.GroupScheme.characterLattice

namespace Langlands.GroupScheme

/-- An actual split-torus isomorphism makes the actual lattice pairing perfect. -/
theorem latticePairing_isPerfPair_of_split
    {k : Type u} [CommRing k] [IsDomain k]
    {G : CommGroupScheme (Spec (CommRingCat.of k))}
    {I : Type u} [Finite I]
    (e : G ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) :
    (latticePairing G).IsPerfPair := by
  refine LinearMap.IsPerfPair.congr
    (characterLattice.congr e).toIntLinearEquiv
    (cocharacterLattice.congr e).toIntLinearEquiv (latticePairing G)
    (p := latticePairing (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)) ?_
  ext χ ν
  change latticePairing G ((characterLattice.congr e).symm χ)
      ((cocharacterLattice.congr e).symm ν) =
    latticePairing (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) χ ν
  simpa only [AddEquiv.apply_symm_apply] using
    (latticePairing_congr e ((characterLattice.congr e).symm χ)
      ((cocharacterLattice.congr e).symm ν)).symm

end Langlands.GroupScheme

namespace Langlands.GroupScheme.WeilGm

variable (k K Ω : Type u) [Field k] [Field K] [Field Ω]
  [Algebra k K] [Algebra k Ω] [FiniteDimensional k K] [Algebra.IsSeparable k K]
  (hsplit : ∀ x : K, ((minpoly k x).map (algebraMap k Ω)).Splits)

local instance : DecidableEq (K →ₐ[k] Ω) := Classical.decEq _

local notation "W_Ω" =>
  (Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k Ω))
    (commGroupScheme (CommRingCat.of k) K))

local notation "N_Ω" =>
  (Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k Ω))
    (normOneCommGroupScheme (CommRingCat.of k) K))

include hsplit in
/-- The pairing on actual norm-one characters and cocharacters is perfect. -/
theorem normOne_latticePairing_isPerfPair : (latticePairing N_Ω).IsPerfPair := by
  obtain ⟨τ₀⟩ := separableEmbedding_nonempty k K Ω hsplit
  exact latticePairing_isPerfPair_of_split
    (normOneSeparableEmbeddingCommIso k K Ω hsplit τ₀)

/-- Restriction from ambient embedding characters along the actual norm-one inclusion. -/
def normOneEmbeddingCharacterRestriction :
    ((K →ₐ[k] Ω) → ℤ) →ₗ[ℤ] characterLattice N_Ω :=
  ((characterLattice.precompose
    ((CommGroupScheme.baseChange (algebraBaseMap k Ω)).map
      (normOneιHom (CommRingCat.of k) K))).comp
        (separableEmbeddingCharacterEquiv k K Ω hsplit).symm.toAddMonoidHom).toIntLinearMap

/-- The pairing of a restricted character with an actual norm-one cocharacter is
the dot product with its sum-zero embedding coordinates. -/
theorem normOneEmbeddingCharacterRestriction_pairing
    (m : (K →ₐ[k] Ω) → ℤ) (ν : cocharacterLattice N_Ω) :
    latticePairing N_Ω (normOneEmbeddingCharacterRestriction k K Ω hsplit m) ν =
      ∑ τ, m τ * (normOneSeparableEmbeddingCocharacterEquiv k K Ω hsplit ν).val τ := by
  change latticePairing W_Ω
      ((separableEmbeddingCharacterEquiv k K Ω hsplit).symm m)
      (ν ≫ (CommGroupScheme.baseChange (algebraBaseMap k Ω)).map
        (normOneιHom (CommRingCat.of k) K)) = _
  rw [embedding_latticePairing_eq_sum k K Ω (embeddingEvaluationStatement k K Ω hsplit)]
  change (∑ τ,
    separableEmbeddingCharacterEquiv k K Ω hsplit
      ((separableEmbeddingCharacterEquiv k K Ω hsplit).symm m) τ *
        separableEmbeddingCocharacterEquiv k K Ω hsplit
          (ν ≫ (CommGroupScheme.baseChange (algebraBaseMap k Ω)).map
            (normOneιHom (CommRingCat.of k) K)) τ) = _
  rw [AddEquiv.apply_symm_apply, normOneSeparableEmbeddingCocharacterEquiv_val]

/-- Restrict the standard dot product to the sum-zero lattice in its second argument. -/
def embeddingSumZeroDualRestriction :
    ((K →ₐ[k] Ω) → ℤ) →ₗ[ℤ]
      Module.Dual ℤ (embeddingCoordinateSum k K Ω).ker := by
  classical
  exact ((embeddingCoordinateSum k K Ω).toIntLinearMap.ker).dualRestrict.comp
    (dotProductEquiv ℤ (K →ₐ[k] Ω)).toLinearMap

omit [Algebra.IsSeparable k K] in
@[simp] theorem embeddingSumZeroDualRestriction_apply
    (m : (K →ₐ[k] Ω) → ℤ) (n : (embeddingCoordinateSum k K Ω).ker) :
    embeddingSumZeroDualRestriction k K Ω m n = ∑ τ, m τ * n.val τ := rfl

/-- A chosen embedding gives a retraction onto the sum-zero lattice. -/
def embeddingSumZeroProjection (τ₀ : K →ₐ[k] Ω) :
    ((K →ₐ[k] Ω) → ℤ) →ₗ[ℤ] (embeddingCoordinateSum k K Ω).ker := by
  classical
  let p : ((K →ₐ[k] Ω) → ℤ) →ₗ[ℤ] ((K →ₐ[k] Ω) → ℤ) :=
    LinearMap.id -
      (LinearMap.single ℤ (fun _ : K →ₐ[k] Ω => ℤ) τ₀).comp
        (embeddingCoordinateSum k K Ω).toIntLinearMap
  exact LinearMap.codRestrict ((embeddingCoordinateSum k K Ω).toIntLinearMap.ker) p
    (fun (m : (K →ₐ[k] Ω) → ℤ) => by
    change (∑ τ : K →ₐ[k] Ω,
      (m τ - (Pi.single τ₀ (∑ σ, m σ) : (K →ₐ[k] Ω) → ℤ) τ)) = 0
    simp [Finset.sum_sub_distrib])

omit [Algebra.IsSeparable k K] in
@[simp] theorem embeddingSumZeroProjection_val (τ₀ : K →ₐ[k] Ω)
    (m : (K →ₐ[k] Ω) → ℤ) :
    (embeddingSumZeroProjection k K Ω τ₀ m).val =
      m - Pi.single τ₀ (embeddingCoordinateSum k K Ω m) := rfl

omit [Algebra.IsSeparable k K] in
@[simp] theorem embeddingSumZeroProjection_subtype (τ₀ : K →ₐ[k] Ω)
    (n : (embeddingCoordinateSum k K Ω).ker) :
    embeddingSumZeroProjection k K Ω τ₀ n.val = n := by
  apply Subtype.ext
  rw [embeddingSumZeroProjection_val, n.property]
  simp

include hsplit in
/-- Every integral functional on the sum-zero lattice extends to embedding coordinates. -/
theorem embeddingSumZeroDualRestriction_surjective :
    Function.Surjective (embeddingSumZeroDualRestriction k K Ω) := by
  classical
  obtain ⟨τ₀⟩ := separableEmbedding_nonempty k K Ω hsplit
  intro l
  let f := l.comp (embeddingSumZeroProjection k K Ω τ₀)
  refine ⟨(dotProductEquiv ℤ (K →ₐ[k] Ω)).symm f, ?_⟩
  ext n
  change (dotProductEquiv ℤ (K →ₐ[k] Ω))
    ((dotProductEquiv ℤ (K →ₐ[k] Ω)).symm f) n.val = l n
  rw [LinearEquiv.apply_symm_apply]
  change l (embeddingSumZeroProjection k K Ω τ₀ n.val) = l n
  rw [embeddingSumZeroProjection_subtype]

/-- Perfectness and the actual cocharacter comparison identify characters with
integral functionals on sum-zero embedding coordinates. -/
def normOneCharacterDualEquiv :
    characterLattice N_Ω ≃ₗ[ℤ] Module.Dual ℤ (embeddingCoordinateSum k K Ω).ker := by
  letI := normOne_latticePairing_isPerfPair k K Ω hsplit
  exact (latticePairing N_Ω).toPerfPair.trans
    (normOneSeparableEmbeddingCocharacterEquiv k K Ω hsplit).toIntLinearEquiv.symm.dualMap

@[simp] theorem normOneCharacterDualEquiv_apply
    (χ : characterLattice N_Ω) (n : (embeddingCoordinateSum k K Ω).ker) :
    normOneCharacterDualEquiv k K Ω hsplit χ n =
      latticePairing N_Ω χ
        ((normOneSeparableEmbeddingCocharacterEquiv k K Ω hsplit).symm n) := rfl

/-- Actual restriction is the dot-product restriction under perfect duality. -/
theorem normOneCharacterDualEquiv_restriction
    (m : (K →ₐ[k] Ω) → ℤ) :
    normOneCharacterDualEquiv k K Ω hsplit
        (normOneEmbeddingCharacterRestriction k K Ω hsplit m) =
      embeddingSumZeroDualRestriction k K Ω m := by
  ext n
  rw [normOneCharacterDualEquiv_apply, normOneEmbeddingCharacterRestriction_pairing]
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- Every actual norm-one character is the restriction of an ambient embedding character. -/
theorem normOneEmbeddingCharacterRestriction_surjective :
    Function.Surjective (normOneEmbeddingCharacterRestriction k K Ω hsplit) := by
  intro χ
  obtain ⟨m, hm⟩ := embeddingSumZeroDualRestriction_surjective k K Ω hsplit
    (normOneCharacterDualEquiv k K Ω hsplit χ)
  refine ⟨m, (normOneCharacterDualEquiv k K Ω hsplit).injective ?_⟩
  rw [normOneCharacterDualEquiv_restriction, hm]

/-- The diagonal submodule consists of constant integral embedding functions. -/
def embeddingDiagonal : Submodule ℤ ((K →ₐ[k] Ω) → ℤ) :=
  LinearMap.range (LinearMap.pi fun _ : K →ₐ[k] Ω => (LinearMap.id : ℤ →ₗ[ℤ] ℤ))

omit [FiniteDimensional k K] [Algebra.IsSeparable k K] in
theorem mem_embeddingDiagonal_iff (m : (K →ₐ[k] Ω) → ℤ) :
    m ∈ embeddingDiagonal k K Ω ↔ ∃ c : ℤ, m = fun _ => c := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩

include hsplit in
/-- An integral embedding vector annihilates the sum-zero lattice exactly when it
is constant; singleton differences detect all coordinate differences. -/
theorem embeddingSumZeroDualRestriction_eq_zero_iff
    (m : (K →ₐ[k] Ω) → ℤ) :
    embeddingSumZeroDualRestriction k K Ω m = 0 ↔ m ∈ embeddingDiagonal k K Ω := by
  classical
  rw [mem_embeddingDiagonal_iff]
  obtain ⟨τ₀⟩ := separableEmbedding_nonempty k K Ω hsplit
  constructor
  · intro hm
    refine ⟨m τ₀, funext fun τ => ?_⟩
    let n : (embeddingCoordinateSum k K Ω).ker :=
      ⟨Pi.single τ 1 - Pi.single τ₀ 1, by
        change (∑ σ, ((Pi.single τ 1 - Pi.single τ₀ 1 : (K →ₐ[k] Ω) → ℤ) σ)) = 0
        simp [Pi.sub_apply, Finset.sum_sub_distrib]⟩
    have hn := congrArg (fun l : Module.Dual ℤ (embeddingCoordinateSum k K Ω).ker =>
      l n) hm
    change m ⬝ᵥ (Pi.single τ 1 - Pi.single τ₀ 1) = 0 at hn
    simpa only [dotProduct_sub, dotProduct_single, mul_one, sub_eq_zero] using hn
  · rintro ⟨c, rfl⟩
    ext n
    change (∑ τ, c * n.val τ) = 0
    rw [← Finset.mul_sum]
    change c * embeddingCoordinateSum k K Ω n.val = 0
    rw [n.property, mul_zero]

/-- The kernel of actual character restriction is precisely the diagonal copy of the integers. -/
theorem normOneEmbeddingCharacterRestriction_ker :
    (normOneEmbeddingCharacterRestriction k K Ω hsplit).ker = embeddingDiagonal k K Ω := by
  ext m
  change normOneEmbeddingCharacterRestriction k K Ω hsplit m = 0 ↔ _
  rw [← (normOneCharacterDualEquiv k K Ω hsplit).map_eq_zero_iff,
    normOneCharacterDualEquiv_restriction]
  exact embeddingSumZeroDualRestriction_eq_zero_iff k K Ω hsplit m

/-- The ambient permutation representation induces an action on the quotient by constants. -/
def embeddingQuotientRepresentation :
    Representation ℤ (Ω ≃ₐ[k] Ω)
      (((K →ₐ[k] Ω) → ℤ) ⧸ embeddingDiagonal k K Ω) :=
  (embeddingPermutationRepresentation k K Ω).quotient (embeddingDiagonal k K Ω)
    (fun σ m hm => by
      change embeddingPermutationRepresentation k K Ω σ m ∈ embeddingDiagonal k K Ω
      obtain ⟨c, rfl⟩ := (mem_embeddingDiagonal_iff k K Ω m).mp hm
      rw [mem_embeddingDiagonal_iff]
      exact ⟨c, rfl⟩)

omit [FiniteDimensional k K] [Algebra.IsSeparable k K] in
@[simp] theorem embeddingQuotientRepresentation_mk (σ : Ω ≃ₐ[k] Ω)
    (m : (K →ₐ[k] Ω) → ℤ) :
    embeddingQuotientRepresentation k K Ω σ
        (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (embeddingPermutationRepresentation k K Ω σ m) := rfl

/-- Actual restriction identifies the embedding lattice modulo the diagonal with
the actual norm-one character lattice. -/
def embeddingQuotientNormOneCharacterEquiv :
    (((K →ₐ[k] Ω) → ℤ) ⧸ embeddingDiagonal k K Ω) ≃ₗ[ℤ] characterLattice N_Ω :=
  (Submodule.quotEquivOfEq _ _
    (normOneEmbeddingCharacterRestriction_ker k K Ω hsplit).symm).trans
      ((normOneEmbeddingCharacterRestriction k K Ω hsplit).quotKerEquivOfSurjective
        (normOneEmbeddingCharacterRestriction_surjective k K Ω hsplit))

@[simp] theorem embeddingQuotientNormOneCharacterEquiv_mk
    (m : (K →ₐ[k] Ω) → ℤ) :
    embeddingQuotientNormOneCharacterEquiv k K Ω hsplit (Submodule.Quotient.mk m) =
      normOneEmbeddingCharacterRestriction k K Ω hsplit m := rfl

/-- Canonical quotient embedding coordinates of actual norm-one characters. -/
def normOneSeparableEmbeddingCharacterEquiv :
    characterLattice N_Ω ≃+ (((K →ₐ[k] Ω) → ℤ) ⧸ embeddingDiagonal k K Ω) :=
  (embeddingQuotientNormOneCharacterEquiv k K Ω hsplit).symm.toAddEquiv

@[simp] theorem normOneSeparableEmbeddingCharacterEquiv_restriction
    (m : (K →ₐ[k] Ω) → ℤ) :
    normOneSeparableEmbeddingCharacterEquiv k K Ω hsplit
        (normOneEmbeddingCharacterRestriction k K Ω hsplit m) =
      Submodule.Quotient.mk m :=
  (embeddingQuotientNormOneCharacterEquiv k K Ω hsplit).symm_apply_apply
    (Submodule.Quotient.mk m)

/-- A quotient representative gives precisely the actual restricted ambient character. -/
@[simp] theorem normOneSeparableEmbeddingCharacterEquiv_symm_mk
    (m : (K →ₐ[k] Ω) → ℤ) :
    (normOneSeparableEmbeddingCharacterEquiv k K Ω hsplit).symm
        (Submodule.Quotient.mk m) =
      (CommGroupScheme.baseChange (algebraBaseMap k Ω)).map
          (normOneιHom (CommRingCat.of k) K) ≫
        (separableEmbeddingCharacterEquiv k K Ω hsplit).symm m := rfl

/-- In quotient and sum-zero coordinates the actual perfect pairing is the dot product. -/
theorem normOne_embedding_latticePairing
    (m : (K →ₐ[k] Ω) → ℤ) (n : (embeddingCoordinateSum k K Ω).ker) :
    latticePairing N_Ω
        ((normOneSeparableEmbeddingCharacterEquiv k K Ω hsplit).symm
          (Submodule.Quotient.mk m))
        ((normOneSeparableEmbeddingCocharacterEquiv k K Ω hsplit).symm n) =
      ∑ τ, m τ * n.val τ := by
  change latticePairing N_Ω (normOneEmbeddingCharacterRestriction k K Ω hsplit m)
    ((normOneSeparableEmbeddingCocharacterEquiv k K Ω hsplit).symm n) = _
  rw [normOneEmbeddingCharacterRestriction_pairing, AddEquiv.apply_symm_apply]

/-- On every test scheme a representative acts by the monomial in the actual
included embedding coordinates. -/
theorem normOneSeparableEmbeddingCharacterEquiv_symm_points
    (m : (K →ₐ[k] Ω) → ℤ)
    (T : Over (Spec (CommRingCat.of Ω))) (x : T ⟶ (N_Ω).X) :
    Gm.pointsEquiv _ T
        (x ≫ (CommGroupScheme.groupHom
          ((normOneSeparableEmbeddingCharacterEquiv k K Ω hsplit).symm
            (Submodule.Quotient.mk m))).hom.hom) =
      ∏ τ, embeddingPointsEquiv k K Ω (embeddingEvaluationStatement k K Ω hsplit) T
        (x ≫ (CommGroupScheme.groupHom
          ((CommGroupScheme.baseChange (algebraBaseMap k Ω)).map
            (normOneιHom (CommRingCat.of k) K))).hom.hom) τ ^ m τ := by
  rw [normOneSeparableEmbeddingCharacterEquiv_symm_mk, comp_groupHom_comp]
  dsimp only [separableEmbeddingCharacterEquiv]
  apply embeddingCharacterEquiv_symm_points

/-- The ordinary Galois action commutes with restriction from embedding characters. -/
theorem galoisRepresentation_normOneEmbeddingCharacterRestriction
    (σ : Ω ≃ₐ[k] Ω) (m : (K →ₐ[k] Ω) → ℤ) :
    characterLattice.galoisRepresentation k Ω
        (normOneCommGroupScheme (CommRingCat.of k) K) σ
        (normOneEmbeddingCharacterRestriction k K Ω hsplit m) =
      normOneEmbeddingCharacterRestriction k K Ω hsplit
        (embeddingPermutationRepresentation k K Ω σ m) := by
  change characterLattice.galoisRepresentation k Ω
      (normOneCommGroupScheme (CommRingCat.of k) K) σ
      ((CommGroupScheme.baseChange (algebraBaseMap k Ω)).map
          (normOneιHom (CommRingCat.of k) K) ≫
        (separableEmbeddingCharacterEquiv k K Ω hsplit).symm m) =
    (CommGroupScheme.baseChange (algebraBaseMap k Ω)).map
        (normOneιHom (CommRingCat.of k) K) ≫
      (separableEmbeddingCharacterEquiv k K Ω hsplit).symm
        (embeddingPermutationRepresentation k K Ω σ m)
  rw [characterLattice.galoisRepresentation_precompose]
  congr 1
  apply (separableEmbeddingCharacterEquiv k K Ω hsplit).injective
  rw [separableEmbeddingCharacterEquiv_galoisRepresentation,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- Actual character Galois transport is the induced inverse-pullback action
on embedding functions modulo constants. -/
theorem normOneSeparableEmbeddingCharacterEquiv_galoisRepresentation
    (σ : Ω ≃ₐ[k] Ω) (χ : characterLattice N_Ω) :
    normOneSeparableEmbeddingCharacterEquiv k K Ω hsplit
        (characterLattice.galoisRepresentation k Ω
          (normOneCommGroupScheme (CommRingCat.of k) K) σ χ) =
      embeddingQuotientRepresentation k K Ω σ
        (normOneSeparableEmbeddingCharacterEquiv k K Ω hsplit χ) := by
  obtain ⟨m, rfl⟩ := normOneEmbeddingCharacterRestriction_surjective k K Ω hsplit χ
  rw [galoisRepresentation_normOneEmbeddingCharacterRestriction,
    normOneSeparableEmbeddingCharacterEquiv_restriction,
    normOneSeparableEmbeddingCharacterEquiv_restriction,
    embeddingQuotientRepresentation_mk]

/-- The character coordinate equivalence intertwines the full ordinary representations. -/
theorem normOneSeparableEmbeddingCharacterEquiv_equivariant
    (σ : Ω ≃ₐ[k] Ω) (χ : characterLattice N_Ω) :
    normOneSeparableEmbeddingCharacterEquiv k K Ω hsplit
        (characterLattice.galoisRepresentation k Ω
          (normOneCommGroupScheme (CommRingCat.of k) K) σ χ) =
      embeddingQuotientRepresentation k K Ω σ
        (normOneSeparableEmbeddingCharacterEquiv k K Ω hsplit χ) :=
  normOneSeparableEmbeddingCharacterEquiv_galoisRepresentation k K Ω hsplit σ χ

end Langlands.GroupScheme.WeilGm
