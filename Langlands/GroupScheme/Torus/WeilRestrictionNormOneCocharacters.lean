import Langlands.GroupScheme.Torus.KernelCocharacters
import Langlands.GroupScheme.Torus.WeilRestrictionNormOne
import Langlands.GroupScheme.Torus.WeilRestrictionSeparableNorm

/-! # Actual norm-one cocharacters in sum-zero embedding coordinates -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Algebra.SeparableTensor
open scoped CategoryTheory.MonObj

namespace Langlands.CommGroupScheme

variable {S S' : Scheme.{u}} (b : S' ⟶ S) {G H : CommGroupScheme S} (f : G ⟶ H)

/-- Base change of the actual commutative kernel is the actual kernel after base change. -/
def kernelBaseChangeIso :
    (baseChange b).obj (kernel f) ≅ kernel ((baseChange b).map f) where
  hom := Additive.ofMul (GroupScheme.kernelBaseChangeIso b (groupHom f)).hom
  inv := Additive.ofMul (GroupScheme.kernelBaseChangeIso b (groupHom f)).inv
  hom_inv_id := congrArg Additive.ofMul
    (GroupScheme.kernelBaseChangeIso b (groupHom f)).hom_inv_id
  inv_hom_id := congrArg Additive.ofMul
    (GroupScheme.kernelBaseChangeIso b (groupHom f)).inv_hom_id

@[reassoc (attr := simp)]
theorem kernelBaseChangeIso_hom_ι :
    (kernelBaseChangeIso b f).hom ≫ kernelι ((baseChange b).map f) =
      (baseChange b).map (kernelι f) :=
  congrArg Additive.ofMul (GroupScheme.kernelBaseChangeIso_hom_ι b (groupHom f))

end Langlands.CommGroupScheme

namespace Langlands.GroupScheme

section DescentNaturality

variable {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)
  {G H : GroupScheme B} (f : G ⟶ H)

/-- Changing the coefficient structure commutes with every base-changed actual morphism. -/
theorem descentPoint_comp_baseChange (U : Over S)
    (y : U ⟶ ((Over.pullback b).mapGrp.obj G).X) :
    descentPoint b a ha H U (y ≫ ((Over.pullback b).mapGrp.map f).hom.hom) =
      descentPoint b a ha G U y ≫ ((Over.pullback b).mapGrp.map f).hom.hom := by
  apply (baseChangePointsEquiv b H ((Over.map a).obj U)).injective
  rw [baseChangePointsEquiv_descentPoint, baseChangePointsEquiv_comp,
    baseChangePointsEquiv_comp, baseChangePointsEquiv_descentPoint, Category.assoc]

end DescentNaturality

namespace cocharacterLattice

section Naturality

variable {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)
  {G H : CommGroupScheme B} (f : G ⟶ H)

/-- Cocharacter transport commutes with postcomposition by an actual descended morphism. -/
theorem transport_postcompose
    (ν : cocharacterLattice ((CommGroupScheme.baseChange b).obj G)) :
    transport b a ha H (ν ≫ (CommGroupScheme.baseChange b).map f) =
      transport b a ha G ν ≫ (CommGroupScheme.baseChange b).map f := by
  apply CommGroupScheme.hom_ext_points
  intro U x
  apply descentPoint_injective b a ha H.toGrp U
  rw [comp_groupHom_comp]
  change descentPoint b a ha H.toGrp U
      (x ≫ (CommGroupScheme.groupHom
        (transport b a ha H (ν ≫ (CommGroupScheme.baseChange b).map f))).hom.hom) =
    descentPoint b a ha H.toGrp U
      ((x ≫ (CommGroupScheme.groupHom (transport b a ha G ν)).hom.hom) ≫
        ((Over.pullback b).mapGrp.map (CommGroupScheme.groupHom f)).hom.hom)
  rw [descentPoint_comp_baseChange, descentPoint_transport,
    descentPoint_transport, comp_groupHom_comp]
  rfl

end Naturality

/-- The ordinary Galois action commutes with every base-changed actual morphism. -/
theorem galoisRepresentation_postcompose
    (k Ω : Type u) [CommRing k] [CommRing Ω] [Algebra k Ω]
    {G H : CommGroupScheme (Spec (CommRingCat.of k))} (f : G ⟶ H)
    (σ : Ω ≃ₐ[k] Ω)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj G)) :
    galoisRepresentation k Ω H σ
        (ν ≫ (CommGroupScheme.baseChange (algebraBaseMap k Ω)).map f) =
      galoisRepresentation k Ω G σ ν ≫
        (CommGroupScheme.baseChange (algebraBaseMap k Ω)).map f :=
  transport_postcompose (algebraBaseMap k Ω) (galoisBaseMap k Ω σ)
    (galoisBaseMap_over k Ω σ) f ν

end cocharacterLattice

end Langlands.GroupScheme

namespace Langlands.GroupScheme.cocharacterLattice

variable {k : Type u} [CommRing k] [IsDomain k]
  {G H : CommGroupScheme (Spec (CommRingCat.of k))}
  (f : G ⟶ H) (e : H ≅ Gm (Spec (CommRingCat.of k)))

/-- Vanishing of the actual composite is equivalent to vanishing of its integer pairing. -/
theorem comp_eq_zero_iff_pairing (ν : cocharacterLattice G) :
    ν ≫ f = 0 ↔ latticePairing G (f ≫ e.hom) ν = 0 := by
  rw [latticePairing_apply, ← Category.assoc]
  constructor
  · intro h
    simp [h]
  · intro h
    apply (cancel_mono e.hom).mp
    apply (gmEndEquiv k).injective
    simpa using h

/-- Cocharacters of the actual kernel form the kernel of the intrinsic integer pairing,
allowing a canonical identification of the target with the multiplicative group. -/
def kernelPairingEquiv :
    cocharacterLattice (CommGroupScheme.kernel f) ≃+
      (latticePairing G (f ≫ e.hom)).toAddMonoidHom.ker where
  toFun ν := ⟨ν ≫ CommGroupScheme.kernelι f,
    (comp_eq_zero_iff_pairing f e _).mp (by simp)⟩
  invFun ν := CommGroupScheme.kernelLift f ν.val
    ((comp_eq_zero_iff_pairing f e ν.val).mpr ν.property)
  left_inv ν := CommGroupScheme.kernel_hom_ext f
    (CommGroupScheme.kernelLift_ι f _ _)
  right_inv ν := Subtype.ext (CommGroupScheme.kernelLift_ι f _ _)
  map_add' ν ν' := Subtype.ext (Preadditive.add_comp _ _ _ _ _ _)

@[simp] theorem kernelPairingEquiv_val
    (ν : cocharacterLattice (CommGroupScheme.kernel f)) :
    (kernelPairingEquiv f e ν).val = ν ≫ CommGroupScheme.kernelι f := rfl

end Langlands.GroupScheme.cocharacterLattice

namespace Langlands.GroupScheme.WeilGm

variable (k K Ω : Type u) [Field k] [Field K] [Field Ω]
  [Algebra k K] [Algebra k Ω] [FiniteDimensional k K] [Algebra.IsSeparable k K]
  (hsplit : ∀ x : K, ((minpoly k x).map (algebraMap k Ω)).Splits)

local notation "W_Ω" =>
  (Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k Ω))
    (commGroupScheme (CommRingCat.of k) K))

local notation "N_Ω" =>
  (Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k Ω))
    (normOneCommGroupScheme (CommRingCat.of k) K))

/-- The intrinsic norm kernel comparison on actual base-changed cocharacters. -/
def normOneCocharacterNormKernelEquiv :
    cocharacterLattice N_Ω ≃+
      (separableEmbeddingNormAugmentation k K Ω).toAddMonoidHom.ker :=
  (cocharacterLattice.congr
    (CommGroupScheme.kernelBaseChangeIso (algebraBaseMap k Ω)
      (normHom (CommRingCat.of k) K))).trans
    (cocharacterLattice.kernelPairingEquiv
      ((CommGroupScheme.baseChange (algebraBaseMap k Ω)).map
        (normHom (CommRingCat.of k) K))
      (Gm.commBaseChangeIso (algebraBaseMap k Ω)))

omit [Algebra.IsSeparable k K] in
/-- The comparison sends an actual cocharacter to its actual composite with inclusion. -/
@[simp] theorem normOneCocharacterNormKernelEquiv_val (ν : cocharacterLattice N_Ω) :
    (normOneCocharacterNormKernelEquiv k K Ω ν).val =
      ν ≫ (CommGroupScheme.baseChange (algebraBaseMap k Ω)).map
        (normOneιHom (CommRingCat.of k) K) := by
  change (ν ≫ (CommGroupScheme.kernelBaseChangeIso (algebraBaseMap k Ω)
    (normHom (CommRingCat.of k) K)).hom) ≫
      CommGroupScheme.kernelι ((CommGroupScheme.baseChange (algebraBaseMap k Ω)).map
        (normHom (CommRingCat.of k) K)) = _
  rw [Category.assoc, CommGroupScheme.kernelBaseChangeIso_hom_ι]
  rfl

/-- The sum of integer embedding coordinates as an additive homomorphism. -/
def embeddingCoordinateSum : ((K →ₐ[k] Ω) → ℤ) →+ ℤ where
  toFun m := ∑ τ, m τ
  map_zero' := by simp
  map_add' m n := by simp [Finset.sum_add_distrib]

omit [Algebra.IsSeparable k K] in
/-- Permuting embedding coordinates preserves their sum. -/
theorem embeddingCoordinateSum_permutation (σ : Ω ≃ₐ[k] Ω)
    (m : (K →ₐ[k] Ω) → ℤ) :
    embeddingCoordinateSum k K Ω (embeddingPermutationRepresentation k K Ω σ m) =
      embeddingCoordinateSum k K Ω m :=
  (embeddingPermutation k K Ω σ).symm.sum_comp m

/-- The inverse-pullback permutation action restricted to the sum-zero submodule. -/
def embeddingSumZeroRepresentation :
    Representation ℤ (Ω ≃ₐ[k] Ω) (embeddingCoordinateSum k K Ω).ker :=
  (embeddingPermutationRepresentation k K Ω).subrepresentation
    (embeddingCoordinateSum k K Ω).toIntLinearMap.ker (fun σ m hm => by
      change embeddingCoordinateSum k K Ω
        (embeddingPermutationRepresentation k K Ω σ m) = 0
      rw [embeddingCoordinateSum_permutation]
      exact hm)

omit [Algebra.IsSeparable k K] in
@[simp] theorem embeddingSumZeroRepresentation_val (σ : Ω ≃ₐ[k] Ω)
    (m : (embeddingCoordinateSum k K Ω).ker) :
    (embeddingSumZeroRepresentation k K Ω σ m).val =
      embeddingPermutationRepresentation k K Ω σ m.val := rfl

/-- Norm-zero cocharacters are exactly the sum-zero embedding functions. -/
def normKernelEmbeddingEquiv :
    (separableEmbeddingNormAugmentation k K Ω).toAddMonoidHom.ker ≃+
      (embeddingCoordinateSum k K Ω).ker where
  toFun ν := ⟨separableEmbeddingCocharacterEquiv k K Ω hsplit ν.val, by
    change (∑ τ, separableEmbeddingCocharacterEquiv k K Ω hsplit ν.val τ) = 0
    rw [← separableEmbeddingNormAugmentation_eq_sum k K Ω hsplit]
    exact ν.property⟩
  invFun m := ⟨(separableEmbeddingCocharacterEquiv k K Ω hsplit).symm m.val, by
    change separableEmbeddingNormAugmentation k K Ω _ = 0
    rw [separableEmbeddingNormAugmentation_eq_sum k K Ω hsplit,
      AddEquiv.apply_symm_apply]
    exact m.property⟩
  left_inv ν := Subtype.ext
    ((separableEmbeddingCocharacterEquiv k K Ω hsplit).symm_apply_apply ν.val)
  right_inv m := Subtype.ext
    ((separableEmbeddingCocharacterEquiv k K Ω hsplit).apply_symm_apply m.val)
  map_add' ν ν' := Subtype.ext
    ((separableEmbeddingCocharacterEquiv k K Ω hsplit).map_add ν.val ν'.val)

/-- Cocharacters of the actual norm-one torus are the sum-zero embedding functions. -/
def normOneSeparableEmbeddingCocharacterEquiv :
    cocharacterLattice N_Ω ≃+ (embeddingCoordinateSum k K Ω).ker :=
  (normOneCocharacterNormKernelEquiv k K Ω).trans
    (normKernelEmbeddingEquiv k K Ω hsplit)

/-- The coordinates of an actual norm-one cocharacter are those of its inclusion composite. -/
@[simp] theorem normOneSeparableEmbeddingCocharacterEquiv_val
    (ν : cocharacterLattice N_Ω) :
    (normOneSeparableEmbeddingCocharacterEquiv k K Ω hsplit ν).val =
      separableEmbeddingCocharacterEquiv k K Ω hsplit
        (ν ≫ (CommGroupScheme.baseChange (algebraBaseMap k Ω)).map
          (normOneιHom (CommRingCat.of k) K)) := by
  change separableEmbeddingCocharacterEquiv k K Ω hsplit
    (normOneCocharacterNormKernelEquiv k K Ω ν).val = _
  rw [normOneCocharacterNormKernelEquiv_val]

/-- The actual norm-one action becomes inverse pullback on its sum-zero coordinates. -/
theorem normOneSeparableEmbeddingCocharacterEquiv_galoisRepresentation
    (σ : Ω ≃ₐ[k] Ω) (ν : cocharacterLattice N_Ω) :
    (normOneSeparableEmbeddingCocharacterEquiv k K Ω hsplit
      (cocharacterLattice.galoisRepresentation k Ω
        (normOneCommGroupScheme (CommRingCat.of k) K) σ ν)).val =
      embeddingPermutationRepresentation k K Ω σ
        (normOneSeparableEmbeddingCocharacterEquiv k K Ω hsplit ν).val := by
  rw [normOneSeparableEmbeddingCocharacterEquiv_val,
    ← cocharacterLattice.galoisRepresentation_postcompose,
    separableEmbeddingCocharacterEquiv_galoisRepresentation,
    normOneSeparableEmbeddingCocharacterEquiv_val]

/-- The sum-zero comparison intertwines the full restricted representation. -/
theorem normOneSeparableEmbeddingCocharacterEquiv_equivariant
    (σ : Ω ≃ₐ[k] Ω) (ν : cocharacterLattice N_Ω) :
    normOneSeparableEmbeddingCocharacterEquiv k K Ω hsplit
      (cocharacterLattice.galoisRepresentation k Ω
        (normOneCommGroupScheme (CommRingCat.of k) K) σ ν) =
      embeddingSumZeroRepresentation k K Ω σ
        (normOneSeparableEmbeddingCocharacterEquiv k K Ω hsplit ν) :=
  Subtype.ext
    (normOneSeparableEmbeddingCocharacterEquiv_galoisRepresentation k K Ω hsplit σ ν)

/-- In the inverse comparison, composition with the actual inclusion gives the ambient
cocharacter with exactly the prescribed embedding coordinates. -/
theorem normOneSeparableEmbeddingCocharacterEquiv_symm_ι
    (m : (embeddingCoordinateSum k K Ω).ker) :
    (normOneSeparableEmbeddingCocharacterEquiv k K Ω hsplit).symm m ≫
        (CommGroupScheme.baseChange (algebraBaseMap k Ω)).map
          (normOneιHom (CommRingCat.of k) K) =
      (separableEmbeddingCocharacterEquiv k K Ω hsplit).symm m.val := by
  apply (separableEmbeddingCocharacterEquiv k K Ω hsplit).injective
  rw [← normOneSeparableEmbeddingCocharacterEquiv_val,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

set_option maxRecDepth 4000 in
/-- On every test scheme, a sum-zero vector gives powers in the actual included coordinates. -/
theorem normOneSeparableEmbeddingCocharacterEquiv_symm_points
    (m : (embeddingCoordinateSum k K Ω).ker)
    (T : Over (Spec (CommRingCat.of Ω)))
    (x : T ⟶ (Gm (Spec (CommRingCat.of Ω))).X) :
    embeddingPointsEquiv k K Ω (Langlands.Algebra.SeparableTensor.embeddingEvaluationStatement
      k K Ω hsplit) T
      ((x ≫ (CommGroupScheme.groupHom
        ((normOneSeparableEmbeddingCocharacterEquiv k K Ω hsplit).symm m)).hom.hom) ≫
          (CommGroupScheme.groupHom
            ((CommGroupScheme.baseChange (algebraBaseMap k Ω)).map
              (normOneιHom (CommRingCat.of k) K))).hom.hom) =
      fun τ => Gm.pointsEquiv _ T x ^ m.val τ := by
  rw [← comp_groupHom_comp, normOneSeparableEmbeddingCocharacterEquiv_symm_ι]
  dsimp only [separableEmbeddingCocharacterEquiv]
  apply embeddingCocharacterEquiv_symm_points

end Langlands.GroupScheme.WeilGm
