import Langlands.GroupScheme.Rational.OrthogonalOrbitSpecialLinear
import Langlands.GroupScheme.Rational.NegativeRootPartner
import Langlands.GroupScheme.Rational.DerivedCoverNormalizerLift
import Langlands.Geometry.Building.NormalizerPointsRingEquiv
import Langlands.GroupScheme.SpecialLinearBinaryBigCell
import Langlands.GroupScheme.Rational.A2OrbitTorusPart

/-! # The Weyl element of the descended `SL₂` normalizes the torus -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open SpecialLinear.BinaryPresentation

/-- The word `lower (-1) * upper 1 * lower (-1)` times the Weyl matrix is the identity. -/
theorem weylWord_mul_weylMatrix {A : Type u} [Field A] :
    (lower (-1) * upper 1 * lower (-1) : Matrix.SpecialLinearGroup (Fin 2) A) *
      SpecialLinear.BinaryUpper.weylMatrix = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinear.BinaryUpper.weylMatrix, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.one_apply]

/-- The inverse Weyl matrix is the word `lower (-1) * upper 1 * lower (-1)`. -/
theorem weylMatrix_inv_eq {A : Type u} [Field A] :
    (SpecialLinear.BinaryUpper.weylMatrix : Matrix.SpecialLinearGroup (Fin 2) A)⁻¹ =
      lower (-1) * upper 1 * lower (-1) :=
  (eq_inv_of_mul_eq_one_left weylWord_mul_weylMatrix).symm

/-- The Weyl matrix has entries in the prime ring, so ring maps fix it. -/
theorem map_weylMatrix {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    Matrix.SpecialLinearGroup.map φ SpecialLinear.BinaryUpper.weylMatrix =
      SpecialLinear.BinaryUpper.weylMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinear.BinaryUpper.weylMatrix]

/-- A rational point normalizing a commutative subgroup `j` normalizes every maximal split
torus factoring through `j`: the conjugate of the torus stays in the commutative group, so
it commutes with the torus. -/
theorem IsMaximalSplitTorus.mem_normalizerPoints_of_mem_normalizerPoints
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))} (s : S.toGrp ⟶ T.toGrp)
    (j : T.toGrp ⟶ G) (hs : IsMaximalSplitTorus (s ≫ j)) {c : rationalPoints G}
    (hc : c ∈ normalizerPoints j) : c ∈ normalizerPoints (s ≫ j) := by
  obtain ⟨σ, hσ⟩ := hc
  apply hs.mem_normalizerPoints_of_commute_conjugate c
  intro U x y
  have h1 : (s ≫ j) ≫ (G.innerIso c).hom = (s ≫ CommGroupScheme.groupHom σ.hom) ≫ j := by
    rw [Category.assoc, hσ, Category.assoc]
  rw [h1, Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc]
  change (x ≫ (s ≫ CommGroupScheme.groupHom σ.hom).hom.hom) ≫ j.hom.hom *
      (y ≫ s.hom.hom) ≫ j.hom.hom =
    (y ≫ s.hom.hom) ≫ j.hom.hom * (x ≫ (s ≫ CommGroupScheme.groupHom σ.hom).hom.hom) ≫ j.hom.hom
  rw [← MonObj.mul_comp, ← MonObj.mul_comp, mul_comm]

namespace SplitPinning

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G}
  (x : p.NormalizedSimpleRootParametrizations)

/-- The rank-one homomorphism of a simple root sends the Weyl matrix into the normalizer of
the pinned torus. -/
theorem rootSL2_weylMatrix_mem (a : p.base.support) :
    rootSL2 x a SpecialLinear.BinaryUpper.weylMatrix ∈ normalizerPoints p.inclusion := by
  have h := ((x a).isOppositeFactorPair_unitPoint).2.2
  have hw : rootSL2 x a (SpecialLinear.BinaryUpper.weylMatrix)⁻¹ =
      (x a).negPoint (-1) * (x a).unitPoint * (x a).negPoint (-1) := by
    rw [weylMatrix_inv_eq, map_mul, map_mul, rootSL2_lower, rootSL2_upper]
    change (x a).negPoint (-1) * (x a).linked.xpPoint 1 * (x a).negPoint (-1) = _
    rw [(x a).xpPoint_linked]
    rfl
  have hinv : rootSL2 x a SpecialLinear.BinaryUpper.weylMatrix =
      ((x a).negPoint (-1) * (x a).unitPoint * (x a).negPoint (-1))⁻¹ := by
    rw [← hw, map_inv, inv_inv]
  rw [hinv]
  exact (normalizerPoints p.inclusion).inv_mem h

section Galois

open GaloisPointComparison

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G)

local instance simpleRootFiberWeylIsAffineHom :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable (p : Langlands.GroupScheme.SplitPinning
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (eT : p.torus ≅ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hT : p.inclusion = CommGroupScheme.groupHom eT.hom ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map i)
    (x : p.NormalizedSimpleRootParametrizations)
    {ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support}
    (hx : RootMapsGaloisCompatible k K p x ρ)
    (hroot : ∀ (σ : K ≃ₐ[k] K) (a : p.base.support),
      characterLattice.congr eT (p.rootDatum.root (ρ σ a)) =
        characterLattice.galoisRepresentation k K T σ
          (characterLattice.congr eT (p.rootDatum.root a)))
    (O : Set p.base.support) (hOs : ∀ (σ : K ≃ₐ[k] K) a, a ∈ O ↔ ρ σ a ∈ O)
    (hO : ∀ a ∈ O, ∀ b ∈ O, a ≠ b → p.rootDatum.IsOrthogonal a b)
    [Fintype O]

/-- The orbit product of Weyl matrices normalizes the pinned torus. -/
theorem orbitSL2_weylMatrix_mem :
    orbitSL2 k K p x O hO (fun _ => SpecialLinear.BinaryUpper.weylMatrix) ∈
      normalizerPoints p.inclusion := by
  rw [orbitSL2_apply, Langlands.Algebra.RankOneRelation.prodHom,
    Subgroup.noncommPiCoprod_apply]
  apply Subgroup.noncommProd_mem
  intro a _
  exact rootSL2_weylMatrix_mem x a

omit [Fintype O] in
include hT in
/-- A normalizer point of the pinning inclusion normalizes the scalar extension of `i`. -/
theorem mem_normalizerPoints_baseChange_of_pinning
    {n : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)}
    (hn : n ∈ normalizerPoints p.inclusion) :
    n ∈ normalizerPoints (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i) := by
  rw [hT] at hn
  have h := mem_normalizerPoints_groupHom_comp eT.symm _ hn
  have he : CommGroupScheme.groupHom eT.symm.hom ≫ CommGroupScheme.groupHom eT.hom =
      𝟙 _ := congrArg CommGroupScheme.groupHom eT.inv_hom_id
  rwa [← Category.assoc, he, Category.id_comp] at h

variable {E : Type u} [Field E] [Algebra k E] (τ : p.base.support → (E →ₐ[k] K))
  (hτ : ∀ (σ : K ≃ₐ[k] K) (a : p.base.support), a ∈ O → τ (ρ σ a) = σ.toAlgHom.comp (τ a))
  [FiniteDimensional k K] [IsGalois k K]

include hT hx hroot hOs hτ in
/-- The descended `SL₂(E)` sends the Weyl matrix into the normalizer of `i`. -/
theorem fieldSL2_weylMatrix_mem [Mono i.hom.hom.left] :
    fieldSL2 k K i p eT hT x hx hroot O hOs hO τ hτ SpecialLinear.BinaryUpper.weylMatrix ∈
      normalizerPoints i := by
  apply (mem_normalizerPoints_rationalExtend_iff (K := K) i _).mp
  rw [rationalExtend_fieldSL2]
  have hw : (fun a => Matrix.SpecialLinearGroup.map (τ a).toRingHom
      (SpecialLinear.BinaryUpper.weylMatrix : Matrix.SpecialLinearGroup (Fin 2) E)) =
      fun _ => SpecialLinear.BinaryUpper.weylMatrix := by
    funext a
    exact map_weylMatrix _
  rw [hw]
  exact mem_normalizerPoints_baseChange_of_pinning k K i p eT hT
    (orbitSL2_weylMatrix_mem k K p x O hO)

include hT hx hroot hOs hτ in
/-- The image of the Weyl matrix under the descended `SL₂(E)`, as a normalizer point of `i`. -/
def fieldSL2WeylPoint [Mono i.hom.hom.left] : normalizerPoints i :=
  ⟨fieldSL2 k K i p eT hT x hx hroot O hOs hO τ hτ SpecialLinear.BinaryUpper.weylMatrix,
    fieldSL2_weylMatrix_mem k K i p eT hT x hx hroot O hOs hO τ hτ⟩

theorem fieldSL2WeylPoint_coe [Mono i.hom.hom.left] :
    (fieldSL2WeylPoint k K i p eT hT x hx hroot O hOs hO τ hτ : rationalPoints G) =
      fieldSL2 k K i p eT hT x hx hroot O hOs hO τ hτ SpecialLinear.BinaryUpper.weylMatrix :=
  rfl

end Galois

end SplitPinning

end Langlands.GroupScheme
