import Langlands.Geometry.Building.Kottwitz.TorusCocharacterTower
import Langlands.GroupScheme.Torus.InducedBasisTransport
import Langlands.GroupScheme.Absolute.CocharacterAveraging
import Langlands.Geometry.Building.CocharacterUniformizerProof
import Langlands.GroupScheme.Torus.SplittingDescentHelpers

/-! # Permuted cocharacter bases of induced tori and rational points from equivariant units -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.GroupScheme.TorusPointsTensorGalois

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building.Kottwitz

namespace InducedCocharacterBasis

section Dual

variable {k E : Type u} [Field k] [Field E] [Algebra k E]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))
  (hE : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp)
  {J : Type u} [Finite J] [DecidableEq J]
  (b : Module.Basis J ℤ
    (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)))

/-- The cocharacter basis dual to a character basis of a split torus. -/
def dualBasis : Module.Basis J ℤ
    (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)) :=
  b.dualBasis.map (cocharacterDualEquiv _ hE).symm

theorem latticePairing_dualBasis (i j : J) :
    latticePairing _ (b i) (dualBasis T hE b j) = if i = j then 1 else 0 := by
  rw [← cocharacterDualEquiv_apply _ hE]
  simp only [dualBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
    Module.Basis.dualBasis_apply_self]

variable (hb : ∀ (σ : E ≃ₐ[k] E) (i : J), ∃ j,
  characterLattice.galoisRepresentation k E T σ (b i) = b j)

/-- The permutation of indices induced by the Galois action on the character basis. -/
abbrev indexHom : (E ≃ₐ[k] E) →* Equiv.Perm J :=
  Langlands.PermutationBasis.indexAction (characterLattice.galoisRepresentation k E T) b hb

omit [Finite J] [DecidableEq J] in
theorem galoisRepresentation_basis (σ : E ≃ₐ[k] E) (i : J) :
    characterLattice.galoisRepresentation k E T σ (b i) = b (indexHom T b hb σ i) :=
  Langlands.PermutationBasis.apply_basis _ b hb σ i

/-- The dual cocharacter basis is permuted in the same way. -/
theorem galoisRepresentation_dualBasis (σ : E ≃ₐ[k] E) (j : J) :
    cocharacterLattice.galoisRepresentation k E T σ (dualBasis T hE b j) =
      dualBasis T hE b (indexHom T b hb σ j) := by
  apply (cocharacterDualEquiv _ hE).injective
  apply b.ext
  intro i
  rw [cocharacterDualEquiv_apply, cocharacterDualEquiv_apply,
    latticePairing_galoisRepresentation_right, galoisRepresentation_basis T b hb,
    latticePairing_dualBasis, latticePairing_dualBasis]
  have hiff : indexHom T b hb σ⁻¹ i = j ↔ i = indexHom T b hb σ j := by
    rw [map_inv]
    exact Equiv.Perm.inv_eq_iff_eq
  exact if_congr hiff rfl rfl

end Dual

section Geometric

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (E : IntermediateField F (SeparableClosure F)) [FiniteDimensional F E] [IsGalois F E]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) [IsAffine T.X.left]
  (hE : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap F E)).obj T).toGrp)
  {J : Type u} [Fintype J] [DecidableEq J]
  (b : Module.Basis J ℤ
    (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F E)).obj T)))
  (hb : ∀ (σ : E ≃ₐ[F] E) (i : J), ∃ j,
    characterLattice.galoisRepresentation F E T σ (b i) = b j)

omit [FiniteDimensional F E] [IsGalois F E] in
/-- The base uniformizer is a unit of `E` of infinite order. -/
theorem not_isOfFinOrder_uniformizer :
    ¬IsOfFinOrder (Units.map (algebraMap F E).toMonoidHom
      (SplitTorusValuation.uniformizerUnit F)) := by
  rw [(Units.map_injective (algebraMap F E).injective).isOfFinOrder_iff]
  intro h
  obtain ⟨n, hn, hpow⟩ :=
    isOfFinOrder_iff_pow_eq_one.mp ((Plancherel.fieldOrderUnits F).isOfFinOrder h)
  have h' := congrArg Multiplicative.toAdd hpow
  rw [toAdd_pow, SplitTorusValuation.fieldOrderUnits_uniformizerUnit, toAdd_one,
    nsmul_eq_mul, mul_one] at h'
  omega

include hE in
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F E] [IsGalois F E] [IsAffine T.X.left] in
/-- An induced torus split over `E` is split over `F^sep`. -/
theorem isSplit_sepClosure :
    IsSplitTorus ((CommGroupScheme.baseChange
      (algebraBaseMap F (SeparableClosure F))).obj T).toGrp :=
  IsSplitTorus.baseChange_fieldTower F E (SeparableClosure F) T.toGrp hE

/-- The geometric cocharacter basis extended from `E`. -/
def geometricBasis : Module.Basis J ℤ (geometricCocharacters F (SeparableClosure F) T) :=
  (dualBasis T hE b).map
    (LinearEquiv.ofBijective
      (extendGeometricCocharacters F E (SeparableClosure F) T).toIntLinearMap
      (extendGeometricCocharacters_bijective F E (SeparableClosure F) T hE))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F E] [IsGalois F E] [IsAffine T.X.left] in
theorem geometricBasis_apply (j : J) :
    geometricBasis F E T hE b j =
      extendGeometricCocharacters F E (SeparableClosure F) T (dualBasis T hE b j) := rfl

/-- The action of `Gal(F^sep/F)` on the indices, through `Gal(E/F)`. -/
def galoisIndexHom : (SeparableClosure F ≃ₐ[F] SeparableClosure F) →* Equiv.Perm J :=
  (indexHom T b hb).comp (AlgEquiv.restrictNormalHom E)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F E] [IsAffine T.X.left] [Fintype J] [DecidableEq J] in
theorem galoisIndexHom_apply (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (j : J) :
    galoisIndexHom F E T b hb σ j = indexHom T b hb (σ.restrictNormal E) j := rfl

omit [FiniteDimensional F E] in
/-- `Gal(F^sep/F)` permutes the geometric cocharacter basis. -/
theorem galoisRepresentation_geometricBasis
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (j : J) :
    cocharacterLattice.galoisRepresentation F (SeparableClosure F) T σ
        (geometricBasis F E T hE b j) =
      geometricBasis F E T hE b (galoisIndexHom F E T b hb σ j) := by
  rw [geometricBasis_apply, geometricBasis_apply, galoisIndexHom_apply,
    ← galoisRepresentation_dualBasis T hE b hb]
  exact (extendGeometricCocharacters_galois F E (SeparableClosure F) T
    (isSplit_sepClosure F E T hE) (not_isOfFinOrder_uniformizer F E)
    (σ.restrictNormal E) σ (fun a => (AlgEquiv.restrictNormal_commutes σ E a).symm)
    (dualBasis T hE b j)).symm

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A `Gal(E/F)`-equivariant family of units in `E` is the cocharacter expansion of the
extension of a rational point. -/
theorem exists_rationalPoint (x : J → Eˣ)
    (hx : ∀ (σ : E ≃ₐ[F] E) (j : J),
      x (indexHom T b hb σ j) = Units.map σ.toMonoidHom (x j)) :
    ∃ t : rationalPoints T.toGrp,
      GaloisPoint.extend F E T.toGrp (rationalCoeffEquiv F T.toGrp t) =
        (coefficientEvaluation F E T
          (∑ j, Additive.ofMul (x j) ⊗ₜ[ULift.{u} ℤ] dualBasis T hE b j)).toMul := by
  set z := ∑ j, Additive.ofMul (x j) ⊗ₜ[ULift.{u} ℤ] dualBasis T hE b j with hz
  have hfix : (coefficientEvaluation F E T z).toMul ∈ GaloisPoint.fixedSubgroup F E T.toGrp := by
    intro σ
    apply Additive.ofMul.injective
    change (GaloisPoint.conjugate F E T.toGrp σ).toAdditive (coefficientEvaluation F E T z) =
      coefficientEvaluation F E T z
    rw [hz, map_sum, map_sum]
    have hterm : ∀ j, (GaloisPoint.conjugate F E T.toGrp σ).toAdditive
        (coefficientEvaluation F E T
          (Additive.ofMul (x j) ⊗ₜ[ULift.{u} ℤ] dualBasis T hE b j)) =
        coefficientEvaluation F E T (Additive.ofMul (x (indexHom T b hb σ j)) ⊗ₜ[ULift.{u} ℤ]
          dualBasis T hE b (indexHom T b hb σ j)) := by
      intro j
      rw [hx, ← galoisRepresentation_dualBasis T hE b hb]
      exact (coefficientEvaluation_galois_tmul F E T σ (Additive.ofMul (x j))
        (dualBasis T hE b j)).symm
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    exact Equiv.sum_comp (indexHom T b hb σ)
      (fun j => coefficientEvaluation F E T
        (Additive.ofMul (x j) ⊗ₜ[ULift.{u} ℤ] dualBasis T hE b j))
  obtain ⟨x0, hx0⟩ :=
    (GaloisPoint.mem_range_extend_iff F E T.toGrp _).mpr hfix
  refine ⟨(rationalCoeffEquiv F T.toGrp).symm x0, ?_⟩
  rw [MulEquiv.apply_symm_apply]
  exact hx0

end Geometric

end InducedCocharacterBasis

end Langlands.Geometry.Building.Kottwitz
