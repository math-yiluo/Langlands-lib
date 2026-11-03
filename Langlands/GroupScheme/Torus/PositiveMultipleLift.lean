import Langlands.GroupScheme.Rational.IndependentStandardCocharacter
import Langlands.GroupScheme.Rational.NormalizerParabolicPoints
import Langlands.GroupScheme.Rational.RelativeRank
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.LinearAlgebra.RationalFiniteIndex
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Positive multiple lifts of actual cocharacters along split-torus epimorphisms -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Epimorphisms of group schemes give injective restriction on actual characters. -/
theorem characterRestrict_injective_of_epi {S : Scheme.{u}} {G H : GroupScheme S}
    (f : H ⟶ G) [Epi f] : Function.Injective (characterRestrict f) := by
  intro χ ψ h
  exact congrArg Additive.ofMul ((cancel_epi f).mp (congrArg Additive.toMul h))

variable {k : Type u} [Field k]
    {T U : CommGroupScheme (Spec (CommRingCat.of k))}

private def cocharacterPairingFunctional (ν : cocharacterLattice U) :
    (ℚ ⊗[ℤ] characterLattice U) →ₗ[ℚ] ℚ :=
  (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).toLinearMap.comp
    (((latticePairing U).flip ν).baseChange ℚ)

private theorem cocharacterPairingFunctional_toRat (ν : cocharacterLattice U)
    (α : characterLattice U) :
    cocharacterPairingFunctional ν (toRat α) = (latticePairing U α ν : ℚ) := by
  simp [cocharacterPairingFunctional, toRat, zsmul_eq_mul]

/-- Every actual cocharacter of the target of an epimorphism of split tori
has a positive integral multiple lifting to an actual cocharacter of the source. -/
theorem IsSplitTorus.exists_positive_multiple_cocharacter_lift
    (hT : IsSplitTorus T.toGrp) (hU : IsSplitTorus U.toGrp)
    (p : T ⟶ U) [Epi (CommGroupScheme.groupHom p)] (ν' : cocharacterLattice U) :
    ∃ d : ℤ, 0 < d ∧ ∃ ν : cocharacterLattice T, ν ≫ p = d • ν' := by
  have hinj : Function.Injective (rationalCharacterRestrictRat (CommGroupScheme.groupHom p)) :=
    rationalization_injective (characterRestrict (CommGroupScheme.groupHom p))
      (characterRestrict_injective_of_epi _)
  obtain ⟨F, hF⟩ := LinearMap.dualMap_surjective_of_injective hinj
    (cocharacterPairingFunctional ν')
  obtain ⟨d, hd, ν, hν⟩ := hT.exists_positive_multiple_pairing F
  refine ⟨d, hd, ν, ?_⟩
  have hpair (α : characterLattice U) :
      latticePairing U α (ν ≫ p) = latticePairing U α (d • ν') := by
    have hFα := congrArg
      (fun f : (ℚ ⊗[ℤ] characterLattice U) →ₗ[ℚ] ℚ => f (toRat α)) hF
    change F (rationalCharacterRestrictRat (CommGroupScheme.groupHom p) (toRat α)) =
      cocharacterPairingFunctional ν' (toRat α) at hFα
    rw [rationalCharacterRestrictRat_toRat, cocharacterPairingFunctional_toRat] at hFα
    have hv := hν (p ≫ α)
    change (latticePairing T (p ≫ α) ν : ℚ) =
      (d : ℚ) * F (toRat (characterRestrict (CommGroupScheme.groupHom p) α)) at hv
    rw [hFα] at hv
    have hnat : latticePairing T (p ≫ α) ν = latticePairing U α (ν ≫ p) := by
      simp only [latticePairing_apply, Category.assoc]
    rw [hnat] at hv
    rw [map_zsmul, zsmul_eq_mul]
    exact_mod_cast hv
  apply sub_eq_zero.mp
  apply hU.cocharacter_eq_zero
  intro α
  rw [map_sub, hpair, sub_self]

/-- An actual lift of a positive multiple of a cocharacter, retaining the
multiplier and its strict positivity. -/
structure PositiveMultipleCocharacterLift (p : T ⟶ U) (ν' : cocharacterLattice U) where
  multiplier : ℤ
  positive : 0 < multiplier
  cocharacter : cocharacterLattice T
  comp_eq : cocharacter ≫ p = multiplier • ν'

/-- Choose a positive-multiple lift along an actual epimorphism of split tori. -/
def IsSplitTorus.positiveMultipleCocharacterLift
    (hT : IsSplitTorus T.toGrp) (hU : IsSplitTorus U.toGrp)
    (p : T ⟶ U) [Epi (CommGroupScheme.groupHom p)] (ν' : cocharacterLattice U) :
    PositiveMultipleCocharacterLift p ν' := by
  let h := hT.exists_positive_multiple_cocharacter_lift hU p ν'
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.choose, h.choose_spec.2.choose_spec⟩

/-- The lifted equality is also equality of the actual underlying group-scheme
homomorphisms. -/
theorem PositiveMultipleCocharacterLift.groupHom_comp {p : T ⟶ U}
    {ν' : cocharacterLattice U} (L : PositiveMultipleCocharacterLift p ν') :
    CommGroupScheme.groupHom L.cocharacter ≫ CommGroupScheme.groupHom p =
      CommGroupScheme.groupHom (L.multiplier • ν') :=
  congrArg CommGroupScheme.groupHom L.comp_eq

/-- In particular, flat surjective maps of split tori have positive-multiple
lifts; neither finiteness nor surjectivity on rational points is required. -/
theorem IsSplitTorus.exists_positive_multiple_cocharacter_lift_of_flat_surjective
    (hT : IsSplitTorus T.toGrp) (hU : IsSplitTorus U.toGrp) (p : T ⟶ U)
    [Flat (CommGroupScheme.hom p)] [Surjective (CommGroupScheme.hom p)]
    (ν' : cocharacterLattice U) :
    ∃ d : ℤ, 0 < d ∧ ∃ ν : cocharacterLattice T, ν ≫ p = d • ν' := by
  have : IsAffineHom T.X.hom := hT.isAffineHom
  have : IsAffineHom U.X.hom := hU.isAffineHom
  have : IsAffine T.X.left := isAffine_of_isAffineHom T.X.hom
  have : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom
  have : Epi (CommGroupScheme.groupHom p).hom.hom := Over.epi_of_epi_left _
  have : Epi (CommGroupScheme.groupHom p) :=
    (Grp.forget (Over (Spec (CommRingCat.of k)))).epi_of_epi_map
      (inferInstanceAs (Epi (CommGroupScheme.groupHom p).hom.hom))
  exact hT.exists_positive_multiple_cocharacter_lift hU p ν'

end Langlands.GroupScheme
