import Mathlib.Algebra.Category.Ring.Adjunctions
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.Topology.Sheaves.LocallySurjective

/-! # Actual unit sheaves and reduction through nilpotent closed immersions -/

universe u v

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.NilpotentUnitReduction

section Rings

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]

/-- Units lift through a surjective ring map with nilpotent kernel. -/
lemma unitsMap_surjective (f : R →+* S) (hf : Function.Surjective f)
    (hker : IsNilpotent (RingHom.ker f)) :
    Function.Surjective (Units.map f.toMonoidHom) := by
  intro s
  obtain ⟨r, hr⟩ := hf (s : S)
  have hq : IsUnit (Ideal.Quotient.mk (RingHom.ker f) r) := by
    simpa only [← hr, RingHom.coe_coe, RingEquiv.toRingHom_eq_coe,
      RingHom.quotientKerEquivOfSurjective_symm_apply] using
      s.isUnit.map (f.quotientKerEquivOfSurjective hf).symm.toRingHom
  have hu : IsUnit r := hker.isUnit_quotient_mk_iff.mp hq
  refine ⟨hu.unit, ?_⟩
  apply Units.ext
  change f (hu.unit : R) = (s : S)
  rw [hu.unit_spec, hr]

end Rings

/-- Actual units of a commutative ring, written additively. -/
abbrev ringUnitsFunctor : CommRingCat.{u} ⥤ AddCommGrpCat.{u} :=
  forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
    commGroupAddCommGroupEquivalence.functor

section Sheaves

variable {X : TopCat.{u}} {F G : X.Presheaf CommRingCat.{u}}

/-- The presheaf of actual units, with additive notation for its group law. -/
abbrev unitsPresheaf (F : X.Presheaf CommRingCat.{u}) :
    X.Presheaf AddCommGrpCat.{u} :=
  F ⋙ ringUnitsFunctor

/-- Taking actual units preserves the sheaf condition. -/
lemma unitsPresheaf_isSheaf (hF : TopCat.Presheaf.IsSheaf F) :
    TopCat.Presheaf.IsSheaf (unitsPresheaf F) :=
  CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf
    (Opens.grothendieckTopology X) F ringUnitsFunctor hF

/-- The abelian-group sheaf of actual units of a commutative-ring sheaf. -/
def unitsSheaf (F : X.Presheaf CommRingCat.{u}) (hF : TopCat.Presheaf.IsSheaf F) :
    X.Sheaf AddCommGrpCat.{u} :=
  ⟨unitsPresheaf F, unitsPresheaf_isSheaf hF⟩

/-- The actual sectionwise unit map induced by a morphism of ring sheaves. -/
def unitsSheafMap (η : F ⟶ G) (hF : TopCat.Presheaf.IsSheaf F)
    (hG : TopCat.Presheaf.IsSheaf G) :
    unitsSheaf F hF ⟶ unitsSheaf G hG :=
  ⟨Functor.whiskerRight η ringUnitsFunctor⟩

end Sheaves

section Schemes

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]

/-- The map on actual units from the structure sheaf to its actual pushforward. -/
def unitsReduction :
    unitsSheaf X.presheaf X.sheaf.property ⟶
      unitsSheaf ((Opens.map i.base).op ⋙ Y.presheaf)
        (TopCat.Sheaf.pushforward_sheaf_of_sheaf i.base Y.sheaf.property) :=
  unitsSheafMap i.c X.sheaf.property
    (TopCat.Sheaf.pushforward_sheaf_of_sheaf i.base Y.sheaf.property)

/-- Nilpotent ideal-sheaf data gives nilpotent actual kernels on affine opens. -/
lemma nilpotentKernel_app (hi : IsNilpotent i.ker) (U : X.Opens)
    (hU : IsAffineOpen U) : IsNilpotent (RingHom.ker (i.app U).hom) := by
  obtain ⟨n, hn⟩ := hi
  refine ⟨n, ?_⟩
  rw [← i.ker_apply ⟨U, hU⟩]
  change (i.ker ^ n).ideal ⟨U, hU⟩ = _
  rw [hn]
  rfl

/-- Actual unit reduction is surjective on each affine open. -/
lemma unitsReduction_app_surjective (hi : IsNilpotent i.ker) (U : X.Opens)
    (hU : IsAffineOpen U) :
    Function.Surjective ((unitsReduction i).hom.app (op U)) := by
  intro s
  obtain ⟨r, hr⟩ := unitsMap_surjective (i.app U).hom (i.app_surjective U hU)
    (nilpotentKernel_app i hi U hU) s.toMul
  exact ⟨Additive.ofMul r, congrArg Additive.ofMul hr⟩

/-- Actual unit reduction is locally surjective on all opens. -/
lemma unitsReduction_isLocallySurjective (hi : IsNilpotent i.ker) :
    TopCat.Presheaf.IsLocallySurjective (unitsReduction i).hom := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U s x hx
  obtain ⟨V, hV, hxV, hVU⟩ :=
    (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
  refine ⟨V, hVU, ?_, hxV⟩
  exact unitsReduction_app_surjective i hi V hV _

/-- Reduction is an epimorphism of the actual abelian-group sheaves of units. -/
lemma unitsReduction_epi (hi : IsNilpotent i.ker) : Epi (unitsReduction i) := by
  let : CategoryTheory.Sheaf.IsLocallySurjective (unitsReduction i) :=
    unitsReduction_isLocallySurjective i hi
  exact CategoryTheory.Sheaf.epi_of_isLocallySurjective _

end Schemes

end Langlands.AlgebraicGeometry.Picard.NilpotentUnitReduction
