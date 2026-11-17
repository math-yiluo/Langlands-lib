import Langlands.AlgebraicGeometry.Modules.FaithfullyFlatHomDescent
import Langlands.AlgebraicGeometry.Modules.SectionVanishingTransportProof
import Langlands.AlgebraicGeometry.Modules.SectionPullbackBridge

/-! # Descent of actual sections along affine flat surjections -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Modules

variable {X Y : Scheme.{u}} (p : X ⟶ Y) (M : Y.Modules)

/-- Actual section pullback is additive. -/
def pullbackSectionAddHom :
    GlobalSections M →+ GlobalSections ((Scheme.Modules.pullback p).obj M) :=
  (Langlands.Scheme.Modules.sectionPullback p M ⊤).toAddMonoidHom

@[simp]
lemma pullbackSectionAddHom_apply (s : GlobalSections M) :
    pullbackSectionAddHom p M s = pullbackSection p M s :=
  (pullbackSection_eq_sectionPullback p M s).symm

/-- A flat surjection detects equality of actual global sections, even without
quasi-coherence. -/
lemma pullbackSection_injective [Flat p] [Surjective p] :
    Function.Injective (pullbackSection p M) := by
  intro s t h
  apply sectionHom_injective
  have := faithful_pullback_of_flat_surjective p
  apply (Scheme.Modules.pullback p).map_injective
  have H := congrArg (sectionHom ((Scheme.Modules.pullback p).obj M)) h
  simpa only [sectionHom_pullbackSection, pullbackSectionHom, cancel_epi] using H

/-- Compatibility of a cover section with the actual equal-composite module
comparisons, on every scheme test. -/
def PullbackSectionCompatible
    (s : GlobalSections ((Scheme.Modules.pullback p).obj M)) : Prop :=
  ∀ (U : Scheme.{u}) (a b : U ⟶ X) (h : a ≫ p = b ≫ p),
    (equalCompositeIso p a b h M).hom.app ⊤
        (pullbackSection a ((Scheme.Modules.pullback p).obj M) s) =
      pullbackSection b ((Scheme.Modules.pullback p).obj M) s

/-- The canonical overlap comparison respects the actual unit trivializations. -/
lemma equalCompositeIso_unit (U : Scheme.{u}) (a b : U ⟶ X)
    (h : a ≫ p = b ≫ p) :
    (equalCompositeIso p a b h (structureModule Y)).hom ≫
        (Scheme.Modules.pullback b).map (pullbackUnitIso p).hom ≫
        (pullbackUnitIso b).hom =
      (Scheme.Modules.pullback a).map (pullbackUnitIso p).hom ≫
        (pullbackUnitIso a).hom := by
  have H := congrArg Iso.hom (equalCompositeUnitAut_pullbackUnitIso p a b h)
  rw [equalCompositeUnitAut_hom, Iso.refl_hom] at H
  rw [← cancel_epi ((pullbackUnitIso a).inv ≫
    (Scheme.Modules.pullback a).map (pullbackUnitIso p).inv)]
  simpa only [structureModule, Category.assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_assoc, Category.comp_id] using H

/-- A compatible actual section defines a compatible morphism from the
pullback of the unit sheaf. -/
lemma compatible_sectionHom
    (s : GlobalSections ((Scheme.Modules.pullback p).obj M))
    (hs : PullbackSectionCompatible p M s) :
    PullbackHomCompatible p
      ((pullbackUnitIso p).hom ≫ sectionHom ((Scheme.Modules.pullback p).obj M) s) := by
  intro U a b h
  have H := congrArg (sectionHom ((Scheme.Modules.pullback b).obj
    ((Scheme.Modules.pullback p).obj M))) (hs U a b h)
  rw [sectionHom_naturality, sectionHom_pullbackSection,
    sectionHom_pullbackSection] at H
  simp only [pullbackSectionHom] at H
  simp only [Functor.map_comp, Category.assoc]
  let P := (Scheme.Modules.pullback a).map (pullbackUnitIso p).hom ≫
    (pullbackUnitIso a).hom
  calc
    _ = P ≫ (((pullbackUnitIso a).inv ≫
        (Scheme.Modules.pullback a).map
          (sectionHom ((Scheme.Modules.pullback p).obj M) s)) ≫
        (equalCompositeIso p a b h M).hom) := by
      simp [P]
    _ = P ≫ ((pullbackUnitIso b).inv ≫
        (Scheme.Modules.pullback b).map
          (sectionHom ((Scheme.Modules.pullback p).obj M) s)) := by rw [H]
    _ = _ := by
      rw [show P = (equalCompositeIso p a b h (structureModule Y)).hom ≫
          (Scheme.Modules.pullback b).map (pullbackUnitIso p).hom ≫
          (pullbackUnitIso b).hom from (equalCompositeIso_unit p U a b h).symm]
      simp [structureModule]

/-- A compatible actual section of the pullback of a quasi-coherent module
descends uniquely along an affine flat surjection. -/
lemma existsUnique_section_of_compatible [IsAffineHom p] [Flat p] [Surjective p]
    [M.IsQuasicoherent]
    (s : GlobalSections ((Scheme.Modules.pullback p).obj M))
    (hs : PullbackSectionCompatible p M s) :
    ∃! t : GlobalSections M, pullbackSection p M t = s := by
  obtain ⟨f, hf, -⟩ := FaithfullyFlatHomDescent.existsUnique_hom p
    ((pullbackUnitIso p).hom ≫ sectionHom ((Scheme.Modules.pullback p).obj M) s)
    (compatible_sectionHom p M s hs)
  let t := (sectionHomEquiv M).symm f
  have ht : sectionHom M t = f := (sectionHomEquiv M).apply_symm_apply f
  refine ⟨t, ?_, fun t' ht' => pullbackSection_injective p M (ht'.trans ?_)⟩
  all_goals
    apply sectionHom_injective
    rw [sectionHom_pullbackSection, pullbackSectionHom, ht, hf]
    simp

/-- Choose the unique descended actual section from its cover section and
the genuine overlap equations. -/
def sectionOfCompatible [IsAffineHom p] [Flat p] [Surjective p]
    [M.IsQuasicoherent]
    (s : GlobalSections ((Scheme.Modules.pullback p).obj M))
    (hs : PullbackSectionCompatible p M s) : GlobalSections M :=
  (existsUnique_section_of_compatible p M s hs).choose

@[simp]
lemma pullbackSection_sectionOfCompatible [IsAffineHom p] [Flat p] [Surjective p]
    [M.IsQuasicoherent]
    (s : GlobalSections ((Scheme.Modules.pullback p).obj M))
    (hs : PullbackSectionCompatible p M s) :
    pullbackSection p M (sectionOfCompatible p M s hs) = s :=
  (existsUnique_section_of_compatible p M s hs).choose_spec.1

end Langlands.AlgebraicGeometry.Modules
