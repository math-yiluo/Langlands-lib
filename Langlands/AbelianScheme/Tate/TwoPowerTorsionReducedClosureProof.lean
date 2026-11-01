import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal
import Langlands.AbelianScheme.Tate.TwoPowerTorsionReducedClosureStatement
import Langlands.AbelianScheme.Tate.TwoPowerTorsionClosureSubgroupProof

/-! # Scheme restrictions on the reduced actual torsion closure -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.Tate

universe u

open Scheme.IdealSheafData

private lemma vanishingIdeal_le_ker_of_range {X Y : Scheme.{u}} [IsReduced X]
    (Z : TopologicalSpace.Closeds Y) (f : X ⟶ Y) (hf : Set.range f ⊆ Z) :
    vanishingIdeal Z ≤ f.ker := by
  rw [← map_bot f, ← Scheme.nilradical_eq_bot (X := X), ← vanishingIdeal_top,
    map_vanishingIdeal]
  apply vanishingIdeal_antimono
  change closure (f '' Set.univ) ⊆ Z
  simpa only [Set.image_univ] using closure_minimal hf Z.isClosed

private lemma vanishingIdeal_le_map_of_image_eq {X : Scheme.{u}}
    (Z : TopologicalSpace.Closeds X) (f : X ⟶ X) (hf : f '' (Z : Set X) = Z) :
    vanishingIdeal Z ≤ (vanishingIdeal Z).map f := by
  rw [map_vanishingIdeal, hf]
  apply vanishingIdeal_antimono
  change closure (Z : Set X) ⊆ Z
  exact Z.isClosed.closure_eq.le

private def restrictClosedIso {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X)
    (e : X ≅ X) (he : e.hom '' (Z : Set X) = Z) :
    (vanishingIdeal Z).subscheme ≅ (vanishingIdeal Z).subscheme := by
  let I := vanishingIdeal Z
  have hi (x : X) : e.inv (e.hom x) = x := by
    rw [← Scheme.Hom.comp_apply, e.hom_inv_id]
    rfl
  have he' : e.inv '' (Z : Set X) = Z := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := he.ge hx
      rwa [← hyx, hi]
    · intro x hx
      exact ⟨e.hom x, he.le ⟨x, hx, rfl⟩, hi x⟩
  have hm : I ≤ I.map e.hom := vanishingIdeal_le_map_of_image_eq Z e.hom he
  have hn : I ≤ I.map e.inv := vanishingIdeal_le_map_of_image_eq Z e.inv he'
  let f := subschemeMap I I e.hom hm
  let g := subschemeMap I I e.inv hn
  exact
    { hom := f
      inv := g
      hom_inv_id := by
        apply (cancel_mono I.subschemeι).1
        simp [f, g, Category.assoc]
      inv_hom_id := by
        apply (cancel_mono I.subschemeι).1
        simp [f, g, Category.assoc] }

private lemma restrictClosedIso_hom_ι {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X)
    (e : X ≅ X) (he : e.hom '' (Z : Set X) = Z) :
    (restrictClosedIso Z e he).hom ≫ (vanishingIdeal Z).subschemeι =
      (vanishingIdeal Z).subschemeι ≫ e.hom := by
  exact subschemeMap_subschemeι _ _ _ (vanishingIdeal_le_map_of_image_eq Z e.hom he)

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- The actual closed subset with its reduced induced scheme structure. -/
abbrev twoPowerTorsionClosureIdeal : A.X.left.IdealSheafData :=
  vanishingIdeal ⟨closure (twoPowerTorsionLocus A), isClosed_closure⟩

/-- The reduced induced subscheme on the actual torsion closure. -/
abbrev twoPowerTorsionReducedClosure : Scheme.{u} :=
  (twoPowerTorsionClosureIdeal A).subscheme

/-- Its actual closed immersion into the ambient abelian scheme. -/
abbrev twoPowerTorsionReducedClosureι : twoPowerTorsionReducedClosure A ⟶ A.X.left :=
  (twoPowerTorsionClosureIdeal A).subschemeι

instance : IsClosedImmersion (twoPowerTorsionReducedClosureι A) := by
  exact inferInstanceAs (IsClosedImmersion (twoPowerTorsionClosureIdeal A).subschemeι)

instance : IsReduced (twoPowerTorsionReducedClosure A) :=
  P2MW.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.AlgebraicGeometry.Scheme.IntegralSubscheme.isReduced_vanishingIdeal _

lemma range_twoPowerTorsionReducedClosureι :
    Set.range (twoPowerTorsionReducedClosureι A) = closure (twoPowerTorsionLocus A) := by
  change Set.range (twoPowerTorsionClosureIdeal A).subschemeι = _
  rw [range_subschemeι]
  exact coe_support_vanishingIdeal _

private lemma inverse_image_closure :
    ι[A.X].left '' closure (twoPowerTorsionLocus A) =
      closure (twoPowerTorsionLocus A) := by
  have h : Set.MapsTo ι[A.X].left (twoPowerTorsionLocus A) (twoPowerTorsionLocus A) := by
    rintro x ⟨n, s, hs, rfl⟩
    refine ⟨n, s⁻¹, by simp [inv_pow, hs], ?_⟩
    rw [Hom.inv_def, Over.comp_left, Scheme.Hom.comp_apply]
  have hc := h.closure ι[A.X].left.continuous
  apply Set.Subset.antisymm hc.image_subset
  intro x hx
  refine ⟨ι[A.X].left x, hc hx, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, GrpObj.inv_comp_inv]
  rfl

/-- The reduced-scheme restrictions needed in the closed subgroup construction. -/
theorem twoPowerTorsionReducedClosure_exists : TwoPowerTorsionReducedClosureStatement.{u} := by
  intro K _ A
  let Z : TopologicalSpace.Closeds A.X.left :=
    ⟨closure (twoPowerTorsionLocus A), isClosed_closure⟩
  let I := vanishingIdeal Z
  refine ⟨I.subscheme, I.subschemeι, inferInstance,
    P2MW.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.AlgebraicGeometry.Scheme.IntegralSubscheme.isReduced_vanishingIdeal Z, ?_, ?_, ?_, ?_⟩
  · rw [range_subschemeι]
    exact coe_support_vanishingIdeal _
  · let e : Spec (CommRingCat.of K) ⟶ A.X.left :=
      (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X).left
    have he : Set.range e ⊆ Z := by
      rintro _ ⟨x, rfl⟩
      have hx : x = default := Subsingleton.elim _ _
      rw [hx]
      exact subset_closure ⟨0, 1, by simp, rfl⟩
    exact ⟨IsClosedImmersion.lift I.subschemeι e (by
      rw [ker_subschemeι]
      exact vanishingIdeal_le_ker_of_range Z e he),
      IsClosedImmersion.lift_fac _ _ _⟩
  · let v : A.X.left ≅ A.X.left := (Over.forget _).mapIso (asIso ι[A.X])
    exact ⟨restrictClosedIso Z v (inverse_image_closure A),
      restrictClosedIso_hom_ι Z v (inverse_image_closure A)⟩
  · intro s hs
    let t : A.X.left ≅ A.X.left := (Over.forget _).mapIso (GrpObj.mulRight s)
    have ht : t.hom '' (Z : Set A.X.left) = Z :=
      image_closure_twoPowerTorsionLocus_mulRight A s hs
    exact ⟨restrictClosedIso Z t ht, restrictClosedIso_hom_ι Z t ht⟩

end Langlands.AbelianScheme.Tate
