/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Category.Ring.Adjunctions
import Mathlib.Algebra.Category.Ring.Limits

/-!
# Local representatives of constant field sections

Source: Stacks Project, Sites, Tag 0H7J; Modules on Sites, Tag 03CY.
-/

@[expose] public section

universe uC vC r m

open CategoryTheory

namespace SheafOfModules

private instance forgetCommRing_reflectsLimits :
    CategoryTheory.Limits.ReflectsLimitsOfSize.{vC, max uC vC}
      (forget CommRingCat.{r}) where
  reflectsLimitsOfShape := {
    reflectsLimit := fun {K} ↦ {
      reflects := fun {c} h ↦ by
        have : CategoryTheory.Limits.HasLimit (K ⋙ forget CommRingCat.{r}) := ⟨⟨_, h⟩⟩
        have := (CategoryTheory.Limits.Types.hasLimit_iff_small_sections
          (K ⋙ forget CommRingCat.{r})).mp inferInstance
        have := CategoryTheory.Limits.reflectsLimit_of_reflectsIsomorphisms
          K (forget CommRingCat.{r})
        exact ⟨CategoryTheory.Limits.isLimitOfReflects (forget CommRingCat.{r}) h⟩ } }

/-- Sections of the associated constant field sheaf locally come from field elements.
Source: Stacks Project, Sites, Tag 0H7J and the associated-sheaf construction, Tag 00W1;
Modules on Sites, Tag 03CY
(auxiliary; not a blueprint node).

Proof: in the plus construction a section is represented by a matching family on a
covering sieve. Restricting to any arrow of that sieve gives a section coming from
one stage earlier. A section of the double plus construction therefore locally comes
from the original presheaf, by transitivity of covering sieves. The double plus
construction is the associated sheaf; the adjunction uniquely identifies its unit
with the unit of any chosen sheafification. For an independently sized site, one can
avoid enlarging the field carrier by taking, inside the chosen associated ring sheaf,
the subpresheaf of sections locally in the image of the unit. It is a subring on each
object: intersect the two covering sieves to check sums and products; negation and
the constants zero and one are immediate. Covering transitivity shows it is a sheaf.
The unit factors through this sheaf of subrings. The universal property of the chosen
sheafification gives a retraction of its inclusion, whose composite with the inclusion
is the identity because it agrees with the identity on the unit. Hence every section
of the chosen associated sheaf is locally in the image. This proves local surjectivity
without identifying all sections of the constant sheaf with field elements globally.
The empty covering sieve causes no exception to this argument. -/
theorem constantFieldUnit_locallySurjective
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{m} C] [HasWeakSheafify J CommRingCat.{r}]
    (κ : Type r) [Field κ] :
    Presheaf.IsLocallySurjective J
      (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of κ))) := by
  classical
  let P := (Functor.const Cᵒᵖ).obj (CommRingCat.of κ)
  let Q := sheafify J P
  let η := toSheafify J P
  let G := (Subfunctor.range (Functor.whiskerRight η (forget CommRingCat))).sheafify J
  have hmem (U : Cᵒᵖ) (x : P.obj U) : η.app U x ∈ G.obj U := by
    change Presheaf.imageSieve η (η.app U x) ∈ J U.unop
    rw [Presheaf.imageSieve_app]
    exact J.top_mem _
  let A (U : Cᵒᵖ) : Subring (Q.obj U) := {
    carrier := G.obj U
    zero_mem' := by simpa only [map_zero] using hmem U 0
    one_mem' := by simpa only [map_one] using hmem U 1
    add_mem' := by
      intro x y hx hy
      change Presheaf.imageSieve η (x + y) ∈ J U.unop
      apply J.superset_covering _ (J.intersection_covering hx hy)
      rintro V f ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      refine ⟨a + b, ?_⟩
      simp only [map_add]
      exact congrArg₂ (· + ·) ha hb
    neg_mem' := by
      intro x hx
      change Presheaf.imageSieve η (-x) ∈ J U.unop
      apply J.superset_covering _ hx
      rintro V f ⟨a, ha⟩
      refine ⟨-a, ?_⟩
      simp only [map_neg]
      exact congrArg Neg.neg ha
    mul_mem' := by
      intro x y hx hy
      change Presheaf.imageSieve η (x * y) ∈ J U.unop
      apply J.superset_covering _ (J.intersection_covering hx hy)
      rintro V f ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      refine ⟨a * b, ?_⟩
      simp only [map_mul]
      exact congrArg₂ (· * ·) ha hb }
  let F : Cᵒᵖ ⥤ CommRingCat.{r} := {
    obj := fun U ↦ CommRingCat.of (A U)
    map := fun {U V} f ↦ CommRingCat.ofHom {
      toFun := fun x ↦ ⟨Q.map f x.val, G.map f x.property⟩
      map_zero' := Subtype.ext (map_zero _)
      map_one' := Subtype.ext (map_one _)
      map_add' := fun x y ↦ Subtype.ext (map_add _ _ _)
      map_mul' := fun x y ↦ Subtype.ext (map_mul _ _ _) }
    map_id := fun U ↦ by
      ext x
      exact congrArg (fun h ↦ h x.val) (Q.map_id U)
    map_comp := fun f g ↦ by
      ext x
      exact congrArg (fun h ↦ h x.val) (Q.map_comp f g) }
  have hQ : Presheaf.IsSheaf J Q := ((presheafToSheaf J CommRingCat).obj P).property
  have hF : Presheaf.IsSheaf J F := by
    apply Presheaf.isSheaf_of_isSheaf_comp J F (forget CommRingCat)
    rw [isSheaf_iff_isSheaf_of_type]
    change Presieve.IsSheaf J G.toFunctor
    apply Subfunctor.sheafify_isSheaf
    rw [← isSheaf_iff_isSheaf_of_type]
    exact Presheaf.isSheaf_comp_of_isSheaf J Q (forget CommRingCat) hQ
  let ι : F ⟶ Q := {
    app := fun U ↦ CommRingCat.ofHom (A U).subtype
    naturality := fun {U V} f ↦ by ext x; rfl }
  let η' : P ⟶ F := {
    app := fun U ↦ CommRingCat.ofHom {
      toFun := fun x ↦ ⟨η.app U x, hmem U x⟩
      map_zero' := Subtype.ext (map_zero _)
      map_one' := Subtype.ext (map_one _)
      map_add' := fun x y ↦ Subtype.ext (map_add _ _ _)
      map_mul' := fun x y ↦ Subtype.ext (map_mul _ _ _) }
    naturality := fun {U V} f ↦ by
      ext x
      exact η.naturality_apply f x }
  have hfac : η' ≫ ι = η := rfl
  have hs : sheafifyLift J η' hF ≫ ι = 𝟙 Q := by
    apply sheafify_hom_ext J _ _ hQ
    rw [← Category.assoc, toSheafify_sheafifyLift, Category.comp_id]
    exact hfac
  constructor
  intro U x
  have heq := congrArg (fun f ↦ (f.app (Opposite.op U)) x) hs
  change ((sheafifyLift J η' hF).app (Opposite.op U) x).val = x at heq
  change x ∈ G.obj (Opposite.op U)
  rw [← heq]
  exact ((sheafifyLift J η' hF).app (Opposite.op U) x).property

end SheafOfModules
