import Langlands.CategoryTheory.Renard.SimpleSupportOrthogonalityStatements
import Langlands.CategoryTheory.Renard.SimpleSubquotientSubobjectQuotient
import Langlands.CategoryTheory.Renard.SimpleSubquotientEmpty

/-!
# Renard A.IX: disjoint supports and canonical subobject maps

Proof of the unnumbered assertion on printed268/PDF274 of the French
edition dated 9 July 2026: objects with disjoint simple supports have
zero Hom, and the internal consequences for arbitrary actual supported
subobjects of one ambient object. The source context, used only through
the published zero-detection clause of A.VI.3, keeps independent family,
Hom and object universes.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- In the source context, an object supported on two disjoint sets of
classes is a zero object. -/
theorem isZero_of_hasSimpleSupport_of_disjoint
    (hG : IsSourceGrothendieck.{w} C) (hAB6 : SourceAB6 C)
    {S T : Set (ObjectClass C)} (hST : Disjoint S T) {Z : C}
    (hS : HasSimpleSupport S Z) (hT : HasSimpleSupport T Z) : IsZero Z :=
  (simpleSubquotientEmpty C hG hAB6 Z).mp
    (Set.subset_eq_empty (Set.subset_inter hS hT)
      (Set.disjoint_iff_inter_eq_empty.mp hST))

/-- In the source context, every actual morphism between objects with
disjoint simple supports is zero: its actual image is supported on both. -/
theorem eq_zero_of_hasSimpleSupport_of_disjoint
    (hG : IsSourceGrothendieck.{w} C) (hAB6 : SourceAB6 C)
    {S T : Set (ObjectClass C)} (hST : Disjoint S T) {X Y : C}
    (hX : HasSimpleSupport S X) (hY : HasSimpleSupport T Y) (f : X ⟶ Y) :
    f = 0 := by
  have hI : IsZero (image f) :=
    isZero_of_hasSimpleSupport_of_disjoint hG hAB6 hST
      ((simpleSubquotientClasses_subset_of_epi (factorThruImage f)).trans hX)
      ((simpleSubquotientClasses_subset_of_mono (image.ι f)).trans hY)
  rw [← image.fac f, hI.eq_of_tgt (factorThruImage f) 0, zero_comp]

/-- In the source context, actual subobjects of one object with disjoint
simple supports have zero intersection. -/
theorem inf_eq_bot_of_hasSimpleSupport_of_disjoint
    (hG : IsSourceGrothendieck.{w} C) (hAB6 : SourceAB6 C)
    {S T : Set (ObjectClass C)} (hST : Disjoint S T) {X : C}
    {P Q : Subobject X} (hP : HasSimpleSupport S (P : C))
    (hQ : HasSimpleSupport T (Q : C)) : P ⊓ Q = ⊥ := by
  have hZ : IsZero ((P ⊓ Q : Subobject X) : C) :=
    isZero_of_hasSimpleSupport_of_disjoint hG hAB6 hST
      ((simpleSubquotientClasses_subset_of_mono
        (Subobject.ofLE (P ⊓ Q) P inf_le_left)).trans hP)
      ((simpleSubquotientClasses_subset_of_mono
        (Subobject.ofLE (P ⊓ Q) Q inf_le_right)).trans hQ)
  rw [← Subobject.mk_arrow (P ⊓ Q), Subobject.mk_eq_bot_iff_zero]
  exact hZ.eq_of_src _ _

/-- In any abelian category, the canonical map from the binary biproduct
of two subobjects with zero intersection to the ambient object is monic. -/
theorem mono_biprod_desc_arrow_of_inf_eq_bot {X : C} {P Q : Subobject X}
    (h : P ⊓ Q = ⊥) : Mono (biprod.desc P.arrow Q.arrow) := by
  refine Preadditive.mono_of_cancel_zero _ fun {Z} g hg => ?_
  have hsum : (g ≫ biprod.fst) ≫ P.arrow + (g ≫ biprod.snd) ≫ Q.arrow = 0 := by
    rw [← hg, biprod.desc_eq, Preadditive.comp_add, Category.assoc, Category.assoc]
  have hneg : (g ≫ biprod.fst) ≫ P.arrow = (-(g ≫ biprod.snd)) ≫ Q.arrow := by
    rw [Preadditive.neg_comp, ← sub_eq_zero, sub_neg_eq_add, hsum]
  have hfac : (P ⊓ Q).Factors ((g ≫ biprod.fst) ≫ P.arrow) :=
    (Subobject.inf_factors _).mpr
      ⟨Subobject.factors_comp_arrow _, hneg ▸ Subobject.factors_comp_arrow _⟩
  rw [h, Subobject.bot_factors_iff_zero] at hfac
  have hfst : g ≫ biprod.fst = 0 := by
    rw [← cancel_mono P.arrow, hfac, zero_comp]
  have hsnd : g ≫ biprod.snd = 0 := by
    rw [← cancel_mono Q.arrow, zero_comp, ← neg_eq_zero, ← Preadditive.neg_comp,
      ← hneg, hfac]
  exact biprod.hom_ext _ _ (by rw [hfst, zero_comp]) (by rw [hsnd, zero_comp])

end

/-- Renard A.IX, Hom orthogonality for disjoint simple supports. -/
theorem simpleSupportHomOrthogonality
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimpleSupportHomOrthogonalityStatement.{w} C := by
  intro hG hAB6 S T _ _ hST X Y hX hY f
  exact eq_zero_of_hasSimpleSupport_of_disjoint hG hAB6 hST hX hY f

/-- Zero intersection of actual subobjects with disjoint simple supports. -/
theorem simpleSupportSubobjectIntersection
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimpleSupportSubobjectIntersectionStatement.{w} C := by
  intro hG hAB6 S T _ _ hST X P Q hP hQ
  exact inf_eq_bot_of_hasSimpleSupport_of_disjoint hG hAB6 hST hP hQ

/-- The canonical map from the binary biproduct of actual subobjects with
disjoint simple supports is monic. -/
theorem simpleSupportSubobjectBiproductMono
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimpleSupportSubobjectBiproductMonoStatement.{w} C := by
  intro hG hAB6 S T _ _ hST X P Q hP hQ
  exact mono_biprod_desc_arrow_of_inf_eq_bot
    (inf_eq_bot_of_hasSimpleSupport_of_disjoint hG hAB6 hST hP hQ)

/-- Renard A.IX: disjoint-support Hom orthogonality and its consequences
for actual supported subobjects, with the complete source hypotheses. -/
theorem simpleSupportOrthogonality
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimpleSupportOrthogonalityStatement.{w} C :=
  ⟨simpleSupportHomOrthogonality.{w} C, simpleSupportSubobjectIntersection.{w} C,
    simpleSupportSubobjectBiproductMono.{w} C⟩

end Langlands.Renard
