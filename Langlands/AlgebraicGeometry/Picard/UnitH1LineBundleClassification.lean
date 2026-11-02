import Langlands.AlgebraicGeometry.Picard.UnitCechH1Comparison
import Langlands.AlgebraicGeometry.Picard.UnitCechRefinement
import Langlands.AlgebraicGeometry.Picard.LineBundleInverse
import Langlands.Cohomology.AbelianSheafH1Refinement

/-! # Actual unit H¹ and line bundles on compact schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard

namespace UnitH1LineBundleClassification

open Langlands.Cohomology Cech AbelianSheafCechH1 AbelianSheafH1Refinement
open UnitCechH1Comparison UnitCechRefinement

variable {X : Scheme.{u}} {ι κ : Type u} [Finite ι] [Finite κ]
  (U : ι → X.Opens) (V : κ → X.Opens)

/-- A finite full refinement leaves the actual unit-sheaf H¹ class unchanged. -/
lemma classOfCocycle_refine (β : κ → ι) (hβ : ∀ j, V j ≤ U (β j))
    (hU : (⨆ i, U i) = ⊤) (hV : (⨆ j, V j) = ⊤)
    (z : cocycles (unitSheaf X).1 U) :
    classOfCocycle V hV (refineCocycles (unitSheaf X).1 U V β hβ z) =
      classOfCocycle U hU z :=
  comparisonHom_refine (unitSheaf X) U V β hβ hU.ge hV.ge
    (QuotientAddGroup.mk z)

/-- Actual H¹ equality detects isomorphisms of gluings on different finite full covers. -/
theorem nonempty_iso_glued_iff_class_eq
    (hU : (⨆ i, U i) = ⊤) (hV : (⨆ j, V j) = ⊤)
    (z : cocycles (unitSheaf X).1 U) (w : cocycles (unitSheaf X).1 V) :
    Nonempty (CocycleGluing.glued (UnitCechLineBundle.pairUnits U z.1) ≅
      CocycleGluing.glued (UnitCechLineBundle.pairUnits V w.1)) ↔
    classOfCocycle U hU z = classOfCocycle V hV w := by
  let W := commonCover U V
  have hW : (⨆ p, W p) = ⊤ := commonCover_eq_top U V hU hV
  let z' := refineCocycles (unitSheaf X).1 U W Prod.fst (fun _ => inf_le_left) z
  let w' := refineCocycles (unitSheaf X).1 V W Prod.snd (fun _ => inf_le_right) w
  have hz := classOfCocycle_refine U W Prod.fst (fun _ => inf_le_left) hU hW z
  have hw := classOfCocycle_refine V W Prod.snd (fun _ => inf_le_right) hV hW w
  calc
    _ ↔ ∃ a : C (unitSheaf X).1 W 0,
        d (unitSheaf X).1 W 0 a = w'.1 - z'.1 :=
      nonempty_iso_glued_iff_commonCover U V hU hV z.2 w.2
    _ ↔ classOfCocycle W hW z' = classOfCocycle W hW w' :=
      (classOfCocycle_eq_iff W hW z' w').symm
    _ ↔ _ := by rw [hz, hw]

end UnitH1LineBundleClassification

namespace UnitCechPresentation.FinitePresentation

open UnitCechH1Comparison UnitH1LineBundleClassification

variable {X : Scheme.{u}} {M N : X.Modules}
  (D : FinitePresentation M) (E : FinitePresentation N)

/-- Presentation classes agree exactly when the actual presented module sheaves are isomorphic. -/
theorem cohomologyClass_eq_iff :
    D.cohomologyClass = E.cohomologyClass ↔ Nonempty (M ≅ N) := by
  have h := nonempty_iso_glued_iff_class_eq D.cover.U E.cover.U
    D.cover.iSup_eq_top E.cover.iSup_eq_top ⟨D.cochain, D.closed⟩ ⟨E.cochain, E.closed⟩
  constructor
  · intro heq
    obtain ⟨e⟩ := h.mpr heq
    exact ⟨D.cochainIso ≪≫ e ≪≫ E.cochainIso.symm⟩
  · rintro ⟨e⟩
    exact h.mp ⟨D.cochainIso.symm ≪≫ e ≪≫ E.cochainIso⟩

/-- The actual H¹ class is independent of the finite presentation. -/
lemma cohomologyClass_eq (E : FinitePresentation M) :
    D.cohomologyClass = E.cohomologyClass :=
  (D.cohomologyClass_eq_iff E).mpr ⟨Iso.refl M⟩

end UnitCechPresentation.FinitePresentation

namespace LineBundle

open Langlands.Cohomology Cech AbelianSheafCechH1 AbelianSheafH1Refinement
open UnitCechH1Comparison UnitH1LineBundleClassification UnitCechPresentation

variable {X : Scheme.{u}} [CompactSpace X]

/-- A chosen finite actual-unit presentation of a line bundle on a compact scheme. -/
def finiteUnitPresentation (L : LineBundle X) : FinitePresentation L.obj :=
  Classical.choice (exists_finitePresentation L.property)

/-- The actual unit-sheaf H¹ class of a line bundle on a compact scheme. -/
def unitCohomologyClass (L : LineBundle X) : Sheaf.H.{u} (unitSheaf X) 1 :=
  L.finiteUnitPresentation.cohomologyClass

/-- Every finite presentation computes the same actual H¹ class. -/
lemma unitCohomologyClass_eq_presentation (L : LineBundle X)
    (D : FinitePresentation L.obj) :
    L.unitCohomologyClass = D.cohomologyClass :=
  L.finiteUnitPresentation.cohomologyClass_eq D

/-- Actual unit H¹ classes classify line bundles up to underlying sheaf isomorphism. -/
theorem unitCohomologyClass_eq_iff (L M : LineBundle X) :
    L.unitCohomologyClass = M.unitCohomologyClass ↔ Nonempty (L.obj ≅ M.obj) :=
  L.finiteUnitPresentation.cohomologyClass_eq_iff M.finiteUnitPresentation

/-- The classification also detects isomorphisms in the category of line bundles. -/
lemma unitCohomologyClass_eq_iff_iso (L M : LineBundle X) :
    L.unitCohomologyClass = M.unitCohomologyClass ↔ Nonempty (L ≅ M) := by
  rw [unitCohomologyClass_eq_iff]
  exact ⟨fun ⟨e⟩ => ⟨ObjectProperty.isoMk _ e⟩,
    fun ⟨e⟩ => ⟨(forget X).mapIso e⟩⟩

/-- Gluing a finite full-cover cocycle realizes its specified actual H¹ class. -/
lemma unitCohomologyClass_glued {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : (⨆ i, U i) = ⊤) (z : cocycles (unitSheaf X).1 U) :
    (UnitCechLineBundle.lineBundle U hU z.1 z.2).unitCohomologyClass =
      classOfCocycle U hU z := by
  let L := UnitCechLineBundle.lineBundle U hU z.1 z.2
  let D := L.finiteUnitPresentation
  exact (nonempty_iso_glued_iff_class_eq D.cover.U U
    D.cover.iSup_eq_top hU ⟨D.cochain, D.closed⟩ z).mp ⟨D.cochainIso.symm⟩

/-- Every actual unit-sheaf H¹ class on a compact scheme is realized by a line bundle. -/
theorem unitCohomologyClass_surjective :
    Function.Surjective (unitCohomologyClass (X := X)) := by
  intro x
  obtain ⟨ι, hι, U, hU, q, hq⟩ := exists_comparisonHom_eq (unitSheaf X) x
  let := hι
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
  have hU' : (⨆ i, U i) = ⊤ := le_antisymm le_top hU
  refine ⟨UnitCechLineBundle.lineBundle U hU' z.1 z.2, ?_⟩
  exact (unitCohomologyClass_glued U hU' z).trans hq

end LineBundle

namespace Group

open UnitCechH1Comparison

variable {X : Scheme.{u}} [CompactSpace X]

/-- The actual unit-sheaf H¹ class of a class in the existing scheme Picard group. -/
def unitCohomologyClass (x : Group X) : Sheaf.H.{u} (unitSheaf X) 1 :=
  (lineBundleRepresentative X x).unitCohomologyClass

/-- On an actual line bundle, the Picard-class map computes its presentation class. -/
@[simp] lemma unitCohomologyClass_classOf (L : LineBundle X) :
    unitCohomologyClass L.classOf = L.unitCohomologyClass :=
  (LineBundle.unitCohomologyClass_eq_iff _ _).mpr
    ((LineBundle.classOf_eq_iff _ _).mp (classOf_lineBundleRepresentative X L.classOf))

/-- Actual H¹ distinguishes all classes in the existing Picard group. -/
theorem unitCohomologyClass_injective :
    Function.Injective (unitCohomologyClass (X := X)) := by
  intro x y h
  have he := (LineBundle.unitCohomologyClass_eq_iff
    (lineBundleRepresentative X x) (lineBundleRepresentative X y)).mp h
  have hclass := (LineBundle.classOf_eq_iff _ _).mpr he
  simpa only [classOf_lineBundleRepresentative] using hclass

/-- All actual unit H¹ classes come from the existing Picard group. -/
theorem unitCohomologyClass_surjective :
    Function.Surjective (unitCohomologyClass (X := X)) := by
  intro x
  obtain ⟨L, hL⟩ := LineBundle.unitCohomologyClass_surjective x
  exact ⟨L.classOf, (unitCohomologyClass_classOf L).trans hL⟩

/-- The actual scheme Picard group and actual unit H¹ have equivalent underlying types. -/
def unitCohomologyEquiv (X : Scheme.{u}) [CompactSpace X] :
    Group X ≃ Sheaf.H.{u} (unitSheaf X) 1 :=
  Equiv.ofBijective unitCohomologyClass
    ⟨unitCohomologyClass_injective, unitCohomologyClass_surjective⟩

@[simp] lemma unitCohomologyEquiv_classOf (L : LineBundle X) :
    unitCohomologyEquiv X L.classOf = L.unitCohomologyClass :=
  unitCohomologyClass_classOf L

end Group

end Langlands.AlgebraicGeometry.Picard
