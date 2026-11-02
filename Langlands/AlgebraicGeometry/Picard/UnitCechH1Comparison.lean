import Langlands.AlgebraicGeometry.Picard.UnitCechLineBundle
import Langlands.AlgebraicGeometry.Picard.UnitCechPresentation
import Langlands.Cohomology.AbelianSheafCechH1

/-! # Actual unit-sheaf H¹ classes of finite-cover line-bundle cocycles -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard

namespace UnitCechH1Comparison

open Langlands.Cohomology Cech AbelianSheafCechH1

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)

/-- The actual abelian-group sheaf of structure-sheaf units. -/
abbrev unitSheaf (X : Scheme.{u}) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  NilpotentUnitReduction.unitsSheaf X.presheaf X.sheaf.property

/-- The two published transition encodings are inverse on overlap units. -/
lemma pairUnits_transitionCochain (g : ∀ i j : ι, (Γ(X, U i ⊓ U j))ˣ) :
    UnitCechLineBundle.pairUnits U (UnitCechPresentation.transitionCochain U g) = g := by
  funext i j
  exact UnitCechPresentation.transitionCochain_pair U g i j

/-- The two published transition encodings are inverse on ordered one-cochains. -/
lemma transitionCochain_pairUnits (z : C (unitSheaf X).1 U 1) :
    UnitCechPresentation.transitionCochain U (UnitCechLineBundle.pairUnits U z) = z :=
  UnitCechPresentation.transitionCochain_pairRestriction U z

/-- Equality in fixed-cover Čech H¹ means a coboundary difference with the gluing sign. -/
lemma quotientClass_eq_iff (z w : cocycles (unitSheaf X).1 U) :
    (QuotientAddGroup.mk z : CechH1 (unitSheaf X).1 U) = QuotientAddGroup.mk w ↔
      ∃ a : C (unitSheaf X).1 U 0, d (unitSheaf X).1 U 0 a = w.1 - z.1 := by
  rw [eq_comm, QuotientAddGroup.eq_iff_sub_mem]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

variable [Finite ι]

/-- The actual Ext-defined H¹ class of a closed unit cochain on a finite full cover. -/
def classOfCocycle (hU : (⨆ i, U i) = ⊤) (z : cocycles (unitSheaf X).1 U) :
    Sheaf.H.{u} (unitSheaf X) 1 :=
  comparisonHom (unitSheaf X) U hU.ge (QuotientAddGroup.mk z)

/-- Actual H¹ equality detects exactly a fixed-cover unit coboundary difference. -/
lemma classOfCocycle_eq_iff (hU : (⨆ i, U i) = ⊤) (z w : cocycles (unitSheaf X).1 U) :
    classOfCocycle U hU z = classOfCocycle U hU w ↔
      ∃ a : C (unitSheaf X).1 U 0, d (unitSheaf X).1 U 0 a = w.1 - z.1 :=
  (comparisonHom_injective (unitSheaf X) U hU.ge).eq_iff.trans (quotientClass_eq_iff U z w)

/-- On a finite full cover, actual H¹ equality is equivalent to an isomorphism
of the actual glued module sheaves. -/
theorem nonempty_iso_glued_iff_classOfCocycle_eq
    (hU : (⨆ i, U i) = ⊤) (z w : cocycles (unitSheaf X).1 U) :
    Nonempty (CocycleGluing.glued (UnitCechLineBundle.pairUnits U z.1) ≅
      CocycleGluing.glued (UnitCechLineBundle.pairUnits U w.1)) ↔
    classOfCocycle U hU z = classOfCocycle U hU w :=
  (UnitCechLineBundle.nonempty_iso_glued_iff U z.2 w.2).trans
    (classOfCocycle_eq_iff U hU z w).symm

end UnitCechH1Comparison

namespace UnitCechPresentation.FinitePresentation

open UnitCechH1Comparison

variable {X : Scheme.{u}} {M : X.Modules} (D : FinitePresentation M)

/-- The actual unit-sheaf H¹ class attached to this chosen finite presentation. -/
def cohomologyClass : Sheaf.H.{u} (unitSheaf X) 1 :=
  classOfCocycle D.cover.U D.cover.iSup_eq_top ⟨D.cochain, D.closed⟩

/-- This presentation recovers the line bundle glued from its closed cochain. -/
def lineBundleIso :
    M ≅ (UnitCechLineBundle.lineBundle D.cover.U D.cover.iSup_eq_top
      D.cochain D.closed).obj := D.cochainIso

end UnitCechPresentation.FinitePresentation

end Langlands.AlgebraicGeometry.Picard
