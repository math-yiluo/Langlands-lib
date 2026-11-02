import Langlands.Cohomology.AbelianSheafCechH1
import Langlands.Cohomology.AbelianSheafH1FiniteCocycles

/-! # Refinements and finite-cover coverage of actual abelian sheaf H¹ -/

noncomputable section

universe w w' w'' u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Langlands.Cohomology.AbelianSheafH1Refinement

open Cech AbelianSheafCechH1

section Refinement

variable {T : TopCat.{u}} (P : TopCat.Presheaf AddCommGrpCat.{u} T)
  {ι : Type w} {ι' : Type w'} (U : ι → Opens T) (U' : ι' → Opens T)
  (β : ι' → ι) (hβ : ∀ j, U' j ≤ U (β j))

/-- Refinement restricts a global zero-cochain to the same global section. -/
lemma refine_globalCochain (s : P.obj (op ⊤)) :
    refine P U U' β hβ 0 (globalCochain P U s) = globalCochain P U' s := by
  funext σ
  exact res_res _ _ s

/-- The additive refinement map on ordered one-cocycles. -/
def refineCocycles : cocycles P U →+ cocycles P U' where
  toFun z := ⟨refine P U U' β hβ 1 z.1, by
    change d P U' 1 (refine P U U' β hβ 1 z.1) = 0
    rw [d_refine, show d P U 1 z.1 = 0 from z.2, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- Refinement on the quotient by ordered Čech coboundaries. -/
def refineHom : CechH1 P U →+ CechH1 P U' :=
  QuotientAddGroup.map _ _ (refineCocycles P U U' β hβ) (by
    rintro z ⟨a, rfl⟩
    exact ⟨refine P U U' β hβ 0 a, Subtype.ext (d_refine hβ 0 a)⟩)

lemma refineHom_mk (z : cocycles P U) :
    refineHom P U U' β hβ (QuotientAddGroup.mk z) =
      QuotientAddGroup.mk (refineCocycles P U U' β hβ z) := rfl

end Refinement

section Representatives

variable {T : TopCat.{u}} {ι : Type w} {ι' : Type w'}
  {U : ι → Opens T} {U' : ι' → Opens T} {β : ι' → ι}
  {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)}
  (hβ : ∀ j, U' j ≤ U (β j))

/-- Refine the primitive while retaining the same global quotient section. -/
def refineRepresentative {z : C S.X₁.1 U 1} (r : Representative (S := S) z) :
    Representative (S := S) (refine S.X₁.1 U U' β hβ 1 z) where
  primitive := refine S.X₂.1 U U' β hβ 0 r.primitive
  quotientSection := r.quotientSection
  primitive_d := by rw [d_refine, r.primitive_d, ← map_refine]
  quotient := by rw [map_refine, r.quotient, refine_globalCochain]

set_option backward.isDefEq.respectTransparency false in
lemma refineRepresentative_value (hS : S.ShortExact) {z : C S.X₁.1 U 1}
    (r : Representative (S := S) z) :
    (refineRepresentative hβ r).value hS = r.value hS := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual connecting-class comparison is compatible with finite full refinements. -/
theorem quotientClassHom_refine [Finite ι] [Finite ι']
    [TopCat.Presheaf.IsFlasque S.X₂.1] (hS : S.ShortExact)
    (hcov : ⊤ ≤ iSup U) (hcov' : ⊤ ≤ iSup U') (x : CechH1 S.X₁.1 U) :
    quotientClassHom hS hcov' (refineHom S.X₁.1 U U' β hβ x) =
      quotientClassHom hS hcov x := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    rw [refineHom_mk, quotientClassHom_mk, quotientClassHom_mk]
    let r := chosenRepresentative (S := S) hcov z
    rw [cocycleClassHom_eq_value hS hcov' _ (refineRepresentative hβ r),
      refineRepresentative_value, cocycleClassHom_eq_value hS hcov z r]

end Representatives

section Comparison

variable {T : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} T)
  {ι : Type w} {ι' : Type w'} [Finite ι] [Finite ι']
  (U : ι → Opens T) (U' : ι' → Opens T) (β : ι' → ι)
  (hβ : ∀ j, U' j ≤ U (β j))

set_option backward.isDefEq.respectTransparency false in
/-- Refinement leaves the actual H¹ comparison class unchanged. -/
theorem comparisonHom_refine (hcov : ⊤ ≤ iSup U) (hcov' : ⊤ ≤ iSup U')
    (x : CechH1 F.1 U) :
    comparisonHom F U' hcov' (refineHom F.1 U U' β hβ x) =
      comparisonHom F U hcov x := by
  let S := AbelianSheafFlasque.injectiveSc F
  let : TopCat.Sheaf.IsFlasque S.X₂ :=
    AbelianSheafFlasque.isFlasque_of_injective (Injective.under F)
  exact quotientClassHom_refine hβ
    (AbelianSheafFlasque.injectiveSc_shortExact F) hcov hcov' x

/-- In degree one, refinement between finite full covers is injective. -/
theorem refineHom_injective (hcov : ⊤ ≤ iSup U) (hcov' : ⊤ ≤ iSup U') :
    Function.Injective (refineHom F.1 U U' β hβ) := by
  intro x y h
  apply comparisonHom_injective F U hcov
  rw [← comparisonHom_refine F U U' β hβ hcov hcov' x,
    ← comparisonHom_refine F U U' β hβ hcov hcov' y, h]

end Comparison

section Coverage

variable {T : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} T)

/-- Regard a finite cocycle presentation as a representative in the chosen sequence. -/
def presentationRepresentative {x : Sheaf.H.{u} F 1}
    (D : AbelianSheafH1FiniteCocycles.FiniteCocyclePresentation F x) :
    Representative (S := AbelianSheafFlasque.injectiveSc F) D.cocycle where
  primitive := D.localLifts.lifts
  quotientSection := D.quotientSection
  primitive_d := D.primitive_eq.symm
  quotient := funext D.localLifts.lift_eq

set_option backward.isDefEq.respectTransparency false in
lemma presentationRepresentative_value {x : Sheaf.H.{u} F 1}
    (D : AbelianSheafH1FiniteCocycles.FiniteCocyclePresentation F x) :
    (presentationRepresentative F D).value
      (AbelianSheafFlasque.injectiveSc_shortExact F) = x := D.value_eq

set_option backward.isDefEq.respectTransparency false in
/-- Every actual H¹ class on a compact space is in the comparison image of some finite
full open cover; the cover may depend on the class. -/
theorem exists_comparisonHom_eq [CompactSpace T] (x : Sheaf.H.{u} F 1) :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → Opens T) (hcov : ⊤ ≤ iSup U)
      (z : CechH1 F.1 U), comparisonHom F U hcov z = x := by
  obtain ⟨D⟩ := AbelianSheafH1FiniteCocycles.exists_finite_cocycle_presentation F x
  let := D.localLifts.finite
  refine ⟨D.localLifts.index, D.localLifts.finite, D.localLifts.cover,
    D.localLifts.cover_top, QuotientAddGroup.mk ⟨D.cocycle, D.closed⟩, ?_⟩
  exact (comparisonHom_eq_value F D.localLifts.cover D.localLifts.cover_top
    ⟨D.cocycle, D.closed⟩ (presentationRepresentative F D)).trans
      (presentationRepresentative_value F D)

end Coverage

end Langlands.Cohomology.AbelianSheafH1Refinement
