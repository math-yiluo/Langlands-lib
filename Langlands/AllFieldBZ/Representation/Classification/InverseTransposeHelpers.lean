import Langlands.AllFieldBZ.Representation.Classification.IrreducibleTwoFactorProductSwapStatement
import Langlands.AllFieldBZ.Representation.Category.Contragredient
import Langlands.AllField.Representation.GodementJacquet.InverseTransposeProductAnalytics
import Langlands.Representation.Smooth.Contragredient.LocalFieldGelfandKazhdan
import Langlands.Representation.Classification.InverseTransposeHelpers

/-!
# All-field port of `Langlands.Representation.Classification.InverseTransposeHelpers`

Shared inverse-transpose constructions for normalized products, over an arbitrary
nonarchimedean local field (`Langlands.AllFieldBZ.LocalFieldPackage`). Gelfand–Kazhdan
is the all-field theorem `Langlands.LocalField.gelfandKazhdanContragredient`, and the
block reversal is the all-field `Langlands.AllField.GodementJacquet.inverseTransposeProductReversalEquiv`.
See the paired Markdown.
-/

noncomputable section
set_option linter.style.haveILetI false
open CategoryTheory
namespace Langlands.AllFieldBZ.Classification
open Langlands.GeneralLinear
universe uF uV
variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)
variable {N : ℕ}

/-- The pullback of a smooth representation of `GL_N(F)` along inverse
transpose, on the same carrier. -/
abbrev hermitianItPullback
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier)) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier) :=
  letI := T.topology
  SmoothRep.of (A.representation.comp (GeneralLinear.inverseTranspose N F.Carrier).toMonoidHom)
    (isSmooth_comp _ (GeneralLinear.continuous_inverseTranspose N F.Carrier) A.isSmooth)

/-- The Gelfand–Kazhdan theorem under the selected topology `T.topology`
of `F`, for an arbitrary positive rank `N`: inverse-transpose pullback realizes
the smooth dual of an irreducible admissible representation. -/
theorem hermitianGelfandKazhdanEquiv (hN : 0 < N) {V : Type uV} [AddCommGroup V]
    [Module ℂ V] :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup N
    ∀ ρ : Representation ℂ (GeneralLinear N F.Carrier) V,
      IsAdmissible ρ → Representation.IsIrreducible ρ →
      Nonempty (Representation.Equiv
        (ρ.comp (GeneralLinear.inverseTranspose N F.Carrier).toMonoidHom)
        (smoothContragredient ρ)) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := T.generalLinearTopologicalGroup (n + 1)
  intro ρ hadm hirr
  obtain ⟨E, hE⟩ := Langlands.LocalField.gelfandKazhdanContragredient F.Carrier n V ρ hadm hirr
  exact ⟨Representation.Equiv.mk E (fun g => LinearMap.ext (hE g))⟩

/-- Inverse transpose reverses the blocks of a normalized product and pulls
back each block by its own inverse transpose. -/
theorem hermitianItPullbackProductIso {n : ℕ} (_hn : 0 < n) (B : BlockShape n)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    Nonempty (hermitianItPullback F T ((T.normalizedProductInductionFunctor B).obj A) ≅
      (T.normalizedProductInductionFunctor B.reverse).obj (fun i => hermitianItPullback F T (A i.rev))) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  let σ := fun i => (A i).representation
  let τ := fun i : Fin B.reverse.length => (hermitianItPullback F T (A i.rev)).representation
  have E : Representation.Equiv ((T.normalizedProductInduced B σ).comp
        (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom)
      (T.normalizedProductInduced B.reverse τ) :=
    Langlands.AllField.GodementJacquet.inverseTransposeProductReversalEquiv T B σ
      (fun i => (A i).isSmooth)
  exact ⟨SmoothRep.mkIso (A := hermitianItPullback F T ((T.normalizedProductInductionFunctor B).obj A))
    (B := (T.normalizedProductInductionFunctor B.reverse).obj
      (fun i => hermitianItPullback F T (A i.rev))) E⟩

/-- Equal block shapes with heterogeneously equal block families give
isomorphic normalized products. -/
theorem hermitianProductFunctor_obj_congr {n : ℕ} {B C : BlockShape n} (h : B = C)
    (A : letI := T.topology
      ∀ i : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (A' : letI := T.topology
      ∀ i : Fin C.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (C.size i) F.Carrier))
    (hA : HEq A A') :
    letI := T.topology
    Nonempty ((T.normalizedProductInductionFunctor B).obj A ≅
      (T.normalizedProductInductionFunctor C).obj A') := by
  letI := T.topology
  subst h
  obtain rfl := eq_of_heq hA
  exact ⟨Iso.refl _⟩

end Langlands.AllFieldBZ.Classification
