import Langlands.Representation.Classification.IrreducibleTwoFactorProductSwapStatement
import Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof
import Langlands.Representation.Parabolic.InverseTransposeProductProof
import Langlands.Representation.Category.Contragredient
import Langlands.LocalField.Normalization.Proof

/-! # Shared inverse-transpose constructions for normalized products -/

noncomputable section
set_option linter.style.haveILetI false
open CategoryTheory
namespace Langlands.Classification
open GeneralLinear
universe uF uV
variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
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

/-- The published Gelfand–Kazhdan theorem under the selected topology `T.topology`
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
  let tc : TopologicalSpace F.Carrier := (letI := F.canonicalNormedField; inferInstance)
  have key : ∀ t : TopologicalSpace F.Carrier, tc = t →
      ∀ [IsTopologicalGroup (GeneralLinear (n + 1) F.Carrier)]
        (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V),
        IsAdmissible ρ → Representation.IsIrreducible ρ →
        Nonempty (Representation.Equiv
          (ρ.comp (GeneralLinear.inverseTranspose (n + 1) F.Carrier).toMonoidHom)
          (smoothContragredient ρ)) := by
    intro t ht
    subst ht
    intro _ ρ hadm hirr
    obtain ⟨E, hE⟩ := gelfandKazhdanContragredient p inferInstance F n V ρ hadm hirr
    exact ⟨Representation.Equiv.mk E (fun g => LinearMap.ext (hE g))⟩
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (n + 1)
  exact key T.topology T.topology_eq_canonicalNormTopology.symm

/-- Inverse transpose reverses the blocks of a normalized product and pulls
back each block by its own inverse transpose. -/
theorem hermitianItPullbackProductIso {n : ℕ} (hn : 0 < n) (B : BlockShape n)
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
    Classical.choice (Parabolic.normalizedProductInverseTranspose T n hn B (fun i => A i)
      σ (fun i => (A i).isSmooth))
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

end Langlands.Classification
