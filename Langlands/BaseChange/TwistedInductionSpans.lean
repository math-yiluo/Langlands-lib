import Langlands.BaseChange.TwistedPseudoCoefficientInterpolation
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof
import Langlands.Representation.Filtration.CentralEigenspaceSplitting
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Subspaces of twisted distributions used in the pseudo-coefficient construction -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis GeneralLinear

universe u v uG z

section LinearExtension

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- Extend a functional from `L` while killing a disjoint subspace `N`. -/
theorem exists_dual_agreeOn_of_disjoint (L N : Submodule ℂ M) (h : Disjoint L N)
    (f : Module.Dual ℂ L) :
    ∃ Φ : Module.Dual ℂ M, (∀ x : L, Φ x = f x) ∧ ∀ x ∈ N, Φ x = 0 := by
  let q := N.mkQ.comp L.subtype
  have hq : Function.Injective q := by
    intro a b hab
    have hh : (a : M) - (b : M) ∈ N := by
      apply (Submodule.Quotient.mk_eq_zero (p := N)).mp
      change N.mkQ ((a : M) - (b : M)) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hab
    exact Subtype.ext (sub_eq_zero.mp
      (Submodule.disjoint_def.mp h _ (L.sub_mem a.property b.property) hh))
  let e := LinearEquiv.ofInjective q hq
  obtain ⟨f', hf'⟩ := (f.comp e.symm.toLinearMap).exists_extend
  refine ⟨f'.comp N.mkQ, fun x => ?_, fun x hx => ?_⟩
  · change f' (e x : M ⧸ N) = f x
    rw [show f' (e x : M ⧸ N) = f (e.symm (e x)) from LinearMap.congr_fun hf' (e x),
      e.symm_apply_apply]
  · change f' (N.mkQ x) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero (p := N)).mpr hx, map_zero]

end LinearExtension

section Spectrum

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
  (θ : G ≃* G)

/-- The subspace spanned by the actual twisted distributions of the irreducible admissible
representations in a specified class `P` (at carrier universe `z`). -/
def twistedSpectrumSpan
    (P : ∀ (W : Type z) [AddCommGroup W] [Module ℂ W], Representation ℂ G W → Prop) :
    Submodule ℂ (Distribution G) :=
  Submodule.span ℂ { d | ∃ (W : Type z) (iAdd : AddCommGroup W),
    letI := iAdd
    ∃ (iMod : Module ℂ W),
      letI := iMod
      ∃ (π : Representation ℂ G W) (hπ : IsAdmissible π) (A : π.Equiv (π.comp θ.toMonoidHom)),
        π.IsIrreducible ∧ P W π ∧ d = twistedDistribution μ π hπ A.toLinearMap }

/-- A twisted distribution of a member of the chosen class belongs to its span. -/
theorem twistedDistribution_mem_twistedSpectrumSpan
    (P : ∀ (W : Type z) [AddCommGroup W] [Module ℂ W], Representation ℂ G W → Prop)
    {W : Type z} [AddCommGroup W] [Module ℂ W] {π : Representation ℂ G W}
    (hπ : IsAdmissible π) (hirr : π.IsIrreducible) (hP : P W π) (A : π.Equiv (π.comp θ.toMonoidHom)) :
    twistedDistribution μ π hπ A.toLinearMap ∈ twistedSpectrumSpan μ θ P :=
  Submodule.subset_span ⟨W, inferInstance, inferInstance, π, hπ, A, hirr, hP, rfl⟩

end Spectrum

section Induced

variable {F : Type u} [CommRing F] [TopologicalSpace F]
  {E : Type v} [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E] {n : ℕ} (σ : E ≃ₐ[F] E)
  [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
  [TotallyDisconnectedSpace (GeneralLinear n E)]
  (μ : Measure (GeneralLinear n E)) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]

/-- The span of the twisted distributions of properly induced representations, from
irreducible admissible `σ`-stable representations of standard Levis. The induced
representation is not required to be irreducible. -/
def sigmaProperInducedSpan : Submodule ℂ (Distribution (GeneralLinear n E)) :=
  Submodule.span ℂ { d | ∃ B : BlockShape n, 2 ≤ B.length ∧
    ∃ (X : Type z) (iAdd : AddCommGroup X),
      letI := iAdd
      ∃ (iMod : Module ℂ X),
        letI := iMod
        ∃ (Ξ : Representation ℂ (B.Levi E) X) (_ : IsAdmissible Ξ) (_ : Ξ.IsIrreducible)
          (BΞ : Ξ.Equiv (Ξ.comp (leviAut σ B).toMonoidHom))
          (hI : IsAdmissible (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E)))),
          d = twistedDistribution μ _ hI (TwistedPaleyWiener.inducedSigmaIntertwiner σ B Ξ BΞ).toLinearMap }

/-- Twisted distributions from admissible proper induction are generators of the span. -/
theorem twistedDistribution_mem_sigmaProperInducedSpan
    (B : BlockShape n) (hB : 2 ≤ B.length) {X : Type z} [AddCommGroup X] [Module ℂ X]
    (Ξ : Representation ℂ (B.Levi E) X) (hΞ : IsAdmissible Ξ) (hΞirr : Ξ.IsIrreducible)
    (BΞ : Ξ.Equiv (Ξ.comp (leviAut σ B).toMonoidHom))
    (hI : IsAdmissible (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E)))) :
    twistedDistribution μ _ hI (TwistedPaleyWiener.inducedSigmaIntertwiner σ B Ξ BΞ).toLinearMap ∈
      sigmaProperInducedSpan.{u,v,z} σ μ :=
  Submodule.subset_span ⟨B, hB, X, inferInstance, inferInstance, Ξ, hΞ, hΞirr, BΞ, hI, rfl⟩

/-- An irreducible admissible representation equivalent to a proper induction from
irreducible admissible `σ`-stable data belongs to the properly induced span, with any
choice of its `σ`-intertwiner. -/
theorem twistedDistribution_mem_sigmaProperInducedSpan_of_equiv
    (B : BlockShape n) (hB : 2 ≤ B.length) {X : Type z} [AddCommGroup X] [Module ℂ X]
    (Ξ : Representation ℂ (B.Levi E) X) (hΞ : IsAdmissible Ξ) (hΞirr : Ξ.IsIrreducible)
    (BΞ : Ξ.Equiv (Ξ.comp (leviAut σ B).toMonoidHom))
    {W : Type z} [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GeneralLinear n E) W}
    (hπ : IsAdmissible π) (hπirr : π.IsIrreducible) (A : SigmaIntertwiner σ n π)
    (e : Representation.Equiv
      (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E))) π) :
    twistedDistribution μ π hπ A.toLinearMap ∈ sigmaProperInducedSpan.{u,v,z} σ μ := by
  have hI := isAdmissible_of_equiv e.symm hπ
  have hirr := (isIrreducible_iff_of_equiv e).mpr hπirr
  obtain ⟨a, ha⟩ := exists_twistedDistribution_eq_smul_of_equiv μ (entrywiseAut σ n)
    hI hirr hπ e (TwistedPaleyWiener.inducedSigmaIntertwiner σ B Ξ BΞ) A
  rw [ha]
  exact Submodule.smul_mem _ a (twistedDistribution_mem_sigmaProperInducedSpan σ μ B hB Ξ hΞ hΞirr BΞ hI)

end Induced

end Langlands.BaseChange
