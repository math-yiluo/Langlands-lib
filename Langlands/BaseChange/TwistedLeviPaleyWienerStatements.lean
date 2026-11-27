import Langlands.BaseChange.TwistedLeviPaleyWiener

/-!
# Inputs of the twisted trace Paley–Wiener theorem on the Levi products of `GL_n(E)`

Six propositions about the Levi products `∏ᵢ GL_{Bᵢ}(E)` of `GL_n(E)`, for a cyclic extension
`E/F` of a nonarchimedean local field of characteristic zero, with the entrywise action of `σ`:
realization of twisted induction on test functions, a descent identity for proper inductions
(Jacquet lifts and the combinatorial lemma), the discrete case of the twisted trace Paley–Wiener
theorem, restriction of good forms along induction, finite length of induction, and closure of
good forms under subtracting trace forms. They are stated here and not proved. See the paired
Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis GeneralLinear

universe u v z

namespace TwistedLeviPaleyWiener

/-! ## Topology of Levi products -/

section Topology

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (E : Type v) [CommRing E] [Algebra F E] [Module.Finite F E] [TopologicalSpace E]
  [IsTopologicalRing E] [IsModuleTopology F E] {n : ℕ} (B : BlockShape n)

include F

omit [IsTopologicalRing E] in
/-- A Levi product of `GL_n(E)` is Hausdorff. -/
theorem levi_t2Space_of_finite : T2Space (B.Levi E) := by
  have : ∀ i, T2Space (GeneralLinear (B.size i) E) := fun i =>
    generalLinear_t2Space_of_finite F E (B.size i)
  infer_instance

/-- A Levi product of `GL_n(E)` is locally compact. -/
theorem levi_locallyCompactSpace_of_finite : LocallyCompactSpace (B.Levi E) := by
  have : ∀ i, LocallyCompactSpace (GeneralLinear (B.size i) E) := fun i =>
    generalLinear_locallyCompactSpace_of_finite F E (B.size i)
  infer_instance

omit [IsTopologicalRing E] in
/-- A Levi product of `GL_n(E)` is totally disconnected. -/
theorem levi_totallyDisconnectedSpace_of_finite : TotallyDisconnectedSpace (B.Levi E) := by
  have : ∀ i, TotallyDisconnectedSpace (GeneralLinear (B.size i) E) := fun i =>
    generalLinear_totallyDisconnectedSpace_of_finite F E (B.size i)
  infer_instance

end Topology

/-- The block shapes `C` with `C.parabolic E ≤ B.parabolic E` and `B.length < C.length`. When `E`
is a field, these are the block shapes refining `B` into more blocks, and their Levi products are
the proper standard Levi subgroups of the Levi product of `B`. -/
abbrev ProperRefinement {n : ℕ} (E : Type v) [CommRing E] (B : BlockShape n) :=
  { C : BlockShape n // C.parabolic E ≤ B.parabolic E ∧ B.length < C.length }

/-! ## The six inputs -/

/-- Realization of twisted induction on test functions. For block shapes `C` refining `B` of `n`
and Haar measures `μ`, `ν` on the two Levi products, some linear map `CT` of test spaces satisfies
`IsLeviInductionTransfer σ B μ C ν CT`: composing the twisted character of any admissible pair
`(Ξ, BΞ)` of the Levi product of `C` with `CT` gives the twisted character of its unnormalized
smooth induction to the Levi product of `B`. The twisting operator is that of Rogawski (1988), §3,
and Henniart–Lemaire (2011), II.4.4; the identity is a derived form of the descent formula of
Henniart–Lemaire (2011), II.4.5, formula (2), explained in the Markdown of
`Langlands.BaseChange.TwistedLeviPaleyWiener`. -/
def TwistedLeviInductionTransferStatement.{u', v', z'} : Prop :=
  ∀ (F : Type u') [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v') [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    letI : ∀ C : BlockShape n, MeasurableSpace (C.Levi E) := fun _ => borel _
    haveI : ∀ C : BlockShape n, BorelSpace (C.Levi E) := fun _ => ⟨rfl⟩
    haveI : ∀ C : BlockShape n, T2Space (C.Levi E) := fun C => levi_t2Space_of_finite F E C
    haveI : ∀ C : BlockShape n, LocallyCompactSpace (C.Levi E) := fun C =>
      levi_locallyCompactSpace_of_finite F E C
    haveI : ∀ C : BlockShape n, TotallyDisconnectedSpace (C.Levi E) := fun C =>
      levi_totallyDisconnectedSpace_of_finite F E C
    ∀ (B C : BlockShape n), C.parabolic E ≤ B.parabolic E →
      ∀ (μ : Measure (B.Levi E)) [μ.IsHaarMeasure] (ν : Measure (C.Levi E)) [ν.IsHaarMeasure],
        ∃ CT : SchwartzBruhat (B.Levi E) →ₗ[ℂ] SchwartzBruhat (C.Levi E),
          IsLeviInductionTransfer.{u', v', z'} σ B μ C ν CT

/-- Descent identity for proper inductions. Given test maps `CT C` realizing induction from every
proper refinement `C` of `B`, there are linear maps `L C` from the test functions of the Levi
product of `C` to those of `B`, and finitely supported coefficients `c`, such that:

* composing an irreducible twisted character of the Levi product of `B` with `L C` gives an
  element of the span of the irreducible twisted characters of the Levi product of `C`;
* every element `x` of `leviProperInducedSpan σ B μ` equals `∑_C c C • (x ∘ L C ∘ CT C)`.

With `L C` the Jacquet lift of Rogawski (1988), Proposition 7.1, `x ↦ x ∘ L C ∘ CT C` is the
operator `i_C ∘ r_C` on twisted characters, and the identity is the combinatorial lemma of
Bernstein–Deligne–Kazhdan (1986), §3.3, in Rogawski's form, Lemma 8.2 and Proposition 9.1. -/
def TwistedLeviJacquetDescentStatement.{u', v', z'} : Prop :=
  ∀ (F : Type u') [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v') [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    letI : ∀ C : BlockShape n, MeasurableSpace (C.Levi E) := fun _ => borel _
    haveI : ∀ C : BlockShape n, BorelSpace (C.Levi E) := fun _ => ⟨rfl⟩
    haveI : ∀ C : BlockShape n, T2Space (C.Levi E) := fun C => levi_t2Space_of_finite F E C
    haveI : ∀ C : BlockShape n, LocallyCompactSpace (C.Levi E) := fun C =>
      levi_locallyCompactSpace_of_finite F E C
    haveI : ∀ C : BlockShape n, TotallyDisconnectedSpace (C.Levi E) := fun C =>
      levi_totallyDisconnectedSpace_of_finite F E C
    ∀ (μs : ∀ C : BlockShape n, Measure (C.Levi E)) [∀ C, (μs C).IsHaarMeasure]
      (B : BlockShape n)
      (CT : ∀ C : ProperRefinement E B,
        SchwartzBruhat (B.Levi E) →ₗ[ℂ] SchwartzBruhat (C.1.Levi E)),
      (∀ C, IsLeviInductionTransfer.{u', v', z'} σ B (μs B) C.1 (μs C.1) (CT C)) →
      ∃ (L : ∀ C : ProperRefinement E B,
          SchwartzBruhat (C.1.Levi E) →ₗ[ℂ] SchwartzBruhat (B.Levi E))
        (c : ProperRefinement E B →₀ ℂ),
        (∀ C, ∀ θ ∈ twistedSpectrum.{z', v'} (μs B) (leviAut σ B),
          θ ∘ₗ L C ∈ Submodule.span ℂ (twistedSpectrum.{z', v'} (μs C.1) (leviAut σ C.1))) ∧
        ∀ x ∈ leviProperInducedSpan.{u', v', z'} σ B (μs B),
          x = c.sum fun C a => a • (x ∘ₗ (L C ∘ₗ CT C))

/-- The discrete case of the twisted trace Paley–Wiener theorem on a Levi product: a compactly
dominated functional, regular on induced families, that vanishes on the twisted characters of
all proper inductions is a twisted trace functional. Bernstein–Deligne–Kazhdan (1986), §3.1 and
Proposition 4.2; Rogawski (1988), Propositions 9.1 and 10.1 and the proof of Proposition 11.2. -/
def TwistedLeviDiscretePaleyWienerStatement.{u', v', z'} : Prop :=
  ∀ (F : Type u') [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v') [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    letI : ∀ C : BlockShape n, MeasurableSpace (C.Levi E) := fun _ => borel _
    haveI : ∀ C : BlockShape n, BorelSpace (C.Levi E) := fun _ => ⟨rfl⟩
    haveI : ∀ C : BlockShape n, T2Space (C.Levi E) := fun C => levi_t2Space_of_finite F E C
    haveI : ∀ C : BlockShape n, LocallyCompactSpace (C.Levi E) := fun C =>
      levi_locallyCompactSpace_of_finite F E C
    haveI : ∀ C : BlockShape n, TotallyDisconnectedSpace (C.Levi E) := fun C =>
      levi_totallyDisconnectedSpace_of_finite F E C
    ∀ (B : BlockShape n) (μ : Measure (B.Levi E)) [μ.IsHaarMeasure]
      (Φ : Module.Dual ℂ (Distribution (B.Levi E))),
      IsCompactlyDominatedFunctional.{v', z'} (leviAut σ B) μ Φ →
      IsLeviSigmaInducedRegularFunctional.{u', v', z'} σ B μ Φ →
      (∀ d ∈ leviProperInducedSpan.{u', v', z'} σ B μ, Φ d = 0) →
      IsTwistedTraceFunctional.{v', z'} (leviAut σ B) μ Φ

/-- Restriction of good forms along induction: if `CT` realizes induction from the Levi product
of a refinement `C` of `B`, composing a compactly dominated regular functional on the Levi product
of `B` with the transpose of `CT` gives a compactly dominated regular functional on that of `C`.
Bernstein–Deligne–Kazhdan (1986), Proposition 3.2(i); Rogawski (1988), Lemma 11.1(b);
Henniart–Lemaire (2011), II.5.7, Remarque (1). -/
def TwistedLeviGoodRestrictionStatement.{u', v', z'} : Prop :=
  ∀ (F : Type u') [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v') [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    letI : ∀ C : BlockShape n, MeasurableSpace (C.Levi E) := fun _ => borel _
    haveI : ∀ C : BlockShape n, BorelSpace (C.Levi E) := fun _ => ⟨rfl⟩
    haveI : ∀ C : BlockShape n, T2Space (C.Levi E) := fun C => levi_t2Space_of_finite F E C
    haveI : ∀ C : BlockShape n, LocallyCompactSpace (C.Levi E) := fun C =>
      levi_locallyCompactSpace_of_finite F E C
    haveI : ∀ C : BlockShape n, TotallyDisconnectedSpace (C.Levi E) := fun C =>
      levi_totallyDisconnectedSpace_of_finite F E C
    ∀ (B C : BlockShape n), C.parabolic E ≤ B.parabolic E →
      ∀ (μ : Measure (B.Levi E)) [μ.IsHaarMeasure] (ν : Measure (C.Levi E)) [ν.IsHaarMeasure]
        (CT : SchwartzBruhat (B.Levi E) →ₗ[ℂ] SchwartzBruhat (C.Levi E)),
        IsLeviInductionTransfer.{u', v', z'} σ B μ C ν CT →
        ∀ Φ : Module.Dual ℂ (Distribution (B.Levi E)),
          IsCompactlyDominatedFunctional.{v', z'} (leviAut σ B) μ Φ →
          IsLeviSigmaInducedRegularFunctional.{u', v', z'} σ B μ Φ →
          IsCompactlyDominatedFunctional.{v', z'} (leviAut σ C) ν
              (Φ ∘ₗ Module.Dual.transpose (R := ℂ) CT) ∧
            IsLeviSigmaInducedRegularFunctional.{u', v', z'} σ C ν
              (Φ ∘ₗ Module.Dual.transpose (R := ℂ) CT)

/-- Finite length of induction, in the form used for twisted characters: the induction of an
irreducible admissible pair from the Levi product of a refinement `C` of `B` is admissible, and
its twisted character lies in the span of the irreducible twisted characters of the Levi product
of `B` (carriers in `Type z`). Henniart–Lemaire (2011), II.5.5; Rogawski (1988), §§2–4. -/
def TwistedLeviInducedSpanStatement.{u', v', z'} : Prop :=
  ∀ (F : Type u') [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v') [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    letI : ∀ C : BlockShape n, MeasurableSpace (C.Levi E) := fun _ => borel _
    haveI : ∀ C : BlockShape n, BorelSpace (C.Levi E) := fun _ => ⟨rfl⟩
    haveI : ∀ C : BlockShape n, T2Space (C.Levi E) := fun C => levi_t2Space_of_finite F E C
    haveI : ∀ C : BlockShape n, LocallyCompactSpace (C.Levi E) := fun C =>
      levi_locallyCompactSpace_of_finite F E C
    haveI : ∀ C : BlockShape n, TotallyDisconnectedSpace (C.Levi E) := fun C =>
      levi_totallyDisconnectedSpace_of_finite F E C
    ∀ (B C : BlockShape n), C.parabolic E ≤ B.parabolic E →
      ∀ (μ : Measure (B.Levi E)) [μ.IsHaarMeasure] (X : Type z') [AddCommGroup X] [Module ℂ X]
        (Ξ : Representation ℂ (C.Levi E) X), IsAdmissible Ξ → Ξ.IsIrreducible →
        ∀ BΞ : Ξ.Equiv (Ξ.comp (leviAut σ C).toMonoidHom),
          ∃ hI : IsAdmissible (Induction.smoothInduced (relParabolic E B C)
              (Ξ.comp (relProjection E B C))),
            twistedDistribution μ _ hI (relInducedSigmaIntertwiner σ B C Ξ BΞ).toLinearMap ∈
              Submodule.span ℂ (twistedSpectrum.{z', v'} μ (leviAut σ B))

/-- Trace forms are good, and good forms form a subspace: subtracting the evaluation at a test
function from a compactly dominated regular functional on a Levi product keeps both properties.
Bernstein–Deligne–Kazhdan (1986), §1.2; Rogawski (1988), Lemma 11.1(a). -/
def TwistedLeviTraceGoodStatement.{u', v', z'} : Prop :=
  ∀ (F : Type u') [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v') [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    letI : ∀ C : BlockShape n, MeasurableSpace (C.Levi E) := fun _ => borel _
    haveI : ∀ C : BlockShape n, BorelSpace (C.Levi E) := fun _ => ⟨rfl⟩
    haveI : ∀ C : BlockShape n, T2Space (C.Levi E) := fun C => levi_t2Space_of_finite F E C
    haveI : ∀ C : BlockShape n, LocallyCompactSpace (C.Levi E) := fun C =>
      levi_locallyCompactSpace_of_finite F E C
    haveI : ∀ C : BlockShape n, TotallyDisconnectedSpace (C.Levi E) := fun C =>
      levi_totallyDisconnectedSpace_of_finite F E C
    ∀ (B : BlockShape n) (μ : Measure (B.Levi E)) [μ.IsHaarMeasure]
      (Φ : Module.Dual ℂ (Distribution (B.Levi E))) (s : SchwartzBruhat (B.Levi E)),
      IsCompactlyDominatedFunctional.{v', z'} (leviAut σ B) μ Φ →
      IsLeviSigmaInducedRegularFunctional.{u', v', z'} σ B μ Φ →
      IsCompactlyDominatedFunctional.{v', z'} (leviAut σ B) μ
          (Φ - Module.Dual.eval ℂ (SchwartzBruhat (B.Levi E)) s) ∧
        IsLeviSigmaInducedRegularFunctional.{u', v', z'} σ B μ
          (Φ - Module.Dual.eval ℂ (SchwartzBruhat (B.Levi E)) s)

/-- The six inputs together. -/
def TwistedLeviPaleyWienerInputsStatement.{u', v', z'} : Prop :=
  TwistedLeviInductionTransferStatement.{u', v', z'} ∧
    TwistedLeviJacquetDescentStatement.{u', v', z'} ∧
    TwistedLeviDiscretePaleyWienerStatement.{u', v', z'} ∧
    TwistedLeviGoodRestrictionStatement.{u', v', z'} ∧
    TwistedLeviInducedSpanStatement.{u', v', z'} ∧
    TwistedLeviTraceGoodStatement.{u', v', z'}

end TwistedLeviPaleyWiener

end Langlands.BaseChange
