import Langlands.BaseChange.TwistedLeviParabolic

/-!
# The twisted trace Paley–Wiener conditions on Levi products of `GL_n(E)`

The good forms of the twisted trace Paley–Wiener theorem on a Levi product `∏ᵢ GL_{Bᵢ}(E)` with
the entrywise action of `σ`: compact domination (the Library's `IsCompactlyDominatedFunctional`)
and regularity on the families induced from the standard Levi subgroups `∏ⱼ GL_{Cⱼ}(E)` of the
Levi product (`IsLeviSigmaInducedRegularFunctional`). Also the set of twisted characters of
irreducible admissible σ-stable representations, the span of the properly induced twisted
characters, and the predicate saying that a linear map of test spaces realizes twisted
induction. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis GeneralLinear

universe u v z uG

namespace TwistedLeviPaleyWiener

/-! ## Twisted characters of a general group -/

section Spectrum

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
  [μ.IsMulLeftInvariant] (θ : G ≃* G)

/-- The twisted characters `Θ^A_π` of the irreducible admissible representations `π` of `G` on
complex vector spaces in `Type z` and of all isomorphisms `A : π ≅ π ∘ θ`; these are the
generators of `twistedSpectrumSpan μ θ (fun _ _ _ _ => True)`. -/
def twistedSpectrum : Set (Distribution G) :=
  { d | ∃ (W : Type z) (iAdd : AddCommGroup W),
    letI := iAdd
    ∃ (iMod : Module ℂ W),
      letI := iMod
      ∃ (π : Representation ℂ G W) (hπ : IsAdmissible π) (A : π.Equiv (π.comp θ.toMonoidHom)),
        π.IsIrreducible ∧ d = twistedDistribution μ π hπ A.toLinearMap }

theorem twistedDistribution_mem_twistedSpectrum {W : Type z} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G W} (hπ : IsAdmissible π) (hirr : π.IsIrreducible)
    (A : π.Equiv (π.comp θ.toMonoidHom)) :
    twistedDistribution μ π hπ A.toLinearMap ∈ twistedSpectrum.{z, uG} μ θ :=
  ⟨W, inferInstance, inferInstance, π, hπ, A, hirr, rfl⟩

/-- A functional is a twisted trace functional exactly when it agrees with evaluation at one
test function on `twistedSpectrum μ θ`. -/
theorem isTwistedTraceFunctional_iff (Φ : Module.Dual ℂ (Distribution G)) :
    IsTwistedTraceFunctional.{uG, z} θ μ Φ ↔
      ∃ φ : SchwartzBruhat G, ∀ d ∈ twistedSpectrum.{z, uG} μ θ, Φ d = d φ := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, ?_⟩
    rintro d ⟨W, iAdd, iMod, π, hπ, A, hirr, rfl⟩
    exact (hφ W π hπ hirr A).symm
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, fun W _ _ π hπ hirr A =>
      (hφ _ (twistedDistribution_mem_twistedSpectrum μ θ hπ hirr A)).symm⟩

end Spectrum

/-! ## Levi products -/

section Levi

variable {F : Type u} [CommRing F] [TopologicalSpace F]
  {E : Type v} [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E] {n : ℕ} (σ : E ≃ₐ[F] E) (B : BlockShape n)
  [MeasurableSpace (B.Levi E)] [BorelSpace (B.Levi E)] [T2Space (B.Levi E)]
  [LocallyCompactSpace (B.Levi E)] [TotallyDisconnectedSpace (B.Levi E)]
  (μ : Measure (B.Levi E)) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]

/-- Regularity on induced families inside a Levi product (Henniart–Lemaire 2011, II.5.7,
condition (A)(ii); Rogawski 1988, §11, condition (II)), at carrier universe `z`: for every block
shape `C` refining `B` (`C.parabolic E ≤ B.parabolic E`), every irreducible admissible
representation `Ξ` of the Levi product of `C` and every `BΞ : Ξ ≅ Ξ^σ`, the value of `Φ` on the
twisted character of `Ind_{relParabolic E B C}^{M_B} (Ξ ⊗ ψ)` is a finite linear combination of
evaluations of `ψ`, for all σ-invariant unramified characters `ψ` of the Levi product of `C`.
The induction is unnormalized, and the twisting operator is `relInducedSigmaIntertwiner`. -/
def IsLeviSigmaInducedRegularFunctional (Φ : Module.Dual ℂ (Distribution (B.Levi E))) :
    Prop :=
  ∀ (C : BlockShape n), C.parabolic E ≤ B.parabolic E →
    ∀ (X : Type z) [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ (C.Levi E) X),
      IsAdmissible Ξ → Ξ.IsIrreducible →
      ∀ BΞ : Ξ.Equiv (Ξ.comp (leviAut σ C).toMonoidHom),
        ∃ (s : Finset (C.Levi E)) (c : C.Levi E → ℂ),
          ∀ (ψ : C.Levi E →* ℂˣ), IsUnramifiedCharacter ψ →
            ∀ (hψ : ∀ m, ψ (leviAut σ C m) = ψ m)
              (h : IsAdmissible (Induction.smoothInduced (relParabolic E B C)
                ((twist ψ Ξ).comp (relProjection E B C)))),
              Φ (twistedDistribution μ _ h
                (relInducedSigmaIntertwiner σ B C (twist ψ Ξ)
                  (twistTwistedIntertwiner (leviAut σ C) ψ hψ BΞ)).toLinearMap) =
                ∑ m ∈ s, c m * (ψ m : ℂ)

/-- The span of the twisted characters of the admissible proper inductions
`Ind_{relParabolic E B C}^{M_B} Ξ`, for block shapes `C` properly refining `B` and irreducible
admissible `Ξ` with `BΞ : Ξ ≅ Ξ^σ`, carriers in `Type z`. The induced representation need not be
irreducible. -/
def leviProperInducedSpan : Submodule ℂ (Distribution (B.Levi E)) :=
  Submodule.span ℂ { d | ∃ C : BlockShape n, C.parabolic E ≤ B.parabolic E ∧
    B.length < C.length ∧
    ∃ (X : Type z) (iAdd : AddCommGroup X),
      letI := iAdd
      ∃ (iMod : Module ℂ X),
        letI := iMod
        ∃ (Ξ : Representation ℂ (C.Levi E) X) (_ : IsAdmissible Ξ) (_ : Ξ.IsIrreducible)
          (BΞ : Ξ.Equiv (Ξ.comp (leviAut σ C).toMonoidHom))
          (hI : IsAdmissible (Induction.smoothInduced (relParabolic E B C)
            (Ξ.comp (relProjection E B C)))),
          d = twistedDistribution μ _ hI (relInducedSigmaIntertwiner σ B C Ξ BΞ).toLinearMap }

theorem twistedDistribution_mem_leviProperInducedSpan (C : BlockShape n)
    (hCB : C.parabolic E ≤ B.parabolic E) (hlen : B.length < C.length)
    {X : Type z} [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ (C.Levi E) X)
    (hΞ : IsAdmissible Ξ) (hirr : Ξ.IsIrreducible)
    (BΞ : Ξ.Equiv (Ξ.comp (leviAut σ C).toMonoidHom))
    (hI : IsAdmissible (Induction.smoothInduced (relParabolic E B C)
      (Ξ.comp (relProjection E B C)))) :
    twistedDistribution μ _ hI (relInducedSigmaIntertwiner σ B C Ξ BΞ).toLinearMap ∈
      leviProperInducedSpan.{u, v, z} σ B μ :=
  Submodule.subset_span ⟨C, hCB, hlen, X, inferInstance, inferInstance, Ξ, hΞ, hirr, BΞ, hI, rfl⟩

variable (C : BlockShape n)
  [MeasurableSpace (C.Levi E)] [BorelSpace (C.Levi E)] [T2Space (C.Levi E)]
  [LocallyCompactSpace (C.Levi E)] [TotallyDisconnectedSpace (C.Levi E)]
  (ν : Measure (C.Levi E)) [IsFiniteMeasureOnCompacts ν] [ν.IsMulLeftInvariant]

/-- `CT` realizes twisted induction from the Levi product of `C` to that of `B`, at carrier
universe `z`: for every admissible representation `Ξ` of the Levi product of `C`, every
`BΞ : Ξ ≅ Ξ^σ` and every admissibility proof of the induction, the twisted character of `Ξ`
composed with `CT` is the twisted character of `Ind_{relParabolic E B C}^{M_B} Ξ` with
`relInducedSigmaIntertwiner`. -/
def IsLeviInductionTransfer
    (CT : SchwartzBruhat (B.Levi E) →ₗ[ℂ] SchwartzBruhat (C.Levi E)) : Prop :=
  ∀ (X : Type z) [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ (C.Levi E) X)
    (hΞ : IsAdmissible Ξ) (BΞ : Ξ.Equiv (Ξ.comp (leviAut σ C).toMonoidHom))
    (hI : IsAdmissible (Induction.smoothInduced (relParabolic E B C)
      (Ξ.comp (relProjection E B C)))),
    twistedDistribution ν Ξ hΞ BΞ.toLinearMap ∘ₗ CT =
      twistedDistribution μ _ hI (relInducedSigmaIntertwiner σ B C Ξ BΞ).toLinearMap

end Levi

end TwistedLeviPaleyWiener

end Langlands.BaseChange
