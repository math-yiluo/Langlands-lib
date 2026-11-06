import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedFourierTransform
import Langlands.Representation.Plancherel.CompactProductFormTransport
import Langlands.Representation.Plancherel.ProductInducedOrbitSections

/-! # The section `ψ_f[O, P]` (Waldspurger VII.1)

Waldspurger VII.1 (printed p. 316): for an orbit `O` in `E_2(M)` under `Im X(M)` and `f ∈ C(G)`,
`ψ_f[O, P]` is the function on `O` with `ψ_f[O, P]_ω = f̂(ω, P)` for all `ω ∈ O`. Its values lie
in the spaces `L(ω, P)`, which VI.1 identifies along equivalences of representatives.

Here the orbit is Worker 200's set `UnitaryOrbitRepresentative ν π` of actual irreducible
admissible representatives of the classes in the orbit of `π` under the unitary unramified
characters, and the identifications are the transports `productInducedCoefficientTransport`.
`productInducedCoefficientTransport_inducedFourierTransform` shows that `f̂(ω, P)` is carried to
`f̂(ω', P)` along every equivalence `ω ≃ ω'`. So `fourierOrbitSection`, the section
`A ↦ f̂(A, P)`, is a coherent section (`fourierOrbitSection_mem_coherent`), and
`f ↦ ψ_f[O, P]` is a linear map into the coherent sections (`fourierOrbitSectionLinear`). The
smoothness asserted in Proposition VII.1.3 is not addressed here.
-/

noncomputable section

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel
open scoped ComplexConjugate NNReal

namespace Langlands.HarishChandraSchwartz

universe uG uV uI

section Transport

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [Nonempty (CompactOpenSubgroup G)]
  {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (hm : Continuous h.projection)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  {A B : SmoothRep.{0, uG, uV} ℂ M} (hcof : CompactOpenCofinal M)
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μM : Measure (M ⧸ C)) [μM.IsHaarMeasure] [μM.IsInvInvariant]
  (hsqA : IsSquareIntegrableModCentralSubgroup C hC A.representation μM)
  (hiA : A.representation.IsIrreducible)
  (hsqB : IsSquareIntegrableModCentralSubgroup C hC B.representation μM)
  (hiB : B.representation.IsIrreducible)
  {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Ξ σ : G → ℝ}
  (hw : L2Weights μ Ξ σ)
  (hTA : HasTemperedCoefficients Ξ σ ((normalizedInductionFunctor h hU).obj A).representation)
  (hTB : HasTemperedCoefficients Ξ σ ((normalizedInductionFunctor h hU).obj B).representation)
  (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g)

/-- **`f̂(ω, P)` does not depend on the representative of `ω`**: for an equivalence
`e : A ≃ B` of inducing representations, the transport of `f̂(A, P)` along `e` is `f̂(B, P)`. -/
theorem productInducedCoefficientTransport_inducedFourierTransform [MeasurableInv G]
    [μ.IsInvInvariant] (e : A.representation.Equiv B.representation) (f : Space Ξ σ) :
    productInducedCoefficientTransport h hU e
        (inducedFourierTransform h hU hP hm K hK hPK hG hδ A hcof C hC μM hsqA hiA hw hTA hΞ hσ
          f) =
      inducedFourierTransform h hU hP hm K hK hPK hG hδ B hcof C hC μM hsqB hiB hw hTB hΞ hσ
        f := by
  let T := productInducedCoefficientTransport h hU e
  symm
  refine inducedFourierTransform_eq_of_forall_integral h hU hP hm K hK hPK hG hδ B hcof C hC μM
    hsqB hiB hw hTB hΞ hσ f _ fun ψ => ?_
  have hψ : ψ = T (T.symm ψ) := (T.apply_symm_apply ψ).symm
  have hE : CompactInduction.coefficientMap h hU B K hK hP hm hPK hG hδ hsqB.1 ψ =
      CompactInduction.coefficientMap h hU A K hK hP hm hPK hG hδ hsqA.1 (T.symm ψ) := by
    conv_lhs => rw [hψ]
    exact CompactInduction.coefficientMap_transport h hU hP K hK hPK hG hδ hm hsqA.1 hsqB.1 e
      (T.symm ψ)
  have hform := CompactInduction.formalDegreeProductForm_ofEquiv h hU hP K hK hPK hG hδ hcof C hC
    μM hsqA hiA hsqB hiB e
  rw [hE, integral_conj_coefficientMap_mul_eq_inner h hU hP hm K hK hPK hG hδ A hcof C hC μM hsqA
    hiA hw hTA hΞ hσ, ← hform]
  conv_rhs => rw [hψ]
  rfl

end Transport

section Orbit

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [Nonempty (CompactOpenSubgroup G)]
  {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (hm : Continuous h.projection)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M)) (hcof : CompactOpenCofinal M)
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μM : Measure (M ⧸ C)) [μM.IsHaarMeasure] [μM.IsInvInvariant]
  (hsq : ∀ A : UnitaryOrbitRepresentative ν π,
    IsSquareIntegrableModCentralSubgroup C hC A.val.obj.representation μM)
  {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Ξ σ : G → ℝ}
  (hw : L2Weights μ Ξ σ)
  (hT : ∀ A : UnitaryOrbitRepresentative ν π,
    HasTemperedCoefficients Ξ σ ((normalizedInductionFunctor h hU).obj A.val.obj).representation)
  (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g)

/-- **Waldspurger's `ψ_f[O, P]`** (VII.1, printed p. 316): for `f ∈ C(G)`, the section
`ω ↦ f̂(ω, P)` over the orbit `O` of `π` under the unitary unramified characters, with one value
in `L(ω, P)` at every actual representative `ω` of a class in `O`. -/
def fourierOrbitSection (f : Space Ξ σ) : ProductInducedOrbitSections ν π h hU :=
  fun A => inducedFourierTransform h hU hP hm K hK hPK hG hδ A.val.obj hcof C hC μM (hsq A)
    A.val.property.1 hw (hT A) hΞ hσ f

theorem fourierOrbitSection_apply (f : Space Ξ σ) (A : UnitaryOrbitRepresentative ν π) :
    fourierOrbitSection h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ f A =
      inducedFourierTransform h hU hP hm K hK hPK hG hδ A.val.obj hcof C hC μM (hsq A)
        A.val.property.1 hw (hT A) hΞ hσ f :=
  rfl

/-- `ψ_f[O, P]` is a coherent section: its values at two representatives correspond under
every equivalence between them. -/
theorem fourierOrbitSection_mem_coherent [MeasurableInv G] [μ.IsInvInvariant] (f : Space Ξ σ) :
    fourierOrbitSection h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ f ∈
      coherentProductInducedOrbitSections ν π h hU := fun A B a =>
  (productInducedCoefficientTransport_inducedFourierTransform h hU hP hm K hK hPK hG hδ hcof C hC
    μM (hsq A) A.val.property.1 (hsq B) B.val.property.1 hw (hT A) (hT B) hΞ hσ a f).symm

/-- The linear map `f ↦ ψ_f[O, P]` from `C(G)` to the coherent sections over `O`. -/
def fourierOrbitSectionLinear [MeasurableInv G] [μ.IsInvInvariant] :
    Space Ξ σ →ₗ[ℂ] coherentProductInducedOrbitSections ν π h hU where
  toFun f := ⟨fourierOrbitSection h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ f,
    fourierOrbitSection_mem_coherent h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ
      f⟩
  map_add' f₁ f₂ := Subtype.ext <| funext fun _ => map_add _ f₁ f₂
  map_smul' c f := Subtype.ext <| funext fun _ => map_smul _ c f

end Orbit

end Langlands.HarishChandraSchwartz
