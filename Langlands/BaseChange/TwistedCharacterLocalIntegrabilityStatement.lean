import Langlands.BaseChange.CharacterFunction
import Langlands.BaseChange.TwistedCharacterRegularValuesStatement

/-!
# Local integrability of twisted characters of `GL_n(E)`

The statement that the twisted character of an irreducible admissible representation of
`GL_n(E)`, for a cyclic algebra `E` over a nonarchimedean local field `F` of characteristic zero
and an isomorphism `A` of the representation onto its σ-conjugate, is given by a locally
integrable function that is locally constant on the σ-regular set (Clozel 1987, Theorem 1,
printed p. 153, with Arthur–Clozel 1989, Chapter 1, Proposition 2.2; formulated as in
Henniart–Lemaire 2011, I.5.1 and II.1.3, who take it from Lemaire 2004, Théorème 7.1). Not
proved here. It gives the Library's `TwistedCharacterRegularValuesStatement`
(lemma `TwistedCharacterLocalIntegrabilityStatement.regularValues`, proved).
-/

namespace Langlands.BaseChange

open Langlands.JacquetLanglands

/-- For every nonarchimedean local field `F` of characteristic zero, every cyclic `F`-algebra
`E` of group `⟨σ⟩` of order `l` with its module topology, and every `n`: for every irreducible
admissible representation `τ` of `GL_n(E)` on a complex vector space `W : Type uW` and every
isomorphism `A` of `τ` onto `τ^σ`, the twisted character `φ ↦ trace(τ(φ) ∘ A)` is represented
by a function `Θ : GL_n(E) → ℂ`, locally integrable for every Haar measure, that is locally
constant near every σ-regular element (Clozel 1987, Theorem 1, printed p. 153, with
Arthur–Clozel 1989, Chapter 1, Proposition 2.2, printed p. 11; formulated as in
Henniart–Lemaire 2011, I.5.1, printed pp. 28–30, and II.1.3, printed p. 57, after Lemaire 2004,
Théorème 7.1, printed p. 38). -/
def TwistedCharacterLocalIntegrabilityStatement.{u, v, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (τ : Representation ℂ (GeneralLinear n E) W) (hτ : IsAdmissible τ), τ.IsIrreducible →
      ∀ A : SigmaIntertwiner σ n τ,
      ∃ Θ : GeneralLinear n E → ℂ, IsTwistedCharacterFunction τ hτ A.toLinearMap Θ ∧
        ∀ δ : GeneralLinear n E, IsSigmaRegular σ l δ → ∀ᶠ x in nhds δ, Θ x = Θ δ

/-- Statement 5 gives the existence of twisted character values at σ-regular elements: the
value of the twisted character function there. -/
theorem TwistedCharacterLocalIntegrabilityStatement.regularValues.{u, v, uW}
    (h : TwistedCharacterLocalIntegrabilityStatement.{u, v, uW}) :
    TwistedCharacterRegularValuesStatement.{u, v, uW} := by
  intro F _ _ _ _ _ E _ _ _ _ _ σ l n hE
  have : Module.Finite F E := hE.1
  have := generalLinear_t2Space_of_finite F E n
  have := generalLinear_locallyCompactSpace_of_finite F E n
  have := generalLinear_totallyDisconnectedSpace_of_finite F E n
  intro W _ _ τ hτ hirr A δ hδ
  obtain ⟨Θ, hΘ, hloc⟩ := h F E σ l n hE τ hτ hirr A
  exact ⟨Θ δ, hΘ.hasTwistedCharacterValue (hloc δ hδ)⟩

end Langlands.BaseChange
