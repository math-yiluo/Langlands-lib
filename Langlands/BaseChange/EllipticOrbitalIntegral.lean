import Langlands.BaseChange.OrbitalIntegral

/-!
# Functions whose (twisted) orbital integrals vanish off the elliptic set

For a topological field `F` and a commutative topological `F`-algebra `E` with
`σ : E ≃ₐ[F] E`:

* `OrbitalIntegralsVanishOffElliptic μF f`: the orbital integrals of `f : GL_n(F) → ℂ`
  vanish at every regular semisimple element of `GL_n(F)` that is not regular elliptic
  (the defining condition of Kazhdan's space `B(G)`, Kazhdan 1986, printed p. 6;
  Henniart–Lemaire's "fonction elliptique", II.6.7, printed p. 123);
* `SigmaOrbitalIntegralsVanishOffElliptic σ l μE φ`: the σ-orbital integrals of
  `φ : GL_n(E) → ℂ` vanish at every σ-regular element of `GL_n(E)` that is not σ-elliptic
  (Henniart–Lemaire II.5.14, Proposition 2 (2), printed p. 115; Arthur–Clozel, Chapter 1,
  Lemma 2.12 (ii), printed p. 19).

Both predicates quantify over every right Haar measure on the centralizer and every quotient
measure compatible with it, as `VanishesOffNorms` does; no measure is chosen or normalized.
The module also proves that the predicates hold for the zero function and are stable under
multiplication by a constant, and that every regular semisimple element of `GL_1(F)` is
regular elliptic, so that the first predicate holds for every function on `GL_1(F)`.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory
open Langlands.QuotientIntegration
open Langlands.TraceFormula
open Langlands.JacquetLanglands

universe u v

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

section Definitions

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
variable {n : ℕ}
variable [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
variable [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]

/-- The orbital integrals of `f` vanish off the elliptic set: for every regular semisimple
`γ ∈ GL_n(F)` that is not regular elliptic, every right Haar measure `μγ` on the centralizer
`G_γ(F)` and every measure `νγ` on `G_γ(F) \ GL_n(F)` compatible with `μF` and `μγ`, the
orbital integral `∫ f(x⁻¹ γ x) dνγ(x)` is `0`. Kazhdan (1986, printed p. 6) defines `B(G)` as
the set of `f` in Harish-Chandra's Schwartz space `𝒞(G)` whose orbital integrals vanish on
every regular nonelliptic conjugacy class; for a locally constant compactly supported `f`
this predicate is membership in `B(G)`. Henniart–Lemaire call such a function "elliptique"
(II.6.7, printed p. 123). -/
def OrbitalIntegralsVanishOffElliptic (μF : Measure (GeneralLinear n F))
    (f : GeneralLinear n F → ℂ) : Prop :=
  ∀ γ : GeneralLinear n F, IsRegularSemisimple γ → ¬ IsRegularElliptic γ →
    ∀ (μγ : Measure (glCentralizer γ)) [μγ.IsHaarMeasure] [μγ.IsMulRightInvariant]
      (νγ : Measure (LeftQuotient (glCentralizer γ))),
      IsCompatible (glCentralizer γ) μF μγ νγ → orbitalIntegral γ νγ f = 0

/-- The σ-orbital integrals of `φ` vanish off the σ-elliptic set: for every σ-regular
`δ ∈ GL_n(E)` that is not σ-elliptic, every right Haar measure `μδ` on the σ-centralizer
`G^σ_δ(F)` and every measure `νδ` on `G^σ_δ(F) \ GL_n(E)` compatible with `μE` and `μδ`,
the σ-orbital integral `∫ φ(x⁻¹ δ x^σ) dνδ(x)` is `0`. This is the conclusion of
Henniart–Lemaire II.5.14, Proposition 2 (2) (printed p. 115) and of the first part of
Arthur–Clozel, Chapter 1, Lemma 2.12 (ii) (printed p. 19). -/
def SigmaOrbitalIntegralsVanishOffElliptic (σ : E ≃ₐ[F] E) (l : ℕ)
    (μE : Measure (GeneralLinear n E)) (φ : GeneralLinear n E → ℂ) : Prop :=
  ∀ δ : GeneralLinear n E, IsSigmaRegular σ l δ → ¬ IsSigmaElliptic σ l δ →
    ∀ (μδ : Measure (sigmaCentralizer σ n δ)) [μδ.IsHaarMeasure] [μδ.IsMulRightInvariant]
      (νδ : Measure (LeftQuotient (sigmaCentralizer σ n δ))),
      IsCompatible (sigmaCentralizer σ n δ) μE μδ νδ → sigmaOrbitalIntegral σ n δ νδ φ = 0

end Definitions

section Closure

/-- A twisted orbital integral of the zero function is `0`. -/
private theorem twistedOrbitalIntegral_zero {G : Type*} [Group G] {Θ : Type*}
    [FunLike Θ G G] [MonoidHomClass Θ G G] (θ : Θ) (δ : G)
    [MeasurableSpace (LeftQuotient (twistedCentralizer θ δ))]
    (ν : Measure (LeftQuotient (twistedCentralizer θ δ))) :
    twistedOrbitalIntegral θ δ ν (0 : G → ℂ) = 0 := by
  have h : twistedOrbitFunction θ δ (0 : G → ℂ) = fun _ => 0 :=
    funext fun q => Quotient.inductionOn q fun _ => rfl
  rw [twistedOrbitalIntegral, h, integral_zero]

/-- A twisted orbital integral is homogeneous: the integrand of `c * f` is `c` times that
of `f`, and `∫ c * u = c * ∫ u` holds without an integrability hypothesis. -/
private theorem twistedOrbitalIntegral_const_mul {G : Type*} [Group G] {Θ : Type*}
    [FunLike Θ G G] [MonoidHomClass Θ G G] (θ : Θ) (δ : G)
    [MeasurableSpace (LeftQuotient (twistedCentralizer θ δ))]
    (ν : Measure (LeftQuotient (twistedCentralizer θ δ))) (c : ℂ) (f : G → ℂ) :
    twistedOrbitalIntegral θ δ ν (fun g => c * f g) = c * twistedOrbitalIntegral θ δ ν f := by
  have h : twistedOrbitFunction θ δ (fun g => c * f g) =
      fun q => c * twistedOrbitFunction θ δ f q :=
    funext fun q => Quotient.inductionOn q fun _ => rfl
  rw [twistedOrbitalIntegral, twistedOrbitalIntegral, h, integral_const_mul]

section General

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
variable [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]

/-- The zero function has vanishing orbital integrals off the elliptic set. -/
theorem orbitalIntegralsVanishOffElliptic_zero (μF : Measure (GeneralLinear n F)) :
    OrbitalIntegralsVanishOffElliptic μF (0 : GeneralLinear n F → ℂ) := by
  intro γ _ _ μγ _ _ νγ _
  exact twistedOrbitalIntegral_zero _ γ νγ

/-- `OrbitalIntegralsVanishOffElliptic` is stable under multiplication by a constant. -/
theorem OrbitalIntegralsVanishOffElliptic.const_mul {μF : Measure (GeneralLinear n F)}
    {f : GeneralLinear n F → ℂ} (h : OrbitalIntegralsVanishOffElliptic μF f) (c : ℂ) :
    OrbitalIntegralsVanishOffElliptic μF (fun g => c * f g) := by
  intro γ hγ hne μγ _ _ νγ hν
  rw [orbitalIntegral, twistedOrbitalIntegral_const_mul, ← orbitalIntegral,
    h γ hγ hne μγ νγ hν, mul_zero]

end General

section Twisted

variable {F : Type u} [Field F]
variable {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
variable {n : ℕ} [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]

/-- The zero function has vanishing σ-orbital integrals off the σ-elliptic set. -/
theorem sigmaOrbitalIntegralsVanishOffElliptic_zero (σ : E ≃ₐ[F] E) (l : ℕ)
    (μE : Measure (GeneralLinear n E)) :
    SigmaOrbitalIntegralsVanishOffElliptic σ l μE (0 : GeneralLinear n E → ℂ) := by
  intro δ _ _ μδ _ _ νδ _
  exact twistedOrbitalIntegral_zero _ δ νδ

/-- `SigmaOrbitalIntegralsVanishOffElliptic` is stable under multiplication by a constant. -/
theorem SigmaOrbitalIntegralsVanishOffElliptic.const_mul {σ : E ≃ₐ[F] E} {l : ℕ}
    {μE : Measure (GeneralLinear n E)} {φ : GeneralLinear n E → ℂ}
    (h : SigmaOrbitalIntegralsVanishOffElliptic σ l μE φ) (c : ℂ) :
    SigmaOrbitalIntegralsVanishOffElliptic σ l μE (fun g => c * φ g) := by
  intro δ hδ hne μδ _ _ νδ hν
  rw [sigmaOrbitalIntegral, twistedOrbitalIntegral_const_mul, ← sigmaOrbitalIntegral,
    h δ hδ hne μδ νδ hν, mul_zero]

end Twisted

end Closure

section RankOne

/-- In `GL_1(F)` every regular semisimple element is regular elliptic: its characteristic
polynomial has degree `1`, hence is irreducible. -/
theorem isRegularElliptic_of_isRegularSemisimple_one {F : Type u} [Field F]
    (g : GeneralLinear 1 F) (hg : IsRegularSemisimple g) : IsRegularElliptic g := by
  refine ⟨hg, Polynomial.irreducible_of_degree_eq_one ?_⟩
  rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin, Nat.cast_one]

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable [MeasurableSpace (GeneralLinear 1 F)] [BorelSpace (GeneralLinear 1 F)]

/-- Every function on `GL_1(F)` has vanishing orbital integrals off the elliptic set, since
there is no regular semisimple element that is not regular elliptic. -/
theorem orbitalIntegralsVanishOffElliptic_one (μF : Measure (GeneralLinear 1 F))
    (f : GeneralLinear 1 F → ℂ) : OrbitalIntegralsVanishOffElliptic μF f := by
  intro γ hγ hne
  exact absurd (isRegularElliptic_of_isRegularSemisimple_one γ hγ) hne

end RankOne

end Langlands.BaseChange
