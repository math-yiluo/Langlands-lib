import Langlands.BaseChange.Norm
import Langlands.TraceFormula.TwistedOrbital
import Langlands.Analysis.Local.QuotientMeasure
import Mathlib.MeasureTheory.Group.Measure

/-!
# Orbital and σ-orbital integrals on `GL_n`, associated measures and concordance

Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle* (2011), Chapter I, §§I.2.4–I.2.5 (printed pp. 14–18).

For a field `F`, a commutative `F`-algebra `E` and `σ : E ≃ₐ[F] E`:

* the σ-centralizer `G^σ_δ(F)` of `δ ∈ GL_n(E)` and the centralizer `G_γ(F)` of
  `γ ∈ GL_n(F)`, both as instances of the generic `twistedCentralizer`;
* the σ-orbital integral `Λ^{G(E)}_σ(φ, δ)`, the generic `twistedOrbitalIntegral` for the
  entrywise action of `σ`; the ordinary orbital integral is the generic `orbitalIntegral`;
* associated Haar measures on the two centralizers (HL I.2.5, "mesure associée");
* concordance of test functions at a pair `(δ, γ)` and concordance (HL I.2.5, Définition),
  with quotient measures entering only through `QuotientIntegration.IsCompatible`;
* regular and σ-regular support.

Every left coset space `LeftQuotient H` of a topological group carries its Borel
σ-algebra through the reducible definition `leftQuotientMeasurableSpace`, which this
module (and the two statement modules) installs as a local instance of high priority.
No measure is chosen or normalized inside a definition.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory
open Langlands.QuotientIntegration
open Langlands.TraceFormula
open Langlands.JacquetLanglands

universe u v w

section Instances

variable {G : Type w} [Group G] [TopologicalSpace G]

/-- The Borel σ-algebra on the left coset space `H \ G` of a topological group. It is a
reducible definition, installed as a local instance in the modules that use it, so that
it is preferred to Mathlib's quotient σ-algebra `Quotient.instMeasurableSpace`. -/
abbrev leftQuotientMeasurableSpace (H : Subgroup G) : MeasurableSpace (LeftQuotient H) :=
  borel (LeftQuotient H)

/-- The left coset space with `leftQuotientMeasurableSpace` is a Borel space. -/
theorem leftQuotient_borelSpace (H : Subgroup G) :
    @BorelSpace (LeftQuotient H) _ (leftQuotientMeasurableSpace H) :=
  @BorelSpace.mk _ _ (leftQuotientMeasurableSpace H) rfl

end Instances

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

section Centralizers

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]

/-- HL's σ-centralizer `G^σ_δ(F) = {x ∈ GL_n(E) | x⁻¹ δ x^σ = δ}` of `δ ∈ GL_n(E)`
(HL I.2.2, printed p. 11): the twisted centralizer for the entrywise action of `σ`. -/
abbrev sigmaCentralizer (σ : E ≃ₐ[F] E) (n : ℕ) (δ : GeneralLinear n E) :
    Subgroup (GeneralLinear n E) :=
  twistedCentralizer (entrywiseAut σ n) δ

/-- HL's centralizer `G_γ(F)` of `γ ∈ GL_n(F)` (HL I.2.4, printed p. 14), stated as the
twisted centralizer for the identity twist, so that its coset space is the domain of the
quotient measure in `orbitalIntegral γ ν f`. -/
abbrev glCentralizer {n : ℕ} (γ : GeneralLinear n F) : Subgroup (GeneralLinear n F) :=
  twistedCentralizer (MonoidHom.id (GeneralLinear n F)) γ

/-- Lemma 7: membership in the σ-centralizer. -/
theorem mem_sigmaCentralizer (σ : E ≃ₐ[F] E) (n : ℕ) (δ x : GeneralLinear n E) :
    x ∈ sigmaCentralizer σ n δ ↔ x⁻¹ * δ * entrywiseAut σ n x = δ :=
  Iff.rfl

/-- Lemma 8: `G_γ(F)` is the ordinary centralizer of `γ`. -/
theorem glCentralizer_eq_centralizer {n : ℕ} (γ : GeneralLinear n F) :
    glCentralizer γ = Subgroup.centralizer {γ} :=
  twistedCentralizer_id γ

/-- Lemma 9: conjugation by `x` carries `G^σ_δ(F)` into `G^σ_{δ'}(F)` with
`δ' = x⁻¹ δ x^σ`. -/
theorem conj_mem_sigmaCentralizer (σ : E ≃ₐ[F] E) (n : ℕ) {δ c : GeneralLinear n E}
    (hc : c ∈ sigmaCentralizer σ n δ) (x : GeneralLinear n E) :
    x⁻¹ * c * x ∈ sigmaCentralizer σ n (x⁻¹ * δ * entrywiseAut σ n x) := by
  rw [mem_sigmaCentralizer] at hc ⊢
  calc (x⁻¹ * c * x)⁻¹ * (x⁻¹ * δ * entrywiseAut σ n x) * entrywiseAut σ n (x⁻¹ * c * x)
      = x⁻¹ * (c⁻¹ * δ * entrywiseAut σ n c) * entrywiseAut σ n x := by
        simp only [map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
    _ = x⁻¹ * δ * entrywiseAut σ n x := by rw [hc]

end Centralizers

section OrbitalIntegrals

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]
variable [TopologicalSpace E] [IsTopologicalRing E]

/-- HL's σ-orbital integral `Λ^{G(E)}_σ(φ, δ) = ∫ φ(x⁻¹ δ x^σ) dν(x)` over
`G^σ_δ(F) \ G(E)` (HL I.2.4, printed pp. 15–16), for a supplied measure `ν` on the left
coset space: the generic twisted orbital integral for the entrywise action of `σ`. -/
abbrev sigmaOrbitalIntegral (σ : E ≃ₐ[F] E) (n : ℕ) (δ : GeneralLinear n E)
    (ν : Measure (LeftQuotient (sigmaCentralizer σ n δ))) (φ : GeneralLinear n E → ℂ) : ℂ :=
  twistedOrbitalIntegral (entrywiseAut σ n) δ ν φ

end OrbitalIntegrals

section Concordance

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
variable {n : ℕ}
variable [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
variable [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]

/-- HL's associated measure (HL I.2.5, printed p. 17), for `γ` regular: there is `x` with
`x⁻¹ N(δ) x = γ` such that the measure `μδ` on `G^σ_δ(F)`, transported by `c ↦ x⁻¹ c x`,
and the measure `μγ` on `G_γ(F)`, transported by the inclusion `GL_n(F) → GL_n(E)`, are
the same measure on `GL_n(E)`. -/
def IsAssociatedMeasure (σ : E ≃ₐ[F] E) (l : ℕ) (δ : GeneralLinear n E)
    (γ : GeneralLinear n F) (μδ : Measure (sigmaCentralizer σ n δ))
    (μγ : Measure (glCentralizer γ)) : Prop :=
  ∃ x : GeneralLinear n E, x⁻¹ * cyclicNorm σ l δ * x = baseChange F E n γ ∧
    Measure.map (fun c : sigmaCentralizer σ n δ => x⁻¹ * (c : GeneralLinear n E) * x) μδ =
      Measure.map (fun t : glCentralizer γ => baseChange F E n (t : GeneralLinear n F)) μγ

/-- HL's "φ et f concordent en (δ, γ)" (HL I.2.5, Définition, printed p. 17), for the
measures `μF` on `GL_n(F)` and `μE` on `GL_n(E)`: for all right Haar measures `μδ` on
`G^σ_δ(F)` and `μγ` on `G_γ(F)` that are associated, and all quotient measures `νδ`,
`νγ` compatible with `μE / μδ` and `μF / μγ`, the σ-orbital integral of `φ` at `δ`
equals the orbital integral of `f` at `γ`. -/
def ConcordAt (σ : E ≃ₐ[F] E) (l : ℕ) (μF : Measure (GeneralLinear n F))
    (μE : Measure (GeneralLinear n E)) (φ : GeneralLinear n E → ℂ)
    (f : GeneralLinear n F → ℂ) (δ : GeneralLinear n E) (γ : GeneralLinear n F) : Prop :=
  ∀ (μδ : Measure (sigmaCentralizer σ n δ)) [μδ.IsHaarMeasure] [μδ.IsMulRightInvariant]
    (μγ : Measure (glCentralizer γ)) [μγ.IsHaarMeasure] [μγ.IsMulRightInvariant]
    (νδ : Measure (LeftQuotient (sigmaCentralizer σ n δ)))
    (νγ : Measure (LeftQuotient (glCentralizer γ))),
    IsCompatible (sigmaCentralizer σ n δ) μE μδ νδ →
    IsCompatible (glCentralizer γ) μF μγ νγ →
    IsAssociatedMeasure σ l δ γ μδ μγ →
    sigmaOrbitalIntegral σ n δ νδ φ = orbitalIntegral γ νγ f

/-- The orbital integrals of `f` vanish at every regular semisimple `γ` that is not a norm,
for every right Haar measure on `G_γ(F)` and every compatible quotient measure. -/
def VanishesOffNorms (σ : E ≃ₐ[F] E) (l : ℕ) (μF : Measure (GeneralLinear n F))
    (f : GeneralLinear n F → ℂ) : Prop :=
  ∀ γ : GeneralLinear n F, IsRegularSemisimple γ → ¬ IsNorm σ l γ →
    ∀ (μγ : Measure (glCentralizer γ)) [μγ.IsHaarMeasure] [μγ.IsMulRightInvariant]
      (νγ : Measure (LeftQuotient (glCentralizer γ))),
      IsCompatible (glCentralizer γ) μF μγ νγ → orbitalIntegral γ νγ f = 0

/-- HL's "φ et f concordent" (HL I.2.5, Définition, printed p. 17): the orbital integrals
of `f` vanish at regular non-norms, and `φ` and `f` concord at every associated pair
`(δ, γ)` with `γ` regular semisimple. -/
def AreConcordant (σ : E ≃ₐ[F] E) (l : ℕ) (μF : Measure (GeneralLinear n F))
    (μE : Measure (GeneralLinear n E)) (φ : GeneralLinear n E → ℂ)
    (f : GeneralLinear n F → ℂ) : Prop :=
  VanishesOffNorms σ l μF f ∧
    ∀ (δ : GeneralLinear n E) (γ : GeneralLinear n F), IsNormAssociated σ l δ γ →
      IsRegularSemisimple γ → ConcordAt σ l μF μE φ f δ γ

end Concordance

section Support

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E] {n : ℕ}

/-- `f` is supported in the regular semisimple set `G(F)_r` (HL I.2.5, printed p. 18). -/
def IsRegularSupported (f : GeneralLinear n F → ℂ) : Prop :=
  ∀ g : GeneralLinear n F, f g ≠ 0 → IsRegularSemisimple g

/-- `φ` is supported in the σ-regular set `G(E)_{σ-r}` (HL I.2.5, printed p. 18). -/
def IsSigmaRegularSupported (σ : E ≃ₐ[F] E) (l : ℕ) (φ : GeneralLinear n E → ℂ) : Prop :=
  ∀ δ : GeneralLinear n E, φ δ ≠ 0 → IsSigmaRegular σ l δ

end Support

end Langlands.BaseChange
