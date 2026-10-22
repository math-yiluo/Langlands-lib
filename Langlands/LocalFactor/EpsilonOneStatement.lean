import Langlands.LocalFactor.NonabelianSystem

/-!
# Tate's `ε₁` normalization and its Galois equivariance

Tate (3.6.10) writes `ε₁(V, ψ) = ε_D(V, ψ, dx₁)`, where `dx₁` gives the ring of
integers volume one, and asserts `ε₁(V^σ, ψ^σ) = ε₁(V, ψ)^σ` for every field
automorphism `σ` of `ℂ` in the nonarchimedean case, by unicity and the rank-one
formula (3.6.11). Here `ε₁` is not a new definition: every clause evaluates the
supplied constant at a supplied Haar measure of integer volume one. The conjugate
objects `V^σ` and `ψ^σ` are described relationally, by a `σ`-semilinear bijective
intertwiner and by pointwise conjugate values. These are propositions only.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.EpsilonOne

open CommonClosure VirtualRepresentation

section Abelian

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The quotient `Oˣ / U^a` of the integral units `U⁰ = Oˣ` by the unit level `U^a`,
the index set of the sum in Tate (3.6.11). -/
abbrev UnitQuotient (a : ℕ) :=
  T.principalUnits 0 ⧸ (T.principalUnits a).subgroupOf (T.principalUnits 0)

/-- Tate (3.6.11): for a Haar measure giving `O` volume one and any `c` of order
`a(χ) + n(ψ)`, `ε₁(χ, ψ) = χ(c) q^(n(ψ)) ∑_(u ∈ Oˣ mod π^(a(χ))) χ⁻¹(u) ψ(u/c)`, the
sum running over any system of representatives of `Oˣ / U^(a(χ))`. The printed
display omits `ψ` and the inverse on `χ(u)`; this is the formula that follows from
(3.2.6.1) and (3.2.6.2), as Tate says. -/
def RankOneFormulaStatement : Prop :=
  letI := T.topology
  ∀ (χ : HarmonicAnalysis.Quasicharacter F.Carrier)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)
    (μ : @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology
      (@borel F.Carrier T.topology)),
    T.integerVolume μ = 1 →
    ∀ c : F.Carrierˣ,
      T.ord (c : F.Carrier) = T.additiveConductor ψ + (T.multiplicativeConductor χ : ℤ) →
    ∀ r : UnitQuotient T (T.multiplicativeConductor χ) → T.principalUnits 0,
      (∀ x, (r x : UnitQuotient T (T.multiplicativeConductor χ)) = x) →
      T.abelianEpsilonExpression χ ψ μ =
        (χ c : ℂ) * (T.residueCardinality : ℂ) ^ T.additiveConductor ψ *
          ∑ᶠ x : UnitQuotient T (T.multiplicativeConductor χ),
            (χ (r x : F.Carrierˣ) : ℂ)⁻¹ *
              ψ.complex (((r x : F.Carrierˣ) : F.Carrier) / (c : F.Carrier))

/-- The rank-one case of Tate's equivariance, `ε₁(χ^σ, ψ^σ) = ε₁(χ, ψ)^σ`, at a Haar
measure giving `O` volume one: `χ'` and `ψ'` take the `σ`-conjugate values of `χ`
and `ψ`. -/
def AbelianGaloisStatement : Prop :=
  letI := T.topology
  ∀ (σ : ℂ ≃+* ℂ) (χ χ' : HarmonicAnalysis.Quasicharacter F.Carrier),
    (∀ u : F.Carrierˣ, (χ' u : ℂ) = σ (χ u : ℂ)) →
    ∀ ψ ψ' : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier,
      (∀ y : F.Carrier, ψ'.complex y = σ (ψ.complex y)) →
    ∀ μ : @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology
        (@borel F.Carrier T.topology),
      T.integerVolume μ = 1 →
      T.abelianEpsilonExpression χ' ψ' μ = σ (T.abelianEpsilonExpression χ ψ μ)

end Abelian

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Tate (3.6.10): `ε₁(V^σ, ψ^σ) = ε₁(V, ψ)^σ` for every automorphism `σ` of `ℂ`, at
every intermediate field of the common closure. Here `ε₁` is the supplied
constant at a Haar measure giving the ring of integers volume one, `ψ'` takes the
`σ`-conjugate values of `ψ`, and `B` is a `σ`-conjugate of the genuine continuous
representation `A`: some `σ`-semilinear bijection `A → B` intertwines the actions. -/
def GaloisEquivarianceStatement : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (_hε : NonabelianSystem.IsSystem F e ε) (E : Extension F) (σ : ℂ ≃+* ℂ),
    letI := (fieldData F E).topology
    ∀ ψ ψ' : AdditiveCharacter F E,
    (∀ y : E.field, ψ'.complex y = σ (ψ.complex y)) →
    ∀ μ : HaarMeasure F E, (fieldData F E).integerVolume μ = 1 →
    ∀ (A B : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
      (hA : A.IsContinuous) (hB : B.IsContinuous) (f : A →ₛₗ[σ.toRingHom] B),
      Function.Bijective f →
      (∀ (g : weilSubgroup F E) (v : A),
        f (A.representation g v) = B.representation g (f v)) →
      (ε E ψ' μ (ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate F E) ⟨B, hB⟩) :
          ℂ) =
        σ (ε E ψ μ (ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate F E) ⟨A, hA⟩))

end Langlands.LocalFactor.EpsilonOne

namespace Langlands.LocalFactor

/-- Tate (3.6.10) and (3.6.11) in the nonarchimedean case: the rank-one formula
for `ε₁` and its rank-one Galois equivariance for every topological datum of every
p-adic field, and Galois equivariance of `ε₁` for every supplied local-constant
system on the common closure. -/
def EpsilonOneStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p),
    (∀ T : F.TopologicalData,
      EpsilonOne.RankOneFormulaStatement T ∧ EpsilonOne.AbelianGaloisStatement T) ∧
      EpsilonOne.GaloisEquivarianceStatement.{uF, uV} F

end Langlands.LocalFactor
