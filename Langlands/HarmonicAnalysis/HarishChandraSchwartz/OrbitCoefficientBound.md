# Coefficients bounded by `Ξ` along unitary unramified orbits

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitCoefficientBound`, namespace
`Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitWavePacket` (Library,
  this author's Unit 20). Only the last section uses it, for the actual objects `rationalLeviXi`
  (`Ξ^{M_I}`), `RationalPointFamily.leviRationalNormCharacters` and `standardLeviPoints`. Through
  its imports come the Library's `UnitaryOrbitRepresentative`, `unitaryUnramifiedInclusion`,
  `unramifiedCharacter_isOpen_ker`, `IrreducibleAdmissibleRep.twist`, `SmoothRep.equivOfIso` and
  `contragredientMap`.
- `Langlands.Representation.Twist.SmoothPartDefinitions` (Library):
  `smoothContragredientTwistEquiv`, which identifies the smooth dual of a twist `ρ ⊗ χ` with the
  smooth dual of `ρ` and keeps each functional.

## Source and provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
pages; the PDF page is the printed page minus 234.

- Lemma VI.2.2, printed p. 298: "Soit `ψ ∈ C^∞(O, P)`. Il existe `C > 0` tel que pour tout
  `ω ∈ O` et tout `g ∈ G`, on ait l'inégalité `|(E_P^G ψ_ω)(g)| ⩽ CΞ(g)`." Its proof reduces to
  coefficients of `I_P^G(ω ⊗ χ)` for all `χ ∈ Im X(M)` and, printed p. 299, uses the bound
  "D'après le Corollaire III.1.2, il existe donc `C > 0` tel que, pour tout `g ∈ G` et tout
  `k ∈ K`, on ait `|⟨ω(m_P(kg))v(k_P(kg)), v̌(k)⟩| ⩽ CΞ^M(m_P(kg))`."

- Corollary III.1.2, printed p. 263: "Supposons `π` de carré intégrable. Alors pour tout
  `f ∈ A(π)` et tout `r ∈ R`, il existe `c > 0` tel que pour tout `g ∈ G¹`, on ait l'inégalité
  `|f(g)| ⩽ cΞ(g)(1 + σ(g))^{−r}`."

The author checked these quotations on the PDF text of pages 29, 64 and 65.

The definition `HasXiBoundedCoefficients Ξ ρ` (provenance: derived) names this bound: every
smooth coefficient of `ρ` is at most `c Ξ`. The units of this author on actual points (Units
19–27) take it as the hypothesis `hcoeff` for `π` and, for the orbit results of Units 26 and 27,
as `hcoeffA` for every representative of the orbit. The source does not state the transfer
results separately: in the proof of Lemma VI.2.2 the factor `χ(m_P(kg))` has absolute value `1`,
which is the twist result here. The equivalence and orbit results are elementary consequences.

## Contents

Section `Bound`: `G` a group with a topology, `V`, `W` complex vector spaces, `Ξ : G → ℝ`.

- **`HasXiBoundedCoefficients Ξ ρ`** (definition, the recorded declaration), for
  `ρ : Representation ℂ G V`: for all `v : V` and `ℓ : SmoothDual ρ` there is `c > 0` with
  `‖ℓ(ρ(g) v)‖ ≤ c Ξ(g)` for all `g`.
- **`HasXiBoundedCoefficients.of_equiv Φ h`** (with `G` a topological group): for an equivalence
  `Φ : ρ.Equiv σ` of representations, the bound for `ρ` gives the bound for `σ`.
- **`HasXiBoundedCoefficients.twist χ hχ hχu h`**: for a character `χ : G →* ℂˣ` with open kernel
  (`hχ`) and `‖χ(g)‖ = 1` for all `g` (`hχu`), the bound for `ρ` gives the bound for the twist
  `Langlands.twist χ ρ : g ↦ χ(g) ρ(g)`.

Section `Orbit`: `G` a nonarchimedean topological group, `M` a subgroup, `ν : I → (M →* ℝ≥0ˣ)`
(defining the unramified characters of `M`), `π` an irreducible admissible representation of `M`.

- **`HasXiBoundedCoefficients.unitaryOrbitRepresentative ν π h A`**: for `Ξ : M → ℝ`, if `π` has
  the bound (`h`), then so does every `A : UnitaryOrbitRepresentative ν π`, that is every
  irreducible admissible `A` isomorphic to `π ⊗ χ` for some unitary unramified character `χ`.

Section `Rational`: the actual setting of Units 20–27 (`G` over a nonarchimedean local field,
maximal split torus `i`, generic cocharacter `ν`, a finite set `I` of simple roots, `M_I(F)` the
subtype `𝐌`, `K` compact open with `hKc`, and
`hM : IsIwasawaPair (P₀(F) ∩ M_I(F)) (K ∩ M_I(F))`).

- **`rationalLeviXi_coefficientBound_unitaryOrbitRepresentative I hKc hM π hcoeff A v ℓ`**: if
  `hcoeff : ∀ v ℓ, ∃ c > 0, ∀ m, ‖ℓ(π(m) v)‖ ≤ c Ξ^{M_I}(m)` with `Ξ^{M_I} = rationalLeviXi hKc hM`,
  then for every `A : UnitaryOrbitRepresentative (leviRationalNormCharacters i ν I) π`, `v` and
  `ℓ` there is `c > 0` with `‖ℓ(A(m) v)‖ ≤ c Ξ^{M_I}(m)` for all `m`. The statement written with
  `∀ A v ℓ` in front is, word for word, the hypothesis `hcoeffA` of the orbit results of
  `RationalInducedConstantTermFourier` (Unit 26) and of `RationalCuspidalConvolution` (Unit 27).
  Applying this theorem to `hcoeff` therefore supplies `hcoeffA`, so those results need only
  `hcoeff` for `π`.

## Proofs

- `of_equiv`: given `w` and `ℓ ∈ SmoothDual σ`, apply `h` to `Φ⁻¹ w` and to the pulled-back
  functional `contragredientMap Φ ℓ = ℓ ∘ Φ`. Then `σ(g) w = Φ(ρ(g) Φ⁻¹ w)` because `Φ`
  intertwines (`isIntertwining`) and `Φ Φ⁻¹ w = w`, so the two coefficients are equal.
- `twist`: apply `h` to `v` and to `ℓ` viewed in `SmoothDual ρ` through
  `smoothContragredientTwistEquiv`. Then `ℓ(χ(g) ρ(g) v) = χ(g) ℓ(ρ(g) v)` by linearity, and
  `‖χ(g)‖ = 1`.
- `unitaryOrbitRepresentative`: the orbit membership of `A` gives `χ` and an equality of classes
  `[π ⊗ χ] = [A]`, hence an isomorphism `π ⊗ χ ≅ A` (`Quotient.exact`) and an equivalence of
  representations (`SmoothRep.equivOfIso`). The character `χ` has open kernel
  (`unramifiedCharacter_isOpen_ker`) and is unitary (the second component of its membership in
  `unitaryUnramifiedCharacters ν`). Apply `twist` and then `of_equiv`.
- The actual statement is `unitaryOrbitRepresentative` with `Ξ = rationalLeviXi hKc hM` and
  `ν = leviRationalNormCharacters i ν I`.

## Scope

The predicate is a bound for each pair `(v, ℓ)`. Uniformity in `v` or `ℓ` is not asserted.
Corollary III.1.2 (printed p. 263, quoted above) bounds coefficients on `G¹` only. The bound on
the whole group, as used in Lemma VI.2.2 for `M`, is not proved here; the units take it as a
hypothesis (`h`, `hcoeff`).
