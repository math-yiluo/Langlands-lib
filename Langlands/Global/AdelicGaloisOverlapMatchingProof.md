# Proof of the twisted split factorization with Galois inverse-orbit matching

Author: Worker 5268.

This module proves
`Langlands.Global.AdelicGaloisUnit.SplitGaloisOverlapMatchingStatement`
(module `Langlands.Global.AdelicGaloisOverlapMatching`) as the theorem
`splitGaloisOverlapMatching`. The statement is an implication: the split
fundamental-set theorem (F) and the split overlap estimate (Springer's
Proposition 2.6) are premises. The proof does not prove those two statements.
It carries out the first half of the proof of (C) in T. A. Springer,
*Reduction theory over global fields* (1994), §3.5: everything before the
Galois descent of the parabolic subgroup and the final contradiction.

Notation follows the statement's Markdown: `G_L = AffineWeil.unitBaseChange F L G`,
`Δ = simpleRelativeRoots i ν`, `j_H = Standard.parabolicHom i ν H` with
`P_H` its source, `|β(t)| = PositiveRealTorus.normCharacter L T β t`,
`innerIso n` is conjugation `x ↦ n x n⁻¹`, and `rationalSection` is the
adelic image of a rational point of `G_L`.

## Group-scheme lemmas

The group-scheme lemmas used below (`radicalGaloisHom_comp_innerIso`,
`range_comp_innerIso_of_mem`, `range_eq_of_innerIso_transport`, namespace
`Langlands.GroupScheme`) live in the helper module
`Langlands.GroupScheme.Rational.RadicalGaloisInnerTransport`, whose Markdown describes them.
They are statements about subgroup functors and inner automorphisms, with no adelic content.

## Existence of a Siegel setup for a given torus

`AdelicSiegelFactors.exists_isSiegelAlgebraicSetup` holds for a connected
reductive group over a number field with a maximal split torus `i` and a
generic cocharacter `ν`, both given. It produces `T₀` and `j : T₀ ⟶ T` with
`IsSiegelAlgebraicSetup F G T i ν T₀ j`. Its proof copies the Library proof
`siegelAlgebraicSetupExistence_of_structural` (module
`Langlands.Global.AdelicSiegelSetupExistence`). The only change is that `T`,
`i` and `ν` are fixed in advance instead of being chosen. The three structural
inputs of that theorem are used in their published proved forms:
`genericMinimalParabolic`, `derivedMaximalSplitTorus` and
`derivedCentralSplitTorusProduct`. This lemma is needed because
`SplitAdelicFundamentalSetStatement` takes a Siegel setup as a hypothesis.
Here the torus is fixed by the finite Galois split maximal model.

## The inverse-orbit matching step

`exists_inverseOrbitMatching` is the algebraic core. Assume the twisting
identities
`range (radicalGaloisHom j_(Δ\{β}) σ) = range (j_(Δ\{a_σ β}) ≫ innerIso m_σ)`,
with `a` an action of `Gal(L/F)` on `Δ` (`a 1 = id` and
`a (σ τ) = a σ ∘ a τ` on `Δ`). Fix `α ∈ Δ` and a rational point `q`. Assume
that for each `σ` the element `m_σ⁻¹ · σ(q) · q⁻¹` is the image of a rational
point `p_σ` of `P_(Δ\{α})`. Then the family `J τ = Δ \ {a_τ α}` satisfies
`J σ ⊆ Δ`, `J 1 = Δ \ {α}`, and the inverse-orbit matching condition of
`HasTwistedOverlapMatching` for the conjugation `innerIso q⁻¹`.

Proof, for a fixed `σ`. Let `β = a_{σ⁻¹} α`, which lies in `Δ`. The twisting
identity at `σ` and `β`, together with `a_σ β = α`, gives
`range (radicalGaloisHom j_(J σ⁻¹) σ) = range (j_(Δ\{α}) ≫ innerIso m_σ)`. By
`radicalGaloisHom_comp_innerIso`, the Galois translate of
`j_(J σ⁻¹) ≫ innerIso q⁻¹` is that translate followed by
`innerIso σ(q⁻¹)`. Then `range_eq_of_innerIso_transport` applies with
`c = σ(q⁻¹)`, `m = m_σ`, target point `q⁻¹` and `pt = p_σ⁻¹`. The required
identity `σ(q)⁻¹ · m_σ = q⁻¹ · (m_σ⁻¹ σ(q) q⁻¹)⁻¹` is checked by `group`.

## The dichotomy for one model

`hasTwistedOverlapMatching_of` proves `HasTwistedOverlapMatching F L G T i ν`.
Its hypotheses are the two premises (F) and Proposition 2.6, together with
the facts that `G_L` is connected reductive, that `i` is a maximal split and a
maximal torus, and that `ν` is generic. It also assumes
`HasGaloisBorelTwisting F L G T i ν`, which supplies the maps `φ_σ`, the
points `m_σ` and the action `a`.

1. *Fundamental set over `L`.* `exists_isSiegelAlgebraicSetup` gives a Siegel
   setup for `(T, i, ν)` over `L`. Then (F) gives a compact
   `C₁ ⊆ G_L(𝔸_L)¹` and a bound `c`. Let `C₀` be the image of `C₁` in
   `G_L(𝔸_L)`.
2. *The compact set.* Put `C = C₀ ∪ ⋃_σ φ_σ(C₀) · M_σ`, where
   `M_σ = rationalSection m_σ`. It is compact because each `φ_σ` is continuous
   and `Gal(L/F)` is finite.
3. *Thresholds.* For each `α ∈ Δ`, Proposition 2.6 over `L`, applied to `C`
   and `c`, gives a threshold `dα`. `Δ` is finite
   (`finite_simpleRelativeRoots`), so the set of these thresholds has a lower
   bound `d`, which serves every root.
4. *Factorization.* Given `g ∈ G(𝔸_F)¹`, (F) factors its scalar extension as
   `x · i(t) · j_∅(p) · q₀` with `x ∈ C₀ ⊆ C`, `i(t)` of norm one and
   `|β(t)| ≤ c` for every `β ∈ Δ`. Here `q` is the rational point of `G_L`
   corresponding to `q₀`, so `q₀ = rationalSection q`. This gives the first
   three clauses.
5. *Second factorization.* Suppose `|α(t)| ≤ d`. Fix `σ`. Apply `φ_σ` to the
   factorization. It fixes the scalar extension of `g` and sends
   `rationalSection q` to `rationalSection σ(q)`. By the torus and Borel
   clauses of the twist, it carries `i(t)` to `M_σ i(t') M_σ⁻¹` and `j_∅(p)`
   to `M_σ j_∅(p') M_σ⁻¹`. The point `i(t')` has norm one, and every simple-root
   norm of `t'` equals one of `t`, so it is at most `c`. Hence the same point
   equals
   `(φ_σ(x) M_σ) · i(t') · j_∅(p') · rationalSection (m_σ⁻¹ σ(q))`,
   and `φ_σ(x) M_σ ∈ C`. The identity is checked by `group` after rewriting.
6. *Overlap.* Proposition 2.6 applies, since `|α(t)| ≤ d ≤ dα`. It gives a
   rational point `r` of `P_(Δ\{α})` with image `m_σ⁻¹ σ(q) q⁻¹`, after the
   identification `rationalCoeffEquiv` of rational points.
7. *Matching.* `exists_inverseOrbitMatching` now gives the family `J` and the
   fourth clause.

`splitGaloisOverlapMatching` instantiates this result for
`D : FiniteGaloisSplitMaximalModel G`, with `L = D.carrier`, `T = D.torus`
and `i = D.inclusion`. It uses `D.isConnectedReductive`, `D.isMaximalTorus`,
`D.isSplitTorus` and the number-field instance
`NumberField.of_module_finite`.

## Axioms

`#print axioms splitGaloisOverlapMatching` reports only `propext`,
`Classical.choice` and `Quot.sound`.
