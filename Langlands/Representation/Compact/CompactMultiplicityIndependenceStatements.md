# Multiplicities for compact groups and independence of compact coefficients: statements

Module `Langlands.Representation.Compact.CompactMultiplicityIndependenceStatements`.
Namespace `Langlands.Renard.CompactRepresentation`.
Entry proposition `CompactMultiplicityIndependenceStatements`; nothing is
proved here.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read IV.1.1–IV.1.3 (printed pp.87–90 / PDF pp.93–96) and IV.3.3
(printed pp.100–102 / PDF pp.106–108). The two assertions stated here are the
last ones of these passages that had no Lean statement.

**IV.1.1, after the Corollary** (printed p.89 / PDF p.95). `K` is a compact
t.d. group and `K̂` the set of classes of irreducible smooth representations of
`K`. For a smooth representation `(π, V)` of `K` and `(σ, V_σ) ∈ K̂`, `V(σ)` is
the image of the canonical map `Hom_K(V_σ, V) ⊗ V_σ → V`, `φ ⊗ v ↦ φ(v)`:

> On appelle `V(σ)` la composante isotypique de type `σ` de `V`. La dimension de
> `Hom_K(V_σ, V)`, que nous noterons `m(σ)`, s'appelle la multiplicité de `σ`
> dans `V`. Lorsque cette dimension est finie, on a :
> `m(σ) = dim V(σ)/dim V_σ`.

**IV.3.3, Corollary, last sentence** (printed p.102 / PDF p.108). The
Corollary says that matrix coefficients `φ_{vᵢ,λᵢ}` of pairwise non-equivalent
irreducible representations, essentially square-integrable modulo the centre
with a common central character, with nonzero `vᵢ ∈ Vᵢ` and `λᵢ ∈ Ṽᵢ`, are
linearly independent, and ends:

> La même conclusion prévaut si l'on considère des représentations compactes
> irréductibles.

The proof adds: "Si les représentations sont compactes, le centre de `G` est
compact (lemme IV.1.3). Il n'y a alors pas besoin de quotienter par le centre
et on adapte les démonstrations précédentes." Chapter IV's standing
hypotheses for compact representations (IV.1.3–IV.1.4) are that `G` is a t.d.
group, unimodular and countable at infinity; a representation is compact when
its coefficients have compact support (IV.1.3, Definition and Theorem).

The rest of IV.1.1 is published: the Theorem in `CompactGroupSmoothStatements`
and the Corollary in `CompactGroupIsotypicDecompositionStatement`, whose
Markdown records that the multiplicity formula is not stated there. The
square-integrable case of the IV.3.3 Corollary is the published
`CoefficientLinearIndependenceStatement` (`UnitarySquareIntegrableStatements`),
whose Markdown records that the compact case is not stated there.

## The objects

- Smooth representations are `SmoothRep.{0, u, v} ℂ G`; irreducibility is
  `SmoothRep.IsIrreducible`; `Hom_K(V_σ, V)` is the complex vector space
  `σ.representation.IntertwiningMap π.representation` of Mathlib intertwiners.
- `V(σ)` is written in the statement as
  `⨆ f : σ.representation.IntertwiningMap π.representation, f.range`, the sum
  of the images of all intertwiners `σ → π`. This is exactly the image of
  `Hom_K(V_σ, V) ⊗ V_σ → V`, and for the class `c` of `σ` it is the published
  `CompactCoefficientClass.isotypicSubrepresentation c π`
  (`isotypicSubrepresentation_eq_iSup_range`), used in the published
  IV.1.1 Corollary statement.
- "Compact" is the published `HasCompactSmoothDualCoefficients`.
- `φ_{v,λ}` is the published `matrixCoefficient ρ λ v`, the function
  `g ↦ λ(ρ(g) v)`; `Ṽ` is the published `SmoothDual`, the smooth vectors of the
  algebraic dual, coerced to `Module.Dual`.

## The Lean statements

### `CompactGroupMultiplicityStatement` (IV.1.1)

For a compact, Hausdorff, totally disconnected topological group `K`, smooth
`π, σ : SmoothRep.{0, u, v} ℂ K` with `σ` irreducible, and
`FiniteDimensional ℂ (Hom_K(V_σ, V))`: `V(σ)` is finite-dimensional and
`finrank V(σ) = finrank Hom_K(V_σ, V) * finrank V_σ`.

Since `V_σ` is finite-dimensional (IV.1.1 Theorem (i)) and nonzero, this is
`m(σ) = dim V(σ)/dim V_σ`. Stating it multiplicatively avoids natural-number
division; the finite-dimensionality conclusion is needed because `finrank`
is `0` on infinite-dimensional spaces. The group hypotheses are those of the
published IV.1.1 statements.

### `CompactCoefficientLinearIndependenceStatement` (IV.3.3, Corollary, last sentence)

For `G` Hausdorff, locally compact, totally disconnected and `SigmaCompactSpace`
(countable at infinity), with its Borel structure and a regular Haar measure
`μ` that is also right invariant (unimodular), every `r` and every family
`π : Fin r → SmoothRep.{0, u, v} ℂ G` of irreducible representations with
compact coefficients that are pairwise non-isomorphic (`IsEmpty (π i ≅ π j)`
for `i ≠ j`), and all nonzero `x i ∈ π i` and nonzero
`ℓ i : SmoothDual (π i).representation`, the family
`i ↦ matrixCoefficient (π i).representation (ℓ i) (x i)` is linearly
independent over `ℂ` in `G → ℂ`. The group binders are those of the published
IV.1.4 and IV.1.7 statements; the measure only expresses unimodularity.

No common central character is assumed. The source sentence transfers the
Corollary's conclusion to compact representations; in that case the centre is
compact and the proof works on `G` itself, where non-isomorphic irreducible
compact representations are orthogonal whatever their central characters.
Dropping the condition gives an assertion at least as strong as the source's
under either reading.

### `CompactMultiplicityIndependenceStatements`

The conjunction of the two statements, at independent universes `u` (group)
and `v` (carriers).

## Scope

This file states the two assertions and proves neither. Proofs belong to a
separate `lean.proof@1` task targeting
`CompactMultiplicityIndependenceStatements`. Routes: for IV.1.1, the published
isotypic decomposition and Schur's lemma for `σ` give
`V(σ) ≅ Hom_K(V_σ, V) ⊗ V_σ`; for IV.3.3, the orthogonality relations on `G`
for compact representations (the formal-degree statements of
`CompactFormalDegreeStatements`, IV.1.4) applied as in the source's proof of
the Corollary.

The file imports `Langlands.Representation.CompactCoefficient.Classes`,
`Langlands.Representation.SubrepresentationLattice`,
`Langlands.Representation.MatrixCoefficient.Definitions`,
`Langlands.Representation.Smooth.Contragredient.Definitions` and pinned Mathlib
`Mathlib.MeasureTheory.Measure.Haar.Basic` (environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`).
