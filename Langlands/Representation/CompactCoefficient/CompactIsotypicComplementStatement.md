# The isotypic decomposition along an irreducible compact representation: statement

Author: Worker 6. Module `Langlands.Representation.CompactCoefficient.CompactIsotypicComplementStatement`, namespace `Langlands.Renard.CompactRepresentation`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, IV.1.4, Theorem, printed p.90 / PDF p.96, together with IV.1.5, Proposition (iii) and Remark 1, printed pp.93–94 / PDF pp.99–100. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

This is a statement unit: nothing is proved.

## The source

In IV.1.3–IV.1.5, `G` is a t.d. group, unimodular and countable at infinity.

- **IV.1.4, Theorem.** Let `(τ, W)` be an irreducible compact representation of `G`. Every representation `(π, V)` of `M(G)` decomposes as `V = V(τ) ⊕ V(τ)^⊥`, where `V(τ)` is a direct sum of representations isomorphic to `(τ, W)` and no irreducible subquotient of `V(τ)^⊥` is isomorphic to `(τ, W)`.
- **IV.1.5, Proposition (iii).** `V = Im π(e_τ) ⊕ ker π(e_τ)` is a decomposition into subrepresentations. `Im π(e_τ)` is a direct sum of irreducible subrepresentations equivalent to `τ`, and no irreducible subquotient of `ker π(e_τ)` is equivalent to `τ`. The proof of this Proposition completes the proof of the Theorem.
- **IV.1.5, Remark 1.** `ker π(e_τ)` is the only `G`-invariant complement of `Im π(e_τ)`.

## The Lean statement

`CompactIsotypicComplementStatement` quantifies over the following data.

- A group `G` with a topology making it a Hausdorff, locally compact, totally disconnected, σ-compact topological group, carrying Borel measurable structure.
- A regular Haar measure `μ` on `G` that is also right invariant. It only expresses unimodularity, with the same binders as the published `CompactCoefficientProjectorStatement` and the companion IV.1.5 statement `CompactProjectionDistributionStatement`.
- An irreducible `τ : SmoothRep.{0, u, v} ℂ G` with `HasCompactSmoothDualCoefficients τ.representation`. This published predicate says that every matrix coefficient `g ↦ λ(τ(g) w)` with `λ` smooth has compact support, which is Renard's notion of compactness by IV.1.3, Theorem.
- A smooth representation `V : SmoothRep.{0, u, v} ℂ G`.

Let `isotypic` be `⨆ f, f.range`, the supremum over all intertwiners `f : τ → V` of their images. This is Renard's `V(τ)`: a nonzero intertwiner from the irreducible `τ` is injective, so its image is a subrepresentation isomorphic to `τ`, and every such subrepresentation arises this way. The conclusion is the conjunction of:

1. **Direct sum of copies of `τ`.** There is a set `s` of intertwiners `τ → V`, all injective, whose images are independent (`iSupIndep`) and have supremum `isotypic`.
2. **Unique complement (Remark 1).** There is exactly one subrepresentation `S` with `IsCompl isotypic S`.
3. **No `τ` in the complement.** For every `S` with `IsCompl isotypic S` and every `B : SmoothRep.{0, u, v} ℂ G` with `SmoothRep.IsSubquotient B (SmoothRep.subrepresentation V S)`, `B` is not isomorphic to `τ`.

`SmoothRep.IsSubquotient B A` is the published subquotient relation (module `Category/Subquotients`): `B` is isomorphic to a quotient `S / T` of a subrepresentation `S` of `A` by a subrepresentation `T` of `S`. Part 3 applies to the unique complement of part 2, which is Renard's `V(τ)^⊥ = ker π(e_τ)`. Isomorphism to `τ` already forces irreducibility, so part 3 says that no irreducible subquotient of `V(τ)^⊥` is isomorphic to `τ`.

## Relation to published statements

The published `CompactCoefficientProjectorStatement` (Bernstein–Zelevinsky 2.42–2.44, module `CompactCoefficient/ProjectorStatement`) asserts a natural idempotent family `P c V` with range the isotypic part `isotypicSubrepresentation c V` and kernel the annihilator `annihilatorSubrepresentation c V`, the intersection of the kernels of all intertwiners `V → τ`. That gives the decomposition `V = V(τ) ⊕ V(τ)^⊥`. The present statement records the remaining source assertions in Renard's form: the direct-sum structure of `V(τ)`, the uniqueness of the complement, and the absence of subquotients isomorphic to `τ` in it. The last property is stronger in form than the vanishing of all intertwiners to `τ`. Renard deduces it from the exactness of `V ↦ π(e_τ) · V` (IV.1.5.1).

## Remarks

- The representations `τ`, `V` and `B` share the carrier universe `v`.
- The proof is not formalized here. It goes through the idempotents `e_{K,τ}` of IV.1.5 (`CompactProjectionDistributionStatement`), Lemma A.VII for the direct sum, naturality of `π(e_τ)` for uniqueness, and exactness of (IV.1.5.1).
