# Trivial unipotent radical under extension of algebraically closed fields: proof

Authors: Worker 1401 and Worker 1524.

This module proves `Langlands.GroupScheme.AlgebraicallyClosedRadicalFieldExtensionStatement`,
stated in `Langlands.GroupScheme.Reductive.RadicalFieldExtensionStatement`. The theorem
`Langlands.GroupScheme.algebraicallyClosedRadicalFieldExtensionStatement` has exactly that
proposition as its type, at an arbitrary universe `u`. Its kernel check uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Main theorem

Let `k ⊆ K` be algebraically closed fields in universe `u` and let `G` be a smooth affine
group scheme over `Spec k` with `HasTrivialUnipotentRadical G`. Then the base change
`G_K = (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G`
satisfies `HasTrivialUnipotentRadical G_K`. That is, every smooth connected unipotent group
scheme `H'` over `Spec K` with a closed subgroup `i : H' ⟶ G_K` of normal range has
`SubgroupFunctor.range i = ⊥`, with the range and normality tested on all schemes over
`Spec K`.

The hypothesis `ConnectedSpace G.X.left` of the target is not used. No unproved statement is
assumed: in particular the proof does not use
`Langlands.GroupScheme.ConnectedReductiveFieldExtensionStatement` (the intended consumer of
the target) or any spreading-out or `G_a`-series statement. The extension `K / k` may be
transcendental of any degree, and the characteristic is arbitrary.

The entry theorem applies
`RadicalFieldExtension.algebraicallyClosedRadicalFieldExtensionStatement_of_rationalSide`
(module `KSide`) to `RadicalFieldExtension.rationalSide` (module `RationalSide`).

## Structure of the proof

The helper modules live in `Langlands/GroupScheme/Reductive/RadicalFieldExtension/`, in
namespace `Langlands.GroupScheme.RadicalFieldExtension`. Each has its own Markdown with the
precise statements and proofs. All of them are internal to this proof.

- `Unipotence`: a smooth affine connected group scheme over an algebraically closed field,
  with a solvable group of rational points that all act unipotently in some closed-immersion
  representation `ρ : H → GL_N`, is unipotent (`IsUnipotent`). This is the Lie–Kolchin
  argument on rational points.
- `RationalSideInterface`: the proposition `RationalSideStatement`, the contradiction
  obtained over the small field `k`. It is an internal interface that lets the two halves of
  the proof be compiled separately.
- `Laws`: normal law systems. Finitely many polynomial identities record that a normal
  solvable group of `K`-points of the coordinate Hopf algebra `H` of `G` kills fixed
  functions `u l ∈ H`. These identities descend to a finitely generated `k`-subalgebra of
  `K` and specialize at a `k`-point. The algebraic core is
  `exists_isPrime_lt_of_normal_solvable`.
- `KSide`: the argument over the large field `K`. It proves
  `RationalSideStatement → AlgebraicallyClosedRadicalFieldExtensionStatement`.
- `RationalSide`: the argument over `k`. It proves `rationalSide : RationalSideStatement`.

## Outline

Fix `G` and a smooth connected unipotent closed subgroup `i : H' ⟶ G_K` of normal range.
Choose a closed-immersion representation `ρ : G → GL_N` (`affineLinearEmbeddingStatement`)
and let `u(a, b) ∈ H` be the `(a, b)` entry of `(M - 1)^N`, where `M` is the universal
matrix of `ρ`.

1. *Over `K` (module `KSide`).* Let `S` be the group of `K`-points of `G_K` that lie in the
   range of `i`, viewed as `k`-algebra maps `H → K`. It is normal, it is solvable because
   `H'` is unipotent, and its members kill every `u(a, b)` because `H'` acts unipotently
   in `ρ_K`. Let `Q ⊆ K ⊗[k] H` be the prime of functions vanishing on `S` (the kernel of
   `i^*`), and `P ⊆ H` the augmentation ideal. Every element of `Q` maps to zero in
   `K ⊗[k] (H/P)`, because every `k`-algebra map `H → K` killing `P` is the identity point,
   which lies in `S`.
   - If `1 ⊗ p ∈ Q` for every `p ∈ P`, every member of `S` is the identity point. Since `K`
     is algebraically closed and `G_K` is separated, `range i = ⊥`.
   - Otherwise the algebraic core of module `Laws` spreads the data out over a finitely
     generated `k`-subalgebra of `K` and specializes at a `k`-point. It produces a prime
     `𝔭 < P` of `H` and a normal solvable group `Γ` of `k`-points that kill every
     `u(a, b)` and contain every `k`-point whose kernel contains `𝔭`. Transported to
     rational points of `G`, these are the hypotheses of `RationalSideStatement`.
2. *Over `k` (module `RationalSide`).* Given such `𝔭` and `Γ`, let `Z ⊆ G` be the smooth
   closed subgroup on the closure of the locations of `Γ` and `Z⁰` its identity component.
   `Z⁰` is unipotent (module `Unipotence`, since `Γ` and hence its closure act unipotently
   and are solvable), normal in `G` (conjugation preserves the closure of a normal group of
   points), smooth and connected. So `HasTrivialUnipotentRadical G` makes `Z⁰` trivial.
   But the generic point of `V(𝔭)` lies on `Z` and specializes to the identity, so it lies
   on `Z⁰`; then it is the identity point, and `𝔭 = P`, contradicting `𝔭 < P`.

## Correspondence with the sources

The target cites B. Conrad, *Reductive group schemes* (2014), Exercise 3.4.1 (p.104), and
J. S. Milne, *Algebraic Groups* (2017), Propositions 19.5 and 19.13 (pp.398–400). Their
argument spreads a nontrivial unipotent normal subgroup of `G_K` out over a finitely
generated `k`-subalgebra `A ⊆ K` and specializes it at a `k`-point of `Spec A`.

This proof follows the same plan, with two changes of route:

- The subgroup is not spread out as a group scheme over `A`. Its group `S` of `K`-points is
  encoded by finitely many polynomial identities (module `Laws`); these are spread out and
  specialized, giving a normal solvable group `Γ` of `k`-points. Module `RationalSide`
  then rebuilds a subgroup scheme of `G` from `Γ` as the identity component of its Zariski
  closure.
- Instead of Conrad's composition series with `G_a` quotients, unipotence is recorded by the
  vanishing of the entries of `(ρ(g) - 1)^N`, and recovered over `k` by the Lie–Kolchin
  argument of module `Unipotence`. Nontriviality is recorded by the strict inclusion
  `𝔭 < P`.

The descent of law systems and the step from `Γ` back to a closed subgroup reuse the points
and Hopf-algebra machinery of `Langlands.GroupScheme.Absolute.BorelFieldExtensionDescent`,
`BorelFieldExtensionMaximality` and `BorelFieldExtensionKSide`.
