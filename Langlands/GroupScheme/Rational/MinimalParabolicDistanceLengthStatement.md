# The distance of two minimal semi-standard parabolics is a Weyl length (Renard VII.3.5, opening paragraph, corrected form): statement

Module `Langlands.GroupScheme.Rational.MinimalParabolicDistanceLengthStatement`.
Namespace `Langlands.GroupScheme`. Universe parameter `u`.
The module contains one **statement**, the `Prop`-valued definition
`MinimalParabolicDistanceLengthStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read the opening paragraph of VII.3.5 (printed p.236 / PDF p.242):

> Quels que soient les sous-groupes paraboliques semi-standards `P` et `Q` de `G` ayant
> même facteur de Levi `M`, posons : `d(P, Q) = |Σ(P) ∩ Σ(Q̄)|`. Il est bien connu que
> `d(P, Q)` est la longueur de l'élément `w` du groupe de Weyl `W(A_M)` tel que
> `w · P = Q`.

Here `Σ(P)` is the set of reduced roots of `A_M` in the Lie algebra of the unipotent
radical of `P` (V.3.4, printed p.110 / PDF p.116), `Q̄` is the parabolic opposite to `Q`
with Levi factor `M`, and `W(A_M) = N_G(A_M)/Z_G(A_M)` (V.3.5).

As printed, the assertion needs two corrections. Both are recorded as source issue I1 of
the published Chapter VII item ledger `notes/renard/item-ledger-vii.md`.

- **Non-minimal `M`.** The element `w` need not exist. In `G = GL_3` with
  `M = GL_2 × GL_1` block diagonal, `A_M = {diag(a, a, b)}`, every element of
  `N_G(A_M)` fixes `A_M` pointwise, so `W(A_M)` is trivial. But the upper
  block-triangular `P` and `Q = P̄` are distinct, with `d(P, Q) = 1`. The book also defines no
  length on `W(A_M)` for non-minimal `M`. This unit does not state the non-minimal case.
- **Minimal `M`, which length.** Here `W(A_M)` is the relative Weyl group `W`, and `w`
  exists and is unique. The equality holds for the length defined by the simple roots of
  `P`. With the length defined by a fixed standard minimal parabolic `P_∅`, it fails
  when `P ≠ P_∅`. Example: in `G = GL_3` with `M` the diagonal torus, take `P = s_1P_∅`
  and `Q = s_1s_2P_∅`. Then `Σ(P) ∩ Σ(Q̄) = {α_1 + α_2}`, so `d(P, Q) = 1`, while
  `w = s_1s_2s_1` has `P_∅`-length 3. In terms of `P_∅`: if `P = uP_∅` and `Q = vP_∅`,
  then `w = vu⁻¹` and `d(P, Q) = ℓ(u⁻¹v)` for the `P_∅`-length.

This unit states the minimal case in both corrected forms. The assertion is not used in
the proofs of the VII.3.5 Proposition or of the other Chapter VII statements.

## The statement

`k` is any field, `G` a connected reductive group scheme over `k`, and
`i : T.toGrp ⟶ G` a maximal split torus `A_∅` (`IsMaximalSplitTorus i`). The minimal Levi
subgroup is `M = Z_G(A_∅)`, and `A_M = A_∅`. The objects are the published ones:

| Renard | Lean |
| --- | --- |
| `W = W(A_∅) = N(k)/Z(k)` | `relativeWeylGroup i` (quotient of `normalizerPoints i` by `centralizerPoints i`) |
| semi-standard `P` with Levi factor `M` | `Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ i)` for a generic cocharacter `ξ` (`IsGenericCocharacter i ξ`) |
| unipotent radical of `P_ξ`, of `P̄_ξ` | `Dynamic.unipotent (groupHom ξ ≫ i)`, `Dynamic.unipotent (groupHom (-ξ) ≫ i)` |
| `P_ξ(k)` | `parabolicPoints ξ`, the carrier of the subgroup functor at the identity test object |
| reduced roots | `RelativeRoot.indivisibleRoots i` |
| `w · P = Q` | `Moves w ξ ξ'`: some representative `n : normalizerPoints i` of `w` satisfies `(parabolicPoints ξ).map (MulAut.conj n) = parabolicPoints ξ'` |
| length for the simple roots of `P_ξ` | `cs.length` for a Coxeter system `cs` with `IsRelativeWeylCoxeterRealization i ξ cs` |

The statement defines inline

`d ξ ξ' = |intertwiningRelativeRoots i (U(ξ)) (U(-ξ')) ∩ indivisibleRoots i|`,

the number of reduced roots of `A_∅` lying in the Lie algebras of both the unipotent
radical `U(ξ)` of `P_ξ` and the unipotent radical `U(-ξ')` of the opposite parabolic
`P̄_ξ'`. This is Renard's `d(P_ξ, P_ξ')`. It is the same count `d` as in the published
VII.3.5 Proposition (i), `PQIntertwiningCompositionStatement`, which applies
`subgroupRelativeRoots` and `indivisibleRoots` to the unipotent radicals. By the proved
`RelativeRoot.intertwiningRelativeRoots_dynamic`, the intersection is the set of relative roots
`α` with `⟨α, ξ⟩ > 0` and `⟨α, ξ'⟩ < 0`.

For all generic `ξ`, `ξ'` the statement asserts:

1. exactly one `w ∈ W` satisfies `Moves w ξ ξ'`;
2. if `Moves w ξ ξ'`, then `d ξ ξ' = cs.length w` for every Coxeter system `cs` on `W`
   realizing the root action with the simple roots of `ξ`, that is, of `P_ξ` (Renard's
   assertion, with the length taken for the simple reflections of `P`);
3. for every generic `ν` (`P_∅ = P_ν`), if `Moves u ν ξ` and `Moves v ν ξ'`, then
   `d ξ ξ' = cs.length (u⁻¹ * v)` for every Coxeter system `cs` on `W` realizing the root
   action with the simple roots of `ν` (the form `d(uP_∅, vP_∅) = ℓ(u⁻¹v)`).

## Formalization choices

- **Minimal semi-standard parabolics as dynamic parabolics.** For a maximal split torus
  `A_∅`, the parabolic subgroups with Levi factor `M_∅ = Z_G(A_∅)` (Renard V.3.8) are
  exactly the dynamic parabolics `P(ξ)` of the cocharacters `ξ` of `A_∅` that pair
  nontrivially with every relative root. Such a `P(ξ)` has Levi factor `Z_G(ξ) = M_∅`.
  Conversely, the proved `parabolicRootPresentationExistence` presents every parabolic
  with a rational Levi factor `M` as a dynamic parabolic `P(ζ)` with `M = Z_G(ζ)`. When
  `M = M_∅`, no relative root vanishes on `ζ`. The statement quantifies over generic
  `ξ`, which is also the parametrization of the published standard-parabolic interface
  (`parabolic i ν ∅` is `P(ν)`).
- **Field.** Renard works over a `p`-adic field. The assertion is purely
  algebraic-group-theoretic and holds over every field, so the statement is over an
  arbitrary field `k`, like the published `RelativeWeylCoxeterStatement`.
- **`w · P = Q` with one representative.** `Moves` asks for one representative `n` of `w`.
  Two representatives differ by an element of `Z(k) ⊆ P_ξ(k)`, so the condition does not
  depend on the representative. Equality of rational points is used, as in the published
  V.4.6 statement `StandardWeylMinimalRepresentativesStatement`. Over every field the
  rational points of `P_ξ` determine `Σ(P_ξ)`, through the nontrivial rational points of
  the root subgroups.
- **Length.** The framework has no canonical length function on `relativeWeylGroup i`.
  The published `IsRelativeWeylCoxeterRealization i ξ cs` gives exactly the Coxeter
  systems whose simple reflections are the reflections of the simple relative roots of
  `ξ`, with length equal to the number of inverted reduced positive roots. Such systems
  exist: the published `RelativeWeylCoxeterStatement` asserts `HasRelativeWeylCoxeterSystem
  i ξ` for generic `ξ`, and the proved `relativeWeylCoxeter` establishes it. So
  conclusions 2 and 3 are not vacuous.
- **Conventions.** `MulAut.conj n` sends `g` to `n g n⁻¹`. The Weyl action
  `schemeWeylCharacterAction i (mk n)` is the published `weylAction i n`, `χ ↦ σ⁻¹ ≫ χ`
  where `n i(t) n⁻¹ = i(σ t)`. Hence `Ad(n)` maps the `α`-weight space to the
  `(w · α)`-weight space, and `Σ(n P n⁻¹) = w · Σ(P)`. Conclusion 3 depends on this
  convention: with the opposite convention it would read `ℓ(v u⁻¹)`.

## Related Library content

- `PQIntertwiningCompositionStatement` (VII.3.5 Proposition (i)) uses the same `d` as a
  hypothesis and does not need this assertion.
- `RelativeWeylCoxeterStatement` and its proof `relativeWeylCoxeter` give the Coxeter
  realizations. `relativeInversionSet` is the inversion set used for the length.
- `RelativeRoot.intertwiningRelativeRoots_dynamic` computes the root set counted by `d`.

## Why the statement is true

Write `Σ⁺(ξ)` for the reduced roots positive on `ξ`. A representative `n` of `w`
conjugates `P(ξ)` to `P(w · ξ)`, and `Σ⁺(w · ξ) = w · Σ⁺(ξ)`. The chambers of generic
cocharacters correspond to the positive systems `Σ⁺(ξ)`. `W` is the Weyl group of the
root system `Σ(A_∅)` (Renard V.3.7, citing Borel–Tits 5.3 and 5.8), so it acts simply
transitively on them. Rational points
of `P(ξ)` determine `Σ⁺(ξ)`, which gives 1. If `Moves w ξ ξ'`, then `Σ⁺(ξ') = w · Σ⁺(ξ)`,
so `d ξ ξ'` is the number of `α ∈ Σ⁺(ξ)` with `w⁻¹ · α ∉ Σ⁺(ξ)`. This is the size of
the inversion set of `w⁻¹` for `ξ`, that is `ℓ(w⁻¹) = ℓ(w)`, which gives 2. For 3,
`Σ⁺(ξ) = u · Σ⁺(ν)` and `Σ⁺(ξ') = v · Σ⁺(ν)`. Substituting `α = u · β` turns the count
into the number of `β ∈ Σ⁺(ν)` with `v⁻¹u · β ∉ Σ⁺(ν)`, that is
`ℓ(v⁻¹u) = ℓ(u⁻¹v)`.

## Remaining obligations

The proof is a separate obligation. It needs the conjugation formula
`n P(ξ) n⁻¹ = P(w · ξ)` for dynamic parabolics, the root description of `U(ξ)` (published
`subgroupRelativeRoots_dynamicUnipotent`), simple transitivity of `W` on chambers, and the
proved Coxeter realization.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.GroupScheme.Rational.RelativeWeylCoxeterStatement` | `IsRelativeWeylCoxeterRealization`, `relativeWeylGroup`, `SimpleRoot`, `normalizerPoints`, `Dynamic.parabolic`, `Dynamic.unipotent` (through its imports) |
| `Langlands.GroupScheme.Rational.SubgroupRelativeRoots` | `RelativeRoot.intertwiningRelativeRoots` |
| `Langlands.GroupScheme.Rational.RootProductStatement` | `RelativeRoot.indivisibleRoots` |
