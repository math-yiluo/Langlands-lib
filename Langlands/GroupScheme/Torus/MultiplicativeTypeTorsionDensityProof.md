# Proof: the torsion subgroups of a group of multiplicative type are dense

Worker 732.

`Langlands.GroupScheme.multiplicativeTypeTorsionDensity.{u}` proves the proposition
`Langlands.GroupScheme.MultiplicativeTypeTorsionDensityStatement.{u}` (module
`Langlands.GroupScheme.Torus.MultiplicativeTypeTorsionDensityStatement`,
[Markdown](MultiplicativeTypeTorsionDensityStatement.md)). The theorem's type is exactly
that proposition, with no added hypotheses. It uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## The statement

Let `G` be a group scheme over a field `k` with `IsMultiplicativeType G`. Then:

1. (Milne 12.33) a closed immersion `z : Z ⟶ G.X.left` through which every point
   `x : T ⟶ G.X` with `x ^ n = 1`, `n > 0`, factors is an isomorphism;
2. (Milne 12.32) if `G` is smooth over `k`, the same holds when only the exponents `n`
   with `(n : k) ≠ 0` are used;
3. (Milne 12.34) two homomorphisms `f₁ f₂ : G ⟶ H` into a group scheme `H` over `k` that
   agree on every such torsion point are equal.

The source is Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`,
Theorems 12.32 and 12.33 and Corollary 12.34, pp. 242–243. The statement's Markdown gives
the quotations and the encoding.

## Route

The implemented proof follows Milne's idea: a function vanishing on all the `G_n` is
zero. It differs from his route in two ways.

- Milne first reduces to an algebraically closed field. The Lean proof instead base-changes
  to the field `K` supplied by `IsMultiplicativeType G`, over which `G_K ≅ D_K(Λ)`. It then
  descends the conclusion back to `k` with Mathlib's fpqc descent of isomorphisms.
- Milne writes `G` as a product of copies of `𝔾_m` and a finite group. The Lean proof
  instead works with the group algebra `K[Λ]` and the maps `K[Λ] → K[Λ ⧸ nΛ]`, through the
  helper modules [`TorsionDensityLattice`](TorsionDensityLattice.md) and
  [`DiagonalizableTorsionDensity`](DiagonalizableTorsionDensity.md).

Part 3 follows Milne: the difference kernel is a closed subscheme because `H` is
separated.

## Auxiliary results in this module

All of them are in the namespace `Langlands.GroupScheme.TorsionDensity`.

### `isIso_of_baseChange` (descent along a field extension)

Let `k → K` be a field extension with `b = Spec.map (algebraMap k K)`. Let `G` be a group
scheme over `k`, `H` one over `K`, and `e : G_K ≅ H` an isomorphism of group schemes over
`K`, where `G_K = (GroupScheme.baseChange b).obj G`. Let `P : ℕ → Prop`. Suppose `H` has
the following property (hypothesis `hH`): every closed immersion into `H.X.left` through
which all `n`-torsion points with `P n` factor is an isomorphism. Then `G` has the same
property.

*Proof.* Let `g = pullback.fst G.X.hom b : G_K → G`, and let
`z' = pullback.snd z g : Z ×_G G_K → G_K`, a closed immersion as a base change of `z`.
Apply `hH` to the closed immersion `z' ≫ e`. Let `x : T ⟶ H.X` be a point with `P n` and
`x ^ n = 1`. Then:

- `x₁ = x ≫ e⁻¹` is an `n`-torsion point of `G_K`, because the Library's
  `isoPointsEquiv` (module [`Torus.Split`](Split.md)) is a group isomorphism;
- its image under the Library's `GroupScheme.baseChangePointsEquiv` (module
  [`AbelianScheme.KernelBaseChange`](../../AbelianScheme/KernelBaseChange.md)) is an
  `n`-torsion point of `G` over `k`. This is the base-change adjunction on points, and it
  is multiplicative;
- by the hypothesis on `z`, this point factors through `z` by some `y`. Then
  `pullback.lift y x₁.left` factors `x` through `z' ≫ e`.

So `z' ≫ e` is an isomorphism, and hence so is `z'`. The projection `g` is a base change of
`b`. The map `b` is surjective, flat and quasi-compact by the Library's
`fieldExtension_fpqc` (module
[`GroupScheme.BaseChangeReflection`](../BaseChangeReflection.md)), so `g` is too. Finally,
Mathlib's `MorphismProperty.of_pullback_snd_of_descendsAlong` (with
`P := isomorphisms Scheme` and `Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact`) shows that `z`
is an isomorphism.

### `isIso_of_isMultiplicativeType`

Let `G` be of multiplicative type over `k`, and let `P : ℕ → Prop` satisfy the following
(hypothesis `hP`). For every field `K` over `k`, every finitely generated `Λ` with
`G_K ≅ D_K(Λ)`, every `N > 0` whose prime divisors are orders of nonzero elements of
`Λ`, and every `M`, there is `n > M` with `P n` and `N ∣ n`. Then every closed immersion
into `G` through which all `n`-torsion points with `P n` factor is an isomorphism.

*Proof.* Unpack `IsMultiplicativeType G` to get `K`, `Λ` and `e : G_K ≅ D_K(Λ)`. Take `N`
from `exists_separating Λ`. Apply `isIso_of_baseChange` with `H = D_K(Λ)`. Its hypothesis
`hH` is `isIso_of_torsion_factors` over the ring `K`.

### `eq_zero_of_smooth`

Let `G` be smooth over `k`, let `e : G_K ≅ D_K(Λ)` with `Λ` finitely generated, and let `p`
be the characteristic exponent of `k` (`ExpChar k p`). Then `p • x = 0` implies `x = 0` in
`Λ`.

*Proof.* `p` is also the characteristic exponent of `K`
(`expChar_of_injective_algebraMap`). The structure morphism of `D_K(Λ)` equals `e⁻¹`
followed by `pullback.snd G.X.hom b`. That projection is smooth as a base change of the
smooth `G.X.hom`, so `D_K(Λ)` is smooth over `K`. Part 2 of the published
`Diagonalizable.diagonalizableSmoothConnectedCriteria K p Λ` (module
[`Torus.DiagonalizableSmoothConnectedCriteriaProof`](DiagonalizableSmoothConnectedCriteriaProof.md))
then says that `Λ` has no `p`-torsion.

### `eq_of_torsion` (homomorphisms agreeing on torsion)

Let `G` and `H` be group schemes over `k`, where `G` has the property of part 1
(hypothesis `hG`). Let `f₁ f₂ : G ⟶ H` agree on every `n`-torsion point, `n > 0`. Then
`f₁ = f₂`.

*Proof.* The published `fieldSeparated` (module
[`GroupScheme.FieldSeparatedProof`](../FieldSeparatedProof.md)) says that every group
scheme over a field is separated. So the diagonal `H → H ×_k H` is a closed immersion.
Let `ℓ = (f₁, f₂) : G → H ×_k H` (`pullback.lift`), and let `z` be the base change of the
diagonal along `ℓ`. This `z` is the difference kernel of `f₁` and `f₂`, a closed immersion
into `G`. A torsion point `x` satisfies `x ≫ f₁ = x ≫ f₂`, so it factors through `z` (by
`pullback.lift`, checked with `pullback.hom_ext`). By `hG`, `z` is an isomorphism. Both
`z ≫ f₁` and `z ≫ f₂` equal the first projection of the pullback (from
`pullback.condition`), so `cancel_epi z` gives equality of the underlying morphisms of
schemes. `Grp.hom_ext` and `Over.OverMorphism.ext` then give `f₁ = f₂`.

This lemma does not use the finite-type hypotheses on `H` from part 3 of the statement,
because separatedness holds for all group schemes over a field.

`isIso_of_baseChange`, `eq_zero_of_smooth` and `eq_of_torsion` use
`set_option backward.isDefEq.respectTransparency false`, as other Library files on
scheme points do (for example `GroupScheme.BaseChangeReflection`).

## The main theorem

`multiplicativeTypeTorsionDensity` introduces `k`, `G` and `hG`, then proves the three
parts.

1. **Part 1.** Apply `isIso_of_isMultiplicativeType` with `P n := 0 < n`. Given `N > 0`
   and `M`, take `n = N * (M + 1)`. It is positive, a multiple of `N`, and larger than
   `M`.
2. **Part 2.** Assume `Smooth G.X.hom`. Apply `isIso_of_isMultiplicativeType` with
   `P n := (n : k) ≠ 0`. Let `p` be the characteristic exponent of `k`
   (`ringExpChar.expChar`), so `p > 0`. Given `K`, `Λ`, `e`, `N` and `M`, take
   `n = N * (M * p + 1)`. It is a multiple of `N` and larger than `M`. To show
   `(n : k) ≠ 0`, split on `ExpChar`:
   - In characteristic zero, `n > 0` and the cast of `n` to `k` is nonzero.
   - If `p` is prime and `k` has characteristic `p`, then `(n : k) = 0` would mean
     `p ∣ N` or `p ∣ M * p + 1`. In the first case `exists_separating` gives a nonzero
     `x ∈ Λ` with `p • x = 0`, which contradicts `eq_zero_of_smooth`. In the second case
     `p ∣ 1`, which is impossible.
3. **Part 3.** For `H`, `f₁`, `f₂` (the finite-type hypotheses on `H` are not needed),
   apply `eq_of_torsion` with part 1 as `hG`.

## Helper modules

Both helper modules are new and are listed in the submission:

- [`TorsionDensityLattice`](TorsionDensityLattice.md): `multiples`,
  `exists_bound_of_ne_zero`, `exists_bound_injOn`, `eq_zero_of_mapDomain_eq_zero`,
  `exists_separating`;
- [`DiagonalizableTorsionDensity`](DiagonalizableTorsionDensity.md):
  `isIso_of_forall_ne_zero`, `quotientMap`, `quotientPoint`, `quotientPoint_pow`,
  `isIso_of_torsion_factors`.
