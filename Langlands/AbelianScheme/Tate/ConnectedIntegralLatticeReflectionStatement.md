# Integral Tate images reflecting rational isomorphisms over connected bases

Author: Worker 239.

`Langlands.AbelianScheme.Tate.ConnectedIntegralLatticeReflectionStatement` is a
universe-polymorphic proposition target. It says that a rational isomorphism of
actual abelian schemes over a connected base comes from an actual isomorphism
when both of its arrows preserve the images of the full integral Tate groups at
one geometric point. It uses only the published abelian schemes, the published
rationalized category, the full integral Tate groups, the canonical maps to their
rationalizations and the existing rational Tate action. It adds no geometric
definitions.

## Exact meaning

For a universe `u`, the proposition is an implication from
`htor : Langlands.AbelianScheme.TorsionFiniteEtaleStatement.{u}`. It then
quantifies over:

- a scheme `S : Scheme.{u}` with instances `IsLocallyNoetherian S` and
  `ConnectedSpace S`;
- a hypothesis `hu` that for every `k : GroupScheme.Tate.Index (fun _ => True)`,
  that is every natural number `k > 0`, the image of `k` in `Γ(S, ⊤)` is a unit;
- a field `Ω : Type u` with instances `IsAlgClosed Ω` and `CharZero Ω`, and a
  geometric point `s : Spec (CommRingCat.of Ω) ⟶ S`;
- actual abelian schemes `A B : Langlands.AbelianScheme S`;
- a rational isomorphism `e : Rationalization.of A ≅ Rationalization.of B`.

Write `T` for the test object `Over.mk s` and `P` for the predicate
`fun _ => True`. The Lean statement writes both out. `TA` is the full integral
Tate group `GroupScheme.Tate.Full A.toGrp T`. It is the inverse limit, over all
positive levels ordered by divisibility, of the `n`-torsion points
`T ⟶ A.X` over `S`, that is the `Ω`-valued points of `A` above `s` that are
killed by `n`. Its rationalization is
`GroupScheme.Tate.Rational A.toGrp T P = ℚ ⊗[ℤ] TA`, and
`GroupScheme.Tate.toRational A.toGrp T P` is the canonical map `x ↦ 1 ⊗ x`.

There are two further hypotheses.

- **Forward:** for every `x : TA` there is a `y : TB` with
  `rationalHomMap T P e.hom (toRational A.toGrp T P x) = toRational B.toGrp T P y`.
- **Inverse:** for every `y : TB` there is an `x : TA` with
  `rationalHomMap T P e.inv (toRational B.toGrp T P y) = toRational A.toGrp T P x`.

So the existing `ℚ`-linear actions of `e.hom` and `e.inv` map the image of the
full integral Tate group on one side into the corresponding image on the other.
Both hypotheses use the one supplied geometric point.

The conclusion is that there is `g : A ≅ B` in the category of actual abelian
schemes over the same `S` such that

```text
Rationalization.ofHom g.hom = e.hom ∧ Rationalization.ofHom g.inv = e.inv.
```

The actual inverse identities of `g` come from its `Iso` structure. Agreement is
required on both arrows of the given rational isomorphism, not only on Tate
modules.

## What the hypotheses are not

The hypotheses concern the actual images (the ranges of `toRational`) of the
full integral Tate groups inside their existing rationalizations. They are not:

- integrality at each prime separately, or at almost every prime, for example
  through `GroupScheme.Tate.PrimeAdic.integralImage`;
- preservation of some chosen lattice or abstract linear equivalence of Tate
  modules;
- vanishing of a torsion kernel, Tate faithfulness, or removal of denominators.
  These are among the things a proof has to establish.

The base is not assumed normal, reduced, affine or a field, and the conclusion
is over all of `S`, not a fibre. The finite-étale torsion target `htor` and the
unit family `hu` are explicit, matching the consumer. With `hu`, the
`CharZero Ω` instance is redundant, since `s` makes every positive integer a
unit in `Ω`. It is kept because the contract asks for it.

## Relation to existing declarations

The following published interfaces go in the opposite direction or prove less.

- `GroupScheme.Tate.rationalMap_toRational` in
  `Langlands/AbelianScheme/Tate/Rational.lean` gives forward preservation: the
  rational map of an actual homomorphism `f` sends `toRational x` to
  `toRational (map T P f x)`. Together with
  `AbelianScheme.Tate.rationalHomMap_ofHom` this shows that the rationalization
  of any actual isomorphism satisfies both hypotheses above. The target asks for
  the converse.
- `GroupScheme.Tate.PrimeAdic.integralImage` and
  `PrimeAdic.rationalMap_mem_integralImage` in
  `Langlands/AbelianScheme/Tate/RestrictedProduct.lean` are the prime-local
  analogue of that forward statement. They remove no denominators.
- `AbelianScheme.rationalIsoIntegralData` in
  `Langlands/AbelianScheme/RationalIntegralComparison.lean` (a
  `Rationalization.IntegralIsoData`) gives actual maps `f : A ⟶ B` and
  `f' : B ⟶ A` with `ofHom f = a • e.hom` and `ofHom f' = b • e.inv` for
  nonzero integers `a, b`, and `f ≫ f' = (a * b) • 𝟙 A`. These represent nonzero
  multiples of `e`, not the arrows of `e` themselves.
- `GroupScheme.IsogenyFactorization.lift` in
  `Langlands/AbelianScheme/IsogenyFactorization.lean` factors a map through a
  supplied finite-flat-surjective isogeny, given a supplied equation saying that
  the map kills the scheme kernel. Nothing published derives that equation from
  Tate-module data.
- `AbelianScheme.Tate.FieldRationalFaithfulnessStatement` (task `1ee31886`) is a
  different, unproved field-level injectivity target. This statement does not
  assume it, and a proof of it would not by itself prove this one.

## Provenance

This is an internal target, derived from what a consumer needs. It is not a
verbatim translation of a published theorem. Worker 344 asked for it as the
denominator-removal step for the division CM representability task `6eac742d`
(revision 1). That task keeps the Harris specialization, the comparison of
normalized rational isogenies, and the construction of the representing scheme.
This proposition establishes none of them.

The field-level input is Edixhoven–van der Geer–Moonen, *Abelian Varieties*,
preliminary draft, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, Lemma (12.8)(i), printed
p.182 (one-based PDF p.186), which was read directly. For abelian varieties `X`,
`Y` over a field `k`, a prime `ℓ ≠ char k` and `f ∈ Hom(X, Y)`: if `T_ℓ(f)` is
divisible by `ℓ^m`, then `f` is divisible by `ℓ^m`. The proof says that `f`
vanishes on `X[ℓ^m](k_s)`, hence on the étale group scheme `X[ℓ^m]`, so it
factors through `[ℓ^m]_X`. The remark after the lemma notes that the quotient is
unique because `Hom(X, Y)` is torsion-free. This target differs from that source
in several ways:

- it is over a connected locally noetherian base, not a field;
- it uses the full Tate group, not one `T_ℓ`;
- it uses the Tate data at a single geometric point;
- it concludes that a rational isomorphism is integral, not that one map is
  divisible.

## Outstanding proof obligation

The proposition is not proved. One expected route:

1. Use `rationalIsoIntegralData e` to write `ofHom f = a • e.hom` with an actual
   `f` and an integer `a ≠ 0`. That interface does not make `a` positive, so
   first normalize the sign: put `n = |a| > 0` and `f₀ = sign(a) • f`. Then
   `f₀` is an actual map with `ofHom f₀ = n • e.hom`. The forward hypothesis,
   `rationalMap_toRational`, and the torsion-freeness of `TB` show that the map
   `f₀` induces on Tate groups lands in `n · TB`. Since `TA` surjects onto the
   `n`-torsion points over `s`, `f₀` kills all `Ω`-valued `n`-torsion points of
   `A` above `s`.
2. By `htor` and `hu`, `A[n]` and `B[n]` are finite étale over `S`. The locus
   where `f₀` restricted to `A[n]` agrees with the zero section is open and
   closed. Every connected component of `A[n]` maps onto the connected base
   `S`, so each one meets the fibre over `s`. Hence `f₀` kills the whole scheme
   kernel of `[n]`.
3. Using that `[n]` is an isogeny, `IsogenyFactorization.lift` factors `f₀`
   through `[n]`: it gives `g₁ : A ⟶ B` with `[n] ≫ g₁ = f₀`. Rationalizing,
   `n • ofHom g₁ = ofHom f₀ = n • e.hom`. Rational Hom groups are `ℚ`-modules
   and `n > 0`, so `ofHom g₁ = e.hom`. Without the sign normalization this step
   would give `ofHom g₁ = sign(a) • e.hom`, which is `-e.hom` when `a < 0`.
   Treat `e.inv` the same way, normalizing its denominator `b` to `|b|`, to get
   `g₂ : B ⟶ A` with `ofHom g₂ = e.inv`.
4. The composites `g₁ ≫ g₂` and `g₂ ≫ g₁` rationalize to identities. Since
   `Rationalization.Hom` is `ℚ ⊗[ℤ]` of the actual Hom group, this makes a
   nonzero integer multiple of each composite minus the identity vanish. Integer
   multiplication is an epimorphism, so Hom groups are torsion-free, and the
   composites are identities.

Steps 2–4 need facts that are not published:

- the clopen-equalizer and connected-component argument for finite étale
  schemes;
- that nonzero integer multiplication on an abelian scheme over `S` is a
  finite-flat-surjective isogeny. Over a general base this is only the unproved
  target `GroupScheme.MultiplicationIsogenyStatement`; over a field it is
  `AbelianScheme.multiplication_isIsogeny_of_ne_zero`;
- torsion-freeness of Hom groups of abelian schemes, which makes
  `Rationalization.ofHom` injective.

The statement does not assume any of these. A proof has to establish them or
get around them. This description explains the intended scope; it is not a
Lean proof.

## Formal status

The declaration is a `Prop`-valued `def`, not a theorem or an axiom. Its proof
is a separate task, to be started after this exact statement has been
independently accepted and published.
