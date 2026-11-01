# Local freeness of the closure of an invertible ideal

This module proves the local part of the invertible-ideal extension across an open immersion
(Stacks Project, Lemma 31.29.2, Tag 0BD8). All declarations are in namespace
`Langlands.AlgebraicGeometry.Picard.OpenImmersionIdeal`. Here `O_X` means
`SheafOfModules.unit X.ringCatSheaf`, and `Γ(X, W)` and `Γ(M, W)` are sections over an open `W`.

## Main theorem

`isLocallyFreeRankOne_of_range_iff` assumes:

- `X` is locally Noetherian and `j : Y ⟶ X` is an open immersion;
- for every `x : X` outside `Set.range j`, the stalk `X.presheaf.stalk x` is a
  `UniqueFactorizationMonoid`;
- `D : LineBundle Y` with a monomorphism `s : D.obj ⟶ O_Y`;
- `M : X.Modules` with a monomorphism `t : M ⟶ O_X`;
- the section condition `ht`: for every open `W` of `X` and every `c : Γ(X, W)`, `c` is
  `t.app W m` for some `m : Γ(M, W)` if and only if `j.app W c` is `s.app (j ⁻¹ᵁ W) d` for some
  `d : Γ(D.obj, j ⁻¹ᵁ W)`.

It concludes `IsLocallyFreeRankOne M`. The module does not construct `M`. It applies to any `M`
with this section image, for instance the closure `closure j s` of
`Langlands.AlgebraicGeometry.Picard.OpenImmersionIdealClosure` once its section image has
been identified. The factoriality hypothesis is used only at points outside the image of `j`.

## Auxiliary definitions

- `secs t W m : Γ(X, W)` is `t.app W m`, read as a function on `W`.
- `IsGood t W f` says that `f : Γ(X, W)` is a nonzerodivisor of `Γ(X, W)` and that every
  `secs t W m` is a multiple of `f`.
- `IsGenerator t O ε` says that for every open `W ≤ O`, the restriction of `ε : Γ(X, O)` to `W`
  is a nonzerodivisor of `Γ(X, W)`, and that the elements of `Γ(X, W)` of the form `secs t W m`
  are exactly its multiples.
- `satIdeal a δ` is the ideal `{c | ∃ N, a ^ N * c ∈ (δ)}` of a commutative ring. It is the
  saturation of the principal ideal `(δ)` with respect to `a`.

## Proof

**Frames.** `isFrameOn_of_locally_isGood` shows the following. Let `σ : Γ(M, O)` be a section
such that every point of every open `W ≤ O` has a smaller open neighbourhood `W'` on which
the restriction of `secs t O σ` is good. Then `σ` is a frame of `M` on `O` in the sense of
`Scheme.Modules.IsFrameOn`. The proof first shows that the restriction of `secs t O σ` is a
nonzerodivisor on every open of `O`, because a function that vanishes near every point is
zero. It then glues the local quotients in the structure sheaf and uses injectivity of `t`
on sections. `exists_isFrameOn_of_generator` turns a generator in the sense of `IsGenerator`
into such a frame. `exists_restrict_iso_of_isFrameOn` turns a frame into a trivialization of
`M.restrict O.ι`, using `IsFrameOn.nonempty_pullback_iso_unit` and
`restrictFunctorIsoPullback`.

**Points of the image.** `exists_generator_of_isFrameOn` takes an open `O` inside
`j.opensRange` and a frame `e` of `D` on `j ⁻¹ᵁ O`. It defines `ε` as the preimage of `s e`
under the bijection `j.app O` and proves `IsGenerator t O ε` from `ht`. The relevant facts are
that `j.app W` is bijective for `W ≤ j.opensRange` (`app_bijective`) and that `s` is injective
on sections. `exists_isFrameOn_of_mem_range` applies this at a point `j z`. It uses a frame
of `D` near `z` (`exists_isFrameOn_of_isLocallyFreeRankOne`) and its image open `j ''ᵁ T`.

**Algebra at a factorial prime.** Let `R` be a factorial domain.

- `exists_split`: a nonzero `d` factors as `φ * ψ`, where `φ` is relatively prime to `a` and
  `ψ` divides a power of `a`. The proof is by induction on prime factors.
- `exists_dvd_iff`: suppose `δ = 0` implies `a = 0`. Then `{r | ∃ N, δ ∣ a ^ N * r}` is the set of
  multiples of a nonzero `φ`.
- `exists_lcm`: for finitely many nonzero elements, the set of their common multiples is the
  set of multiples of a nonzero least common multiple. The proof uses
  `UniqueFactorizationMonoid.toGCDMonoid`.

`exists_generator_near_prime` then takes a Noetherian ring `A`, a prime `P`, and an
`IsLocalization.AtPrime R P` with `R` factorial. It also takes a finite family `(a i, δ i)` in
which `δ i * h = 0` always implies `a i ^ N * h = 0` for some `N`. It produces three things:

- an element `f` of `I = ⨅ i, satIdeal (a i) (δ i)`;
- an element `g ∉ P` with `g * c ∈ (f)` for all `c ∈ I`;
- the property that `f * h = 0` implies `g * h = 0`.

In the proof, `I` maps to the principal ideal of the least common multiple `Φ` in `R`.
`PrimeDivisor.exists_numerator_generator` then gives `f ∈ I` with `I R = (f)`, and the image
of `f` is nonzero. `PrimeDivisor.exists_denominator_of_map_le` is applied twice, using
finite generation in the Noetherian ring. The first application, to `I ≤ (f)` after
localization, gives `g₁`. The second, to the annihilator of `f`, which becomes zero in the
domain `R`, gives `g₂`. Then `g = g₁ * g₂`.

**Points with factorial stalk.** `exists_isFrameOn_of_factorial` works at any point `x` with
factorial stalk. It does not use the assumption that `x` lies outside the image.

- Choose an affine open `V₀ ∋ x` with `A = Γ(X, V₀)`, which is Noetherian, and the prime
  `P = hV₀.primeIdealOf x`. The stalk is the localization of `A` at `P` by
  `IsAffineOpen.isLocalization_stalk`.
- Since `j` is quasi-compact, `exists_finite_generators` covers `j ⁻¹ᵁ V₀` by finitely many
  preimages of basic opens `D(a i)` of `V₀`. In its proof each `D(a i)` lies in the image of a
  trivializing open of `D`, so each carries a generator `ε i` (`IsGenerator t (D(a i)) (ε i)`)
  from the previous step.
- Write `ε i` as `δ i / a i ^ m` in the localization `Γ(X, D(a i))` of `A` at `a i`. The
  nonzerodivisor property of `ε i` gives the hypothesis of `exists_generator_near_prime`.
- The resulting `f` lies in the section image on `V₀`, by `ht` and locality of the section
  image of `s` (`exists_secs_eq_of_locally`). The resulting `g` gives the neighbourhood
  `D(g) ∋ x`, by `mem_basicOpen_iff`.
- On every basic open `D(b) ≤ D(g)`, the restriction of `f` is good. First write a section
  image as `c₀ / b ^ n`. The section image is generated by `ε i` on `D(b * a i)`, so
  `(b * a i) ^ k * c₀ ∈ (δ i)`. One power of `b` clears all these exponents
  (`exists_pow_mem_sat`), which puts `b ^ N * c₀` in `I`. Finally, `g` and `b` are units on
  `D(b)` (`isUnit_res_of_le_basicOpen`). Being a nonzerodivisor follows in the same way from
  the annihilator property of `g`.
- The frame criterion then applies on `D(g)`.

The main theorem combines the two pointwise results: `exists_isFrameOn_of_mem_range` for
points of `Set.range j`, and `exists_isFrameOn_of_factorial` for the remaining points.

## Provenance

The mathematical statement is the local part of Stacks Project Lemma 31.29.2 (Tag 0BD8). The
divisor `D'` there is the scheme-theoretic image, whose ideal has the section image described by
`ht`, and the conclusion is that its ideal is invertible. The Stacks proof uses the
decomposition of an effective Cartier divisor into prime divisors in the local UFD. The proof
here is a different, elementary route: it uses saturations of principal ideals on a finite
affine cover, divisibility in the factorial stalk, and denominator clearing by finite
generation. The auxiliary definitions `secs`, `IsGood`, `IsGenerator` and `satIdeal` are
internal to this proof.
