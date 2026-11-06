# Realizing commensurable monodromy-invariant full Tate lattices

Author: Worker 1701.

`Langlands.AbelianScheme.Tate.CommensurableInvariantLatticeRealizationStatement`
is a universe-polymorphic proposition target. It says the following. Take an
actual abelian scheme `A` over a connected locally noetherian base that
satisfies an explicit finite-set fibre-affineness condition. Take a submodule
`L` of the rational Tate module of `A` at one geometric point, over the
integral finite adeles. Suppose `L` is stable under the actual rational
monodromy and is commensurable with the image of the full integral Tate group
by one positive integer bound. Then `L` is exactly the image of the full
integral Tate group of some actual abelian scheme `B` over the same base,
under an actual rational isomorphism from `B` to `A`. The statement uses only
published carriers and maps and adds no definitions. It is a statement, not a
proof.

## Exact meaning

For a universe `u`, the proposition quantifies, in this order, over:

- `htor : Langlands.AbelianScheme.TorsionFiniteEtaleStatement.{u}`, the
  published proposition saying that positive torsion of an abelian scheme is
  finite étale when its index is invertible on the base;
- `h : Langlands.Global.RationalProfiniteIntegerAdeleComparison`, the published
  comparison of the profinite integers with the integral finite adeles of `ℚ`,
  and of their rationalization with the finite adeles. It is used only to
  install the finite-adelic module structure below;
- a scheme `S : Scheme.{u}` with instances `IsLocallyNoetherian S` and
  `ConnectedSpace S`;
- `hu`: for every `k : GroupScheme.Tate.Index (fun _ => True)`, that is every
  natural number `k > 0`, the image of `k` in `Γ(S, ⊤)` is a unit;
- a field `Ω : Type u` with instances `IsAlgClosed Ω` and `CharZero Ω`, and a
  geometric point `s : Spec (CommRingCat.of Ω) ⟶ S`;
- `hs`: for every finite étale cover `Y : Langlands.AlgebraicGeometry.FiniteEtale.Cover S`,
  the fibre `Langlands.AlgebraicGeometry.FiniteEtale.Fiber s Y` is finite. The
  published fundamental group `FundamentalGroup s hs` takes this as an
  argument;
- an actual abelian scheme `A : Langlands.AbelianScheme S`;
- an unnamed hypothesis, the **source fibre-affineness condition**: for every
  finite set `F : Finset A.X.left` and every point `t : S` with
  `A.X.hom x = t` for all `x ∈ F`, there is an open `W : A.X.left.Opens` with
  `IsAffineOpen W` and `x ∈ W` for all `x ∈ F`. In words, every finite set of
  points of `A` lying over one point of `S` is contained in one affine open of
  `A`.

Write `T` for the test object `Over.mk s`, `P` for the predicate
`fun _ => True`, `Af` for `Langlands.Global.FiniteAdeles ℚ` and `Rf` for the
subring `Langlands.Global.integralFiniteAdeles ℚ` of `Af`. The Lean statement
writes all of these out. `TA` is the full integral Tate group
`GroupScheme.Tate.Full A.toGrp T`. It is the inverse limit, over all positive
levels ordered by divisibility, of the `n`-torsion points `T ⟶ A.X` over `S`,
that is of the `Ω`-valued points of `A` above `s` killed by `n`. Its
rationalization is `VA = Langlands.AbelianScheme.Tate.Rational A T P`, which is
`ℚ ⊗[ℤ] TA`. The canonical map `GroupScheme.Tate.toRational A.toGrp T P` is
`x ↦ 1 ⊗ x`. Write `im(TA)` for its range.

Next, the statement installs two local module structures on `VA` by `letI`:

- the `Af`-module structure `Langlands.AbelianScheme.Tate.finiteAdeleModule A T P h`;
- the `Rf`-module structure `Module.compHom _ (Rf.subtype)`, so `r • w` means
  `(r : Af) • w`. This is the same pattern as the published
  `harrisHodgePELIntegralAdeleSpan` in
  `Langlands/Shimura/PEL/HarrisIntegralTateImages.lean`.

It then quantifies over an `Rf`-submodule `L : Submodule Rf VA` and assumes
exactly two further hypotheses.

- **Monodromy invariance.** For every
  `gamma : Langlands.AlgebraicGeometry.FiniteEtale.FundamentalGroup s hs` and
  every `w : VA`,
  `rationalMonodromy s hs htor A P hu gamma w ∈ L ↔ w ∈ L`. Here
  `Langlands.AbelianScheme.Tate.rationalMonodromy` is the published rational
  geometric monodromy. It is the base change to `ℚ` of the action of the
  fundamental group on each actual torsion level of `TA`.
- **Commensurability with one bound.** There is `n : ℕ` with `0 < n` such that
  1. for every `x : TA`, `n • toRational A.toGrp T P x ∈ L`; and
  2. for every `w : VA` with `w ∈ L`, there is `x : TA` with
     `toRational A.toGrp T P x = n • w`.

  Here `n •` is additive natural multiplication on `VA`. So
  `n · im(TA) ⊆ L` and `n · L ⊆ im(TA)`. Inside the `ℚ`-vector space `VA` this
  says `n · im(TA) ⊆ L ⊆ n⁻¹ · im(TA)`.

The conclusion is that there are an actual abelian scheme
`B : Langlands.AbelianScheme S` and a rational isomorphism
`e : Rationalization.of B ≅ Rationalization.of A` such that for every `w : VA`,

```text
w ∈ L ↔ ∃ x : GroupScheme.Tate.Full B.toGrp T,
  rationalHomMap (A := B) (B := A) T P e.hom
    (GroupScheme.Tate.toRational B.toGrp T P x) = w.
```

`Langlands.AbelianScheme.Tate.rationalHomMap T P` is the published `ℚ`-linear
action of rational homomorphisms on rational Tate modules. So `e` points from
the output model `B` to the given `A`. The image of the full integral Tate
group of `B` under `toRational` and then `e.hom` is exactly the set `L`. The
model `B` is over all of `S`, not over a fibre or an étale cover. The
statement asserts existence only. It says nothing about uniqueness of `B` or
`e`.

## What is assumed and what is not

The source fibre-affineness condition is an explicit hypothesis on the given
`A`. It is the hypothesis of the published quotient construction
`FiniteEtaleQuotientExistence.nonempty_quotientData_of_forall_finset_fibre`,
in the same form, with the point of `S` named `t` instead of `s`. The statement
does not replace it by a given quotient, a given isogenous model or a global
projective embedding. Showing that it holds for the abelian schemes of the
eventual consumer (see Provenance) is the consumer's obligation. It is not
part of this statement or its later proof. Generic work on this condition
belongs to the proper-fibre geometry task `30938d34`.

The statement does not take as inputs:

- the model `B`, the isomorphism `e`, a finite étale subgroup of `A` realizing
  the lattice, or a quotient scheme;
- normality, reducedness or affineness of `S`, a projective embedding of `A`,
  a polarization, freeness of `L` or of the Tate groups, or the Tate rank;
- prime-to or prime-local data in place of the full index predicate
  `fun _ => True`;
- either inclusion of the image equality it concludes;
- injectivity of `toRational`. All conditions refer to images in `VA`.

`htor`, `h`, `hu` and `hs` are explicit inputs, matching the consumer and the
published monodromy and module interfaces, which take them as arguments. Both
propositions `htor` and `h` already have published proofs,
`Langlands.AbelianScheme.torsionFiniteEtale` and
`Langlands.Global.rationalProfiniteIntegerAdeleComparison`, so these two inputs
can always be supplied. They are quantified rather than fixed because the task
contract asks for that. With `hu`, the `CharZero Ω`
instance is redundant, since `s` makes every positive integer a unit in `Ω`.
It is kept because the task contract asks for it.

## Relation to existing declarations

- `Langlands.AbelianScheme.FiniteEtaleQuotientExistence.nonempty_quotientData_of_forall_finset_fibre`
  in `Langlands/AbelianScheme/FiniteEtaleQuotientExistenceProof.lean` takes a
  locally noetherian `S`, an actual `A` with the same fibre-affineness
  condition, and a given `K : FiniteEtaleSubgroup A`. It gives
  `Nonempty K.QuotientData`, that is an actual abelian scheme quotient, a finite
  étale surjective homomorphism `q`, and the cartesian square identifying `K`
  with the scheme kernel of `q`. It does not produce `K` from `L`, and it says
  nothing about Tate images. Its specialization under a global projective
  embedding is `Langlands.AbelianScheme.finiteEtaleQuotientExistence`. This
  statement does not assume a projective embedding.
- `Langlands.AbelianScheme.integralOrderModelOfForallFinsetFibre`
  in `Langlands/AbelianScheme/OrderSaturationExistence.lean` builds an
  `IntegralOrderModel`, an isogenous model on which a supplied rational order
  action becomes integral, under the same fibre-affineness condition. It needs
  a characteristic-zero field structure map and a finite integer basis. It
  does not make a chosen full integral Tate image equal a given `L`.
- `Langlands.AbelianScheme.Tate.ConnectedIntegralLatticeReflectionStatement`
  is a different, unproved target with proof task `79e5606f`. It starts from
  two given actual abelian schemes and a given rational isomorphism that
  preserves both full integral Tate images, and asks for an actual isomorphism.
  It produces no isogenous model. This statement neither assumes nor
  duplicates it.
- The consumer's `HarrisIntegralLevelLattice` development (candidate
  `53ef4c4a`, not imported here) builds monodromy-invariant lattices and their
  integral order actions. It realizes no lattice by an abelian scheme.

## Provenance

This is an internal target, derived from the exact need of a consumer. It is
not a translation of a located source theorem, and no external source is
cited. Worker 344 asked for it as a generic prerequisite of the division CM
representability task `6eac742d` (revision 1). That task keeps the Harris
specialization, the integral order and polarization descent, the determinant
condition, the comparison of normalized moduli and the representing scheme
with its properties. This proposition establishes none of them. The consumer
must also supply the integer bound `n` and the fibre-affineness condition.

Worker 142 reported that the generic Tate task `74795b53` has no overlapping
realization theorem reserved or in progress. A task search for "Tate lattice
realization" and "commensurable" found no matches. These are ownership and
search findings, not mathematical claims.

The hypotheses and conclusion are the ones fixed by the task contract: the
single geometric point, the full index predicate, the actual monodromy, the
one-bound commensurability and the direction of `e` from `B` to `A`.

## Outstanding proof obligations

The proposition is not proved. One expected route, with `N = n²` and
`M = n · L`, is:

1. **Lattice to torsion subgroup.** By the two bounds, `N · im(TA) ⊆ M ⊆ im(TA)`,
   and `M` is monodromy-stable. Identify `TA / N · TA` with the `Ω`-points of
   the `N`-torsion `A[N]` above `s`. This needs surjectivity of `TA` onto each
   torsion level and control of the kernel of `toRational`. Then `M` gives a
   monodromy-stable subgroup of those points.
2. **Subgroup realization.** By `htor` and `hu`, `A[N]` is finite étale over
   the connected base `S`. Show that a monodromy-stable subgroup of its
   geometric fibre is the fibre of a unique open and closed finite étale
   subgroup scheme. This gives an actual `K : FiniteEtaleSubgroup A`. This
   correspondence between stable subsets and open and closed subschemes is not
   published for these carriers.
3. **Quotient.** Apply `nonempty_quotientData_of_forall_finset_fibre` with the
   fibre-affineness condition to get `B` and `q : A ⟶ B` with scheme kernel
   `K`.
4. **Rational inverse.** Since `K ⊆ A[N]`, factor `[N]` through `q`, for
   example with `GroupScheme.IsogenyFactorization.lift`. This gives
   `q' : B ⟶ A` with `q ≫ q' = N • 𝟙 A`, and also `q' ≫ q = N • 𝟙 B`. So
   `Rationalization.ofHom q` is invertible. Take `e` so that
   `e.hom = n • N⁻¹ • Rationalization.ofHom q'`, which is
   `n • (Rationalization.ofHom q)⁻¹`.
5. **Tate-image comparison.** Show that the rational map of `q` sends
   `n⁻¹ · L` onto `im(TB)`. This uses that `q` is finite étale surjective, that
   `Ω` is algebraically closed so `Ω`-points of `B` above `s` lift along `q`,
   and the kernel square. Applying `e.hom` then gives exactly `L`. The task
   contract names Worker 1584's narrow full-index evaluation-surjectivity
   helper in the connected-reflection proof task as distinct work, not to be
   duplicated.

Steps 1, 2 and 5 need facts that are not published for these carriers. The
statement assumes none of them. A proof has to establish them or get around
them. This description explains the intended scope. It is not a Lean proof.

## Formal status

The declaration is a `Prop`-valued `def`, not a theorem or an axiom. Its proof
is a separate task, to be started after this exact statement has been
independently accepted and published.
