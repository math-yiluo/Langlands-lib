# Baire constancy for finite-dimensional function germs

`Langlands.Topology.baireFiniteDimensionalGermConstancy` proves exactly the
closed Library proposition
`Langlands.Topology.BaireFiniteDimensionalGermConstancyStatement.{uX,uY}`.
The two universes are independent and unrestricted. The statement is imported
by module name; its source and companion explanation are unchanged.

For an antitone sequence of subsets `D m` of an arbitrary type `X`, let `V`
be a finite-dimensional complex linear subspace of the functions `X → ℂ`,
whose restriction to each `D m` is injective. On a nonempty Baire space `Y`,
assume each scalar function `y ↦ f y x` is locally constant. Suppose that for
each `y` some index `m`, allowed to depend on `y`, makes `f y` agree on `D m`
with the assigned element `v y` of `V`. The theorem produces a nonempty open
subset of `Y` on which all assigned elements `v y` are equal in `V`, hence
as functions on all of `X`.

## Finite observations and reconstruction

The local construction `reconstruct m` builds a locally constant function
`g m : Y → V` such that, whenever `f y` agrees with `v y` on `D m`, one has
`g m y = v y`.

Fix `m`. For each `x : D m`, the linear form `L x` on `V` is evaluation at
`x`, implemented by composing `LinearMap.proj` with `V.subtype`. The common
kernel of these linear forms is zero: an element in every kernel restricts
to the zero function on `D m`, so restriction injectivity makes it zero in
`V`. Consequently this common kernel is contained in the kernel of every
linear form `K` on `V`. Mathlib's
`FiniteDimensional.mem_span_of_iInf_ker_le_ker` places each `K` in the span
of the evaluations. Thus these evaluations span the whole algebraic dual.

The dual is finite dimensional and therefore finitely generated. Applying
`Submodule.fg_span_iff_fg_span_finset_subset` chooses a finite set `s` of
evaluation forms with the same span. For each `i : s`, choose a point
`p i : D m` representing that evaluation form. Define

- `R w i = i.val w`, the finite tuple of observations of `w : V`;
- `F y i = f y (p i).val`, the same observations of the given family.

The map `R` is injective. Indeed, equality of two observation tuples gives
equality of their evaluations by every member of `s`. Induction on linear
span extends this equality to the whole dual and in particular to every
`L x`, for `x : D m`. The original restriction injectivity then gives equality
of the two elements of `V`.

`LocallyConstant.unflip` shows that the finite tuple `F` is locally constant:
its finitely many scalar components are locally constant by hypothesis.
Set `g m = Function.invFun R ∘ F`. Local constancy is preserved by
postcomposition with any function, so this candidate is locally constant.
No topology or continuity of the inverse is needed. If `f y` agrees with
`v y` on `D m`, the chosen evaluation points give `F y = R (v y)`.
`Function.leftInverse_invFun` then gives `g m y = v y`. Values of the
chosen inverse outside the image of `R` cause no problem.

## The closed cover and Baire step

Define `C m` to consist of parameters `y` for which `f y` and `g m y`
agree at every point of `D m`. This is the intersection, indexed by
`x : D m`, of the corresponding scalar agreement sets. For each `x`, both
`y ↦ f y x` and `y ↦ (g m y) x` are locally constant. Their difference is
locally constant, and its zero fiber is closed by
`IsLocallyConstant.isClosed_fiber`. Arbitrary intersections of closed sets
are closed, so `C m` is closed. This argument does not need a topology on
`V` or the usual topology on `ℂ`.

The sets `C m` cover `Y`. For each `y`, choose its given eventual-equality
index `m`; the reconstruction property gives `g m y = v y`, hence `y ∈ C m`.

For every `y ∈ C m`, the candidate also equals the assigned element `v y`,
even if `m` was not the index furnished for `y`. Choose that index `k` and
compare on `D (max m k)`. Antitonicity puts this set inside both `D m` and
`D k`. There, membership in `C m` and the given agreement at `k` show that
`g m y` and `v y` have identical restrictions. Injectivity at `max m k`
forces `g m y = v y`.

Mathlib's `nonempty_interior_of_iUnion_of_closed` supplies `m` and a point
`y` in the interior of `C m`. The final set is

`O = interior (C m) ∩ {z | g m z = g m y}`.

It is open, since the fiber of a locally constant function is open, and it
contains `y`. On `O`, the candidate `g m` is constant and agrees with `v`,
so `v` is constant as required. No monotonicity of the sets `C m` is used.

## Degenerate cases and scope

The construction uses neither a basis of positive size nor a point of `X`
or `D m`. A finite set of observations may be empty. In dimension zero,
`V` still contains zero, so `Function.invFun` has the required nonempty
domain and the same proof applies. Empty `X` and empty restriction sets
are therefore covered without additional assumptions. The nonemptiness of
`Y` is used in the Baire theorem. Each eventual index is chosen only after
its parameter, and no uniform eventual-equality hypothesis is introduced.
There is no premise asserting continuity or local constancy of `v`.

This generic result supplies the finite-dimensional Baire helper only.
Identifying the actual coordinate quotient and proving coordinate-unit
invariance for the parent JPS application remain separate obligations.

## Provenance

Worker 345 implemented this proof. Worker 454 supplied the generic interface,
Worker 451 formalized its accepted statement and explanation, and Worker 625
supplied the proposed Baire argument. The implementation follows that closed
cover argument, using finite separating evaluations and a set inverse in
place of explicit basis-coordinate linear combinations. This is an internal
derived helper, not a theorem attributed verbatim to Jacquet,
Piatetski-Shapiro and Shalika. The algebraic and topological tools named above
come from Mathlib's `LinearAlgebra/Dual/Lemmas.lean`,
`RingTheory/Finiteness/Defs.lean`, `Topology/LocallyConstant/Basic.lean`, and
`Topology/Baire/Lemmas.lean` in the pinned Lean environment.
