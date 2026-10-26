# Natural upper/opposite normalized Jacquet duality

The proposition `Langlands.Parabolic.NaturalNormalizedJacquetDualityStatement`
is the conjunction of `StandardNaturalJacquetDualityClause` and
`RefinedNaturalJacquetDualityClause`. It specifies natural duality families;
this file supplies no proof of either family or of second adjointness.

## Scope and actual representations

Both clauses quantify every prime `p`, algebraic `PadicField.{uF} p`,
compatible `F.TopologicalData T`, natural rank `n`, and block shape `B`.
The refined clause also quantifies every `BlockRefinement B`. The topology
is `T.topology`, with its induced GL, product, and subgroup topologies.
The representation carrier universe `uV` is independent of `uF`.

In the standard clause the input is any bundled complex representation
`π : Rep.{uV} ℂ (GeneralLinear n F.Carrier)` satisfying `IsAdmissible π.ρ`.
In the refined clause it is any admissible representation of the whole
coarse product Levi `B.Levi F.Carrier`. Here admissibility includes
smoothness and finite-dimensional fixed spaces for open subgroups.
There is no irreducibility, finite-length, finite-dimensional-carrier,
tensor-decomposition, or factorwise-admissibility hypothesis.

Write `D` for `smoothContragredient`, the action on smooth vectors in the
algebraic complex-linear dual. For each fixed field, topology, and parabolic,
the clause asserts the existence of one family of complex-linear
representation equivalences

`E_π : r_P(D π) ≃ D(r_opP π)`

indexed by all admissible inputs in universe `uV`. The family is quantified
before its naturality law. Its dependence on an admissibility proof is
immaterial by proof irrelevance.

In the standard clause, `r_P` is `T.normalizedJacquet B`.
Its carrier `B.JacquetModule (D π)` is the coinvariant quotient after
restriction to the actual upper parabolic by its internal unipotent radical.
The opposite functor is `CuspidalJacquetMultiplicity.oppositeJacquet T B`:
its carrier is the ambient quotient
`Jacquet.Coinvariants π.ρ (B.oppositeUnipotentSubgroup F.Carrier)`.
The embedded Levi action is pulled back along `B.leviEquiv` to the
product Levi. The two quotient presentations are kept distinct.

In the refined clause, `r_P` and `r_opP` are respectively
`T.normalizedRefinedJacquet B S` and
`T.normalizedRefinedOppositeJacquet B S`. Their carriers are the actual
`RefinedJacquetModule` and `RefinedOppositeJacquetModule`, and the target
group is the actual subgroup `refinedLevi F.Carrier B S`.

If `δ` is the upper full modulus, upper normalized Jacquet acts by
`δ^(-1/2)` times the quotient action. The opposite full modulus is `δ⁻¹`,
so opposite normalized Jacquet acts by `δ^(1/2)` times its quotient action.
The refined formulas use the product of the inner block moduli.
The smooth dual is a linear contragredient, without complex conjugation.

## Naturality on quotient vectors

For every actual intertwiner `a : π.ρ.IntertwiningMap τ.ρ` between admissible
objects, every `x ∈ r_P(D τ)`, and every `y ∈ r_opP π`, the equation is

`E_π(r_P(D a)(x))(y) = E_τ(x)(r_opP(a)(y))`.

Thus `E_π ∘ r_P(D a) = D(r_opP(a)) ∘ E_τ`, with the contravariant order.
The notation `.1 y` in Lean evaluates the underlying linear functional of a
smooth-dual vector. Quantifying all `y`, rather than selected representatives,
makes this the full equality of smooth functionals by extensionality.

The standard left side uses `T.normalizedJacquetMap B (contragredientMap a)`.
The standard right side uses `Jacquet.map` for the actual opposite radical
and embedded Levi. Its underlying linear map is exactly the map of normalized
opposite quotients: twisting both actions by the common character and pulling
them back to the product Levi do not change that linear map.
On representatives it takes `[v]` to `[a(v)]`.
The refined clause uses `T.normalizedRefinedJacquetMap` and
`T.normalizedRefinedOppositeJacquetMap` directly, with the same formula.

## Original source and derived formulation

The source is W. Casselman, *Introduction to representations of p-adic
groups*, Chapter III, revision April 29, 2019, registered as
`casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The retained original is
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.
The relevant passages are page 1 for connected reductive scope, pages 4–5
for normalized Jacquet modules, and pages 7–8, especially III.5.5–7,
III.6.2, and III.6.3, for canonical lifts and canonical duality.
The opposite bars in III.6.2–3 were checked in the original page images.

For an upper parabolic `P`, the source pairs `r_P(π)` with `r_opP(D π)`.
Apply the source to the opposite parabolic to obtain the orientation here:
`r_P(D π) ≃ D(r_opP π)`. Its opposite modulus is the inverse upper
modulus, accounting for the two normalization signs above.

The coherent-family naturality is a derived consequence of the canonical
pairing construction, not a verbatim additional theorem in the source.
For `a : π → τ`, choose sufficiently small common compact open subgroups
adapted to the parabolic. Averaging and the contracting Hecke operators
commute with `a` and its dual. Therefore `a` preserves the stable-image
subspaces used for canonical lifts; on their quotient images it carries
the unique canonical lift to the canonical lift. Evaluation then gives
`(D a)(ℓ)(v) = ℓ(a(v))`. The canonical pairing's independence of the
chosen compact open subgroup gives the displayed naturality equation
for all quotient vectors. This explains the provenance of the target;
the Lean construction and its proof remain a separate obligation.

A finite product of GL groups is itself connected reductive. Its actual
refined parabolic is the product of its inner parabolics. Thus the same
source applies to arbitrary admissible representations of that whole group,
without any reduction to tensor products. Rank zero and empty shapes are
retained: the group and radicals are trivial and the equivalence is
evaluation. One-block parabolics likewise have trivial radical, with
arbitrary admissible ambient representations.

## Relationship to existing targets

The existing `OppositeJacquetDualityClause` uses the opposite orientation
`r_opP(D π) ≃ D(r_P π)` on the embedded Levi and characterizes equivalences
by every supplied asymptotic pairing. This target instead asks for an
existential family in the orientation needed after first adjointness,
with naturality and a refined product-Levi clause. It does not identify
the family with a particular supplied pairing or assert its uniqueness.
The existing canonical-pairing and pointwise-duality obligations remain.

Together with natural same-parabolic induction duality, Hom duality,
reflexivity, and first adjointness, this family is intended as a prerequisite
for normalized second adjointness. The proposition alone establishes no
duality, reciprocity, multiplicity comparison, or irreducible-head theorem.
