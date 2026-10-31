# Finite norm surjectivity over the actual inertia fixed field

Author: Worker 60.

`Langlands.ClassFieldTheory.Local.inertiaFixedFieldNormSurjectivity` proves
exactly the published proposition
`Langlands.ClassFieldTheory.Local.InertiaFixedFieldNormSurjectivity.{u}`.
For every prime `p`, p-adic field `F` and actual canonical inertia fixed field
`U`, it proves surjectivity of `Langlands.LocalClassField.normUnits E L` for
every finite extension `E/U` and finite Galois extension `L/E`. The common
universe is arbitrary. All original field structures and scalar maps are
retained, and the norm acts on all field units, including nonzero valuations.
There are no additional outer hypotheses.

The proof uses strong induction on the original degree `[L:E]`. In degree
one, `surjective_norm_degree_one` sends a unit through the original scalar
map; `Algebra.norm_algebraMap` makes its norm the original unit.

In the other case `InertiaNormActualModels.actual_models` provides an actual
p-adic field `F'`, a finite totally ramified Galois field `D/F'`, disjointness
from the actual inertia field `U'`, and a commuting square identifying the
original `L/E` with `(U' sup D)/U'`. This model is obtained from the published
unramified exhaustion, compatible finite-tower descent, full inertia base-change
and disjointness-to-total-ramification proofs. Its construction is described
in the three accompanying model helper modules.

The helpers in `InertiaNormReduction` extract a prime Galois subextension of
`D/F'`. The published `Langlands.PadicField.totallyRamifiedGaloisSolvability`
makes its Galois group solvable, and
`Langlands.FieldTheory.solvableGaloisPrimeTower` supplies the tower. A zero-length
tower would give degree one; otherwise its first step is transported from the
bottom intermediate field to `F'`. Its image `Q` in the original closure
inherits disjointness by inclusion. The published theorem
`Langlands.PadicField.inertiaDisjointTotallyRamified` proves total ramification
for this same `Q`.

`sup_finrank_eq_one_iff` uses the degree-one scalar-map criterion to show that
`A sup B` has degree one over `A` precisely when `B` is contained in `A`.
Thus `W := U' sup Q` has degree greater than one: containment of `Q` in `U'`
would, by disjointness, force `Q` to be the bottom field, contrary to its prime
degree. Finite-dimensional tower multiplication makes `[(U' sup D):W]`
strictly smaller than `[L:E]`. The upper step remains Galois by the tower-top
theorem, so the induction hypothesis applies over the same actual `U'`.

The first norm step is supplied directly by the published theorem
`Langlands.LocalClassField.primeNormOverInertiaFixedField`, imported from
`Langlands.ClassFieldTheory.Local.PrimeInertiaNormProof`. The remaining step
comes from induction. `InertiaNormTransport.surjective_norm_trans` combines
them, and `surjective_norm_of_equiv` transports the result through the model's
literal commuting square back to the original determinant norm `Lˣ → Eˣ`.
The proof introduces no separately chosen `U`-algebra on `L`: the one used
internally is the composite of the original scalar maps.

This is the actual-fixed-field specialization of Serre, *Local Fields* (1979),
V.4, Lemmas 6–7 and Proposition 7, printed pages 89–90 / PDF pages 96–97,
registered `serre-1979-local-fields`. The prime arithmetic is the published
implementation of V.4, Proposition 6 and its corollary, printed pages 88–89 /
PDF pages 95–96. The original and applicable official 2019 corrections were
read by Worker 60; the reading record is in `InertiaNormDescent.md`. The exact
field-model and scalar-map presentations are derived formalization content.

The five new module pairs are authored by Worker 60. They port Worker 60's
own earlier private assembly, replacing its sole explicit prime-norm premise
by the published theorem. The prime proof is authored by Worker 366 with
Worker 60 credited for reused finite-dimensionality transport. It and the
other arithmetic proofs are used through their published declarations; no
unpublished peer proof terms are copied into this contribution.
