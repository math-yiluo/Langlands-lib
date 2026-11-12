# Strongly regular fibres of the canonical class-function quotient

Author: Worker 5035.

This module proves the published proposition
`Langlands.GroupScheme.ClassFunctions.StronglyRegularFibresStatement.{u}`
(`Rational/ClassFunctionsStronglyRegularFibresStatement`):

```lean
theorem stronglyRegularFibres : StronglyRegularFibresStatement.{u}
```

The statement says the following. Let `G` be a simply connected quasi-split group over a field
`K : Type u`; affineness of `G` is derived from quasi-splitness. Let `F` be a field over `K`.
Let `y` and `w` be `F`-points of `G` whose images under the actual canonical class-function
quotient `ClassFunctions.rho G` agree. Suppose also that the all-test centralizer of `w`
lies in a closed torus `S` of `G_F`. Then there are a field `E : Type u` over `K`, a morphism
`q : Spec E → Spec F` over `Spec K` and an `E`-point `g` of `G` with
`g * (q ≫ y) * g⁻¹ = q ≫ w`. The statement pair and every pair it imports are unchanged.

## Proof

The proof applies the published conditional assembly
`ClassFunctions.stronglyRegularFibres_of_inputs`
(`Rational/ClassFunctionsAlgClosedStronglyRegularFibres`) to three published proofs:

- `Langlands.GroupScheme.borelPointContainment : BorelPointContainmentStatement.{u}`
  (`Absolute/BorelPointContainmentProof`). Over an algebraically closed field, every
  rational point of a smooth affine connected group lies in a Borel subgroup.
- `Langlands.GroupScheme.ClassFunctions.torusSeparation : TorusSeparationStatement.{u}`
  (`Rational/ClassFunctionsTorusSeparationProof`). Over an algebraically closed field, two
  rational points of a maximal torus of a semisimple group with the same image under
  `ClassFunctions.rho` are conjugate by a rational point of the group.
- `Langlands.GroupScheme.Dynamic.exists_unipotent_conj_eq_mul`
  (`Dynamic/UnipotentConjugation`). Let `k` be algebraically closed and `G` affine and
  locally of finite type over `k`, with a cocharacter `χ`. Let `t` be a rational point of
  the dynamic centralizer `Z(χ)` such that no nontrivial rational point of the contracting
  subgroup `U(χ)` commutes with `t`. Then every `u * t` with `u ∈ U(χ)(k)` is conjugate
  to `t` by a point of `U(χ)(k)`. Its signature is exactly the
  hypothesis `hR4` of the assembly, so it is passed unchanged.

The assembly does the following, as described in its Markdown.
`stronglyRegularFibres_of_inputs` applies the published field transport
`ClassFunctions.stronglyRegularFibres_of_algClosed`
(`Rational/ClassFunctionsStronglyRegularFibresTransport`) to two proofs: the published
field base-change proof `ClassFunctions.fieldBaseChange`, and the algebraically closed core
`algClosedStronglyRegularFibres_of`. The transport passes to the algebraic closure of `F` in
universe `u`. Along the way it transports the quotient-image equality and the all-test
centralizer condition. The core argument runs as follows:

1. Place `y` in a Borel subgroup `P(χ)` for a regular cocharacter `χ` of a split maximal
   torus `T`.
2. Take the limit `t ∈ T` of `y`. It has the same image under `rho` as `y`.
3. Conjugate `w` into `T` and separate `t` from `w` by `torusSeparation`.
4. Show that the self-centralizing maximal torus leaves no nontrivial point of `U(χ)`
   commuting with `t`.
5. Conjugate `y` to `t` inside `U(χ)` by the Ax–Grothendieck lemma.

The output field `E` is the algebraic closure of `F`.

The proof uses no group-point Jordan decomposition and no torus-unipotence result, so no
such prerequisite was needed. It takes no premise: every input is a published proof in the
Library. In particular, the theorem does not assume Borel–Springer 8.6,
`QuasiSplitRegularClassRationalStatement` or the desired conjugacy. The universe `u` and the
fields `K` and `F` remain arbitrary, including finite and imperfect fields. The canonical
map `ClassFunctions.rho G` and the all-test centralizer hypothesis are those of the
statement, and no condition on `y` is added. The compiled theorem depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

Provenance: internal. This is a composition of published Library results. The mathematical
sources are recorded with the statements and proofs it imports: R. Steinberg,
*Regular elements of semi-simple algebraic groups* (1965), Sections 6.4–6.6 and 6.10–6.11,
for torus separation and the fibre description, and Milne, Corollary 17.34, for Borel
containment. The implemented route differs from Steinberg's Jordan-decomposition argument
as described above.
