# KP Lemma C.5.3 for actual unramified root-depth special-fibre kernels

Lean module: `Langlands.BruhatTits.IntegralModels.RootDepthKernel`.

Worker 286, for Task 6392 (`714e9a16-da57-41b5-93cd-3d91fea0c964`).

## The theorem

```
theorem Langlands.BruhatTits.IntegralModels.unramifiedRootDepthKernel :
    UnramifiedRootDepthKernelStatement.{u}
```

It proves the published statement
`Langlands.BruhatTits.IntegralModels.UnramifiedRootDepthKernelStatement`
(module `Langlands.BruhatTits.IntegralModels.RootDepthKernelStatement`) at an
arbitrary universe `u`. The theorem has no hypotheses of its own. This module
does not change the statement or anything it imports.

The statement covers the following situation:

- `F` is a nonarchimedean local field, `K = inertiaFixedField F` is its actual
  maximal unramified field and `O = fixedFieldIntegers F` its ring of integers;
- `G` is an affine group scheme over `K` with supplied building data
  `C : MaximalUnramified.BuildingData F G`;
- `x` is a point of the apartment, `a : relativeRoots C.i` is **any** relative
  root, and `r ≤ s` are real depths.

Then for

- arbitrary supplied presentations `U` and `V` (`RootFiltrationModelData`) of
  the filtration groups `U_{a,x,r}` and `U_{a,x,s}`,
- any generic map `f : V.rootGroup ⟶ U.rootGroup` with
  `f ≫ U.inclusion = V.inclusion`, and
- any integral-model map `φ : V.model.Hom U.model f`,

the scheme-theoretic kernel of `φ.specialFibreMap` is smooth, has connected
underlying space and is unipotent over the residue field of `O`.

The proof keeps this whole scope:

- every relative root is covered: roots whose double is a root (multipliable
  roots), divisible roots (`a = 2b`), and all other roots;
- the depths only satisfy `r ≤ s`, so `r = s` is included;
- the presentations `U`, `V` and the generic map `f` are arbitrary. They are
  not required to be the models constructed in the proof.

This is the conclusion of Kaletha–Prasad, *Bruhat–Tits theory: a new approach*
(2023), Lemma C.5.3 (printed p. 705 / PDF p. 736). It is stated there for the
constructed models of Proposition C.5.1 (printed pp. 703–704 / PDF
pp. 734–735). The Library statement allows arbitrary supplied presentations
instead.

## Proof

The Lean proof is a single application of two published theorems:

```
unramifiedRootDepthKernel_of_multipliableCoordinates
  Langlands.Geometry.Building.multipliableRootGroupCoordinatesExistence
```

- `unramifiedRootDepthKernel_of_multipliableCoordinates` (module
  `Langlands.BruhatTits.IntegralModels.RootDepthKernelMultipliable`) has type
  `MultipliableRootGroupCoordinatesExistenceStatement.{u} →
  UnramifiedRootDepthKernelStatement.{u}`.
- `multipliableRootGroupCoordinatesExistence` (module
  `Langlands.Geometry.Building.MultipliableRootGroupCoordinatesExistenceProof`,
  Task 7077, Worker 7 with Worker 4783) proves
  `MultipliableRootGroupCoordinatesExistenceStatement.{u}` with no hypotheses.

Only the axioms `propext`, `Classical.choice` and `Quot.sound` are used. There
is no `sorry` and no new axiom. The proof does not use the host kernel
statement of KP Proposition 8.4.15 (`UnramifiedModelKernelStatement`): no
module in the import closure of this module mentions it.

### How the three kernel properties are proved

The conditional theorem first introduces all the data of the target. It then
splits on whether `2 • a` is a relative root.

**Multipliable roots (`2 • a ∈ Φ`).** The existence theorem gives a record
`P : ValuedUnitaryRootGroupCoordinates C a`. It consists of a finite separable
extension `E / K`, a separable quadratic extension `L / E`, and a scheme
homomorphism `R_{E/K} U_{L/E} ⟶ G` representing the root subgroup of `a`. It
also gives an apartment point at which the root valuation of every unitary
parameter `(u, v)` is its tower depth. `P.specialFibreKernel_properties` is
then applied to the supplied `x`, `r ≤ s`, `U`, `V`, `f` and `φ`. It also uses
`MaximalUnramified.valuationSubring_eq F` and the smooth-hom extension property
`IntegralModel.fixedField_hasSmoothHomExtension IntegralModel.smoothHomExtension F`.
That theorem works as follows:

1. It builds explicit presentations `P.rootFiltrationModelData x r` and
   `P.rootFiltrationModelData x s`. They share the root group
   `R_{E/K} U_{L/E}` and use the published canonical restricted unitary
   lattice models `R_{O_E/O} X_{r', 2r'}` and `R_{O_E/O} X_{s', 2s'}`. Here
   `r' ≤ s'` are the depths renormalized on `E` (KP's model
   `U_{a,x,r} = R_{O_E/O} U'_{a,x,r}` of Proposition C.5.1).
2. Their transition map has smooth, connected and unipotent special-fibre
   kernel. This is the published `canonicalWeilLatticeModel_kernel_properties`,
   the Library form of KP Lemma C.4.4 combined with Weil restriction.
3. The published presentation-invariance theorem
   `RootFiltrationModelData.specialFibreKernel_properties_of_presentation`
   transfers the three properties to the kernel of `φ`, for the arbitrary
   supplied `U`, `V` and `f`. That theorem uses smooth-model point
   determination and generic rigidity (KP Corollaries 2.10.10–2.10.11 and
   Remark 2.10.19).

**All other roots (`2 • a ∉ Φ`).** `C.hasOppositeFactorPairs.hasNoHigherRoots_of_two_not_mem`
shows that no multiple `n • a` with `n ≥ 2` is a relative root. This case
includes divisible roots. The published theorem `unramifiedNoHigherRootDepthKernel`
(module `Langlands.BruhatTits.IntegralModels.RootDepthKernelNoHigher`) then
applies. It works the same way:

1. It builds explicit root-field depth models of `U_{a,x,r}` and `U_{a,x,s}`
   (`rootFieldDepthModelOfOrbit`), at depths shifted by the root-field depth
   shift. They are vector-group models of lattices in the root field `L_a`.
   They play the role of KP's restriction of scalars from `O_{L_a}` to `O` of
   the additive models of §C.2.
2. Their transition kernel is smooth, connected and unipotent
   (`rootFieldDepthModelOfOrbit_kernel_properties`). This corresponds to KP
   Fact C.2.1.
3. The same presentation-invariance theorem transfers the properties to `φ`.

In both cases the explicit transition map and its kernel theorem only need
`r ≤ s`, so they also cover `r = s`. KP's Facts C.2.1 and C.3.1 are stated
for `s > r`.

## Provenance

The route through valued unitary coordinates, the root-field depth models and
presentation invariance is internal to this project. KP prove Lemma C.5.3 in
one line, from Facts C.2.1 and C.3.1 and Lemma C.4.4. Each module named above
explains in its own Markdown how its part corresponds to KP.
