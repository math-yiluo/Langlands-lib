# The Isomorphism Theorem over a reduced local ring, assuming root groups exist

Module `Langlands.GroupScheme.Reductive.LocalSplitReducedIsomorphismReduction`. Declarations in
`Langlands.GroupScheme.LocalSplitCell` and `Langlands.GroupScheme`.

## Main results

- `localSplitReducedIsomorphismTheorem_of_rootGroups (hRG : LocalSplitRootGroupStatement.{u}) :
  LocalSplitReducedIsomorphismTheoremStatement.{u}`.
- `localSplitReducedIsomorphismTheorem_of_simpleRootGroups
  (h : LocalSplitSimpleRootGroupStatement.{u}) : LocalSplitReducedIsomorphismTheoremStatement.{u}`.

These are conditional results. The module proves neither `LocalSplitRootGroupStatement` nor
`LocalSplitSimpleRootGroupStatement`, so it does not prove the target statement on its own. It
adds no axioms.

The target (Library module `Reductive/LocalSplitReducedIsomorphismTheoremStatement`) concerns
two reductive groups `G`, `H` over a reduced local ring `R`. Each carries a closed coordinate
split torus, `i : T_I ⟶ G` and `i' : T_{I'} ⟶ H`, maximal on every residue fibre, and a
fibrewise root datum, `P` on `I` and `Q` on `I'`. If `P` and `Q` are equivalent, the target
asserts `G ≅ H`. The hypothesis `LocalSplitRootGroupStatement` (Library module
`Reductive/LocalSplitCell`) asserts the following. For every base `b` there are root
parametrizations `u α : 𝔾ₐ ⟶ G` of all roots. Moreover, for each simple root `a`,
`u_{-a}(-1) u_a(1) u_{-a}(-1)` normalizes the torus and acts on it by the simple reflection
`s_a`.

## Definition

- `LocalSplitSimpleRootGroupStatement` (namespace `Langlands.GroupScheme`): the hypotheses of
  `LocalSplitRootGroupStatement` are kept, but the conclusion asks only for the simple roots.
  Thus for every base `b` there is `u : J → (𝔾ₐ ⟶ G)` with the following properties. For every
  simple root `a`, `u a` is a root parametrization of `P.root a`, and
  `u (P.reflectionPerm a a)` is a root parametrization of `P.root (P.reflectionPerm a a) = -a`.
  Moreover, `IsWeylPoint i (weylPoint (u a) (u (P.reflectionPerm a a))) (P.reflection a)`
  holds for every simple `a`. Here `weylPoint u v` is `v(-1) u(1) v(-1)`. The values of `u` at
  the other roots are unconstrained. This is the form of the root-group input agreed with
  Worker 712, who is proving it.

## Results

- `exists_rootParametrizations_of_simple`: suppose root parametrizations are given at the simple
  roots and their negatives, and the Weyl condition holds at the simple roots. Then they extend
  to root parametrizations of all roots with the same Weyl condition. Each other root takes the
  Weyl-conjugate parametrization `weylFamily` (module `LocalSplitWeylFamily`). This lemma lets
  `LocalSplitRootGroupStatement` be proved from the simple roots and their negatives alone.
- `exists_fieldPointsEquiv_of_simpleRoots`: in the common-torus setting (both groups on `T_I`
  with the same fibrewise datum `P`), fix simple-root data `u`, `u'` as above. Then for every
  field `K` over `R` there is an isomorphism of point groups over `fieldPoint R K`. It matches the
  tori and the Weyl families `weylFamily P W u` and `weylFamily P W u'`.
- `nonempty_iso_of_commonTorus`: the common-torus case of the theorem, assuming
  `LocalSplitRootGroupStatement`.
- `localSplitReducedIsomorphismTheorem_of_rootGroups`: the theorem, assuming
  `LocalSplitRootGroupStatement`.
- `localSplitRootGroup_of_simple`: `LocalSplitSimpleRootGroupStatement` implies
  `LocalSplitRootGroupStatement`.
- `localSplitReducedIsomorphismTheorem_of_simpleRootGroups`: the theorem, assuming
  `LocalSplitSimpleRootGroupStatement`.

## Proof

`exists_rootParametrizations_of_simple`. Choose a simple word `W α` for every root
(`nonempty_simpleWord`). Define `u' α = u α` if `α` is simple or the negative of a simple root,
and `u' α = weylFamily P W u α` otherwise. At the simple roots and their negatives the given
parametrizations are kept. At the other roots, `isRootParametrization_weylFamily` (module
`LocalSplitWeylFamily`) shows that `weylFamily P W u α` is a root parametrization; its inputs
are the simple-root parametrizations and the Weyl condition. The Weyl condition for `u'` at a
simple `a` is the given one, since `u'` agrees with `u` at `a` and `-a`.

`exists_fieldPointsEquiv_of_simpleRoots`. Fix a field `K` over `R`. Over `K` we apply the field
comparison theorem `exists_iso_of_simpleRootParametrizations` (module
`LocalSplitFieldComparison`) to the fibres `G_K`, `H_K` with their field-fibre torus maps. Its
hypotheses are supplied as follows.
- `G_K` and `H_K` are connected reductive (Library `IsReductive.isConnectedReductive_algebraMap`).
- The tori are maximal (`splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise`).
- `fieldRealization K P` is their root datum (`IsFibrewiseRootDatumOf.field`).
- The base is the image of `b` under `fieldRealizationEquiv`; it has the same simple roots.
- The simple-root maps are the base changes `baseChangeRoot K (u a)` and
  `baseChangeRoot K (u (-a))`, which are root parametrizations
  (`isRootParametrization_baseChangeRoot`, module `LocalSplitBigCellProof`). Here
  `P.root (P.reflectionPerm a a) = -P.root a`.
- Their Weyl points normalize the torus: `IsWeylPoint.baseChange` (module
  `LocalSplitFieldPoints`) and `IsWeylPoint.mem_normalizerPoints`.
The resulting `Φ : G_K ≅ H_K` matches the tori, the simple-root maps and the points
`u_{-a}(-1)`. Then `exists_fieldPointsEquiv` gives the point-group isomorphism.

`nonempty_iso_of_commonTorus`. Let `J` be finite and `P` reduced (from `IsFibrewiseRootDatumOf`).
Choose a base `b` of `P` (Library `RootDatumBase.nonempty_base`). `hRG` gives root
parametrizations `u` for `G` and `u'` for `H`, Weyl-normalized at the simple roots. Choose a
simple word for every root (`nonempty_simpleWord`) and form the Weyl families of `u` and `u'`.
They are root parametrizations of all roots (`isRootParametrization_weylFamily`). Enumerate the
negative and the positive roots. Worker 712's theorem `localSplitBigCell`
(`LocalSplitBigCellStatement`, module `LocalSplitBigCellProof`) shows that both big-cell maps
are open immersions. Finally, `nonempty_iso_of_fieldAlgebras` (module
`LocalSplitCellIsomorphism`) glues `G ≅ H` from the big cells. Its field-point hypothesis is
`exists_fieldPointsEquiv_of_simpleRoots`.

`localSplitReducedIsomorphismTheorem_of_rootGroups`. Let `e : P ≃ Q`. Replace `i'` by
`precompTorus e.weightEquiv i' : T_I ⟶ H` (module `LocalSplitCommonTorus`). It is a closed
subgroup, maximal on residue fibres, and has fibrewise root datum `P`. Then apply
`nonempty_iso_of_commonTorus`.

`localSplitRootGroup_of_simple`. Given the setting of `LocalSplitRootGroupStatement` and a base
`b`, `J` is finite and `P` is reduced (from `IsFibrewiseRootDatumOf`). The hypothesis gives the
simple-root data, and `exists_rootParametrizations_of_simple` extends it to all roots.

`localSplitReducedIsomorphismTheorem_of_simpleRootGroups` composes the two previous results.

## Provenance

The target is the Isomorphism Theorem of Conrad, *Reductive group schemes*, Theorem 6.1.17
(PDF p.197), for `S = Spec R` with `R` a reduced local ring; this module proves it conditionally
on the existence of root groups. `LocalSplitSimpleRootGroupStatement` is an internal statement
of that input; for root groups over a base ring see Conrad Thm. 4.1.4 (PDF p.110), and for the
Weyl points Cor. 5.1.9 (PDF pp.140-141). The argument is internal to this project. It glues an isomorphism along the open cells (Conrad Thm. 5.1.13 and the Weil extension
argument of the Library's `CellGluing`). The cell compatibility is checked at field points,
which suffices because `R` is reduced. At field points the pinned Isomorphism Theorem over a
field applies. This replaces Conrad's generators-and-relations argument (§6.2), which works over
any base.
