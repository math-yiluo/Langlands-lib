# The root-datum map induced by a split group isogeny

`Langlands.GroupScheme.IsogenyRootDatumStatement` is the lattice,
centrality and isomorphism portion of Milne Proposition 23.5. It is a
proposition declaration; this module does not prove it.

Let `G` and `G'` be connected reductive group schemes over an arbitrary
field `k`. Let `i : T → G` and `i' : T' → G'` be split maximal tori,
with specified finite reduced root data `P` and `P'` on their actual
character and cocharacter lattices. Given an isogeny `φ : G → G'` and
a torus homomorphism `t : T → T'` satisfying `i ≫ φ = t ≫ i'`, the
statement asserts that `t` is an isogeny and that there exists

```
f : RootDatumIsogeny (ringExpChar k) P' P
```

whose maps are exactly

```
f.weightMap χ = t ≫ χ
f.coweightMap ν = ν ≫ t.
```

The root-datum structure supplies injective, mutually transposed integral
lattice maps, a bijection of root indices, and paired root and coroot
equations with root-dependent powers of `ringExpChar k`. This exponent
is one in characteristic zero and the prime characteristic otherwise.
It is fixed by the field, rather than supplied independently.

The conclusion also says that `φ` is central exactly when every root
factor of `f` is one, and that `φ` is an isomorphism exactly when `f` is
central and its weight map is bijective. The latter is precisely
Milne's Definition 23.2 of an isomorphism of root data. Weight-map
bijectivity alone is insufficient, as Milne warns after the proof of
Proposition 23.5, referring to Example 23.30.

## Group-scheme and lattice conventions

The ambient groups and homomorphisms use the existing `Grp (Over (Spec k))`
architecture. `IsIsogeny` means finite, flat and surjective on the
underlying scheme morphism. `IsCentralIsogeny` additionally requires local
finite presentation and centrality of the full scheme-theoretic kernel,
tested on every test scheme. There is no kernel-smoothness or
separability assumption.

Finiteness of each character and cocharacter module is obtained from the
corresponding split-torus hypothesis using
`IsSplitTorus.finite_characterLattice` and
`IsSplitTorus.finite_cocharacterLattice`. Root indexing types are finite,
and both root data are explicitly reduced, in agreement with the
conventions of Milne §23.a. Roots and coroots need not span the whole
lattice; central torus directions are retained. `IsRootDatumOf` identifies
the datum's pairing with the actual torus pairing, its roots with the
adjoint roots, and its reflections with normalizer actions.

## Original sources and scope

The source is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of
Finite Type over a Field* (2017), Definitions 23.1–23.2, printed
pp.483–484, and Proposition 23.5 and its proof, printed pp.485–486
(one-based PDF pp.499–502). The registered source is
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The complete retained official errata snapshot,
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
has no correction to these definitions or Proposition 23.5.

The direction `P' → P` agrees with Milne's pullback `X(T') → X(T)`.
The factor at a root index `j'` of `P'` is his factor at the receiving
root `P.root (f.indexEquiv j')`. The two scaled root equations and the
centrality criterion therefore have his orientations.

This focused statement does not assert the root-subgroup image comparison
or the root-coordinate polynomial formula also present in Proposition
23.5. It supplies the actual-lattice comparison for general isogenies,
including inseparable ones. The existing
`CentralIsogenyRootDatumHomStatement` covers the central specialization
using exact `RootPairing.Hom`; the present statement permits nontrivial
characteristic-power factors.
