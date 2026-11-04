# Ground-field characters and cocharacters of the norm-one group

This file declares a focused proposition about the actual norm-one group scheme.
It contains statement definitions; a proof remains a separate obligation.

Let `k` and `K` be fields in the same arbitrary universe, with a specified
`k`-algebra structure on `K` and `[FiniteDimensional k K]`. Write `N` for
`WeilGm.normOneCommGroupScheme (CommRingCat.of k) K`. Its underlying group scheme
is the published kernel of the determinant norm from the actual Weil restriction
of `Gm` to `Gm_k`.

The component proposition `normOneRationalCharacterVanishingStatement k K`
says that every element of `characterLattice N` is zero. These elements are
actual homomorphisms of commutative group schemes `N → Gm_k`, written additively.
The component `normOneRationalCocharacterVanishingStatement k K` says that every
element of `cocharacterLattice N` is zero; these elements are actual
homomorphisms `Gm_k → N`. Zero is the trivial group-scheme homomorphism in each
case. These are assertions about whole morphisms of schemes and therefore
retain all relative tests, including nonreduced tests.

The selected aggregate proposition
`Langlands.GroupScheme.WeilGm.normOneRationalLatticesStatement k K`
takes the explicit premise `Algebra.IsSeparable k K` and concludes the
conjunction of these two component propositions. The component definitions name
only the conclusions; when used alone, they do not include the separability
premise. There is no restriction on characteristic or extension degree.
In particular, degree one is included. No normality or Galois hypothesis on
`K/k`, chosen embedding, coefficient field, splitting datum, or descent
surjectivity is assumed.

The provenance is internal. The published `WeilGm.normOneGaloisFixedLattices` result in the module
`Langlands.GroupScheme.Torus.WeilRestrictionNormOneFixedProof` proves that the ordinary
Galois actions have no nonzero fixed vectors in the actual character and
cocharacter lattices after base change to a normal splitting field. The
published `LatticeBaseInvariants` construction gives canonical base change
into these actual invariant lattices and proves its injectivity for every
field extension. Applied with an algebraic closure as coefficient field, these
results give the intended route to the present ground-field conclusion:
canonical base change is fixed, hence zero, and injectivity detects zero
before base change. This describes the intended proof route and is not a proof
of the new proposition.

The target asserts neither that every invariant morphism descends nor an
anisotropy criterion formulated using split subtori of the actual group.
Those comparisons remain separate obligations. The actual kernel construction,
geometric lattice comparisons and fixed-lattice result are reused from the
published Library; no abstract lattice or supplied vanishing conclusion replaces
the actual ground-field character and cocharacter groups.
