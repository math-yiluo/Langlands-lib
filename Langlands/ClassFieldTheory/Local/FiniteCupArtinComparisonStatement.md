# Character comparison of finite inverse-cup reciprocity and Artin symbols

`Langlands.ClassFieldTheory.Local.FiniteCupArtinCharacterComparison` is an
internal comparison target between two published constructions. It is a
proposition definition, not a comparison theorem.

For every prime and every p-adic field package `F` in an arbitrary carrier
universe, let `D/F` be a finite Galois extension in that same universe.
Its Galois group may be nonabelian. The relative invariant is exactly
`FiniteArtinSymbol.relInv F D`, obtained from the published local invariant
family with the proved unramified second-cohomology exhaustion.
The class `c` has positive invariant `1 / [D : F]`, as expressed by the
existing `IsFundamentalClass` predicate. Bijectivity of its degree-minus-two
cup map is an explicit hypothesis of this comparison target.

For each base-field unit `a`, the inverse of that cup equivalence produces
`arithmeticReciprocityOfCup` of the actual norm-quotient class of `a`.
The target asserts that every character
`ψ : Gal(D/F) →* Multiplicative (ZMod [D : F])`, lifted through the actual
group abelianization, evaluates this element as the published
`FiniteArtinSymbol.symbolValue ψ a`. That value is defined by applying the
same canonical relative invariant to the explicit positive carry cocycle
of `ψ` and `a`. No unspecified invariant map or comparison isomorphism is
introduced.

The provenance is internal: the statement asks for equality of the
existing inverse-cup and carry-symbol constructions, with their existing
arithmetic sign conventions. For an abelian Galois group the published
finite-character separation theorem would identify the inverse-cup map
with `FiniteArtinSymbol.artinSymbol`. Output inversion would give the
geometric convention. These are intended uses of the comparison after it
is proved, not assertions proved by this statement file.

In particular, the target does not assert a Weil reciprocity system or
its transfer compatibility. The inverse-cup transfer square and this
normalized character comparison have separate proof obligations.
