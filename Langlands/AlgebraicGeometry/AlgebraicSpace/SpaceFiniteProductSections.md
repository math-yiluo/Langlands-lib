# Sections over the factors of a finite product base

This internal construction uses the fppf sheaf condition and the published
finite-product decomposition of actual test schemes. It is intended for
the finite-product decomposition of Weil restriction, before topology.

`FppfCoproduct.sectionsEquiv` identifies sections of any fppf sheaf on an
actual coproduct of schemes over a fixed base with the product of its
sections on the components. The coproduct is supplied through its actual
component maps and their colimit property as schemes. No separation,
finite type, or representability hypothesis on the sheaf is required.

The proof first makes the component maps into an fppf cover: their
coproduct structure identifies them with open immersions covering the
target. A family of sections is compatible because different components
have empty overlap, on which every sheaf has a unique section. For equal
components, monicity gives compatibility. The sheaf condition then glues
every family uniquely.

For a finite family of commutative rings `B i` and any actual test scheme
`T` over `Spec (∏ B i)`, `FiniteProductSections.equiv` applies this argument
to the pullbacks of `T` to `Spec (B i)`. Each pullback is viewed over the
original product base. The forward map is restriction along its ordinary
first pullback projection. The inclusion naturality lemma records its
compatibility with every morphism of test schemes.

All schemes and sheaves are actual objects in the published categories.
This is a categorical derivation with no external source claim. It does
not assert a topological comparison.
