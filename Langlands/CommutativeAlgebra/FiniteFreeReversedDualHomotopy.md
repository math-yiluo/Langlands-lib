# Transposed maps and homotopies on reversed duals

Authors: Worker 975 (Lean construction), Worker 1015 (documentation and integration).

This internal construction extends `FiniteFreeReversedDual` to maps and
homotopies. Despite the inherited module name, its declarations apply to all
integer cochain complexes of modules over a commutative ring `R : Type u`;
they require neither finite freeness nor degree bounds. The reversal center
`g` is an arbitrary integer.

For a cochain map `φ : C ⟶ D`, `reversedDualMap g φ` goes from the reversed
dual of `D` to the reversed dual of `C`. Its degree-`i` component is the dual
map of `φ.f (g - i)`. Evaluating on a functional and an element reduces the
cochain-map identity to that for `φ`. Transposition preserves identity maps
and reverses composition, giving the contravariant `reversedDualFunctor`.

For a homotopy `h` from `φ` to `ψ`, `reversedDualHomotopy g h` has component
from degree `i` to degree `j` equal to the transpose of
`h.hom (g - j) (g - i)`. Reversing the indices preserves the required
degree restriction. The proof evaluates the homotopy identity on a functional
and an element; the two differential terms exchange roles. Additivity of
the functional and commutativity of addition give exactly the homotopy
identity for the transposed maps. No extra sign is inserted, in accordance
with the existing unsigned reversed-dual differential.

`reversedDualHomotopyEquiv g e` therefore sends a homotopy equivalence
`e : HomotopyEquiv C D` to one from the reversed dual of `D` to the reversed
dual of `C`. Its two inverse homotopies combine the preceding transpose
construction with the identity and composition formulas. Taking homology
gives `reversedDualHomologyIsoOfHomotopyEquiv` in every integer degree.
`reversedDualIsoOfIso` similarly transposes an isomorphism of complexes.

The provenance is a direct derivation from the existing reversed-dual
definition, linear dual maps, and the cochain homotopy identities. This unit
supplies homotopy compatibility; it does not assert that dualizing an arbitrary
quasi-isomorphism preserves quasi-isomorphisms.
