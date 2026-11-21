# Finite local norm kernels for a cyclic number-field extension

`CyclicFiniteLocalNormImageStatement.{uF,uE}` identifies the preimage of the global
idele-class norm range under `finiteClassInclusion F v` with the range of the actual
completion norm at any finite place \(w\) above \(v\). The fields form a cyclic
Galois extension and can belong to separate Lean universes. The corollary
`HeckeCharacter.finiteComponent_ker_eq_localNorm` gives this local norm range as
the kernel of the finite component of a Hecke character with global norm kernel.

## Proof

For number fields in one universe, choose the arithmetic fundamental class
and a local-to-relative Weil map \(W_{F_v} \to W_{E/F}\) for \(w\). Choose an
element of \(W_{F_v}\) with geometric reciprocity value equal to the given
coordinate \(a \in F_v^\times\). The transfer of its image in \(W_{E/F}\)
is the inverse of the one-place idele class of \(a\).

If this class is a global norm, the transfer value is the norm of an idele class
of \(E\). Multiplying in the relative Weil group by the inverse of the image of
this idele class gives an element in the kernel of transfer. That kernel is the
commutator subgroup, which maps trivially to the cyclic Galois group. Exactness
also sends the image of the upper idele class to the identity. Hence the chosen
local Weil element lies in the preimage of the trivial Galois element. The published
`ker_projection_comp_eq` identifies this preimage with the image of \(W_{E_w}\).
On an element of that image the local-to-relative map and transfer compute the
global norm of an inverse one-place class. Comparing the two transfer values and
using injectivity of the map from a finite completion to idele classes shows
that \(a\) is the local norm of the upstairs reciprocity value.

For fields in separate universes, replace \(F\) by its image \(B\) in \(E\), and
take the place of \(B\) below \(w\). The norm \(C_B\to C_F\) is injective by the
Galois product formula and the degree-one condition. The corresponding local
degree is one, so the base completion map on units gives a local norm preimage
of \(a\). The global norm tower law and injectivity carry the norm condition
to the class of this preimage over \(B\). Apply the one-universe argument to
\(E/B\), then use the tower law on the resulting one-place class and injectivity
of the finite-place inclusion to recover the local norm equality over \(F\).
The converse follows by taking the idele class supported at \(w\) with the
given local norm preimage. The character corollary takes the preimage of its
global norm kernel under the finite-place inclusion.

## Provenance

This comparison combines the relative Weil transfer identities and the
local-to-global compatibility in Tate, *Number theoretic background* (1979),
§1.5 and Proposition (1.6.1). The Lean proof uses the published forms of
relative transfer reciprocity, local map existence and the local transfer
formula. It generalizes the two finite single-place norm computations in
`RelativeWeilAssemblyCharacters` to independent field universes using their
existing coordinate calculations.
