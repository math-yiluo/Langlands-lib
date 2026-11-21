# Cuspidal operator realization at a prescribed central character

`centralCharacterCuspidalOperatorRealization` takes a Hecke character and
realizes the cusp forms with that character as a subrepresentation of the
concrete operator algebra on actual automorphic forms. Membership requires the
scalar-idele transformation law and the vanishing of the proper constant
terms. The same conditions describe the image in the full automorphic form
space. The construction gives the corresponding `IsCuspidal` and
`HasCentralCharacter` properties of the realization.

The existing cuspidal operator realization supplies stability of the
constant-term condition. Right translations preserve the character law
because left multiplication by a scalar idele associates with right
translation. On each smooth archimedean slice, the character law identifies
the left translate of the slice at the shifted finite argument with a scalar
multiple of the original slice. The published left-translation identity for
the enveloping action and its complex linearity give the same equality for
the operator applied to the slices. This proves the character law for every
enveloping derivative on the adelic group. Stability under the three
families gives stability under the concrete operator algebra.

This is the fixed-character cuspidal coefficient space used before choosing a
cuspidal Levi summand in Langlands, *On the notion of an automorphic
representation*, Corvallis Part I (1979), p. 205 (PDF p. 200), in the proof of
Proposition 2 after Lemma 6. The registered source is
`langlands-1979-notion-automorphic-representation`. The Lean construction
uses the existing finite-action character and cusp conditions on each general
linear block and proves their compatibility with its full operator action.
