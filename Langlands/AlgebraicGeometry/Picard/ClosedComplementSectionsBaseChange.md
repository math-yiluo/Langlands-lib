# Canonical sections base change on a closed complement

This internal derived construction supplies the sections comparison on the
actual base change of the closed complement of an open subscheme. It retains
arbitrary fields and arbitrary morphisms between their spectra, in an arbitrary
universe.

For an open `U` in `X`, write `i : Z → X` for the published closed complement
immersion and `q : X_K → X` for the field base change projection. The first lemma
pastes the Cartesian square defining `Z ×_X X_K` with the field base change
square. This gives a Cartesian square over the original field spectra, with
structure maps `i ≫ p` downstairs and `pullback.snd i q ≫ pullback.snd p b`
upstairs. The complement after base change is the full fiber product; no
reduction or reducedness assumption is used.

`closedComplementSectionsIsoOfAmpleBaseChange` assumes that the pullback of one
specified bundle `L` is ample. The existing topological preparation then gives
compactness and quasi-separatedness of `X`. The closed immersion gives
compactness and quasi-separatedness of `Z`, and the projection to `Z` is affine
by base change. The proved canonical QCQS line-bundle sections comparison now
applies to the restriction of any actual line bundle `M` to `Z`. Flatness comes
from the field structure. Its forward map is precisely the existing canonical
scalar sections base change map for the pasted square.

This supplies an isomorphism on sections over the complement, rather than a
descent theorem for a section or a proof of ampleness reflection. Its provenance
is the imported published constructions, the companion QCQS sections theorem
and topological preparation, and Mathlib's Cartesian pasting and
quasi-separatedness facts.
