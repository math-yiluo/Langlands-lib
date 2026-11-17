# Global dynamic presentations of Borels through split maximal tori

This internal construction gives one global torus cocharacter presenting
any supplied relative Borel containing a supplied split fibrewise maximal
torus in a reductive group over a connected scheme. It requires no
Picard-triviality or affineness hypothesis on the base.

`centralizer_eq_splitTorus_of_residue_of_connected` first compares the
given split torus with an actual smooth affine representative of its
cocharacter centralizer. The comparison is monomorphic and is an
isomorphism on the specified residue fibre. Both families have
geometrically connected fibres; connected monomorphism rigidity makes
the comparison a global isomorphism. Its inclusion equation gives the
global centralizer equality.

`globalBorelCocharacter` chooses a base point and the published residue
Borel cocharacter of the original torus. The torus factors through the
supplied Borel. The resulting cocharacter of the Borel presents it as
the ambient dynamic parabolic on that residue fibre. The connected
presentation theorem makes this equality global. The preceding
centralizer argument gives precisely the original torus as centralizer.

The result is the concrete `GlobalBorelCocharacterData`, recording the
actual cocharacter and both all-test subgroup-functor equalities.
Closedness and geometric connectedness of the supplied Borel are
proved published consequences of its relative Borel property and the
ambient reductivity; they are not extra hypotheses.
