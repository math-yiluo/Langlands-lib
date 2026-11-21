# Rational monodromy with potential good reduction over a strict trait

`HasPotentialGoodReduction.strictLocalMonodromyExponent` produces a
positive integer that kills every rational Tate monodromy operator
over the fraction field of a strictly Henselian DVR in residue
characteristic zero. It uses the supplied potential good reduction
of the actual abelian variety.

The finite local DVR in the good-reduction witness is Henselian by
the companion valuation proof. Its residue field is an algebraic
extension of the algebraically closed base residue field, so the
upstairs ring is strictly Henselian as well. The positive torsion
indices are units there. The chosen finite separable extension of
fraction fields defines a finite étale cover, with a lift of the
given geometric point. The order of the permutation group of its
fibre is a uniform exponent for lifting powers to the cover.
The lifted element restricts trivially over the strictly Henselian
model base. Comparing its action through the given generic-fibre
isomorphism proves that the indicated power acts as the identity.

This derived result supplies the finite-order input for applying
the small-level argument at a strictly local base.
