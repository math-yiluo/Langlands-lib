# Appending one row to a real Rankin–Selberg rectangle

For each prefix of the rectangular variable in the unequal-rank integral, `point` fills the remaining rows with zero. The empty and full prefixes give ordinary padding and the rectangular point, respectively. The next row is inserted by right translation by the exponential of a square-zero lower row matrix. The prefix point is also the leading lower-block matrix padded by the remaining identity.

`realRectangularRowAction` proves `RealRectangularRowActionStatement` for a prefix with at least one filled row and at least one trailing identity coordinate. Right multiplication by the column just after the filled rows, with entries from the first block, is left multiplication by an upper unipotent. Its Whittaker character at the supplied nonzero real scale pairs the column with the last filled row. Conjugating the column by the leading block gives the last entry that the character reads.

These identities give the row coordinates and modulation for the rectangular integral in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), equation (2.5), p. 6. The rectangular modulation is the column calculation in the proof of Lemma 6.2, p. 39. The padded leading-block calculation also appears in the proof of Proposition 6.1, pp. 41–42. [Author-posted edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf#page=39)
