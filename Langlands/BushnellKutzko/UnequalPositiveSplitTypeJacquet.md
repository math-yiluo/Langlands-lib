# Jacquet nonvanishing for unequal positive levels

`SplitBlocks.unequalPositiveSplitTypeJacquet` proves
`UnequalPositiveSplitTypeJacquetStatement` for a split type of level
\((x,y)\) with \(x>y>0\). The proof uses the simple character and the
derived split stratum in `IsUnequalPositiveSplitType`.

Write \(m\) for the second integral depth, \(H=H^m(\beta,\mathfrak A)\)
and \(E=F[\beta]\). Lowering the stratum index to zero preserves the
defining sequence's tail and hence the character on \(H\). The split
stratum \([\mathfrak B,m,m-1,s(c)]\) gives two nonzero complementary
idempotents \(e_1,e_2\) over \(E\) and a shift on the first block.
Restriction of scalars places these endomorphisms in the corresponding
filtration lattices over \(F\). The tame corestriction has the same
value on \(c\) and on its block-diagonal part \(d\).
`exists_conj_twist_character` therefore carries \(\theta\psi_c\) to
\(\vartheta=\theta\psi_d\) by conjugation. Precomposing the representation
by that conjugation identifies the two isotypic subspaces and transports
the respective character-kernel relations.

For the normalized character, `exists_shift_element` supplies a block
shift \(z\) and a corrected shift \(y\), which raises the filtration
depth of upper block unipotents. The character comparison for the two
shifts gives the action on the \(z\)-conjugate of \(H\). In depth one,
`exists_isotypic_of_shiftedSimpleLowerH` uses the lower extension of the
simple character to get isotypy on \(K\), the subgroup of \(H\) whose
lower block has depth at least \(m+1\). For \(m\geq 2\), the overlap
character under \(z\) agrees with \(\vartheta\), and
`exists_isotypic_of_shiftedHOverlap` gives isotypy on \(K\).
`exists_isotypic_of_lowerBlock` then transfers from \(K\) to \(H\).
The two transfers preserve existence of a vector outside the
relations of the upper block group at the depth in the descent.
`unequal_not_le_relations_blockUnipotent` concludes that an
\(H\)-isotypic vector survives coinvariants by the entire upper block
unipotent subgroup.

Conjugating the idempotents back transports the radical and its Jacquet
relations to the original representation. In matrix coordinates,
`jacquet_nonvanishing_of_characterType` uses compact openness,
admissibility and containment to initialize the descent. It uses a
basis adapted to the two idempotents to express the final radical as
the conjugate of the unipotent radical of a proper standard parabolic.

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via
compact open subgroups* (1993), (8.2.5)(iv), printed pp. 276–277.
The normalization and descent are in (8.2.8)–(8.2.28), printed
pp. 278–289. Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
