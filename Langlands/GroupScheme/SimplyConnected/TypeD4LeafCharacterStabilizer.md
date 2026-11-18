# Full centre character stabilizers of the leaves of D4

Author: Worker 177.

Let `d : TitsIndexData G` for an affine, locally finite type group scheme `G`
over a field `K`. The stabilizer `d.centerCharacterStabilizer χ` uses the
ordinary absolute Galois representation on the character lattice of the
full geometric centre. The construction views the representation as an
action and takes the subgroup fixing `χ`.

For the leaf results, assume `IsSimplyConnected G` and a numbering `e` of
all simple vertices that identifies every ordered Cartan entry with
`CartanMatrix.D 4`. The leaves have labels 0, 2 and 3. The proof compares
the sums of the integral pairings with coroots 0 and 2, and with coroots
0 and 3, each reduced modulo two. Both sums are even on every simple
root by the Cartan entries. Since the simple roots generate the integral
root span, both parity maps vanish on that span.

The fundamental weights are dual to the simple coroots. Their parity
pairs at the three leaves are respectively `(1,1)`, `(1,0)` and `(0,1)`.
If two fundamental centre characters agree, the difference of their
torus weights restricts trivially. The exact kernel of centre restriction
places this difference in the integral root span, so the two parity pairs
agree. The finite comparison gives equality of the leaves. This proves
`centerFundamentalCharacter_D4_leaf_eq_iff`.

`centerCharacterStabilizer_D4_leaf` uses the ordinary Galois covariance
of the actual fundamental centre characters and the fact that the star
permutation preserves the leaves. The character stabilizer is exactly
the star stabilizer of the same leaf. Taking the actual intermediate
fixed field inside `SeparableClosure K` gives
`fixedField_centerCharacterStabilizer_D4_leaf`. In the case with no
globally fixed leaf, the published vertex-field computation therefore
identifies this exact character field as a separable cubic extension.

The results are internal deductions from the integral coroot pairing,
full centre restriction, and the full star action. They apply over every
field and characteristic, including the scheme-theoretic centre in
characteristic two.
