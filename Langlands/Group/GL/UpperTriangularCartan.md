# Cartan covering and upper triangular contraction

`HasUpperTriangularCartanContraction n R` packages a compact open subgroup
`K` of `GL_n(R)` and a set `M` of double-coset representatives. The covering
allows repetitions. For each ambient open subgroup `J`, it gives a compact
open subgroup `L` of the actual upper triangular subgroup such that
`m⁻¹ L m ⊆ J` for every `m ∈ M`. This is the group-theoretic input for
Harish-Chandra's compact averaging argument in §4 of *A submersion principle
and its applications* (1981). The proposition translates that input into
the subgroup and Cartan interfaces of the Library.

`hasUpperTriangularCartanContraction_localField` uses the level-zero
principal subgroup as `K`. Applying the Cartan decomposition to `g⁻¹`
gives an inverse diagonal representative in the double coset of `g`.
The diagonal entries before inversion are powers of a uniformizer with
antitone exponents.

Given `J`, choose a positive principal level contained in `J`. Intersect
it with the upper triangular subgroup, which is closed because the
entries below the diagonal vanish. This gives `L`. Conjugating by an
antitone diagonal multiplies the entry differences from the identity
above the diagonal by integral ratios. The diagonal differences are
fixed, and the differences below the diagonal vanish. The same
calculation applies to the inverse matrix. The two entry conditions
identify the conjugate as a member of the chosen principal level.
In rank zero the matrix group has only the identity.
