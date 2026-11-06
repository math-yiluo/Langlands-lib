# Normal unipotent subgroups inside cocharacter centralizers

Work over any algebraically closed field `k`. Let `j : H → G`
be a smooth connected unipotent normal closed subgroup of
an affine group scheme, let `χ : Gm → G` be an actual
cocharacter, and let `z : Z → G` be a closed representative
of the existing all-test dynamic centralizer of `χ`.

The actual scheme-theoretic intersection `H ×_G Z` is connected.
The proof views its first projection as a representative of the
fixed subgroup of the actual normalized-conjugation action of
`Gm` on `H`. Normality supplies this action and its normalization
hypotheses. The published diagonalizable fixed-subgroup theorem
makes the intersection smooth. Since `k` is perfect, the smooth
connected unipotent group `H` has a finite split series, hence
is solvable on all scheme tests. The published connectedness
theorem for smooth invariant subgroups containing torus fixed
points then applies to the fixed subgroup itself. No containment
of `H` in a dynamic parabolic is required.

If `Z` has trivial unipotent radical in the existing ground-field
sense, the second projection of this intersection has trivial
range on every scheme test. It is a closed immersion, its
source is smooth and connected by the preceding argument, and
the first projection exhibits its source as a closed subgroup
of the unipotent group `H`. Its source is therefore unipotent.
Ambient normality of `H` makes the intersection normal in `Z`.
These are exactly the hypotheses in `HasTrivialUnipotentRadical Z`,
which yields the asserted trivial all-test range.

`normalUnipotentCentralizerIsoUnit` identifies this actual
intersection with the trivial group scheme. It compares the
second projection, now representing the bottom subgroup
functor, with the actual identity-section representative of
that same subgroup. Composing its forward map with the
identity-section inclusion of `Z` recovers the specified
intersection projection.

The provenance is internal: the implementation composes
published normalized conjugation and intersection models,
smoothness of fixed intersections, perfect-field unipotent
splitting, all-test solvability, connectedness of solvable
torus fixed subgroups, and uniqueness of represented subgroups.
It supplies a field reduction tool toward detecting
reductivity by small torus centralizers. It does not assert
that the required centralizers have trivial radicals, and
does not itself establish the reductivity-locus theorem.
