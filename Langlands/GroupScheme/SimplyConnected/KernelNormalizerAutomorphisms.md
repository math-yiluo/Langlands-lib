# Normalizing points act on an actual anisotropic kernel

Let `d` be actual Tits-index data for an affine locally finite type group scheme
over an arbitrary field. Let `a : d.AnisotropicKernelIndex` be any supplied
actual centralizer of the distinguished maximal split torus, its actual derived
group, and the actual anisotropic-kernel index comparison. In particular, `a`
may be the published choice `d.anisotropicKernelIndex`.

For every actual normalizing rational point `n` of `d.splitInclusion`,
`a.normalizerCentralizerIso n` is the automorphism of `a.centralizer` induced
by ambient conjugation by `n`. The published
`torusCentralizer_comap_innerIso_normalizer` preserves the full centralizer
functor on all test schemes. The actual representative and `isoOfComap` turn
that equality into an actual automorphism with forward and inverse inclusion
squares.

`a.normalizerKernelIso n` is the resulting actual automorphism of `a.kernel`.
It applies the derived-subgroup isomorphism construction
`IsDerivedSubgroup.mapIso` to the centralizer automorphism and `a.isDerived`.
Composing the two inclusion squares proves the forward and inverse ambient
squares for `a.derived ≫ a.inclusion`. Evaluating the forward square on any
test scheme and using `comp_innerIso_hom` gives exactly ambient conjugation
of each included kernel point.

The full-centre criterion equates `AutomorphismFixesCenter` for this
automorphism with fixation by ambient conjugation of every included central
kernel point over every test scheme. One direction follows from the point
formula. The other cancels the two actual subgroup inclusions, each of which
is a monomorphism, to reflect equality back to the kernel. Consequently, a
single test point in the full kernel centre whose ambient image is moved
provides a witness to `HasCenterMovingAutomorphism a.kernel`.

These constructions and proofs have internal provenance and compose published
full-functor invariance, representability transport and derived-subgroup
functoriality. They impose no characteristic restriction and use the full
scheme-theoretic centre, including nonreduced tests. They do not produce a
normalizing point or a moved central test point from an exceptional Cartan
marking. That existence step in
`RankOneTypeEKernelCenterMovementStatement` remains unproved, as does the
separate norm-one automorphism to opposite-algebra implication and the local
rank-one enumeration.
