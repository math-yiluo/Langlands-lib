# Statement: compact real points of anisotropic reductive groups

`Langlands.GroupScheme.RealAnisotropicCompactnessStatement : Prop`
asserts that every connected reductive real group scheme with split rank
zero has compact full real point set. This module states the assertion and
supplies no proof. It has no universe parameters.

`IsAnisotropic G` is the existing predicate `splitRank G = 0`. Equivalently,
every finite split torus admitting a closed-subgroup inclusion into `G`
has empty index type. This convention excludes central split tori as well
as noncentral ones. `HasCompactRealPoints G` means compactness of the
entire carrier `G.affinePoints (CommAlgCat.of ℝ ℝ)` in its canonical
regular-evaluation topology. No compactness, boundedness, chosen
representation or supplied Cartan decomposition is a premise.

Source: Kazuo Suzuki, *A note on a theorem of E. Cartan*, Tohoku
Mathematical Journal 23 (1971), 17–20, source ID `suzuki-1971-cartan`,
Remark 2 on printed p.17 (one-based PDF p.1). The remark identifies
anisotropy of a reductive group with the absence of a nontrivial split
torus and, for a local field including ℝ, identifies anisotropy with
compactness of the rational point group. We use only the implication to
compactness over ℝ, with connected reductivity.

Provenance: derived. The Library's closed split-subtorus formulation
encodes the no-nontrivial-split-torus condition in Suzuki's remark.
Connected reductive group schemes over ℝ are smooth connected affine
algebraic groups, and their usual point topology is encoded by
regular-function evaluations. Thus the asserted compactness concerns the
same full real point group. No use is made of Suzuki's terminology of
a “k-Borel subgroup,” or of his introductory Theorem 2; only the explicit
split-torus and point-compactness sentences of Remark 2 are used.

The opposite implication for affine real group schemes is already proved
by `isAnisotropic_of_hasCompactRealPoints` in `Rational.RealCompactPoints`.
The nonarchimedean statement `AnisotropicCompactnessStatement` cannot be
specialized to ℝ, so it does not supply this assertion.
