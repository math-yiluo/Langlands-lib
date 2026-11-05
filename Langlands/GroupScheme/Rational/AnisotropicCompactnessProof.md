# Compact rational points are equivalent to anisotropy over local fields

Authors: Worker 1617 and Worker 1563.

`Langlands.GroupScheme.anisotropicCompactness_proof` proves exactly the
published `Langlands.GroupScheme.AnisotropicCompactnessStatement.{u}` from
`Langlands.GroupScheme.Rational.AnisotropicCompactnessStatement`.
For every actual nonarchimedean local field `F : Type u`, actual group scheme
`G` over `Spec F`, and witness `hG : IsConnectedReductive G`, it proves
compactness of the full rational-point set if and only if `IsAnisotropic G`.
The latter predicate means `splitRank G = 0`, including central split tori in
the rank convention.

The proof installs `IsAffineHom G.X.hom` as `hG.isAffineHom` and obtains
`IsAffine G.X.left` by `isAffine_of_isAffineHom`. It then explicitly installs
`rationalPointTopology F G.X` on `rationalPoints G`. These are the same
instances and the same regular-function evaluation topology used in the
target definition. Both implications therefore refer to this canonical
topology on the actual rational sections.

For compactness implying anisotropy, the proof applies the published
`compactPointsAnisotropy_proof`. That result needs only the affineness already
obtained from `hG`. Its implementation pulls compactness back along each
closed split-torus inclusion. The canonical split-torus point homeomorphism
identifies the torus points with a finite product of field unit groups.
Any nonempty coordinate would give a continuous surjection onto `Fˣ`, whose
full point set is not compact. Thus every closed split subtorus has rank zero.

For anisotropy implying compactness, the proof applies the published
`anisotropicPointsCompactness_of_spectral`, supplying the published theorems
`reductiveSpectralBoundedness` and `anisotropicSpectralIntegrality`. The first
proves the exact reductive spectral boundedness statement; the second proves
integrality of all characteristic coefficients in every actual
finite-dimensional representation of an anisotropic connected reductive
group. The assembly lemma obtains a closed faithful matrix representation
internally from the published affine linear embedding theorem. Integrality
and the spectral criterion then bound all regular functions on the original
group's full rational-point set. Finally
`localFieldAffineBoundedCompactness_proof` converts this algebraic boundedness
of the closed full set into compactness in `rationalPointTopology F G.X`.
No change of rational-point space or topology is made in the closing proof.

The theorem is uniform in universe `u` and retains all the original field and
group hypotheses. It covers mixed and equal characteristic, including
imperfect local fields in positive characteristic, and split rank zero.
Its representation input is constructed internally; the imported spectral
theorems allow dimension zero. No compactness, boundedness, splitting,
representation, quotient-existence or building premise is added.

This is an internal composition of published results proving the local-field
compactness consequence of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Theorem 2.2.9, printed pp. 71–73 / PDF pp. 102–104. The target's paired
Markdown records the original source and the November 2024 Section 2.2
corrections. The proof here follows the precise implemented route described
above. Worker 1563 supplied the compactness-to-anisotropy proof and the final
composition plan and rehearsal; Worker 1617 assembled and checked this closing
proof. The spectral proofs and their prerequisites are imported unchanged,
with their authorship recorded in their own published modules.
