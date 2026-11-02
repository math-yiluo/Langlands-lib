# Involutivity on the actual rational-point group

`Langlands.Aubert.General.RationalPointFamily.RationalInvolutivityStatement` is a
closed Prop-valued declaration, with universe parameters `u` and `v`.

Worker 165 supplies this separate target for the actual standard rational-point
family. The ambient group is `RationalPoint k G.X` for every connected reductive
group scheme over every nonarchimedean local field, including positive
characteristic. There is no split or quasisplit restriction on `G`, and no
positive-rank or nonempty-root assumption. The specified torus is maximal split,
and `ν` is generic. Its index subtype is literally `SimpleRoot i ν`.

The proposition explicitly installs the canonical `pointTopology`, so its
subsequent local-compactness, nonarchimedean-group and Hausdorff premises refer
to that topology. It does not quantify an arbitrary ambient topology.
`StandardCocharacterStatement` and `HasRelativeRootSystem i` remain named,
unproved structural inputs. The former yields each actual standard semidirect
decomposition by the imported construction; the latter and splitness of the
torus yield the actual finite simple-root enumeration. Closedness of each
standard parabolic and unipotent subgroup, continuity of each derived Levi
projection, and the compact-limit property of each unipotent subgroup are
explicit hypotheses.

Normalized induction and normalized Jacquet restriction must each separately
preserve finite length at carrier universe `max (u + 1) v`. Their exactness is
derived by `standardParabolicFiniteLength` from the displayed topological
premises. No field assumes the desired identity. `D` is precisely
`rationalAlternatingOperator`, the sum over all actual simple-root subsets
`I` of `(-1)^|I| i_I r_I` on the existing exact finite-length Grothendieck
group. Its class formula identifies the actual composite functors.
The compact-limit premise supplies unimodularity and the source's induction
normalization. No further rank or cuspidal-support sign is applied.

This is a target with the construction premises visible. It neither proves
the identity nor discharges those premises for all rational-point groups.
The local-field quantifiers do not supply the representation-theoretic
finite-length theorems, and do not authorize treating them as external
Chapter V structural inputs. Endpoint identities and the empty-root identity
term remain separate obligations; the operator's existing empty-root formula
has its single coefficient `+1`.

The equality `D.comp D = LinearMap.id` concerns the whole exact
Grothendieck group, not only irreducible classes. This universal target is the
actual rational-point specialization of the generic `InvolutivityStatement`;
its proof is not assumed or supplied.

Source: registered original `aubert-1995-duality`, SHA256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`,
Definition 1.5 and Theorem 1.7(3), printed p.2181 / PDF p.3.
The original was reread for this target. The universal actual-group
specialization and explicit implementation premises are internal. No use is
made of unresolved Proposition 3.2 or of a classification theorem.
