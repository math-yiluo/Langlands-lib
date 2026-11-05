# Realizing a prescribed finite separable generic extension

`finiteSeparableGenericCover` proves the published proposition
`FiniteSeparableGenericCover` in an arbitrary common universe `u`.
It uses the published `PrescribedGenericCoverData.construct` construction
from `FiniteSeparableGenericCoverData`, developed by Worker 105.
The statement and all of its imports are unchanged.

For an arbitrary irreducible scheme `Y`, a specified whole-space generic
point `η`, and a prescribed finite separable extension `L` of the actual
residue field `Y.residueField η`, the proof applies that constructor to
exactly these inputs. It takes its nonempty open, affine irreducible model,
finite étale surjective morphism, generic point and residue-field spectrum
isomorphism as the existential witnesses of the statement. All property
proofs and the structural triangle are the corresponding fields of the
constructed data. Thus the triangle uses the original given algebra map
from `Y.residueField η` to `L`.

This is an internal proof adapter to the already published construction,
which implements the prescribed-extension step in the proof of Stacks
Lemma 37.24.8 (0551). It adds no hypotheses or additional mathematical
construction. In particular, it permits nonreduced irreducible schemes.
It proves the prescribed-cover existence input only; choosing a field
extension that splits every actual geometric component and proving
`FiniteTypeFiniteEtaleGenericComponentSplitting` remain separate obligations.
