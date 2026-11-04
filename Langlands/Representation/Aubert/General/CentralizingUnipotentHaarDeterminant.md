# Haar determinants for homomorphisms into a dynamic centralizer

This internal deduction restricts the actual full-centralizer action to
any homomorphism whose range lies in that centralizer. The displayed
factorization intertwines the actions on every test scheme; cancellation
of the representing unipotent monomorphism proves their equality.
Functoriality of the actual determinant character then gives equality of
their determinant characters after restriction.

The rational-point homomorphism into the actual normalizer retains the
original ambient rational point. The Haar theorem factors the acting map
through the canonical affine dynamic centralizer, applies
`dynamicUnipotentHaarDeterminant`, and rewrites its determinant using the
proved restriction formula. Thus the normalized absolute determinant
describes forward conjugation Haar scaling even when the acting group
does not represent the entire centralizer. Ambient connected reductivity,
the canonical point topology, local compactness, nonarchimedeanness,
Hausdorffness, actual unipotent closedness and finite Lie coordinates
remain explicit. No character-detection or modulus-balance premise is used.

The action equality works over an arbitrary base scheme. Its proof uses
`centralizerAdjointAction_act_comp`, `centralizingUnipotentAction_act_comp`
and cancellation of the representing monomorphism. The determinant
comparison works over a commutative ring, with affine acting schemes and
the displayed affine structure morphism on the unipotent model, and uses
`AutomorphicAction.determinantCharacter_restrict` in the same coordinates.
The normalizer homomorphism uses
`centralizer_le_normalizer_unipotent` on the identity test scheme.

For the Haar formula the proof uses
`Dynamic.Affine.isRepresentedBy_centralizerHom` and
`SubgroupFunctor.IsRepresentedBy.factorHom` with its factorization equation.
The canonical centralizer inclusion is closed, which supplies its affine
source. `rationalCharacterEval_characterRestrict` and the determinant
comparison above identify the character in the existing Haar theorem.
Equality of the two normalizer elements follows from their ambient point
equality; their membership proofs introduce no extra premise.

The transitive analytic and algebraic dependencies of
`dynamicUnipotentHaarDeterminant` are the actual rational vector filtration,
compact-open containment and vector-filtration Haar-modulus theorem,
as documented in its paired Markdown. The proof uses no geometric lemma,
representation-theoretic adjointness, cuspidal-support, representation-character
independence or Langlands-classification theorem. Representation constructions
in its imported-module closure supply no premises to this proof. The
common-centralizer module imports the torus determinant balance, but the
proof bodies here use only its actual action and normalization constructions.
Whole-common-Levi determinant balance, intersection Haar formulas,
normalized orbit comparison and the exact-K0 expansion remain separate
obligations.
