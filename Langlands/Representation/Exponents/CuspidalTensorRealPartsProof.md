# Actual cuspidal scalar characters and rank-weighted real parts

This internal proof establishes
`Langlands.CuspidalTensorRealPartsStatement F T` for arbitrary supplied
compatible topology, independently quantified field and carrier universes, and
every actual supercuspidal block family.

For one factor of rank `n`, `supercuspidalRepRealUnitarization` gives a real
number `t` such that twisting the actual action by `|det|^t` is unitarizable.
The twisted object remains irreducible and admissible, so
`unitarizableCentralCharacter` gives its actual norm-one character on the full
center. Restrict this character to scalar matrices and multiply by the inverse
of the determinant twist restricted to scalars. Multiplying the twisted scalar
action equation by the inverse twisting scalar proves that this character acts
on the original representation. Its norm is the inverse of `|a|^(n*t)`, hence
`|a|^(-(n*t))`.

Apply the single-factor construction independently to every block. The proved
pure-tensor lemma
`GeneralLinear.BlockShape.hasScalarCharacter_blockTensor_splitCentre` gives the
product character on the actual block tensor. The norm of a finite product,
together with the individual norm formulas, proves that this character has real
part `i ↦ -((B.size i : ℝ) * t i)`. The proof includes the empty block family.
Every block retains its own rank; no equality of block ranks is needed.

The provenance is composition of the published actual real unitarization,
unitary central-character and elementary tensor scalar-action proofs. This
calculation does not construct a Jacquet occurrence or a common integral
cuspidal line, and it uses no classification or one-line support conclusion.

The dependency audit follows the implemented lower proofs.
`supercuspidalRealUnitarization` transports the product-Levi construction
through the one-block Levi. `leviCuspidalRealUnitarization` first takes the
admissible Schur central character and decomposes its norm into real powers
block by block. Harish-Chandra compactness applies to coefficients on the
determinant-unit subgroup, where the real twist is trivial. Its finite index
modulo the center gives compact support of coefficient norms on the central
quotient. A right Haar coefficient-product integral then supplies the actual
invariant positive form. This is a local compactness and integration route.
`unitarizableCentralCharacter` uses Schur's actual scalar action and
preservation of the positive form to prove that the character has norm one.
The tensor helper is proved directly by induction on pure tensors.

The complete project import closure of this proof contains 178 modules.
Its only `Classification` modules are the definitions and lower results
`ConstituentRelations`, `Supercuspidal`, `SupercuspidalContragredientAux`,
`SupercuspidalContragredientStatement` and `SupercuspidalTwist`. All imports
resolve, and the closure contains no segment classification, multisegment
exhaustion, ordered quotient coverage, square-integrable classification or
integral-line support conclusion. The internal scalar calculation above
uses the lower proofs just described, rather than assuming any of those
conclusions.
