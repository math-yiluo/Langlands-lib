# Isomorphisms on residue fibres from isomorphisms on geometric fibres

This is a helper for the proof of
`Langlands.GroupScheme.MaximalTorusFibreSpreadingStatement`.

This module proves one theorem, in the namespace
`Langlands.GroupScheme.MaximalFibreSpreading`:

- `isIso_residueFibre_of_isIso_geometricFibre`. Let `S` be a scheme, `P` and `H` group
  schemes over `S`, `f : P ⟶ H` a homomorphism and `s : S` a point. If the base change
  of `f` along the geometric point `geometricPoint S s : Spec κ(s)^alg ⟶ S` is an
  isomorphism, then so is the base change of `f` along
  `S.fromSpecResidueField s : Spec κ(s) ⟶ S`. No smoothness, finiteness or affineness
  hypotheses are needed.

## Provenance

This is an internal helper, not a result taken from the literature. It is the standard
fact that an isomorphism can be detected after a field extension (fpqc descent of
isomorphisms).

## Proof

The geometric point `geometricPoint S s` is by definition the composite
`toAlgebraicClosure κ(s) ≫ S.fromSpecResidueField s`. Write `a` for
`S.fromSpecResidueField s` and `b` for `toAlgebraicClosure κ(s)`.

1. `baseChangeCompIso_hom_naturality a b f` says that the base change of `f` along
   `b ≫ a` and the base change along `b` of the base change of `f` along `a` agree up
   to the comparison isomorphisms `baseChangeCompIso a b P` and
   `baseChangeCompIso a b H`. So the base change along `b` of the residue-fibre map is
   `(baseChangeCompIso a b P).inv ≫ (base change of f along b ≫ a) ≫
   (baseChangeCompIso a b H).hom`. This is a composite of isomorphisms, so it is an
   isomorphism.
2. `fieldExtension_fpqc` shows that `b`, the `Spec` of the field extension
   `κ(s) → κ(s)^alg`, is surjective, flat and quasi-compact. Then
   `isIso_of_baseChange b` (fpqc base change reflects isomorphisms of group schemes)
   shows that the residue-fibre map is an isomorphism.
