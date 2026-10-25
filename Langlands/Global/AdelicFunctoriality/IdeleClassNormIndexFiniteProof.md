# Proof of the idele-class norm index lemma

This module, in namespace `Langlands.Global.AdelicFunctoriality`, proves the
published proposition
[`IdeleClassNormIndexFinite`](IdeleClassNormIndexFiniteStatement.md).
It changes no imported definition and declares no instances.

## Main theorem

- `ideleClassNormIndexFinite : IdeleClassNormIndexFinite.{u, v}`.
  For number fields `K : Type u` and `L : Type v` in independent universes,
  with `Algebra K L` and no normality or Galois hypothesis, let `H` be the
  range of `(ideleClassNorm (K := K) (L := L)).toMonoidHom`, the range of the
  actual idele-class norm `C_L → C_K`. Then `H.FiniteIndex`, and
  `H.index ∣ (Module.finrank K L) ^ r` for some natural number `r`.

## Implemented proof

The proof is one application of two published theorems.

- `ideleClassNormIndexFinite_of_integralIdeleClassQuotientFinite`, from
  [IdeleClassNormIndexReduction](IdeleClassNormIndexReduction.md), proves
  `IdeleClassNormIndexFinite.{u, v}` from the hypothesis
  `IntegralIdeleClassQuotientFinite.{u}`: the actual idele class group of
  every number field in universe `u`, modulo its integral idele classes, is
  finite. That module shows that the integral ideles whose coordinates are
  local-degree powers at the finitely many ramified chosen places and at the
  infinite places are idele norms, and that they have finite index in the
  integral ideles. The degree-power bound comes from the norm-of-inclusion law
  `ideleClassNormInclusionPower` and a finite-abelian-group exponent argument.
- `Langlands.ClassField.Global.integralIdeleClassQuotientFinite`, from
  [IntegralIdeleClassQuotientFinite](../../ClassField/Global/IntegralIdeleClassQuotientFinite.md),
  proves `IntegralIdeleClassQuotientFinite.{u}`. It injects `C_E / C∞` into
  the ideal class group, which is finite.

Neither input uses global reciprocity, global fundamental classes, vanishing
of idele-class cohomology or the second inequality.

## Source

The statement is the first lemma of Emil Artin and John Tate, *Class Field
Theory*, AMS Chelsea edition (2009), Chapter VI §1, printed p.20 (PDF p.29);
registered source `artin-tate-2009-class-field-theory`. The degree-power half
follows the source. The finiteness half avoids the source's reduction to a
normal overextension, as described in
[IdeleClassNormIndexReduction](IdeleClassNormIndexReduction.md).
