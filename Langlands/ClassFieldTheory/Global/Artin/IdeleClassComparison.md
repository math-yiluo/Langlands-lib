# The idèle class group of the NYLL library against the Library's

Module `Langlands.ClassFieldTheory.Global.Artin.IdeleClassComparison`, name space
`Langlands.ClassFieldTheory.Global.Artin`. This file belongs to the Library; it states a
theorem of the NYLL library (the copy under `Nyll/`) in the Library's vocabulary.

The Library's idèle class group of a number field `K` is `Langlands.Global.IdeleClasses K`, an
`abbrev` of Mathlib's `NumberField.IdeleClassGroup (𝓞 K) K`, the units of the adèle ring modulo
the principal idèles. NYLL has its own group `_root_.IdeleClassGroup K`: its idèle group is an
infinite part times the restricted product of the unit groups of the adic completions, and the
class group is its quotient by the principal idèles. NYLL proves that the two groups are
isomorphic as topological groups. The file names the isomorphism and records where a local
unit put at one finite place goes.

## Main declarations

```lean
def nyllIdeleClassEquiv (K : Type u) [Field K] [NumberField K] :
    _root_.IdeleClassGroup K ≃ₜ* IdeleClasses K

theorem nyllIdeleClassEquiv_apply (K : Type u) [Field K] [NumberField K]
    (c : _root_.IdeleClassGroup K) :
    nyllIdeleClassEquiv K c = _root_.IdeleGroup.ideleClassGroupEquivMathlib K c

theorem nyllIdeleClassEquiv_finitePlaceIdeleClass (K : Type u) [Field K] [NumberField K]
    (v : Langlands.Global.FinitePlace K) (x : (FiniteCompletion K v)ˣ) :
    nyllIdeleClassEquiv K (_root_.IdeleGroup.finitePlaceIdeleClass v x) =
      finiteClassInclusion K v x

theorem nyllIdeleClassEquiv_symm_finiteClassInclusion (K : Type u) [Field K] [NumberField K]
    (v : Langlands.Global.FinitePlace K) (x : (FiniteCompletion K v)ˣ) :
    (nyllIdeleClassEquiv K).symm (finiteClassInclusion K v x) =
      _root_.IdeleGroup.finitePlaceIdeleClass v x
```

## Proofs

`nyllIdeleClassEquiv K` is NYLL's `IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K`. The
one-place statement is NYLL's `IdeleGroup.ideleClassGroupEquivMathlib_finitePlaceIdeleClass`:
both sides are the class of Mathlib's `NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v x`,
which is what the Library's `finiteClassInclusion K v x` unfolds to. The inverse form follows by
applying the inverse equivalence.

## Declarations used

- From the NYLL copy: `IdeleClassGroup`, `IdeleGroup.ideleClassGroupContinuousMulEquivMathlib`
  (`Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/ClassGroup/MathlibTopologyComparison.lean`),
  `IdeleGroup.ideleClassGroupEquivMathlib`,
  `IdeleGroup.ideleClassGroupEquivMathlib_finitePlaceIdeleClass`
  (`…/Idele/ClassGroup/MathlibComparison.lean`), `IdeleGroup.finitePlaceIdeleClass`
  (`…/Idele/SinglePlace.lean`).
- From the Library: `Langlands.Global.IdeleClasses`, `FinitePlace`, `FiniteCompletion`,
  `finiteClassInclusion` (`Langlands/Global/Adelic.lean`).

The names `IdeleClassGroup` and `IdeleGroup` of NYLL are in the root name space; they are written
with the prefix `_root_` to keep them apart from Mathlib's `NumberField.IdeleClassGroup` and
`NumberField.IdeleGroup`.

## Sources

Neukirch, *Algebraic Number Theory*, Chapter VI, §1 (idèles and idèle classes; the idèle group
as a restricted product of the local unit groups).
