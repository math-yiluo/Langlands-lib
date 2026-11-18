# Flatness of the chosen dual parameter scheme over a quasi-separated base: proof

Author: Worker 1406. The assembly follows an earlier conditional draft that
Worker 443 suggested and Worker 525 implemented. It is internal derived content:
it combines published Library theorems and makes no new literature assertion.

## Result

`Langlands.AbelianScheme.relativeDualSchemeFlat` has exactly the type
`Langlands.AbelianScheme.RelativeDualSchemeFlatStatement.{u}` from module
`Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeFlatStatement`. That
statement covers every scheme `S : Scheme.{u}` with `[QuasiSeparatedSpace S]`,
every `A : AbelianScheme S` and every proof `hA : HasDualScheme A`. Its
conclusion is that `(dualScheme A hA).hom` is flat. The theorem keeps the
arbitrary universe `u` and adds no hypothesis. In particular the chosen
parameter scheme `(dualScheme A hA).left` is never assumed quasi-separated.

## Published inputs

The proof imports these published declarations by their Lean names:

- `Langlands.AbelianScheme.dualScheme`, `poincareFamily` and
  `poincareFamily_universal` (module
  `Langlands.AlgebraicGeometry.Picard.DualScheme`, imported through the target
  statement). They are the parameter `P : Over S` and the rigidified family
  `L : RigidifiedFamily A P` chosen from `hA`, together with the proof of
  `IsUniversalPicardZero A L`.
- `Langlands.AbelianScheme.smoothFamilyPicardZeroComparison` (module
  `Langlands.AlgebraicGeometry.Picard.SmoothFamilyPicardZeroComparisonProof`)
  proves `SmoothFamilyPicardZeroComparisonStatement.{u}`. Among other things,
  this statement relates the smooth-family algebraic-triviality predicates on
  families and on classes to the geometric Picard-zero predicates.
- `Langlands.AbelianScheme.isUniversalSmoothFamilyOnQuasiSeparatedTests_of_isUniversalPicardZero`
  (module
  `Langlands.AlgebraicGeometry.Picard.SmoothFamilyUniversalOfPicardZeroUniversal`).
  Given that comparison statement and `IsUniversalPicardZero A L` for an
  actual family `L` on any parameter `P : Over S`, it proves
  `IsUniversalSmoothFamilyOnQuasiSeparatedTests A L` for the same `L`.
- `Langlands.AbelianScheme.smoothFamilyFlat` (module
  `Langlands.AlgebraicGeometry.Picard.SmoothFamilyFlatProof`) proves
  `SmoothFamilyFlatStatement.{u}`. Over a quasi-separated base `S`, it says
  that `P.hom` is flat for every parameter `P : Over S` carrying a family `L`
  with `IsUniversalSmoothFamilyOnQuasiSeparatedTests A L`. The parameter `P`
  is unrestricted.

## Proof

1. Fix `S`, the instance `QuasiSeparatedSpace S`, `A` and `hA`.
2. Take `P := dualScheme A hA` and `L := poincareFamily A hA`. The lemma
   `poincareFamily_universal A hA` gives `IsUniversalPicardZero A L`.
3. Apply `isUniversalSmoothFamilyOnQuasiSeparatedTests_of_isUniversalPicardZero`
   to `A`, the published proof `smoothFamilyPicardZeroComparison` and the
   proof from step 2. This gives
   `IsUniversalSmoothFamilyOnQuasiSeparatedTests A L` for the same `L`. The
   reason is as follows. The comparison turns the family conjunct
   `IsPicardZeroFamily A L` into the smooth-family conjunct. On a
   quasi-separated test, a smooth-family class is a geometric Picard-zero
   class by the comparison. The unrestricted Picard-zero universal property
   then supplies the same unique classifying morphism.
4. Apply `smoothFamilyFlat` to `S`, `A`, `P`, `L` and the result of step 3.
   The quasi-separatedness instance on `S` is the one fixed in step 1. This
   gives `Flat (dualScheme A hA).hom`, which is the goal.

No step changes the parameter scheme or the family. The theorem is about the
actual chosen `dualScheme A hA`, not about an isomorphic replacement. The
proof uses no flatness of fibres and no new geometric argument. The geometric
content is in `smoothFamilyFlat`, which identifies a universal parameter with
the smooth structure morphism of a published abelian-scheme representer.

## Checks and scope

A development `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (diagnostic
`4742ea3d-842d-4c82-8058-e9b88415d28e`) built the module with 0 errors and 0
warnings. Its inspection of `Langlands.AbelianScheme.relativeDualSchemeFlat`
reports a theorem with universe parameter `u` and the axioms `propext`,
`Classical.choice` and `Quot.sound` only.

The module adds only the theorem `relativeDualSchemeFlat`. It does not modify
the target statement or anything it imports. It uses no conditional draft and
constructs no second representer. Task IDs mentioned in other files record
ownership only; they are not mathematical evidence.
