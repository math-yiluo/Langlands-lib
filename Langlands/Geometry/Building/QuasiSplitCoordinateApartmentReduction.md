# Actual quasi-split apartments from root coordinates and central split tori

Author: Worker 1045.

`quasiSplitIntegerApartmentExistence_of_coordinates` proves
`QuasiSplitIntegerApartmentExistenceStatement.{u}` from two unproved Library
propositions, both taken as explicit hypotheses at the same universe:

- `hCST : CentralSplitTorusCharacterStatement.{u}`. A nonzero rational
  character of a connected reductive group restricts nontrivially to some
  central split torus.
- `hcoord : QuasiSplitCoordinateApartmentStatement.{u}`. For every
  centralizer datum, there is an apartment class with a member described on
  every relative root group by coordinates of the three types.

No other hypothesis is used. In particular, connected reductivity of dynamic
centralizers is not a hypothesis: the proof uses the Library theorem
`dynamicCentralizerReductive : DynamicCentralizerReductiveStatement`.

## Proof

Introduce the data of the target: `k`, `v`, surjectivity, the henselian
proof `hH`, `G`, quasi-splitness `hQS`, `S`, `i` and `hi`. Then:

1. Record `Mono i.hom.hom.left` from `mono_of_isMaximalSplitTorus hi`, which
   is the instance used in the target. Record `IsAffineHom S.toGrp.X.hom`
   from the split-torus part of `hi`
   (`hi.isSplitSubtorus.1.isAffineHom`), and hence `IsAffine S.toGrp.X.left`
   by `isAffine_of_isAffineHom`.
2. Obtain a centralizer datum `C : CentralizerDatum i` from
   `CentralizerDatum.nonempty_of_structure dynamicCentralizerReductive hCST
   hQS.isConnectedReductive i hi`.
3. Apply `hcoord` to the same data and to `C`, obtaining `D`, `φ ∈ D.carrier`
   and the three-case coordinate hypothesis `hc`.
4. Conclude with `D`, `C`, and
   `IntegerValuation.isOmegaCompatible_of_rootCoordinateTypes hH hφ hc :
   IntegerValuation.IsOmegaCompatible v D C`.

The surjectivity hypothesis is only passed to `hcoord`.

## Scope

This is a reduction, not a proof of the target. The target still requires a
proof of `CentralSplitTorusCharacterStatement` and of
`QuasiSplitCoordinateApartmentStatement`. The latter is the construction of the
Chevalley valuation with its coordinates, V0–V5 and normalizer stability.
