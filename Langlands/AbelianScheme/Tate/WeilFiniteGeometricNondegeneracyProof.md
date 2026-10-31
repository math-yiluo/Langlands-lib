# Geometric-point nondegeneracy of the actual finite Weil pairing

Authors: Worker 935 and Worker 989.

`Langlands.AbelianScheme.geometricFiniteWeilNondegeneracy` proves exactly
`Langlands.AbelianScheme.GeometricFiniteWeilNondegeneracyStatement` from
`Langlands.AbelianScheme.Tate.WeilFiniteGeometricNondegeneracyStatement`.
Let `A` be an actual abelian scheme over a quasi-separated base `S`, with
the statement's chosen dual and constructor inputs. Let
`s : Spec K ⟶ S` be a geometric point with `K` algebraically closed and
`(n : K) ≠ 0`. Then the existing `finiteWeilLevelBilinearMap ... n
(Over.mk s)` has trivial left kernel and trivial right kernel on
`n`-torsion points over `s`.

The theorem keeps every input of the target unchanged. Of the four inputs
whose names carry the prefix `_`, the proof uses `_universality`, to give
the base change of `A` a dual scheme; `_square`, `_compatibility` and
`_geometryA` are not used. It adds no hypothesis and no axiom. Lean
reports only `propext`, `Classical.choice` and `Quot.sound`.

## Implemented proof

The proof is a single application of two published theorems.

1. `geometricFiniteWeilNondegeneracy_of_fieldDualKernelCharacterBijective`,
   from `Langlands.AbelianScheme.Tate.WeilFiniteGeometricNondegeneracyFromField`,
   derives `GeometricFiniteWeilNondegeneracyStatement` from
   `FieldDualKernelCharacterBijectiveStatement`. Its proof does the
   following:
   - It passes to `A' = (baseChange s).obj A` over `Spec K`, with the
     dual `hasDualScheme_baseChange` and inverse Poincaré data. The
     published `finiteWeilLevelBilinearMap_nondegenerate_baseChange_iff`
     transports nondegeneracy from `A'` at `Over.mk (𝟙 (Spec K))` to `A`
     at `Over.mk s`.
   - Over the field, `[n]` is an isogeny and `A'[n]` is finite étale and
     killed by `n`. The field statement then makes the dual-kernel
     character for `[n]` bijective, and a pairing value is zero exactly
     when the dual torsion character evaluates to `1` at the primal
     kernel lift.
   - *Right kernel.* A dual point pairing to zero with every `x` has a
     character that is trivial on all rational points, hence zero.
     Injectivity of the dual-kernel character then makes the point zero.
   - *Left kernel.* For `x ≠ 0`, `finiteEtaleCharacterSeparation`
     gives a character `χ` with `χ(x) ≠ 1`. It rests on
     `Cartier.exists_characterEvaluation_ne_one_of_isAlgClosed`.
     Surjectivity writes `χ` as the character of a dual `n`-torsion
     point `y`, and the pairing of `x` with `y` is `χ(x) ≠ 1`.
2. `fieldDualKernelCharacterBijective`, from
   `Langlands.AlgebraicGeometry.Picard.FieldDualKernelCharacterBijectiveProof`
   (by Worker 129), proves `FieldDualKernelCharacterBijectiveStatement`.
   That statement says that for an isogeny of actual abelian schemes over
   an arbitrary field, the existing normalized dual-kernel character is
   bijective on every test scheme.

Applying the first theorem to the second gives the target.

## Provenance and scope

This module is a derived assembly of published Library results. The
mathematical source of the target is Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary draft built 2012-02-08, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`:

- Chapter XI, Definition (11.11), printed p.162 / PDF p.166, defines the
  Weil pairing `e_n`.
- Printed p.163 / PDF p.167 notes that this pairing is perfect.
- Chapter VII, Theorem (7.5), printed p.100 / PDF p.104, gives the
  Cartier duality `Ker(f^t) ≅ Ker(f)^D` behind that perfectness.

The Lean route follows this argument. Its field input is the Library's
Cartier bijectivity theorem for the actual dual constructors.

The result covers only the trivial-kernel assertion at geometric points
with characteristic prime to `n`. It proves no group-scheme isomorphism
with a Cartier dual, no perfect pairing of group schemes over `S`, and
nothing about other test schemes.
