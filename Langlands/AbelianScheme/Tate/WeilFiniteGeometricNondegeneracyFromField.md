# Geometric-point finite Weil nondegeneracy from field Cartier bijectivity

## Statement and main theorem

`FiniteEtaleCharacterSeparationStatement` is the proposition that characters separate
rational points. Take an algebraically closed field `K`, a commutative group scheme `G` over
`Spec K` with finite étale structure morphism, and `n` with `(n : K) ≠ 0` and
`multiplication G.toGrp n = 1`. Then every rational point `x ≠ 1` of `G` has a character `χ`
over `Over.mk (𝟙 (Spec K))` with `Cartier.characterEvaluation χ x ≠ 1`.

`geometricFiniteWeilNondegeneracy_of_field` proves the published
`GeometricFiniteWeilNondegeneracyStatement` from two hypotheses:
`FieldDualKernelCharacterBijectiveStatement` and `FiniteEtaleCharacterSeparationStatement`.
The theorem does not prove either hypothesis.

`finiteEtaleCharacterSeparation` proves the separation proposition from
`Cartier.exists_characterEvaluation_ne_one_of_isAlgClosed` (module
`Langlands.GroupScheme.Cartier.AlgClosedCharacterSeparation`, by Worker 970).
`geometricFiniteWeilNondegeneracy_of_fieldDualKernelCharacterBijective` therefore derives
`GeometricFiniteWeilNondegeneracyStatement` from `FieldDualKernelCharacterBijectiveStatement`
alone. That field statement is the open target of task ece22f73 and is not proved here.

## Proof

1. *Over the field.* `finiteWeilLevelBilinearMap_nondegenerate_of_field` treats an abelian
   scheme `B` over `Spec K`, `K` algebraically closed and `(n : K) ≠ 0`, at the test object
   `T = Over.mk (𝟙 (Spec K))`. Let `G = kernelCommGroupScheme [n]`. It is finite étale
   (`multiplicationKernel_isFinite_of_ne_zero`, `multiplicationKernel_etale_of_ne_zero`) and
   killed by `n` (`torsion_multiplication_eq_one`). `[n]` is an isogeny
   (`multiplication_isIsogeny_of_ne_zero`). These three lemmas come from module
   `Langlands.AbelianScheme.FieldMultiplicationFiniteEtale`. So the field statement gives
   bijectivity of `dualKernelPointCharacter` for `[n]` at `T`. By `finiteWeilLevelBilinearMap_coe`, a pairing
   value is zero exactly when the dual torsion character evaluates to `1` at the primal kernel
   lift (`finiteWeilLevelBilinearMap_eq_zero_iff`).
   - *Right kernel.* If `y` pairs to zero with every `x`, its character is trivial on all
     rational points of `G`. `characters_eq_zero_of_evaluation` makes it zero. Injectivity of
     `dualKernelPointCharacter`, transported through `relativeDualMultiplicationKernelIso` and
     `dualTorsionCharacter_one`, then gives that the kernel lift of `y` is `1`, so `y = 0`.
   - *Left kernel.* If `x ≠ 0` pairs to zero with every `y`, the separation hypothesis gives a
     character `χ` with `χ(x) ≠ 1`. Surjectivity writes `χ` as the character of a dual-kernel
     point, which corresponds through `relativeDualMultiplicationKernelIso` to an `n`-torsion
     point `y` of the dual. Then `χ(x)` is the pairing of `x` and `y`, a contradiction.
2. *Base change.* For a point `s : Spec K ⟶ S`, put `A' = (baseChange s).obj A`, with dual
   `hasDualScheme_baseChange` and inverse data from `LineBundle.exists_tensorObj_iso_structureSheaf`.
   The published `finiteWeilLevelBilinearMap_nondegenerate_baseChange_iff` (module
   `FiniteWeilBaseChange`) transports nondegeneracy from `A'` at `Over.mk (𝟙 (Spec K))` to `A`
   at `(Over.map s).obj (Over.mk (𝟙 _)) = Over.mk s`, by `Category.id_comp`.

Of the inputs quantified in the target statement, `universality` is used, for the dual of the
base change. `_square`, `_compatibility` and `_geometryA` are not used.

## Provenance

Edixhoven, van der Geer and Moonen, Chapter XI, Definition (11.11), define the finite Weil
pairing through the Cartier duality of Chapter VII, Theorem (7.5), and note that it is perfect.
Over an algebraically closed field, with `n` invertible, the `n`-torsion group schemes are
finite étale. Perfectness then gives trivial kernels on rational points. The field
bijectivity input is exactly the published statement of task ece22f73. This module derives
the geometric-point consequence for the Library's constructions.
