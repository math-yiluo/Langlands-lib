# The conditional intertwining theorem from growth, squared modulus and character decay

Lean module: `Langlands.Representation.Plancherel.ParabolicIntertwiningDecayAssembly`,
namespace `Langlands.Plancherel`.

## Purpose and provenance

Provenance: internal. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), IV.1.1, printed pp. 277–281 (PDF pp. 43–47), proves convergence
of the standard intertwining integral from three ingredients: moderate growth of the
coefficients of the inducing representation (Corollary I.4.4), the relation between the moduli
of the unipotent radicals, and the decay of `δ^{1/2} χ` at the Levi components of `Ū(F) ∩ U'(F)`
on a cone of characters. This module assembles the published reductions so that the exact host
proposition `ConditionalParabolicIntertwiningStatement` follows from three named propositions:
the published `RationalFiniteLengthModerateGrowthStatement` and two propositions introduced here,
`ParabolicSquaredModulusInput` and `ParabolicCharacterDecayInput`. Neither of the two new
propositions is proved here. The assembly is derived from Library results and is not transcribed
from the source.

## Setting and notation

The data are those of `ConditionalParabolicIntertwiningStatement` (module
`ParabolicIntertwiningStatement`): a nonarchimedean local field `F` of arbitrary characteristic;
a connected reductive group `G` over `F` (`hG`), whose point group `G(F)` carries
`rationalPointTopology F G.X` and is assumed locally compact, nonarchimedean and Hausdorff; a
commutative group scheme `A`; group schemes `M`, `P`, `P'`, `U`, `U'` with `M.X.left` affine and
`M` locally of finite type; parabolic root presentations `r : ParabolicRootPresentation p l a`
and `r' : ParabolicRootPresentation p' l' a` with common Levi (`l ≫ p = l' ≫ p'`) and geometric
unipotent radicals `n : U ⟶ P`, `n' : U' ⟶ P'`. The point subgroups of `G(F)` are
`Ppt`, `P'pt` (images of `p`, `p'`), `Mpt = parabolicLeviPointSubgroup p l`, `Upt`, `U'pt`
(images of `n ≫ p`, `n' ≫ p'`). For `ParabolicCharacterDecayInput`, `q : Q ⟶ G` represents the
dynamic parabolic of the negative of the split-component cocharacter of `r'` (`hQ`), `v : V ⟶ Q`
is a geometric unipotent radical (`hv`), `B` is the Weyl-invariant form
`weylInducedCharacterForm` (under `Fintype` of the relative Weyl group), and
`C = parabolicPointUnramifiedIntertwiningRegion r B n q v` is the family of regions of the host
statement. These are exactly the expressions of the host statement.

## Declarations

- `ParabolicSquaredModulusInput` (definition, a `Prop`): for all host data as above (through
  `r`, `r'`, the common Levi and the two radicals), every pair of semidirect decompositions
  `h : Ppt = Mpt ⋉ Upt`, `h' : P'pt = Mpt ⋉ U'pt` with closed `Upt`, `U'pt`, and all Borel
  measurable structures on `U'pt` and `Upt ∩ U'pt`, the public `SquaredModulusCompatibility h hU
  h' hU'` holds: on `Mpt`, the moduli of conjugation on `Upt` and on `U'pt` multiply to the square
  of the modulus of conjugation on `Upt ∩ U'pt`.
- `ParabolicCharacterDecayInput` (definition, a `Prop`): for all host data as above together with
  `q`, `v`, `hQ`, `hv` and `Fintype (relativeWeylGroup r.data.i)`, every semidirect decomposition
  `h : Ppt = Mpt ⋉ Upt` with closed `Upt`, and every compact open subgroup `K` of `G(F)` with
  `G(F) = Ppt K`, there are `N : ℕ` and a closed representation `ρ₀` of `G` on `Fin (N + 1)` such
  that `ParabolicOppositeCharacterDecay r h hU K ρ₀ C` holds, with the implicit `U'pt` the image
  of `n' ≫ p'` and `C` the host regions. Explicitly (module
  `ParabolicIntertwiningCharacterDecay`): for every `s` there is `R` such that along every section
  of `(Upt ∩ U'pt) \ U'pt → U'pt` with values in `Ū(F)`, the weight `‖δ^{1/2}(m)‖ ‖χ(m)‖` at the
  Levi projection `m` of every factorization `σ q = p κ` is bounded by a constant times
  `‖σ q‖ ^ (-s)`, locally uniformly in `χ` on `C R`. The index `Fin (N + 1)` makes the matrix
  index nonempty, as `ParabolicOppositeCharacterDecay` requires.
- `conditionalParabolicIntertwiningInputs_of_characterDecay`: the three propositions
  `RationalFiniteLengthModerateGrowthStatement`, `ParabolicSquaredModulusInput` and
  `ParabolicCharacterDecayInput` imply the public `ConditionalParabolicIntertwiningInputs`
  (module `ParabolicIntertwiningReduction`).
- `conditionalParabolicIntertwiningStatement_of_characterDecay`: the same three propositions
  imply `ConditionalParabolicIntertwiningStatement`.

## Proof as implemented

1. `conditionalParabolicIntertwiningInputs_of_characterDecay`. Introduce the data of
   `ConditionalParabolicIntertwiningInputs`. The character-decay input applied to these data and
   to the compact open subgroup `K` with `G(F) = Ppt K` gives `N`, a closed `ρ₀` and
   `ParabolicOppositeCharacterDecay`; the squared-modulus input gives
   `SquaredModulusCompatibility h hU h' hU'` for the host's measurable structures. The public
   `parabolicOppositeConeDecay_of_characterDecay` (with `hPpt`, `hUpt` by `rfl`) turns the
   character decay into `ParabolicOppositeConeDecay`. The public
   `parabolicLevi_exists_coefficientGrowth` turns the moderate-growth statement into
   `HasCommonCoefficientGrowth π (‖·‖_{ρ₀})` for the admissible finite-length `π` of `Mpt`. The
   public `exists_region_convergence_domination_of_coneDecay` (module
   `ParabolicIntertwiningConeReduction`) then gives `R` such that the standard integral
   converges on the whole source at every parameter of `C R`, with local integrable domination on
   `C R`; together with the squared-modulus compatibility this is the required conclusion.
2. `conditionalParabolicIntertwiningStatement_of_characterDecay`. Apply the public
   `conditionalParabolicIntertwiningStatement_of_inputs` to step 1.

## Scope

The host theorem is reduced to its three named inputs; none of them is proved here.
`RationalFiniteLengthModerateGrowthStatement` is published as a statement. For the host regions,
both `ParabolicSquaredModulusInput` and `ParabolicCharacterDecayInput` need the structure of
relative roots (relative root reflections and equality of the dimensions of opposite root
spaces), which is not established in the Library. The module therefore does not complete the
host theorem.
