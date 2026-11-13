# The simultaneous standard basis from the congruence tower of an integral model

This internal unit proves the simultaneous standard-basis property
`SimultaneousStandardBasisAt i ν K0` in two settings.

1. `K0` is the group of integral points of any integral model to which every
   cocharacter of the maximal split torus lifts
   (`simultaneousStandardBasisAt_integralPoints`).
2. `K0` is the special compact subgroup at any special vertex of a KP
   assignment available for `G` (`available_simultaneousStandardBasisAt`).

The property is the published Renard V.5.2(i)–(iv) predicate in
`Langlands.BruhatTits.SpecialCompact.StandardBasisProperty`.

`F` is any nonarchimedean local field in universe `u`. `G` is any connected
reductive group scheme over `F`. There is no split, quasi-split, tameness or
residue-characteristic hypothesis. The compact open normal subgroups used are
the congruence subgroups `M.congruenceSubgroupAt n` of the chosen integral
model `M`.

## Scope

This unit proves the third conjunct of
`AvailableSimultaneousStandardBasisStatement` for every available
assignment, and hence, through `KPBuildingAssignment.IsValid.isAvailableFor`,
for every valid one. It does **not** prove
`AvailableSimultaneousStandardBasisStatement` itself, which is the target of
Task 5310. It also proves neither `JointSpecialCompactBasisExistenceStatement`
nor `BruhatTitsAvailabilityStatement`. No existence of a valid or available
assignment is asserted or assumed.

The unit builds on four helper modules in
`Langlands/BruhatTits/SpecialCompact/CongruenceBasis/`, each with its own
Markdown:

- `GLCongruence`: principal congruence subgroups of `GL_N` and their block
  factorizations;
- `LinearSetting`: their pullbacks along a closed embedding, with Iwahori
  factorization and contraction;
- `ModelCongruence`: the model congruence tower as such a pullback, made
  diagonal for one model cocharacter;
- `ModelCocharacter`: the full model at a special vertex and lifts of torus
  cocharacters.

## Definition

- `integralUniformizer : 𝒪[F]` is the chosen uniformizer
  `LocalField.uniformizer F`, viewed in the valuation ring.
  `uniformizer_mem_integer` shows that it is integral, using
  `FML.ord_nonneg_iff_mem_integer` and `LocalField.ord_uniformizer`. The
  contraction step uses it as the integral element whose image is the unit
  `SplitTorusValuation.uniformizerUnit F`.

## Results on standard subgroups

Let `i : S ⟶ G` be a maximal split torus, `ν` a generic cocharacter and `J`
a set of simple relative roots.

- `map_conj_mem_standardUnipotentPoints`: rational points of the torus
  normalize every standard unipotent radical `U_J`. A torus point lies in the
  torus centralizer (`range_le_torusCentralizer`), hence in the dynamic
  centralizer of every cocharacter (`torusCentralizer_le_dynamicCentralizer`),
  which normalizes the dynamic radical.
- `isStandardCocharacter_zeroSet`: a cocharacter `y` that vanishes on `J` and
  is nonnegative on all simple roots is standard for the set `J'` of simple
  roots on which it vanishes. Moreover `J ⊆ J'`.
- `mem_parabolic_of_mem_standardUnipotentPoints`: for such `y`, the radical
  `U_J` lies in the dynamic parabolic `P(y)`. The steps are
  `U_J ⊆ P_J ⊆ P_{J'}`, using the published `standardParabolicOrder`, and
  `P_{J'} = P(y)` because `y` is standard for `J'` (`mem_standardParabolic`).

## Results on the congruence tower of a model

Let `M : IntegralModel 𝒪[F] F G` satisfy the lifting hypothesis `hχ`: for
every cocharacter `y` of `S` there is a cocharacter `χ` of `M.group` with
`M.genericCocharacter χ = groupHom y ≫ i`.

- `uniformizerPowers_eq`: the published uniformizer power
  `Aubert.General.uniformizerPowers i y` is the image of
  `SplitTorusValuation.uniformizerUnit F` under the cocharacter
  `groupHom y ≫ i`. This holds by definition.
- `conj_mem_congruenceSubgroupAt_inf_standardUnipotentPoints`: let `A, q` be a
  compatible standard split component for `J`, and let `m` lie in the weak
  chamber `standardComponentCAplus i ν J q`. Then conjugation by `m`
  preserves `M.congruenceSubgroupAt n ⊓ U_J`. The proof runs as follows.
  1. The published `IsCompatibleStandardSplitComponent.exists_eq_uniformizerPowers`
     writes `m` as `uniformizerPowers i y`, with `y` vanishing on `J` and
     nonnegative on simple roots.
  2. Lift `y` to a model cocharacter `χ`. `exists_model_linearCongruence`
     gives a closed embedding `ρ` that diagonalizes `groupHom y ≫ i` and
     identifies every `M.congruenceSubgroupAt n` with
     `linearCongruence ρ (algebraMap 𝒪[F] F) (𝔪ⁿ)`.
  3. The element lies in `P(y)` by the previous section.
     `conj_mem_linearCongruence` applies with `t = uniformizerUnit F` and
     `r = integralUniformizer`.
  4. `U_J` is preserved by `map_conj_mem_standardUnipotentPoints`.
- `weakChamberContraction_congruenceSubgroupAt`: for each `n`,
  `WeakChamberContraction (M.congruenceSubgroupAt n) U_J Ū_J (weak chamber)`.
  Conjugation by `m` preserves the positive intersection by the previous
  result. Conjugation by `m⁻¹` preserves the negative intersection by the
  same result for the reversed data: `-ν` (`hν.neg`), the negated roots
  `-J`, which are simple for `-ν` (`neg_mem_simpleRelativeRoots` with the
  published `relativeRootNegation`), the reversed component `hA.reversed`, and
  `m⁻¹` in its weak chamber (`inv_mem_standardComponentCAplus_reversed`).
- `hasIwahoriIntersectionDecomposition_congruenceSubgroupAt`: **Iwahori
  factorization.** For each `n`, `M.congruenceSubgroupAt n` has the
  intersection decomposition with respect to `(M_J, U_J, Ū_J)`. The proof
  runs as follows.
  1. The published `standardCocharacter` gives a cocharacter `ζ` with
     `M_J = Z(ζ)` and `U_J = U(ζ)`. The published
     `standard_eq_dynamic_of_relativeRootNegation`, applied to `-ν`, `-J` and
     `-ζ`, together with `groupHom_neg_comp_eq_oppositeCocharacter`, gives
     `Ū_J = U(ζ⁻¹)`.
  2. Lift `ζ` to the model and take the diagonal embedding from
     `exists_model_linearCongruence`. Then `exists_linearCongruence_triple`
     (with `𝔪ⁿ ≤ 𝔪`) writes each element as an ordered product of factors in
     the congruence subgroup and in `U(ζ⁻¹)`, `Z(ζ)` and `U(ζ)`.
  3. The published `hasIwahoriIntersectionDecomposition_of_surjective`, with
     ambient uniqueness from `standardTripleProduct_injective`, turns this
     surjectivity into the decomposition.
- `simultaneousStandardBasisAt_integralPoints`: **the simultaneous standard
  basis of an integral model.** Under `hχ`,
  `SimultaneousStandardBasisAt i ν M.integralPoints` holds. The proof applies
  the published `simultaneousStandardBasisAt_of_cofinal_weakIwahoriNormalFamily`
  with the published family `standardSplitComponentFamily i ν hG hi hν`. For
  each identity neighborhood `W`, the published
  `LocalFieldIntegralModel.congruenceNeighborhoodBasis_proof` gives three
  things: some `M.congruenceSubgroupAt n ⊆ W`; that this subgroup is compact,
  open and normal in `M.integralPoints`; and, via
  `congruenceSubgroupAt_le_integralPoints`, that it lies in `M.integralPoints`.
  The two preceding results supply its Iwahori decomposition and weak
  contraction for every standard `J`.

## The special vertex of an available assignment

- `available_simultaneousStandardBasisAt`: let `𝔅` be a KP assignment with
  `𝔅.IsAvailableFor F G hG`, and let `D := (𝔅.datum F G hG).base`. Let `ν` be
  a generic cocharacter of `D.S` and `x` a special apartment vertex. Then
  `SimultaneousStandardBasisAt D.i ν (D.apartment.specialCompactSubgroup x)`
  holds. `exists_specialVertexModel` gives a model with integral points
  `specialCompactSubgroup x` that satisfies `hχ`, and the previous theorem
  applies with `D.isMaximalSplitTorus`.

## Provenance

The provenance is internal composition. The property proved is the published
formalization of Renard, *Représentations des groupes réductifs p-adiques*,
V.5.2(i)–(iv), at the published special compact subgroup. The implemented
route uses congruence subgroups of the KP full model at the vertex, linearized
by a faithful integral representation, rather than Renard's own argument. No
new literature statement is formalized.
