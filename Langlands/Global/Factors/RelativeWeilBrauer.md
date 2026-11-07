# Degree-zero Brauer decompositions on relative Weil groups

## Contents

The module supports the proof of
`Langlands.Global.FunctionalEquationComparison.RelativeWeilTwistFunctionalEquationStatement`.
Let `E/F` be a finite Galois extension of number fields and `c` a class family. The module
writes the twist by a continuous character of a continuous virtual representation of
`W_{E/F}` as a degree term plus a signed sum of inductions from relative Weil groups
`W_{E/K}` of differences of two characters. It then restricts this decomposition to the
local Weil group at a finite place. Two published propositions enter as explicit
hypotheses and are not proved here. Brauer induction for `W_{E/F}`
(`InducedCharacterGeneration`, module
`Langlands.VirtualRepresentation.Global.RelativeWeilInductionGenerationStatement`) is
the argument `hgen`. The local restriction formula (`LocalInducedRestriction`, module
`Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionStatement`) is the
argument `hloc`. As in those modules, `Gal(E/F)` has the discrete topology
`relativeGaloisTopology`, which is a local instance throughout the
`RelativeWeilGroup` namespace of this file.

Notation: `[θ]` is `ExactGrothendieckGroup.characterClass θ`, the exact virtual class of
the character line of a continuous character `θ`. `Ind_S` is
`ExactGrothendieckGroup.continuousInduce S`, and `IndAlong φ` is
`ExactGrothendieckGroup.continuousInduceAlong φ`. `deg` is
`ExactGrothendieckGroup.degree`, and `W_H` is `galoisPreimage c F E H`, the inverse image
in `W_{E/F}` of a subgroup `H` of `Gal(E/F)`.

### Generic lemmas on continuous exact virtual groups

These are in namespace `Langlands.VirtualRepresentation.ExactGrothendieckGroup`, for
arbitrary topological groups `G` and `H`:

- `continuousRestrict_characterClass`: restriction along `φ : H →ₜ* G` sends `[η]` to
  `[η ∘ φ]`.
- `codRestrictOfRange φ S hS`: if the range of `φ : H →ₜ* G` is the subgroup `S`, this is
  `φ` as a continuous homomorphism `H →ₜ* S`.
- `continuousInduce_characterClass_eq_along`: if `φ` is an open embedding with
  finite-index range `S`, then `Ind_S [θ] = IndAlong φ [θ ∘ φ]`, for every continuous
  character `θ` of `S`.
- `continuousTwist_continuousInduce_eq_along`: under the same hypotheses, and for every
  continuous character `η` of `G`,
  `η ⊗ Ind_S ([θ] - [θ']) = IndAlong φ ([(η ∘ φ)(θ ∘ φ)] - [(η ∘ φ)(θ' ∘ φ)])`.

### Brauer decomposition on `W_{E/F}`

These are in namespace `Langlands.ClassField.Global.RelativeWeilGroup`:

- `characterDifferenceGenerators c F E`, the main definition: the set of classes
  `Ind_{W_H} ([θ] - [θ'])` in `ContinuousVirtual c F E`, for a subgroup `H` of `Gal(E/F)`
  and continuous characters `θ`, `θ'` of `W_H`. Character lines on `W_H` have carriers in
  universe `max u uV`, as in `inducedCharacterGenerators`.
- The imported `isOpen_ker_projection` from `RelativeWeilInductionGenerationStatement`:
  the kernel `C_E` of the projection `W_{E/F} → Gal(E/F)` is open.
- `galoisCharacter c F E S χ`: a character `χ` of a subgroup `S` of `Gal(E/F)`, composed with
  the projection `W_S → S`. It is continuous because `S` is discrete.
- `inflate_induce_oneDimensional`: inflation along the projection, applied to the induced
  class `Ind_S χ` of the finite group `Gal(E/F)`, gives `Ind_{W_S} [galoisCharacter χ]`.
  `inflate_one` is the same statement for the trivial character of `Gal(E/F)`.
- `induce_one_sub_mem_span`: `Ind_{W_H} [1] - [W_{E/F} : W_H] · [1]` lies in the `ℤ`-span of
  `characterDifferenceGenerators`.
- `sub_degree_smul_mem_span` (hypothesis `hgen`): for every `x : ContinuousVirtual c F E`,
  `x - deg x · [1]` lies in the `ℤ`-span of `characterDifferenceGenerators`.

### The twisting character

- `continuousReciprocityCharacter c F E χ`: for a continuous character `χ` of `C_F`, the
  published character `reciprocityCharacter c F E χ = (χ ∘ transfer)⁻¹` of `W_{E/F}`, as a
  continuous homomorphism. `continuousReciprocityCharacter_toMonoidHom` states that the
  underlying homomorphism is `reciprocityCharacter c F E χ`.

### Rewriting with intermediate fields

All results here take `h : FundamentalClass.Restriction c`, which the published
`restrictionInclusion c F E K h : W_{E/K} →ₜ* W_{E/F}` requires.

- `range_restrictScalarsHom`: for an intermediate field `K`, the image of `Gal(E/K)` in
  `Gal(E/F)` is the fixing subgroup of `K`.
- `range_restrictionInclusion_fixedField`: for `K` the fixed field of `H`, the range of
  `restrictionInclusion c F E K h` is `W_H`.
- `exists_twist_decomposition` (hypotheses `h`, `hgen`): for every
  `x : ContinuousVirtual c F E` there are `n : ℕ`, integers `r i`, intermediate fields `K i`
  and continuous characters `θ i`, `θ' i` of `W_{E/K i}`, indexed by `i : Fin n`, with the
  following property. For every continuous character `η` of `W_{E/F}`,
  `η ⊗ x = deg x · [η] + Σ_i r i · IndAlong ι_i ([(η ∘ ι_i) · θ i] - [(η ∘ ι_i) · θ' i])`,
  where `ι_i = restrictionInclusion c F E (K i) h`. The data `n`, `r`, `K`, `θ`, `θ'` do not
  depend on `η`.

### Restriction to a local Weil group

- `exists_continuousRestrict_decomposition` (hypothesis `hloc`): let `z` be a finite place of
  `F`, `ιd : W_{F_z} →ₜ* W_{E/F}` a continuous homomorphism, and `K i` intermediate fields.
  Assume `LocalInducedRestriction.{max u uV, u} c F (K i) E h z ιd` for every `i`. Then there
  are continuous homomorphisms `ιu i u : W_{K_u} → W_{E/K i}`, one for each place `u` of `K i`
  above `z`, whose transfer to `C_{K i}` is the inverse of every geometric local reciprocity
  map at `u` (the first condition of `LocalInducedRestriction`). For all integers `d`, `r i`
  and continuous characters `η`, `α i`, `β i`, the restriction along `ιd` of
  `d · [η] + Σ_i r i · IndAlong ι_i ([α i] - [β i])` equals
  `d · [η ∘ ιd] + Σ_i r i · Σ_{u | z} IndAlong (completionWeilMap z u) ([α i ∘ ιu i u] - [β i ∘ ιu i u])`.

Combining `exists_twist_decomposition` with `exists_continuousRestrict_decomposition` for
`ιd = discreteLocalMap ι` gives the input identity of
`Langlands.Weil.Local.InertiaEuler.arithmeticPairLFactor_eq_of_virtualIdentity` (module
`Langlands.Global.Factors.RelativeWeilLocalEuler`).

## Source and provenance

John Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979),
3–26 (registered `tate-1979-number-theoretic-background`). Printed page `p` is PDF page
`p + 9` of `Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.

- Proposition (2.3.1), printed p.11, states that `R°(W_F)` is generated by the elements
  `Ind_{E/F}([χ] - [χ'])`. Its proof uses the degree-zero form of Brauer's theorem for the
  Galois group, the formula `Ind(ρ ⊗ Res χ) = (Ind ρ) ⊗ χ`, and the decomposition
  `[ρ] - (dim ρ)[1] = Ind([ρ_E] - (dim ρ_E)[1_E]) + (dim ρ_E)(Ind[1_E] - [E:F][1_F])`.
  `sub_degree_smul_mem_span` is a derived relative form for `W_{E/F}`. It starts from
  Brauer induction for `W_{E/F}` (hypothesis `hgen`) rather than from Tate's reduction to
  primitive representations. It uses the same decomposition with `ρ_E` a character, and
  treats the Galois-type term `Ind[1] - [E:F][1]` through the finite degree-zero Brauer
  theorem for `Gal(E/F)`.
- The formula `Ind(ρ ⊗ Res χ) = (Ind ρ) ⊗ χ` in the same proof is the published
  `continuousInduce_continuousTwist`, used in `continuousTwist_continuousInduce_eq_along`.
- Example (2.3.5), printed p.12, gives the restriction to a local Weil group of an induced
  representation. In the Library this is the hypothesis `LocalInducedRestriction`, applied
  in `exists_continuousRestrict_decomposition`.

The generic lemmas, the identification of `W_H` with the image of `W_{E/K}` for the fixed
field `K` of `H`, and the continuity of `reciprocityCharacter` are internal bookkeeping that
connect these facts with the published definitions.

## Proof

- `continuousRestrict_characterClass` reduces to `restrict_ofRepresentation`. The restricted
  character line and the line of the composite character are the same representation.
- `continuousInduce_characterClass_eq_along` substitutes the range of `φ` for `S`. It unfolds
  `continuousInduceAlong` as induction from the range after restriction along
  `InductionAlong.rangeInverse`, applies `continuousRestrict_characterClass`, and uses
  `InductionAlong.apply_rangeInverse` to show that `θ ∘ φ ∘ rangeInverse = θ`.
  `continuousTwist_continuousInduce_eq_along` combines this with
  `continuousInduce_continuousTwist` and `continuousTwist_characterClass`.
- `inflate_induce_oneDimensional` is the published
  `ExactGrothendieckGroup.inflate_ofClass_induce` for the projection `W_{E/F} → Gal(E/F)`.
  The projection is surjective (`projection_surjective`) with open kernel
  (`isOpen_ker_projection`, the inverse image of the trivial subgroup). The preimage
  subgroup is `W_S`, and the representation of `W_S` is the character line of
  `galoisCharacter χ`, matched by `ULift.moduleEquiv`. `inflate_one` follows from
  `inflateClass_classOf` and an explicit equivalence of representations.
- `induce_one_sub_mem_span`: in the split virtual representation group of the finite group
  `Q = Gal(E/F)`, put `x = Ind_H [1_H] - [Q : H] · [1_Q]`. By
  `DegreeZeroBrauer.virtualCharacter_induce` and `ind_at_one`, its virtual character at `1`
  is `|H|⁻¹ |Q| - [Q : H] = 0`, using `Subgroup.index_mul_card`. So
  `DegreeZeroBrauer.finiteDegreeZeroBrauer Q` puts `x` in the span of the generators
  `Ind_S([χ] - [χ'])`. Inflation is `ℤ`-linear, so it maps that span into the span of
  `characterDifferenceGenerators`, by `inflate_induce_oneDimensional` on each generator. The
  inflation of `x` is the required class, by `inflate_induce_oneDimensional`, `inflate_one`,
  `galoisCharacter c F E H 1 = 1`, and
  `Subgroup.index_comap_of_surjective` (which gives `[W_{E/F} : W_H] = [Q : H]`).
- `sub_degree_smul_mem_span`: by `hgen`, `x` is in the span of `inducedCharacterGenerators`,
  and the proof is by span induction. The property `x - deg x · [1] ∈ span` is closed under
  `0`, sums and integer multiples, because `deg` is linear. For a generator
  `Ind_{W_H}[θ]`, `degree_induce` and `degree_characterClass` give degree `[W_{E/F} : W_H]`,
  and `Ind_{W_H}[θ] - [W_{E/F} : W_H][1]` is the generator `Ind_{W_H}([θ] - [1])` plus the
  class of `induce_one_sub_mem_span`.
- `continuousReciprocityCharacter`: a homomorphism of topological groups is continuous if it
  is continuous at `1` (`continuous_of_continuousAt_one`). The inclusion `C_E → W_{E/F}` is an
  open embedding (`isOpenEmbedding_inclusion`), so continuity at `1` may be checked on `C_E`.
  There the character is `a ↦ χ(N_{E/F} a)⁻¹`, by `reciprocityCharacter_apply` and
  `transfer_inclusion`, and this is continuous by `continuous_ideleClassNorm`.
- `range_restrictScalarsHom`: an automorphism over `K` fixes `K`, and conversely an element of
  the fixing subgroup is the image of its `fixingSubgroupEquiv` value.
  `range_restrictionInclusion_fixedField` rewrites with `range_restrictionInclusion`,
  `range_restrictScalarsHom` and `IntermediateField.fixingSubgroup_fixedField`.
- `exists_twist_decomposition`: `Submodule.mem_span_set'` writes `x - deg x · [1]` as
  `Σ_i r i · g i` with each `g i = Ind_{W_{H i}}([θ₀ i] - [θ₀' i])` a generator, and `choose`
  selects `H i`, `θ₀ i`, `θ₀' i`. Put `K i` the fixed field of `H i`, and let `θ i`, `θ' i` be
  `θ₀ i`, `θ₀' i` composed with `codRestrictOfRange` of `restrictionInclusion` onto `W_{H i}`.
  For a given `η`, twisting is linear, `η ⊗ [1] = [η]` by `continuousTwist_characterClass`,
  and each `η ⊗ g i` is rewritten by `continuousTwist_continuousInduce_eq_along`, with
  `range_restrictionInclusion_fixedField`.
- `exists_continuousRestrict_decomposition`: `choose` applied to `hloc` gives the maps
  `ιu i u`, their transfer property, and the restriction formula for each `K i`.
  Restriction is linear. `continuousRestrict_characterClass` gives `[η] ↦ [η ∘ ιd]`, each
  induced term is rewritten by the restriction formula, and
  `continuousRestrict_characterClass` is applied once more inside each summand.
