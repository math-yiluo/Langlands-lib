# Conic decay bounds from the actual relative roots of a parabolic

Lean module: `Langlands.Representation.Plancherel.ParabolicRootCone`,
namespace `Langlands.Plancherel`.

## Purpose and provenance

Provenance: internal. This module applies the abstract conic bound
`Langlands.LinearAlgebra.RootFaceCone.exists_pos_rootCone_decay` to the relative roots of the
split component `A` of a parabolic presentation. The result is one host theorem,
`exists_parabolicRootCone_decay`, for the convergence step of the standard intertwining
integrals (Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra* (2003), IV.1.1, printed pp. 278–280). Waldspurger proves convergence by a
gallery induction, so the theorem is not transcribed from a source. It is the combinatorial
step that turns lower bounds of a functional `H` at the positive-weight characters of
admissible cocharacters into decay in the root values of `ν`.

The interface (cocharacters `λ, λ'`, the admissibility and region conditions, and the root
sum) was agreed with the consumer of the theorem, which assembles
`ParabolicCharacterDecayInput`. The three inputs of the abstract lemma are proved here for
the actual groups:

- Levi orthogonality, first on a maximal split torus from relative reflections, then on `A` by
  restriction;
- orthogonality of the relative roots of `A` to the restricted rational characters of `G`,
  together with the real spanning property;
- integral realization of the sign pattern of a real character by a cocharacter.

## Setting and notation

- `k` is a field and `G` an affine group scheme over `Spec k`. `A` is a split torus, with
  `a : A.toGrp ⟶ M`, `l : M ⟶ P` and `p : P ⟶ G`, and
  `r : ParabolicRootPresentation p l a`. The presentation supplies a maximal split torus
  `r.data.i : r.data.T.toGrp ⟶ G` and `r.data.f : A ⟶ r.data.T` with
  `groupHom r.data.f ≫ r.data.i = a ≫ l ≫ p` (`r.isCompatible.factor_comp`).
- `Vstar T = ℝ ⊗[ℤ] characterLattice T`. A character `α` gives `1 ⊗ α : Vstar T`.
- `B = weylInducedCharacterForm hA hT r.data.f r.data.i` is the form on `Vstar A` induced from
  the relative-Weyl-invariant form of `r.data.T`. It is symmetric and positive definite, and
  it is compatible with the lift `weylCharacterRestrictionLift`.
- `relativeRoots (a ≫ l ≫ p)` are the relative roots of `A`. The multiplicity of `α` is
  `finrank k (weightSpace (a ≫ l ≫ p) α)`.
- `latticePairing A α μ ∈ ℤ` is the pairing of a character with a cocharacter of `A`.
- `positiveWeightCharacter (a ≫ l ≫ p) μ = ∑_{⟨α, μ⟩ > 0} (dim 𝔤_α) • α` is defined in
  `Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityReduction`.
- `RelativeRootSystemStatement` is the open relative-root-system statement. It is a premise
  wherever it is used; this module does not prove it.

## Declarations

Definition:

- `relativeRootAbsSum i B ν = ∑ᶠ α ∈ relativeRoots i, |B ν (1 ⊗ α)|` (an `abbrev`).
- `relativeRootAbsSum_eq_sum`: for a finset `R` with `α ∈ R ↔ α ∈ relativeRoots i`, it equals
  `∑ α ∈ R, |B ν (1 ⊗ α)|`.

Maximal split torus (`i : T.toGrp ⟶ G`, `[Mono i.hom.hom.left]`):

- `one_tmul_character_injective` (`hT`): `χ ↦ 1 ⊗ χ` is injective on the characters of a split
  torus.
- `IsRelativeReflection.exists_fullRatAction_eq_add`,
  `IsRelativeReflection.exists_realAction_eq_add`: let `w` be a relative reflection in `β`, and
  assume the relative roots and the restricted characters span (`hspan`). Then `w` moves every
  rational, respectively real, character along `β`.
- `IsRelativeReflection.realReflectionData` (`[Fintype (relativeWeylGroup i)]`, `hT`,
  `hspan`): the real action of a relative reflection `w` in `β` is an isometry of
  `relativeWeylInvariantForm`. It negates `1 ⊗ β`, moves vectors along `1 ⊗ β`, acts on
  `1 ⊗ χ` through the lattice action, and maps relative roots to relative roots. It also
  preserves weight-space dimensions and fixes the restricted rational characters of `G`.
- `relativeWeylInvariantForm_rootWeight_levi` (`HasRelativeRootSystem i`, `hspan`, a finset
  `RT` of exactly the relative roots): for all `z` and `χ ∈ RT` with `B_T(1 ⊗ χ, z) = 0`,
  `1 ⊗ χ` is orthogonal to `∑_{χ' ∈ RT, B_T(1 ⊗ χ', z) > 0} (dim 𝔤_χ') • (1 ⊗ χ')`.
- `relativeWeylInvariantForm_root_character`: relative roots are `B_T`-orthogonal to the
  restricted rational characters of `G`.
- `realSpan_relativeRoots_sup_characters` (`IsConnectedReductive G`, `IsMaximalSplitTorus i`):
  every `x : Vstar T` lies in the real span of the relative roots plus the real span of the
  restricted rational characters.
- `finrank_biSup_eq_sum`, imported from
  [SubmoduleFinrank](../../LinearAlgebra/SubmoduleFinrank.md): dimensions add over a
  finite supremum of independent subspaces.
- `finrank_weightSpace_comp_eq_sum`: for `f : T' ⟶ T` of split tori and `ψ ≠ 0`, the dimension
  of the `ψ`-weight space of `groupHom f ≫ i` is the sum of the dimensions of the
  `χ`-weight spaces of `i` with `f ≫ χ = ψ`.

Split component (`r` as above):

- `parabolic_restrictReal_tmul`, `parabolic_restrictReal_character`: real restriction along
  `r.data.f` is composition on characters, and it maps restricted characters of `G` along
  `r.data.i` to restricted characters along `a ≫ l ≫ p`.
- `parabolic_mem_relativeRoots_iff` (`hA`, `hT`): `α` is a relative root of `A` if and only if
  `α ≠ 0` and `α = r.data.f ≫ χ` for a relative root `χ` of `r.data.T`.
- `parabolic_neg_mem_relativeRoots` (`HasRelativeRootSystem r.data.i`): the relative roots of
  `A` are closed under negation.
- `parabolic_finrank_weightSpace_eq_sum`: the multiplicity of a nonzero `α` is the sum of the
  multiplicities of the relative roots of `r.data.T` restricting to `α`.
- `finrank_weightSpace_pos`: a relative root has a nonzero weight space.
- `parabolic_mem_span_of_restrictReal_eq_zero`: a real character of `r.data.T` restricting to
  `0` on `A` is a real combination of relative roots restricting to `0`. The proof uses the
  published kernel identification `IsSplitComponent.restriction_kernels_eq_relativeRootSpans`
  on the Levi.
- `parabolic_rootWeight_levi` (`[Mono r.data.i.hom.hom.left]`,
  `[Mono (groupHom r.data.f).hom.hom.left]`, `[Fintype (relativeWeylGroup r.data.i)]`, `hA`,
  `hT`, `HasRelativeRootSystem r.data.i`, `hspan`, a finset `RA` of exactly the relative roots
  of `A`): Levi orthogonality for `B` on `A`. If `B(1 ⊗ α, y) = 0` with `α ∈ RA`, then
  `1 ⊗ α` is `B`-orthogonal to
  `∑_{α' ∈ RA, B(1 ⊗ α', y) > 0} (dim 𝔤_α') • (1 ⊗ α')`.
- `parabolic_root_orthogonal_character`: `B(1 ⊗ α, 1 ⊗ (restriction of ξ)) = 0` for every
  relative root `α` of `A` and every rational character `ξ` of `G`.
- `parabolic_realSpan_relativeRoots_sup_characters` (`IsConnectedReductive G`): every
  `x : Vstar A` lies in the real span of the relative roots of `A` plus the real span of the
  restricted rational characters of `G`.

Realization:

- `exists_cocharacter_sign_realization` (`hT`): for any bilinear form `B` on `Vstar T`, finset
  `R` and `y : Vstar T`, some cocharacter `μ` satisfies
  `0 < ⟨α, μ⟩ ↔ 0 < B(1 ⊗ α, y)` for every `α ∈ R`.
- `one_tmul_positiveWeightCharacter`: for a finset `R` of exactly the relative roots,
  `1 ⊗ positiveWeightCharacter i μ = ∑_{α ∈ R, ⟨α, μ⟩ > 0} (dim 𝔤_α) • (1 ⊗ α)`.

Host:

- `parabolic_neg_mem_relativeRoots_of_statement` (`RelativeRootSystemStatement`,
  `IsConnectedReductive G`): the relative roots of `a ≫ l ≫ p` are closed under negation.
- `exists_parabolicRootCone_decay` (the instance arguments of `parabolic_rootWeight_levi`,
  `hA`, `hT`, `RelativeRootSystemStatement`, `IsConnectedReductive G`). Let
  `λ, λ' : cocharacterLattice A`, `c : cocharacterLattice A → ℝ`, `ψ : Vstar A` and `s : ℝ`.
  Call `μ` *admissible* when `0 ≤ ⟨α, μ⟩` for every relative root `α` with `⟨α, λ⟩ < 0` and
  `0 < ⟨α, λ'⟩`. Then there are `R, K : ℝ` such that the following holds for every real
  linear `H : Vstar A → ℝ` that satisfies
  - `-c μ ≤ H(1 ⊗ positiveWeightCharacter (a ≫ l ≫ p) μ)` for every admissible `μ`, and
  - `H(1 ⊗ characterRestrict (a ≫ l ≫ p) ξ) = 0` for every rational character `ξ` of `G`.

  For every `ν : Vstar A` with `R < B(ν, 1 ⊗ α)` for each relative root `α` with
  `⟨α, λ⟩ > 0` and `⟨α, λ'⟩ < 0`,
  `H ν ≤ -s |H ψ| + K (1 + relativeRootAbsSum (a ≫ l ≫ p) B ν)`.

Intended reading: the roots with `⟨α, λ⟩ > 0 > ⟨α, λ'⟩` are those of `U ∩ Ū'`. Admissible
`μ` are those whose parabolic `P(μ)` contains `Ū ∩ U'`, and the lower bound at
`positiveWeightCharacter μ` is the Iwasawa bound for the corresponding adjoint line. The
module states only the implication above; it does not construct these bounds.

## Proofs as implemented

**Reflections on the maximal split torus.** A relative reflection acts on the rational span of
the roots as `Module.reflection`, and it fixes restricted characters
(`relativeWeylFullRatAction_restrictionRange`). Since these together span everything
(`hspan`), it moves every vector along `β`. The real statement follows by induction on pure
tensors. Invariance of the form, `w β = -β`, preservation of roots and weight-space dimensions
(`finrank_weightSpace_weylAction`), and fixing of restricted characters are published facts.
`HasRelativeRootSystem.exists_isRelativeReflection` supplies a reflection for every root, so
`rootWeight_levi_of_reflections` and `apply_eq_zero_of_isometry_fixed` from
`RootFaceReflection` give the two torus-level orthogonality results.

**Spanning.** `relativeRootsRestrictedCharactersSpan` gives the rational statement. It is
transported to `ℝ` with `toReal_mem_span_iff` and extended to all tensors by induction.

**Multiplicities.** `weightSpace_comp_eq_iSup` writes the weight space of `A` as a supremum of
weight spaces of `r.data.T`. Indices with zero weight space drop out, and the remaining indices
are relative roots in `RT`. The weight spaces are independent
(`isInternal_weightSpace_of_isSplitTorus`), so dimensions add (`finrank_biSup_eq_sum`, proved
by finset induction with `Submodule.finrank_sup_add_finrank_inf_eq`).

**Kernel of restriction.** The Levi factor `j` of `r.data.i` through `l ≫ p` exists by
`parabolic_exists_torusLeviFactor`. `restriction_kernels_eq_relativeRootSpans` identifies
`ker q` with the real span of the relative roots of `j`, and these are relative roots of
`r.data.i` restricting to zero.

**Levi orthogonality on `A`.** Apply `indexedRootWeight_levi_descent` with
`BT = relativeWeylInvariantForm`, `BA = B`, `q` real restriction along `r.data.f`, and
`L = weylCharacterRestrictionLift`. Compatibility of the forms is
`weylInducedCharacterForm_compatible`. The hypotheses are the root restriction criterion, the
additivity of multiplicities, the kernel lemma and the torus-level Levi orthogonality. The
character orthogonality uses `restrict_orthogonal_roots` in the same way. The real spanning on
`A` is the image of the spanning on `r.data.T` under `q`, using `q ∘ L = id`.

**Realization.** The real character space of a split torus is perfectly paired with the real
cocharacter space (`isPerfPair_of_isSplitTorus`). So `B(·, y)` is evaluation at a real
cocharacter, and `exists_int_sign_realization` gives an integral `μ` with the same positive
roots. `one_tmul_positiveWeightCharacter` rewrites the defining `finsum` as a finset sum over
`R`.

**Host theorem.** Put `RA` for the finset of relative roots of `A`, `Φ = RA.image (1 ⊗ ·)`,
`m` the multiplicities, and `S` the image of the roots with `⟨α, λ⟩ > 0 > ⟨α, λ'⟩`. The
hypotheses of `exists_pos_rootCone_decay` are positivity of `B`, `Φ = -Φ` (from
`RelativeRootSystemStatement`), positive multiplicities and Levi orthogonality, which
`rootWeight_image_eq` matches with `parabolic_rootWeight_levi`. The lemma gives `ε > 0` and
`L ≥ 0`.

- *Uniform lower bound.* For each subset `U ⊆ RA` that is the positive set of some admissible
  cocharacter, choose one such cocharacter `μ_U` (and `μ_U = 0` otherwise), and put `c₀ = ∑_{U ⊆ RA} |c(μ_U)|`. Let `y`
  be a fixed point of the root weight with `B(x, y) ≤ 0` for `x ∈ S`, and realize its sign
  pattern by `μ`. Then `μ` is admissible: if `⟨α, λ⟩ < 0 < ⟨α, λ'⟩`, then `-α` lies in the
  set defining `S`, so `B(1 ⊗ (-α), y) ≤ 0` and hence `⟨-α, μ⟩ ≤ 0`. Also `μ_U` for
  `U = pos(μ)` is admissible with the same positive set. Hence
  `1 ⊗ positiveWeightCharacter μ_U = ρ(y) = y` and `H y ≥ -c(μ_U) ≥ -c₀`.
- *Decomposition.* Write `ψ = ψ_Φ + ψ_G` and `ν = ν_Φ + ν_G` with root parts in the span of
  `Φ` and character parts in the span of restricted characters. `H` and every `B(x, ·)`
  with `x ∈ Φ` vanish on the character parts. Write `ψ_Φ = ∑ t_x x`, put
  `T₀ = ∑ |t_x|` and `s' = max(s, 0) T₀`, and choose `β ∈ Φ` maximizing `|H x|`. Then
  `s |H ψ| ≤ s' |H β|`.
- *Conclusion.* Take `R = s' L` and `K = (c₀/ε)(1 + s' L)`. The region hypothesis gives
  `B(x, ν_Φ) ≥ s' L` on `S`, so the decay lemma yields
  `H ν_Φ + s' |H β| ≤ (c₀/ε)(∑_{x ∈ Φ} |B(x, ν_Φ)| + s' L)`. Moreover
  `∑_{x ∈ Φ} |B(x, ν_Φ)| = relativeRootAbsSum` by symmetry and injectivity of `1 ⊗ ·`, and
  `H ν = H ν_Φ`. If `Φ` is empty, `ν_Φ = 0` and the bound is immediate.

## Scope

The module proves the conic decay implication for the actual relative roots of the split
component of a parabolic presentation, under `RelativeRootSystemStatement`. It does not
construct the adjoint lines or prove the Iwasawa lower bounds for `H`, and it does not compare
`H` with the height of a group element. It does not prove `ParabolicCharacterDecayInput` or the
conditional standard intertwining theorem.
