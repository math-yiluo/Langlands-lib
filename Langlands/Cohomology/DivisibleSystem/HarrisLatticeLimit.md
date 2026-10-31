# Harris's lattice as the inverse limit of its reductions

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DivisibleSystem.HarrisLatticeHom`
(`harrisLatticeBasis`, `harrisPermutationIhomSystem`, the instance
`mono_powSMul_harrisLatticeTrivial`),
`Langlands.Cohomology.DivisibleSystem.ReductionLimit` (`reductionCone`,
`nonempty_isLimit_reductionCone_iff`, `isLimitReductionCone`,
`reductionSystemLimitIso`, `ihomReductionSystemLimitIso`),
`Langlands.ClassField.Global.LocalUnitPowers`
(`Langlands.ClassField.Global.isAdicComplete_adicCompletionIntegers`: the
completed valuation ring at a finite place is complete for its maximal ideal)
and Worker 57's `Langlands.Shimura.Coefficients.HarrisReduction`
(`mem_principalPower_smul_top`: `x ∈ (b) ^ k • ⊤` exactly when
`x = b ^ k • y` for some `y`). Through their imports it uses
`reductionTower`, `reductionπ`, `reductionSystem`
(`Langlands.Cohomology.DivisibleSystem.Reduction`), `reductionTowerCompIso`
and `map_reductionπ_reductionCompIso_hom`
(`Langlands.Cohomology.DivisibleSystem.ReductionAdic`),
`actionToRep_additive`, `harrisReductionSystem`, the instance
`mono_powSMul_harrisLatticeAction` and `stableLatticeReductionSystem`
(`Langlands.Cohomology.DivisibleSystem.ReductionLattice`),
`DivisibleSystem.inverseLimit`
(`Langlands.Cohomology.DivisibleSystem.InverseLimit`),
`Langlands.Global.CompletionResidue.adicResidueEquiv_mk`
(`Langlands.Global.CompletionResidueAdic`: the residue of the image of an
integer `x` of `L` in the completion at `l` is the class of `x` modulo `l`),
`NYLL.ValuationTheory.DiscreteValuationField.isAdicComplete_of_moduleFinite`
(a finite module over a Noetherian ring complete for an ideal `I` is
`I`-adically complete), `FinitePlace`, `FiniteCompletion`
(`Langlands.Global.Adelic`), `FinitePlacesAbove`
(`Langlands.Global.AdelicFunctoriality.Norm`), Worker 57's
`Langlands.Shimura.Coefficients.Lattice` (`CoefficientIntegers`,
`StableCoefficientLattice` with `carrier` and its finiteness instance) and
`Langlands.Shimura.Coefficients.HarrisLattice`
(`HarrisCoefficientIntegers`, `harrisLattice`, `harrisLatticeAction`), and
`Induction.permutation`
(`Langlands.Representation.Induction.PermutationModule`). From Mathlib it
uses `IsAdicComplete` with `IsHausdorff.haus'` and `IsPrecomplete.prec'`,
`SModEq.sub_mem`, `SModEq.mono`, `SModEq.trans`, `Submodule.smul_mono_left`,
`Ideal.pow_right_mono`, `Ideal.pow_le_pow_right`, `Ideal.mem_of_liesOver`,
`IsLocalRing.residue_eq_zero_iff`, `Ideal.Quotient.eq_zero_iff_mem`,
`Algebra.charZero_of_charZero`, `IsDiscreteValuationRing.exists_irreducible`,
`IsDiscreteValuationRing.associated_pow_irreducible`,
`IsDiscreteValuationRing.irreducible_iff_uniformizer`,
`Ideal.span_singleton_pow`, `Ideal.span_singleton_eq_span_singleton`,
`Module.Finite.of_basis`, the instance that a finite product of Noetherian
rings is Noetherian, `Cone.postcompose`, `Functor.mapCone`, `Cone.ext`,
`IsLimit.postcomposeHomEquiv`, `IsLimit.ofIsoLimit`, `isLimitOfPreserves`,
`isLimitOfReflects`, `IsLimit.conePointUniqueUpToIso` with
`IsLimit.conePointUniqueUpToIso_hom_comp`, the equivalence
`Rep.ActionToRep`, `Rep.trivial` and `Rep.ihom`.

## Conventions

`ℓ` and `m` are natural numbers. For an object `L` of an abelian category,
the published `reductionTower ℓ L : ℕᵒᵖ ⥤ C` is the inverse system of the
cokernels `L / ℓ ^ m L` of multiplication by `ℓ ^ m`, `reductionπ ℓ L m` is
the projection `L ⟶ L / ℓ ^ m L`, and the published `reductionCone ℓ L` is
the cone over `reductionTower ℓ L` with vertex `L` and legs `reductionπ`.
When multiplication by `ℓ` is a monomorphism on `L`, `reductionSystem ℓ L`
is the `ℓ`-divisible system with this tower and `inverseLimit` of an
`ℓ`-divisible system is the limit of its tower.

For a commutative ring `R`, an ideal `I` and an `R`-module `M`,
`IsAdicComplete I M` is Mathlib's statement that `M` is Hausdorff and
complete for the `I`-adic topology: an element congruent to `0` modulo
`I ^ n • M` for every `n` is `0`, and every sequence `f` with `f m ≡ f n`
modulo `I ^ m • M` for `m ≤ n` has an element `x` with `f n ≡ x` modulo
`I ^ n • M` for all `n`. "`ℓ`-adically complete" means complete for the
ideal `(ℓ) = Ideal.span {(ℓ : R)}`. For an action `M` of a group on an
`R`-module (an object of `Action (ModuleCat R) G`), completeness is stated
for the underlying module `M.V`.

## Adic completeness for comparable ideals (namespace `Langlands.Cohomology.DivisibleSystem`)

`R` is a commutative ring and `M` an `R`-module.

- `isAdicComplete_of_le_of_pow_le hIJ hk h`: if `I ≤ J`, `J ^ k ≤ I` and
  `M` is `J`-adically complete, then `M` is `I`-adically complete. Since
  `I ^ n ≤ J ^ n`, an element of every `I ^ n • M` lies in every
  `J ^ n • M` (Hausdorff), and an `I`-adic Cauchy sequence `f` is `J`-adic
  Cauchy, so it has a `J`-adic limit `x`. As
  `J ^ ((k + 1) n) ≤ (J ^ k) ^ n ≤ I ^ n`, `f ((k + 1) n) ≡ x` modulo
  `I ^ n • M`, and `f n ≡ f ((k + 1) n)` modulo `I ^ n • M` because `f` is
  `I`-adic Cauchy; so `x` is an `I`-adic limit.

## Products over a product of rings

`R i` is a commutative ring and `V i` an `R i`-module for each `i` in an
index type `ι`; `∏ i, V i` is a module over `∏ i, R i` acting componentwise,
and `a` is an element of `∏ i, R i`.

- `smodEq_pi_span_singleton_iff`: `x ≡ y` modulo `(a) ^ n • ⊤` in
  `∏ i, V i` exactly when `x i ≡ y i` modulo `(a i) ^ n • ⊤` for every `i`.
  By `mem_principalPower_smul_top` both sides say that the differences are
  multiples by `a ^ n`, respectively `a i ^ n`, and the multipliers can be
  chosen componentwise.
- `isAdicComplete_pi_span_singleton R V a h`: if every `V i` is complete for
  `(a i)`, then `∏ i, V i` is complete for `(a)`. Both conditions are checked
  componentwise, with limits chosen in each component.
- `isAdicComplete_pi_span_singleton_self R a h`: the case `V = R`: a product
  of rings `R i` complete for `(a i)` is complete for `(a)`.

## The local integer rings

`L : Type u` is a number field, `p` a finite place of `ℚ` (a height-one prime
`p.asIdeal` of the integers of `ℚ`), and `l` a finite place of `L` above `p`
(`l.asIdeal.LiesOver p.asIdeal`). `CoefficientIntegers l`, written `𝒪_l`, is
the valuation ring of the completion `L_l = FiniteCompletion L l`, a complete
discrete valuation ring. The hypothesis `hℓ : (ℓ : 𝓞 ℚ) ∈ p.asIdeal` says
that `p` divides `ℓ`.

- `natCast_mem_maximalIdeal_coefficientIntegers ℓ hℓ l`: `ℓ` lies in the
  maximal ideal of `𝒪_l`. Since `l` lies over `p`, `ℓ` lies in `l.asIdeal`
  (`Ideal.mem_of_liesOver`), so its class modulo `l` is `0`, and by
  `adicResidueEquiv_mk` that class corresponds to the residue of `ℓ` in
  `𝒪_l`.
- `isAdicComplete_coefficientIntegers ℓ hℓ l`: if moreover `ℓ ≠ 0`
  (`[NeZero ℓ]`), `𝒪_l` is `ℓ`-adically complete. As `L_l` has
  characteristic zero (`Algebra.charZero_of_charZero`), `ℓ ≠ 0` in `𝒪_l`; for
  a uniformizer `ϖ`, `ℓ` is associated to `ϖ ^ k` for some `k`
  (`IsDiscreteValuationRing.associated_pow_irreducible`), so with `𝔪` the
  maximal ideal, `(ℓ) ≤ 𝔪` and `𝔪 ^ k = (ϖ ^ k) = (ℓ)`. The published
  completeness of `𝒪_l` for `𝔪` then gives completeness for `(ℓ)` by
  `isAdicComplete_of_le_of_pow_le`.

## Transport of the limit criterion along functors

`C` and `D` are abelian categories and `F : C ⥤ D` is an additive functor
preserving cokernels (`PreservesColimitsOfShape WalkingParallelPair F`), so
that the published `reductionTowerCompIso ℓ F L` identifies the image under
`F` of the tower of `L` with the tower of `F L`, compatibly with the
projections (`map_reductionπ_reductionCompIso_hom`).

- `mapReductionConeIso ℓ F L`: the image under `F` of `reductionCone ℓ L`,
  composed with `reductionTowerCompIso ℓ F L`, is isomorphic to
  `reductionCone ℓ (F L)`, with the identity of `F L` on vertices
  (`Cone.ext`).
- `isLimitReductionConeMap h`: if `F` preserves limits of shape `ℕᵒᵖ` and
  `reductionCone ℓ L` is a limit cone (`h`), so is `reductionCone ℓ (F L)`:
  `F` sends `h` to a limit cone (`isLimitOfPreserves`), which stays a limit
  after composing with an isomorphism of diagrams
  (`IsLimit.postcomposeHomEquiv`) and is transported along
  `mapReductionConeIso` (`IsLimit.ofIsoLimit`).
- `isLimitReductionConeOfMap h`: conversely, if `F` reflects limits of shape
  `ℕᵒᵖ` and `reductionCone ℓ (F L)` is a limit cone, so is
  `reductionCone ℓ L` (`isLimitOfReflects`).

## Actions of a group on modules

`R : Type u` is a commutative ring, `G : Type v` a group, and `M` an object
of `Action (ModuleCat.{w} R) G`. Mathlib's `Rep.ActionToRep R G` is an
equivalence of categories from these actions to `Rep R G`; it is additive
(the published `actionToRep_additive`) and, being an equivalence, preserves
cokernels and preserves and reflects limits. The underlying module of
`(Rep.ActionToRep R G).obj M` is `M.V`.

- `nonempty_isLimit_reductionCone_action_iff ℓ M`: `reductionCone ℓ M` is a
  limit cone exactly when `M.V` is `ℓ`-adically complete. This is the
  published `nonempty_isLimit_reductionCone_iff` for
  `(Rep.ActionToRep R G).obj M`, transported by `isLimitReductionConeMap` and
  `isLimitReductionConeOfMap`.

Below `M.V` is `ℓ`-adically complete (hypothesis `hM`).

- `isLimitReductionConeAction hM`: the limit cone structure on
  `reductionCone ℓ M`, transported from the published `isLimitReductionCone`.
- `reductionLimitIsoAction ℓ hM : limit (reductionTower ℓ M) ≅ M` is the
  comparison of the chosen limit with this limit cone
  (`IsLimit.conePointUniqueUpToIso`);
  `reductionLimitIsoAction_hom_reductionπ`: its composite with
  `reductionπ ℓ M m` is the limit projection at `m`.
- `reductionSystemLimitIsoAction ℓ hM : inverseLimit (reductionSystem ℓ M) ≅ M`
  is `reductionLimitIsoAction` for the published reduction system, when
  multiplication by `ℓ` is a monomorphism on `M`.

## Harris's coefficient ring and lattice

Here `ℓ` is nonzero (`[NeZero ℓ]`) and `p` divides `ℓ` (hypothesis `hℓ`).
`HarrisCoefficientIntegers L p`, written `R`, is Worker 57's product
`∏_{l | p} 𝒪_l` over the places of `L` above `p`.

- `isAdicComplete_harrisCoefficientIntegers ℓ L hℓ`: `R` is `ℓ`-adically
  complete: `isAdicComplete_pi_span_singleton_self` with every factor
  complete by `isAdicComplete_coefficientIntegers`. In `R` the element `ℓ`
  is the family of the elements `ℓ` of the factors.

For the remaining sections, `A` is a finite-dimensional `ℚ`-algebra with
Worker 13's involution `σ : AlgebraInvolution ℚ A`, `W : Type u` an
`L`-module and `ρ` an algebraic representation of `σ.baseChange L` on `W`, as
in the published `HarrisLattice`. With `W` finite over `L` and a compact open
level `U` of `σ.FiniteAdelicPoints`, Worker 57's `harrisLattice ρ p U`,
written `𝓛`, is an `R`-lattice in `(L ⊗_ℚ ℚ_p) ⊗_L W`, and the published
`harrisLatticeAction ρ p U` is the action of `U.subgroup` on it.

- `isAdicComplete_harrisLattice ℓ ρ U hℓ`: `𝓛` is `ℓ`-adically complete over
  `R`. `R` is Noetherian (a finite product of discrete valuation rings) and
  `ℓ`-adically complete, and `𝓛` is finite over `R`, having the published
  basis `harrisLatticeBasis` (`Module.Finite.of_basis`); the claim is the
  published NYLL theorem `isAdicComplete_of_moduleFinite`.
- `harrisReductionSystemLimitIso ℓ ρ U hℓ` (the entry declaration):
  `inverseLimit (harrisReductionSystem ℓ ρ p U) ≅ harrisLatticeAction ρ p U`,
  that is, `𝓛` is the inverse limit of `{𝓛 / ℓ ^ m 𝓛}` as a representation of
  the level `U`. This is `reductionSystemLimitIsoAction` with
  `isAdicComplete_harrisLattice`.

Let `G : Type u` be a group, `X : Type u` a `G`-set and `M : Type u` a finite
free `R`-module.

- `harrisLatticeTrivialReductionSystemLimitIso ℓ ρ U hℓ G`: for `𝓛` with the
  trivial action of `G` (`Rep.trivial R G 𝓛`), the inverse limit of its
  reduction system is isomorphic to it, by the published
  `reductionSystemLimitIso`.
- `harrisPermutationIhomSystemLimitIso ℓ ρ U hℓ G X M`: the inverse limit of
  the published `harrisPermutationIhomSystem ℓ ρ p U G X M`, with levels
  `Hom_R(M[X], 𝓛 / ℓ ^ m 𝓛)`, is isomorphic to `Hom_R(M[X], 𝓛)`, that is
  `(Rep.ihom (Rep.of (Induction.permutation R G X M))).obj (Rep.trivial R G 𝓛)`,
  by the published `ihomReductionSystemLimitIso`. Here `M[X] = X →₀ M` with
  `G` permuting the points of `X`, and `Hom_R` is Mathlib's internal Hom of
  representations.

## One place of the coefficient field

Here `l` is a finite place of `L` above `p`, `U` a subgroup of
`σ.FiniteAdelicPoints`, and `Λ` is Worker 57's
`StableCoefficientLattice ρ p l U`: a full lattice `Λ.carrier` over `𝒪_l` in
`L_l ⊗_L W`, stable under `U`, with action `Λ.action`.

- `isAdicComplete_stableCoefficientLattice ℓ hℓ Λ`: `Λ.carrier` is
  `ℓ`-adically complete over `𝒪_l`, by `isAdicComplete_of_moduleFinite`
  (`𝒪_l` is a discrete valuation ring, hence Noetherian, and `Λ.carrier` is
  finite over it by the published instance).
- `stableLatticeReductionSystemLimitIso ℓ hℓ Λ`:
  `inverseLimit (stableLatticeReductionSystem ℓ Λ) ≅ Λ.action`, by
  `reductionSystemLimitIsoAction`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999) (Worker 61 read the rendered scanned pages):

- §3, printed p.306 (one-based PDF page 8): "`L_v = L ⊗_ℚ ℚ_v`" for a place
  `v` of `ℚ`, so `L_ℓ` is in general a finite product of finite extensions of
  `ℚ_ℓ`.
- §3, printed p.307 (one-based PDF page 9): "Let `𝒪` denote the ring of
  integers of `L_ℓ`, and let `𝓛_W` be a `K_ℓ`-stable `𝒪`-lattice in
  `W(L)`."
- §4, printed p.311 (one-based PDF page 13): "Now we want to let `m` vary.
  Let the `K_ℓ`-modules `(ρ, W)` and `𝓛 = 𝓛_W` be as in §3; let
  `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m` for any `m`. Then `𝓛_m` forms an inverse system of
  `𝒪`-modules, and the inverse system `{𝓛̃_m}` defines a lisse `ℓ`-adic sheaf
  `W̃ = lim 𝓛̃_m ⊗_𝒪 L_ℓ` on `S̄_K(N)`."
- proof of Proposition 4.10, printed p.312 (one-based PDF page 14): "In fact,
  we have proved the stronger (integral) statement (4.10.4)
  `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̆_N, 𝒪(n − 1)), 𝒜_ℓ(GJ, 𝓛, H)) ⇒ H^{i+j}(S̄_K(N), 𝓛̃)`."

Harris passes from coefficients `𝓛_m` to coefficients `𝓛` by taking limits
over `m`; he does not state that `𝓛` is the inverse limit of the `𝓛_m`. The
published ReductionLimit module proves, for representations, that a module
is the inverse limit of its reductions exactly when it is `ℓ`-adically
complete, and it took the completeness of Harris's `𝒪` (read as the integral
closure of `ℤ_ℓ` in `L_ℓ`, a finite product of complete discrete valuation
rings) as a hypothesis. This module proves that completeness for the
published model `HarrisCoefficientIntegers L p = ∏_{l | p} 𝒪_l` of `𝒪`, and
the completeness of the published lattice `harrisLattice`, and so obtains,
without completeness hypotheses, `𝓛 ≅ lim 𝓛 / ℓ ^ m 𝓛` as representations of
the level and `Hom_R(M[X], 𝓛) ≅ lim Hom_R(M[X], 𝓛 / ℓ ^ m 𝓛)` for Harris's
permutation modules. With `𝒪_m` read as `𝒪/ℓ^m𝒪`, so that `𝓛_m = 𝓛/ℓ^m𝓛`
(published ReductionLattice and ReductionAdic), and `U` in the role of
`K_ℓ`, `harrisReductionSystemLimitIso` is our reading of the passage to the
limit for the lattice itself, and `harrisPermutationIhomSystemLimitIso` for
the coefficients `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` of (4.8), as in the published
ReductionLimit and HarrisLatticeHom modules.

In Harris `ℓ` is a rational prime and the coefficient place is the place `ℓ`
of `ℚ`. Here `ℓ` is any nonzero natural number and `p` any finite place of
`ℚ` dividing `ℓ`; for `ℓ` prime this forces `p` to be the place `ℓ`. The
hypothesis cannot be dropped: if `p` does not divide `ℓ`, then `ℓ` is a unit
in every `𝒪_l`, every reduction `𝓛 / ℓ ^ m 𝓛` is zero, and a nonzero lattice
is not their limit (a remark, not formalized). The statements and all proofs
are ours; the completeness of `𝒪_l` for its maximal ideal and of finite
modules over complete Noetherian rings are published theorems. The module is
derived.

## Scope

The module proves completeness and limit statements for the published
lattices; it does not construct Harris's sheaves `𝓛̃_m`, `𝓛̃` or `W̃`, the
spectral sequences (4.9), (4.10.4), or the identifications (4.7), (4.8), and
it does not prove that limits over `m` commute with cohomology. The Lean
levels of `harrisPermutationIhomSystem` are `R`-linear maps
`Hom_R(M[X], 𝓛 / ℓ ^ m 𝓛)`; their identification with Harris's
`𝒪_m`-linear maps out of `𝒪_m[C_p/H_p]^M` is not formalized. The group `G`
acts trivially on `𝓛` in the Hom statements, and the data `G`, `X`, `M` are
in the universe `u` of the coefficient data. Everything concerns categories
of actions and representations of abstract groups, not smooth
representations.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
