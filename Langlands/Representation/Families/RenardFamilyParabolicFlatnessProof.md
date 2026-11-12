# Renard VI.8.2–VI.8.3: proofs of flatness of induction and Jacquet modules and of admissibility of induction

Author: Worker 68. Module
`Langlands.Representation.Families.RenardFamilyParabolicFlatnessProof`, namespace
`Langlands.Renard.AlgebraicFamily`. It proves the four unchanged published
propositions of
[RenardFamilyParabolicFlatnessStatements](RenardFamilyParabolicFlatnessStatements.md),
each by a theorem whose type is exactly that proposition at its published universe
parameters:

| Theorem | Type | Universe parameters |
| --- | --- | --- |
| `inductionFlat` | `InductionFlatStatement.{u', uB', uE'}` | `u', uB', uE'` |
| `inductionAdmissible` | `InductionAdmissibleStatement.{u', uB', uE'}` | `u', uB', uE'` |
| `jacquetFlat` | `JacquetFlatStatement.{u', uB', uV'}` | `u', uB', uV'` |
| `parabolicFlatness` | `ParabolicFlatnessStatements.{u', uB', uE', uV'}` | `u', uB', uE', uV'` |

`parabolicFlatness` is the triple `⟨inductionFlat, inductionAdmissible, jacquetFlat⟩`.
The statement module, the functors module
[RenardFamilyParabolicFunctors](RenardFamilyParabolicFunctors.md) and their imports
are unchanged. The proofs add no hypothesis and no axiom. Every quantified field,
group, parabolic (including `P = G`) and coefficient ring of the statements is
covered. The development checks report only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, literature ID `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`:
VI.8.2, the opening paragraph with (VI.8.2.1) and the Lemma, printed pp. 189–190 /
PDF pp. 195–196; VI.8.3, the opening paragraph, printed p. 191 / PDF p. 197.
Worker 68 read PDF pp. 195–197. The statement Markdown records the source
correspondence of the targets. The proof routes below follow the source for
induction. For the Jacquet module they use a different but elementary argument,
explained in its section.

## Compactness of `P(F) \ G(F)`

Both induction theorems need `CompactSpace (Induction.LeftQuotient (pointImage p))`,
the source's compactness of `P\G` (V.5.1 Corollary). The proofs neither assume nor
add it. They obtain it from published theorems, as
`compactSpace_leftQuotient_pointImage_of_dynamic parabolicDynamic
BruhatTits.dynamicParabolicQuotientCompact hG p hp`. Here
`Langlands.Aubert.General.RepresentedParabolic.compactSpace_leftQuotient_pointImage_of_dynamic`
is a published helper. It derives this exact quotient compactness from
`GroupScheme.ParabolicDynamicStatement` and
`BruhatTits.DynamicParabolicQuotientCompactStatement`, and the published theorems
`Langlands.GroupScheme.parabolicDynamic` (Milne 25.1) and
`Langlands.BruhatTits.dynamicParabolicQuotientCompact` prove those two
statements. The proof candidate `9528020c-5777-4963-8966-e4d5818f35b1` of task
`c1ce4629-6768-4eb5-b4ee-0086526913ea` makes the same composition for
`ArbitraryParabolicQuotientCompactStatement`. This module does not depend on that
candidate.

## General lemmas

These lemmas work over any commutative `ℂ`-algebra `B`. Only the admissibility
lemma uses that `B` is Noetherian. None uses that `B` is of finite type or
reduced.

**`flat_fixedVectors`.** For a smooth `ρ : Representation B G V` of a topological
group on a flat `B`-module and a compact open `K`, `fixedVectors ρ K` is flat. The
published `coefficientFixedProjection ρ hρ K hK` (compact averaging, from
[RenardFamilyFixedTensorProof](RenardFamilyFixedTensorProof.md)) is a `B`-linear
retraction of the inclusion, by `coefficientFixedProjection_comp`. So
`Module.Flat.of_retract` applies.

**`coefficientAverage_apply_rho`.** The published `coefficientAverage ρ hρ K hK`
satisfies `coefficientAverage (ρ x v) = coefficientAverage v` for `x ∈ K`. It is
the orbit mean of the underlying complex representation, so the published
`Compact.CharZero.orbitMean_apply` gives this.

**`exists_compact_mem_relations`.** Let `U` satisfy `IsLimitOfCompactSubgroups U`.
If `v` lies in the relation submodule `relations ρ U 1`, the span of the
`ρ u w - w`, then `v ∈ relations (ρ.comp U.subtype) K 1` for some compact subgroup
`K` of `U`. The proof works over any ring. It is the argument of the published
complex lemma `Jacquet.Localization.mem_relations_iff_compact`: `v` is a
combination of finitely many generators, and their finitely many elements of `U`
lie in one compact subgroup.

**`flat_coinvariants`** (the Jacquet step). For a topological group `G`, a smooth
`ρ : Representation B G V` on a flat `B`-module and `U` with
`IsLimitOfCompactSubgroups U`, the coinvariants `Jacquet.Localization.Coinvariants ρ U 1`
are flat. The proof uses the equational criterion
`Module.Flat.of_forall_isTrivialRelation`. Suppose `∑ fᵢ xᵢ = 0` in the
coinvariants. Lift `xᵢ = mk vᵢ`. Then `∑ fᵢ vᵢ ∈ relations ρ U 1`, so by
`exists_compact_mem_relations` it is a relation of a compact subgroup `K ≤ U`.
Let `ρK` be the restriction of `ρ` to `K`. It is smooth, by the published
`isSmooth_comp`, and `⊤ : OpenSubgroup K` is compact. Let
`e = coefficientFixedProjection ρK _ ⊤ _ : V → V^K`.

- `e` vanishes on the relations of `K`, by `relations_le_ker_iff` and
  `coefficientAverage_apply_rho`. Hence `∑ fᵢ e(vᵢ) = 0` in `V^K`.
- `mk (e w) = mk w` for every `w`. This follows from the published
  `coefficientAverage_natural`, applied to the intertwiner `mk` from `ρK` to the
  trivial representation on the coinvariants, and from `coefficientAverage_fixed`
  for that trivial representation.

`V^K` is flat by `flat_fixedVectors`. By
`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero` there are `y_j ∈ V^K` and
`a_{ij}` with `e(vᵢ) = ∑_j a_{ij} y_j` and `∑ᵢ fᵢ a_{ij} = 0`. Applying `mk` gives
`xᵢ = mk vᵢ = mk (e vᵢ) = ∑_j a_{ij} mk y_j`, which is a trivial relation.

**`isSmooth_inducingRepresentation`.** For a semidirect decomposition
`h : IsSemidirectDecomposition P M U` with `U` closed and continuous
`h.projection`, the inducing representation `inducingRepresentation h hU σ` of a
smooth `σ` is smooth. It is the twist by the smooth character
`inductionCharacter` (`isSmooth_twist_iff`), pulled back along `h.projection`
(`isSmooth_comp`).

**`flat_induced`.** Assume compact `P \ G`, `P` closed, continuous `h.projection`,
smooth `σ` and flat `V`. Then `Induced h hU σ` is flat. By the published
`Plancherel.RationalNormalized.flat_of_smooth_fixed_flat` (the VI.8.1 Remark), it
suffices that each compact-open fixed module of `inducedRepresentation h hU σ` is
flat. Fix compact open `K`. The published
`Induction.exists_finset_doubleCoset_representatives` gives a finite transversal
`t` of `P \ G / K`. The published `Induction.fixedEvaluationEquiv` identifies the
`K`-fixed vectors with the finite product over `i ∈ t` of the fixed vectors of
`inducingRepresentation h hU σ` under `Induction.conjOpenSubgroup P K i`, that is
under `P ∩ i K i⁻¹`. This is (VI.8.2.1). Each factor is flat by
`flat_fixedVectors`: the subgroup is compact by
`Induction.isCompact_conjOpenSubgroup`, and the inducing representation is
smooth. The finite product is flat through `DFinsupp.linearEquivFunOnFintype` and
`Module.Flat.dfinsupp`.

**`exists_inducing_fixedVectors_le`.** Let `M` be closed and let `Q` be a compact
open subgroup of `P`. Then there is a compact open subgroup `N` of `M` with
`fixedVectors (inducingRepresentation h hU σ) Q ≤ fixedVectors σ N`. Take for `N`
the elements `n ∈ M` with `n ∈ Q` and `inductionCharacter n = 1`. It is open,
since the character has open kernel. It is compact: the elements of `M` lying in
`Q` are the preimage of the compact image of `Q` in `G` under the closed embedding
`M → G`, and the kernel is closed. For `n ∈ N` the inducing action is
`inductionCharacter (h.projection n) • σ (h.projection n) = σ n`, by
`h.projection_levi`. So `Q`-fixed vectors are `N`-fixed. This `N` lies in the
source's `K_M^g`, the projection of `P ∩ gKg⁻¹`. The proof needs only this
inclusion, not the source's equality.

**`finite_fixedVectors_induced`.** Assume `B` Noetherian, `P \ G` compact, `P` and
`M` closed, and `fixedVectors σ N` finitely generated for every compact open `N`
of `M`. Then every compact-open fixed module of `inducedRepresentation h hU σ` is
finitely generated. A finite double-coset cover from
`Induction.exists_finset_doubleCoset_cover` makes the published evaluation map
`Induction.fixedEvaluation` injective (`Induction.fixedEvaluation_injective`),
into a finite product of the fixed modules under the `P ∩ i K i⁻¹`. Each factor
is a submodule of some finitely generated `fixedVectors σ N`, by
`exists_inducing_fixedVectors_le`, so it is finitely generated over the
Noetherian `B`. Finite generation passes to the product and back along the
injection, by `Module.Finite.of_injective`.

## The four targets

After introducing the binders, each proof installs `hG.isAffineHom` and the
canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, as the
statements do. The induction proofs also install `leviPointTopology l hl`. They
apply the general lemmas to the published data of
[RenardFamilyParabolicFunctors](RenardFamilyParabolicFunctors.md).

- **`inductionFlat`.** `LeviInduced p l r hp hr hl hmul σ` is by definition
  `Induced h hU σ'`. Here `h` is
  `isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul`, `hU`
  is `isClosed_pointImage_comp p r …` and `σ' = leviImageRepresentation p l hp hl σ`.
  `flat_induced` applies with the compactness above. `pointImage p` is closed by
  `isClosed_pointImage`. The projection is continuous by the published
  `continuous_projection_pointImage`. `σ'` is smooth because it is `σ` pulled back
  along the continuous inverse of the published topological isomorphism
  `leviPointsEquiv p l hp hl`.
- **`inductionAdmissible`.** `finite_fixedVectors_induced` applies to the same
  data, with `isClosed_leviPoints` for the Levi image. A compact open `N` of
  `pointImage (l ≫ p)` corresponds to the compact open
  `N' = N.comap (leviPointsEquiv p l hp hl)` of `M(F)`. It is compact because
  `leviPointsEquiv` is a homeomorphism. The submodules `fixedVectors σ' N` and
  `fixedVectors σ N'` of `E` are equal, so the statement's hypothesis on `σ`
  applies. The hypothesis `Module.Flat B E` of the statement is not used here.
- **`jacquetFlat`.** `Jacquet ρ (pointImage (r ≫ p))` is by definition
  `Coinvariants ρ (pointImage (r ≫ p)) 1`. `flat_coinvariants` applies, and the
  published `isLimitOfCompactSubgroups_pointImage_radical p r hp.isClosedSubgroup hr.1`
  supplies its hypothesis. No Levi is used, matching the statement.
- **`parabolicFlatness`.** This is the conjunction of the three.

## Comparison with the source

- Induction (VI.8.2): as in the source, flatness reduces to the compact-open fixed
  modules (Remark VI.8.1), and these are described by (VI.8.2.1) as a finite
  product over `P\G/K`. Each factor is flat because it is a retract of `E`. The
  Lean factors are the fixed vectors of the normalized inducing representation of
  `P` under `P ∩ gKg⁻¹`. The proof shows they are averaging retracts of `E`
  directly. It does not identify them with the source's `E^{K_M^g}`.
- Lemma of VI.8.2: the source calls it "facile", generalizing III.2.3. The Lean
  proof uses the injective evaluation of (VI.8.2.1) and the Noetherian property of
  `B`.
- VI.8.3: the source shows `E ⊗_B V_N ≅ (E ⊗_B V)_N` and uses exactness of
  `· ⊗_B V` and of `N`-coinvariants. The Lean proof uses instead the equational
  criterion for flatness. A relation in `V_N` is a relation of one compact
  subgroup of `N(F)`, and compact averaging moves it into the flat fixed module.
  The input is the same: `N(F)` is a limit of compact subgroups, and compact
  averaging is exact.
