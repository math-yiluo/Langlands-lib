# Exact-K0 adapters and Aubert's unadjusted alternating operator

Implementation and documentation: Worker 23 (task
`593ef603-6672-4424-976c-14e11e920d9c`).

This module adapts the functors of
[`Aubert.General.Parabolic`](Parabolic.md) to the published exact Grothendieck
group of finite-length smooth complex representations. It then defines
Aubert's unadjusted alternating operator for an actual family of semidirect
decompositions, together with its class formula, its Levi version and its
empty-root-set case. It also gives K0 maps for conjugation transport and for the
smooth contragredient.

**This module is conditional.** The induction and Jacquet maps, and hence `D_G`,
take as explicit arguments the named hypothesis `ParabolicFiniteLength` (finite
length preservation and exactness). The contragredient map takes
`ContragredientPreservesFiniteLength` and compact-open cofinality; the latter is
proved here for locally compact nonarchimedean groups. The two
exactness conjuncts of `ParabolicFiniteLength` are proved below from structural
inputs (see "Exactness from structural inputs"). Finite-length preservation,
for `i`, `r` and the contragredient, is not proved here, and no finite-length
witness is invented. Only the conjugation map is unconditional. Nothing here
proves involutivity or any other part of Aubert's theorem.

## The Grothendieck group

Every K0 is the published
`SmoothRep.FiniteLengthGrothendieckGroup.{0, uG, uV} ℂ H`. It is the free
integral module on isomorphism classes of actual smooth representations of
finite length over the group algebra, modulo the relations of all actual short
exact sequences, nonsplit ones included. No free group on labels is used.
Induction and Jacquet use carriers `Type (max uG uV)`, so that `i ∘ r` is an
endomorphism.

## Named prerequisites

`ParabolicFiniteLength h hU : Prop` is the conjunction of four published
predicates of `Smooth.FiniteLengthGrothendieckFunctor`:
`PreservesFiniteLength` and `PreservesFiniteLengthShortExact` for
`normalizedInductionFunctor h hU`, and the same two for `jacquetFunctor h hU`.
The latter means that short exact sequences of finite-length objects go to short
exact sequences of the underlying intertwiners. For a connected reductive `G`
and a parabolic `P`, they are in Renard: exactness is the VI.1.2 Proposition
(printed p. 136); finite length is preserved by `i^G_P` (VI.6.2, printed
p. 178, which uses the geometric-lemma consequence VI.5.4) and by `r^G_P`
(VI.6.4, printed p. 179, from Howe's theorem VI.6.3, VI.1.3 and the Jacquet
lemma VI.6.1). They are false for arbitrary subgroups, which is why the generic
layer takes them as hypotheses. Exactness reduces to structural inputs, as
proved in the next subsection. For the actual group, finite-length preservation
is a representation-theoretic proof obligation. It is to be stated as a Prop
target of this task in a separate submission, not in this module.

### Exactness from structural inputs

The two exactness conjuncts are proved from published theorems, given
structural inputs. Each is first proved for every actual short exact sequence
`0 → A → B → C → 0` of smooth representations, of any length (the `_map_`
theorems). The finite-length conjunct is then that theorem with the three
finite-length hypotheses unused.

* `jacquetFunctor_map_isShortExact h hU hUc f g hfg` assumes `hUc :
  Jacquet.Localization.IsLimitOfCompactSubgroups U`. It applies clause `.2` of the
  published `characterLocalizationExactness` with the trivial character, which is
  locally constant, and `M ≤ normalizer U`. Twisting does not change the
  underlying maps, and the three components are reordered into `IsShortExact`.
  `jacquetFunctor_preservesShortExact h hU hUc` is its finite-length case.
* `normalizedInductionFunctor_map_isShortExact hcof h hU hP hproj f g hfg`
  assumes `[T2Space G]`, `hcof : CompactOpenCofinal G`, a closed `P` and a
  continuous projection. Continuity makes the inducing representations smooth
  (`isSmooth_comp` and `isSmooth_twist_iff`). The proof then uses the published
  `Induction.smoothInducedMap_injective`,
  `Induction.smoothInducedMap_range_eq_ker` and
  `Induction.smoothInductionSurjectivity`.
  `normalizedInductionFunctor_preservesShortExact hcof h hU hP hproj` is its
  finite-length case.
* `compactOpenCofinal_of_nonarchimedean H` proves `CompactOpenCofinal H` for
  every locally compact nonarchimedean group `H`. Given an open subgroup `K`,
  take a compact neighbourhood `C` of `1`. Some open subgroup `V` lies in
  `C ∩ K`. Being an open subgroup, `V` is closed, hence compact. So the argument
  `hcof` above, and the one of `contragredientK0` below, is always available for
  the locally compact nonarchimedean groups of this module.
* `ParabolicFiniteLength.of_preservesFiniteLength` assembles the named
  prerequisite from these structural inputs and the two finite-length
  preservation hypotheses. So the only representation-theoretic content left in
  `ParabolicFiniteLength` is finite-length preservation (Renard VI.6.2 and VI.6.4).

`ContragredientPreservesFiniteLength H : Prop` says that `A.contragredient`
has finite length whenever `A` does, for every `A : SmoothRep.{0, uG, uV} ℂ H`.

## The maps

* `inductionK0 h hU hl hx` and `jacquetK0 h hU hl hx` are the published
  `FiniteLengthGrothendieckGroup.map` of the two functors.
  `inductionK0_ofRepresentation` and `jacquetK0_ofRepresentation` give the
  generator formulas `[A] ↦ [i A]` and `[A] ↦ [r A]`, and
  `inductionK0_comp_jacquetK0` identifies the composite with the map of
  `inductionJacquetFunctor` (published `map_comp`).
* `conjugationK0 g hMN` is the published
  `FiniteLengthGrothendieckGroup.pullback` along `conjugationEquiv g hMN`. It
  is unconditional, because the published pullback preserves finite length and
  exactness. Its generator formula is `conjugationK0_ofRepresentation`.
* `contragredientClass H hl` sends the class of `A` to the class of
  `A.contragredient`. It is well defined by `contragredientIso`.
  `isExactAdditive_contragredientClass` proves exact additivity. Given
  `0 → A → B → C → 0`, the published `smoothContragredientShortExact`, under
  `CompactOpenCofinal H`, gives `0 → C̃ → B̃ → Ã → 0`, so
  `[B̃] = [C̃] + [Ã] = [Ã] + [C̃]`. Range equals kernel is converted to Mathlib's
  `Function.Exact` with `LinearMap.exact_iff`. `contragredientK0 H hcof hl` is
  the published `lift`, and `contragredientK0_ofRepresentation` is its
  generator formula `[A] ↦ [Ã]`.

## The alternating operator

Fix a finite index type `ι` (in applications, the simple relative roots `S`)
and families `P M U : Finset ι → Subgroup G` with
`h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I)`, closed `U I`, and
`hfl : ∀ I, ParabolicFiniteLength (h I) (hU I)`. This is the layout of Worker
194's `Aubert.SubgroupComplex`.

* `alternatingTerm .. I := (inductionK0 ..).comp (jacquetK0 ..)`, which is
  `i_I ∘ r_I` on K0.
* `alternatingOperator P M U h hU hfl := ∑ I : Finset ι, (-1)^{|I|} •
  alternatingTerm .. I`.

This is Aubert's Définition 1.5 (printed p. 2181):

    D_G = ∑_{I ⊆ S} (-1)^{|I|} i_{L_I} ∘ r_{L_I}.

`I` is the set of simple roots of the Levi `L_I = M I`. `I = ∅` is the minimal
Levi, with sign `+1`. `I = S` is `G` itself, with sign `(-1)^{|S|}`, provided the
family has `P S = M S = ⊤`. That proviso is a property of the supplied family,
not something this module imposes. Likewise, the terms are Aubert's normalized
`i_{L_I} ∘ r_{L_I}` only when every `U I` is unimodular, for example a limit of
compact subgroups as for the standard unipotent radicals. See "Source
identification" in [`Parabolic.md`](Parabolic.md). This is the unadjusted operator. The
cuspidal-support sign of Aubert's Définition 2.1 is not applied.

* `alternatingOperator_apply` evaluates `D_G` on any virtual class.
* `inductionJacquet_hasFiniteLength` shows that `i_I (r_I A)` has finite length
  whenever `A` does, under `hfl`.
* `alternatingOperator_ofRepresentation` is the class formula:
  `D_G [A] = ∑_I (-1)^{|I|} [i_I (r_I A)]`.
* `alternatingOperator_of_isEmpty` is the empty-root-set case. If `ι` is empty,
  the only subset is `∅`, and `D_G = i_∅ ∘ r_∅`.

## Levi versions

For `J : Finset ι` with `M J` closed, `leviIndex J I` reads `I : Finset J` as a
finset of `ι`, and `card_leviIndex` shows the cardinality is unchanged.
`leviAlternatingOperator P M U J hM hJ hU hfl` is `alternatingOperator` for
the group `M J` (with `letI := hM.locallyCompactSpace`), the index type `J`,
and the families `(P I).subgroupOf (M J)`, `(M I).subgroupOf (M J)`,
`(U I).subgroupOf (M J)`. Their closedness comes from preimages, and the
decompositions `hJ` inside `M J` are inputs, as in Renard VI.1.4.
`leviAlternatingOperator_eq` writes it as
`∑_{I ⊆ J} (-1)^{|I|} i^{M_J}_I ∘ r^{M_J}_I`, that is, `D_{L_J}` of Aubert
§1. When `J = ∅`, `J` is empty and the empty-root-set case applies.

The Levi operator lives on the K0 of `M J`. The K0 maps between `M I` and
`M I`'s copy `(M I).subgroupOf (M J)` are the unconditional pullbacks along
`subgroupOfContinuousEquiv`.

## Universes

`alternatingOperator` has level parameters `uI` (index), `uG` (group) and `uV`
(carrier). Its K0 is `FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ G`.

## Sources

* A.-M. Aubert, *Dualité dans le groupe de Grothendieck de la catégorie des
  représentations lisses de longueur finie d'un groupe réductif p-adique*,
  Trans. AMS 347 (1995), registered as `aubert-1995-duality`: Définition 1.5,
  printed p. 2181. The functors of p. 2180 are the normalized BZ functors.
  The generic `i` agrees with them only when `U` is unimodular; see
  "Source identification" in [`Parabolic.md`](Parabolic.md).
* D. Renard, *Représentations des groupes réductifs p-adiques* (2026 version),
  registered as `renard-2026-representations-groupes-reductifs-padiques`:
  VI.1.2 (printed pp. 135–136) for exactness, VI.1.4 (p. 136) for
  Levi-in-Levi parabolics, VI.6.2 and VI.6.4 (printed pp. 178–179) for
  finite length.
* The GL specialization `Langlands.Aubert.alternatingOperator` (module
  `Aubert.AlternatingOperator`) is the template. There the finite-length
  hypotheses are published theorems.
