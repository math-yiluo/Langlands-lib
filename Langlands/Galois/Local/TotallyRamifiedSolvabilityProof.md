# Proof of solvability of totally ramified finite local Galois groups

Author: Worker 231.

The closing theorem `Langlands.PadicField.totallyRamifiedGaloisSolvability` has type
`Langlands.PadicField.TotallyRamifiedGaloisSolvability.{u}`, the proposition published
in `Langlands.Galois.Local.TotallyRamifiedSolvabilityStatement`, for an arbitrary
universe `u`. Thus, for every prime `p`, every `F : PadicField.{u} p`, every
`E : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier` and every
instance `IsGalois F.Carrier E.field`, it proves that

```lean
(E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
    Module.finrank F.Carrier E.field * F.canonicalTopologicalData.ramificationIndex →
  Group.IsSolvable Gal(E.field/F.Carrier)
```

The proof adds no hypotheses. The statement pair and its imports are unchanged. Besides
the statement, the module imports the published modules
`Langlands.Galois.Local.UnramifiedCriterionProof` and
`Langlands.LocalFactor.Ramification.Galois`. The `IsGalois` instance is never used,
and no auxiliary lemma assumes it. The closing theorem depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Strategy

Write `G = Gal(E.field/F.Carrier)`, `O` for the integer ring of the canonical data of
`E`, `m` for its maximal ideal, and `G_i` for the Library's lower ramification group
`Langlands.Ramification.lowerGroup O G i`. This is the group of elements `g` with
`g • x - x ∈ m ^ (i + 1)` for all `x : O`. The proof has three steps.

1. For any group acting on a local ring, commutators of elements of `G_i` lie in
   `G_{2i}`. Hence `G_i / G_{i+1}` is abelian for `i ≥ 1`.
2. Suppose `O` is a discrete valuation ring and every residue class contains an
   element fixed by the whole group. Then `G_0` is the whole group. The action on a
   uniformizer gives a homomorphism from `G_0` to the commutative residue field, and
   its kernel lies in `G_1`. Hence the `n`th derived subgroup of `G` lies in `G_n`.
   Since the filtration reaches `⊥`, `G` is solvable.
3. The arithmetic hypothesis makes the relative residue degree of `E/F` equal to one.
   Then the elements of `F` supply the fixed residue representatives required in
   step 2.

This route differs from the source derivation recorded in the statement Markdown. It
does not prove that `G_0 / G_1` is cyclic or that `G_1` is a `p`-group. It shows
only that the derived series lies inside the lower filtration, and solvability then
follows from the published termination of the filtration.

The group `G_0` used here is the published `Padic.lowerRamificationGroup _ F.Carrier 0`,
which the published `Padic.lowerRamificationGroup_zero` identifies with the actual
inertia kernel `Padic.inertia _ F.Carrier`. Step 2 therefore shows that actual inertia
is the whole Galois group. The Lean proof works directly with `G_0` and never uses
this identification. No comparison with any other inertia construction is used.

## Generic commutator bounds

Section `Generic` in namespace `Langlands.Ramification` works with a commutative
local ring `R` and a group `G` acting on it by `[MulSemiringAction G R]`. Write
`m = maximalIdeal R`. The Library's `congruenceGroup R G n` consists of the elements
`g` with `g • x - x ∈ m ^ n` for all `x`, and `lowerGroup R G i` is, by definition,
`congruenceGroup R G (i + 1)`.

- `smul_mem_maximalIdeal_pow`: every `g` maps `m ^ n` into itself. The ring
  automorphism `MulSemiringAction.toRingAut G R g` maps `m` onto `m`
  (`IsLocalRing.map_maximalIdeal_of_surjective`), and `Ideal.map_pow` handles the
  power. `smul_mem_maximalIdeal` is the case `n = 1`.
- `smul_sub_mem_pow_add`: if `g ∈ congruenceGroup R G (i + 1)`, `k ≥ 1` and
  `x ∈ m ^ k`, then `g • x - x ∈ m ^ (k + i)`. The proof is by induction on `k ≥ 1`.
  The base case is the hypothesis on `g`. In the inductive step,
  `m ^ (k + 1) = m ^ k * m`, and the proof inducts over products
  (`Submodule.mul_induction_on`). For `a ∈ m ^ k` and `b ∈ m`,

  ```text
  g • (a * b) - a * b = (g • a - a) * (g • b) + a * (g • b - b),
  ```

  where the first term lies in `m ^ (k + i) * m` and the second in
  `m ^ k * m ^ (1 + i)`. Sums are handled by additivity.
- `commutatorElement_mem_congruenceGroup`: if `g` and `h` lie in
  `congruenceGroup R G (i + 1)`, then the commutator `⁅g, h⁆ = g * h * g⁻¹ * h⁻¹`
  lies in `congruenceGroup R G (2 * i + 1)`. Every `x` has the form `h • g • z`,
  and `⁅g, h⁆ • h • g • z = g • h • z`. Hence

  ```text
  ⁅g, h⁆ • x - x = (g • (h • z - z) - (h • z - z)) - (h • (g • z - z) - (g • z - z)).
  ```

  Here `h • z - z` and `g • z - z` lie in `m ^ (i + 1)`. So the previous lemma with
  `k = i + 1` puts both brackets in `m ^ (i + 1 + i) = m ^ (2 * i + 1)`.
- `commutator_lowerGroup_le i`: `⁅G_i, G_i⁆ ≤ G_{2i}`, by `Subgroup.commutator_le`.
- `commutator_lowerGroup_le_succ`: for `1 ≤ i`, `⁅G_i, G_i⁆ ≤ G_{i+1}`. This uses
  the published antitonicity `lowerGroup_antitone` and `i + 1 ≤ 2 * i`.

## The uniformizer character and fixed representatives

Section `Uniformizer` also assumes `[IsDomain R]`, an element `ϖ` with
`hϖ : maximalIdeal R = Ideal.span {ϖ}` and, from `uniformizerCharacter` on,
`hϖ0 : ϖ ≠ 0`. These are hypotheses of the auxiliary lemmas only. They are
discharged in the last section.

- `exists_smul_uniformizer_eq`: for every `g` there is `u` with `g • ϖ = ϖ * u`,
  because `g • ϖ ∈ m = (ϖ)`.
- `uniformizerFactor hϖ g` is a chosen such `u`, and `smul_uniformizer` records
  `g • ϖ = ϖ * uniformizerFactor hϖ g`.
- `uniformizerCharacter hϖ hϖ0 : lowerGroup R G 0 →* ResidueField R` sends `g` to
  the residue of `uniformizerFactor hϖ g`. Its target is the multiplicative monoid
  of the residue field. Cancelling `ϖ` in the domain `R` gives
  `uniformizerFactor hϖ 1 = 1` and
  `uniformizerFactor hϖ (g * h) = uniformizerFactor hϖ g * (g • uniformizerFactor hϖ h)`.
  An element `g` of `G_0` acts trivially modulo `m`, so the second factor has the
  same residue as `uniformizerFactor hϖ h`.
- `smul_uniformizer_sub_mem_of_eq_one`: if the character sends `g` to `1`, then
  `g • ϖ - ϖ = ϖ * (uniformizerFactor hϖ g - 1)` lies in `m * m = m ^ 2`.

The remaining lemmas also assume fixed residue representatives:

```lean
hrep : ∀ x : R, ∃ a : R, (∀ g : G, g • a = a) ∧ x - a ∈ maximalIdeal R
```

- `lowerGroup_zero_eq_top_of_fixed`: `G_0 = ⊤`, because
  `g • x - x = g • (x - a) - (x - a)` lies in `m`.
- `mem_lowerGroup_one_of_fixed`: if `g ∈ G_0` and `g • ϖ - ϖ ∈ m ^ 2`, then
  `g ∈ G_1`. Write `x = a + b * ϖ` with `a` fixed. Then
  `g • x - x = (g • b) * (g • ϖ - ϖ) + (g • b - b) * ϖ`, and both terms lie in
  `m ^ 2`.
- `commutator_lowerGroup_zero_le_of_fixed`: `⁅G_0, G_0⁆ ≤ G_1`. The character sends
  every commutator to `1`. In Lean this goes through `MonoidHom.toHomUnits`, which
  lands in the commutative unit group of the residue field, together with
  `map_commutatorElement` and `commutatorElement_eq_one_iff_mul_comm`. The two
  previous lemmas then apply.
- `derivedSeries_le_lowerGroup_of_fixed n`: `derivedSeries G n ≤ G_n`. The proof is
  by induction on `n`. The case `n = 0` is `G_0 = ⊤`. The successor step uses
  `Subgroup.commutator_mono`, followed by the bound for `G_0` when `n = 0` and by
  `commutator_lowerGroup_le_succ` when `n ≥ 1`.
- `isSolvable_of_fixed`: if `G_b = ⊥` for some `b`, then `derivedSeries G b = ⊥`,
  which gives `Group.IsSolvable G`.

## Residue degree one and the closing theorem

Namespace `Langlands.PadicField` fixes `F : PadicField.{u} p` and
`E : FiniteIntermediateExtension F.Carrier`, and writes `EP` for
`E.asPadicField (p := p)`. As in the published module
`Langlands.Weil.Local.IntermediateWeil`, it installs `(EP).algebra` as a local
`Algebra (Padic p) E.field` instance. Because that algebra map factors through
`F.Carrier` by definition, it also installs the local instance
`IsScalarTower (Padic p) F.Carrier E.field` through
`IsScalarTower.of_algebraMap_eq' rfl`. Write `f = intermediateEmbedding F E`, the
published literal inclusion `F.Carrier →ₐ[Padic p] E.field`.

- `extensionDegree_intermediateEmbedding`: `extensionDegree F EP f` equals
  `Module.finrank F.Carrier E.field`. The algebra `extensionAlgebra F EP f` built
  from `f` is pointwise equal to the existing `F.Carrier`-algebra structure of
  `E.field`, so `Algebra.algebra_ext` identifies them.
- `extensionResidueDegree_eq_one_of_ramificationIndex`: under the arithmetic
  hypothesis `e_E = [E : F] * e_F`, the relative residue degree
  `extensionResidueDegree F EP f` is `1`. The published identity
  `ramificationIndex_mul_extensionResidueDegree` gives
  `e_E * f(E/F) = [E : F] * e_F`. Rewriting with the previous lemma and the
  hypothesis gives `e_E * f(E/F) = e_E`, and `ramificationIndex_pos` allows
  cancellation.
- `fixedResidueRepresentatives`: if the residue degree is `1`, then the group
  `Gal(E.field/F.Carrier)`, acting on the canonical integer ring of `EP` through the
  published `Padic.integerAction`, has fixed residue representatives in the sense of
  `hrep`. By `finrank_eq_one_iff_of_nonzero'`, the residue class of any `x` is
  `c • 1` for some `c` in the residue field of `F`. That `c` is the residue of an
  integer `y` of `F`. The representative is `extensionIntegerMap F EP f y`, that is,
  `y` regarded in `E`. Every `σ` fixes it because `σ` is an `F.Carrier`-algebra map
  (`AlgEquiv.commutes`), and its residue is `c • 1` by the definition of the residue
  algebra `extensionResidueAlgebra F EP f`.
- `isSolvable_of_extensionResidueDegree_eq_one`: if the residue degree is `1`, then
  `Gal(E.field/F.Carrier)` is solvable. After the canonical topology, valuative
  relation and local-field instances of the canonical data of `EP` are installed,
  Mathlib shows that its integer ring is a discrete valuation ring. An irreducible
  `ϖ` from `IsDiscreteValuationRing.exists_irreducible` satisfies
  `maximalIdeal = Ideal.span {ϖ}` (`Irreducible.maximalIdeal_eq`) and `ϖ ≠ 0`. The
  published `Padic.exists_lowerRamificationGroup_eq_bot` provides `b` with
  `Padic.lowerRamificationGroup _ F.Carrier b = ⊥`. By definition this is
  `lowerGroup` for `Padic.integerAction`. Then `isSolvable_of_fixed` applies with
  the previous lemma.
- `totallyRamifiedGaloisSolvability`: introduce `p`, `F`, `E`, the instances and the
  hypothesis `h`. Then combine the last lemma with
  `extensionResidueDegree_eq_one_of_ramificationIndex F E h`.
