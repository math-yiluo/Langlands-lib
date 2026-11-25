# Self-dual bicharacters

The module `Langlands.HarmonicAnalysis.Bicharacter.SelfDual` defines self-dual bicharacters on
totally disconnected locally compact abelian groups, the class of groups with arbitrarily large
and small compact open subgroups, and gives the examples on finite-dimensional vector spaces over a
nonarchimedean local field.

## Content

- `CompactOpenExhaustion X` (a `Prop`-valued class): every compact subset of `X` lies in a compact
  open subgroup, and every neighbourhood of `0` contains one. It is transported along additive
  homeomorphisms (`CompactOpenExhaustion.of_addEquiv`), holds for `Fⁿ` over a nonarchimedean local
  field `F` (instance `compactOpenExhaustion_pi`, with the boxes `∏ {x | v x ≤ v s}`), hence for
  every finite-dimensional `F`-vector space with its module topology
  (`compactOpenExhaustion_of_finiteDimensional`). Such a space is also Hausdorff, locally compact
  and second countable (`t2Space_of_finiteDimensional`, `locallyCompactSpace_of_finiteDimensional`,
  `secondCountableTopology_of_finiteDimensional`), through the additive homeomorphism with `Fⁿ`
  given by a basis (`finiteDimensionalCoordinates`). These are not instances, because `F` cannot be
  found from `V`. The class `IsFiniteDimensionalOverLocalField F V` (fields `finiteDimensional` and
  `isModuleTopology`; `F`, its structure and the module structure are out-parameters) records that
  `V` is such a space; for a `V` carrying an instance of it, the four properties are instances
  (`IsFiniteDimensionalOverLocalField.compactOpenExhaustion`, `.t2Space`, `.locallyCompactSpace`,
  `.secondCountableTopology`, priority 100). It has instances for `n → F` and `Matrix m n F`
  (`n`, `m` finite: `IsFiniteDimensionalOverLocalField.pi`, `.matrix`).
- `IsSelfDualBicharacter e`, for `e : X → X → ℂ` on a commutative topological group: `e` is
  additive in each variable (`map_add_left`, and `map_add_right` by symmetry), symmetric, of
  modulus one, locally constant on `X × X`, and `x ↦ e x ·` is a topological isomorphism of `X`
  onto its Pontryagin dual in the following form: for every neighbourhood `U` of `0` there is a
  compact `K` whose annihilator lies in `U` (`small`), and a compact `K` containing the
  annihilator of `U` (`big`). Consequences: `ne_zero`, `map_zero_left`, `map_zero_right`,
  `conj_apply` (`conj (e x y) = e (-x) y`), `continuous`; the annihilator of a set as a subgroup
  (`annihilator`, `mem_annihilator`), open for a compact set (`isOpen_annihilator`, by the tube
  lemma).
- `isSelfDualBicharacter_of_symm`: for a non-trivial continuous character `ψ : F → ℂ` of modulus
  one and a non-degenerate symmetric bilinear form `β` on a finite-dimensional `F`-vector space,
  `(x, y) ↦ ψ (β x y)` is self-dual. In coordinates in which `β` is the dot product, if
  `ψ(t₀) ≠ 1`, a vector `v` with `ψ(u · v) = 1` for all `u` in the box of radius `s` lies in the box
  of radius `t₀ s⁻¹`; this gives both `small` and `big`.
- Closed balls in `F`: `{x | v x ≤ v s}` is open (`isOpen_setOf_valuation_le`; it is `s • 𝒪`) and
  compact (Mathlib's `IsNonarchimedeanLocalField.isCompact_closedBall`), and every neighbourhood of
  `0` contains one (`exists_setOf_valuation_le_subset`). The integral of a non-trivial character
  over a ball containing a point where it is not `1` vanishes
  (`exists_setIntegral_setOf_valuation_le_eq_zero`), by translation invariance.

The pairings of the Library's row and rectangular Fourier transforms are examples
(`Langlands/HarmonicAnalysis/Bicharacter/Instances.lean`), and so is the Hermitian pairing
`ψ(½ tr_{E/F} tr(xᵀ Q c(y)))` on `M_{α×ν}(E)` used for unitary dual pairs
(`Langlands/Theta/DualPair/Unitary/`). The notion is Weil's (A. Weil, *Sur certains groupes d'opérateurs
unitaires*, Acta Math. 111 (1964), chapter I, n° 1, pp. 145–146: every bicharacter is
`f(x, y) = ⟨x, yα⟩`, symmetric exactly when `α = α*`, and non-degeneracy asks the associated morphism
to be an isomorphism of `G` onto `G*`); a self-dual bicharacter is `⟨x, yα⟩` for a symmetric
isomorphism `α` of `X` onto its dual, and Weil does not use the term. It is not the alternating
bicharacter of the Heisenberg group (`Langlands/Theta/Heisenberg/SelfDualSubgroup.lean`), which serves a
different purpose.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`, under
`src/Development/AbelianVarietyTheory/`: `Definitions/Divisors/UnipVal.lean` lines 17–35 (`Good`,
`IsPair`); `Proofs/DivisorProofs/CompactOpenSubgroupExhaustion.lean` (whole);
`Proofs/DivisorProofs/IsSelfDualBicharacterPairingOfSymmBilinForm.lean` (whole);
`Proofs/DivisorProofs/ExistsIntegralClosedBallAddCharEqZero.lean` (whole);
`Proofs/DivisorProofs/BicharacterFourierTransformTwiceEqPosSmulReflect.lean` lines 15–58 (`ne_zero`,
`add_right`, `zero_right`, `ann`, `isOpen_ann`); `Proofs/DivisorProofs/LintegralFourSq.lean`
lines 15–35 (`e_zero`, `conj_e`); from `Proofs/TwistedOperators/FourierTransformInversionLocalFieldPi.lean`
lines 15–32 (`box`, `isOpen_box`, `isCompact_box`, `exists_box_subset`) and from
`Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean` lines 79–109 (`cball` and its
lemmas). The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespaces `GlobalTheory.KSp`, `GlobalTheory.KSp.GoodSpace`, `GlobalTheory.KSp.FourInv`,
  `GlobalTheory.KSp.Planch` → `Langlands.HarmonicAnalysis` (public) and
  `Langlands.HarmonicAnalysis.SelfDual.Internal` (boxes).
- `KSp.Good X` (a structure bundling the topological group structure, Hausdorffness, local
  compactness, second countability and two exhaustion fields) is replaced by Mathlib's classes and
  the class `CompactOpenExhaustion X` holding the two exhaustion fields.
- `KSp.IsPair e` → `IsSelfDualBicharacter e`, fields renamed `add` → `map_add_left`, `norm` →
  `norm_eq_one`, `lc` → `isLocallyConstant`; `FourInv.ann` → `IsSelfDualBicharacter.annihilator`,
  `isOpen_ann` → `isOpen_annihilator`, `add_right` → `map_add_right`, `zero_right` →
  `map_zero_right`, `Planch.e_zero` → `map_zero_left`, `Planch.conj_e` → `conj_apply`.
- `good_of_addEquiv`, `good_pi`, `good_of_finiteDimensional` → `CompactOpenExhaustion.of_addEquiv`,
  `compactOpenExhaustion_pi`, `compactOpenExhaustion_of_finiteDimensional` and the three topological
  theorems; `isPair_addChar_form` → `isSelfDualBicharacter_of_symm`;
  `exists_integral_cball_char_eq_zero` → `exists_setIntegral_setOf_valuation_le_eq_zero`.
- The source's `cball s` is written as Mathlib's set `{x | valuation F x ≤ valuation F s}`;
  `isOpen_cball`, `exists_cball_subset` → `isOpen_setOf_valuation_le`,
  `exists_setOf_valuation_le_subset`; the source's local-field facts are the Library's
  `GeneralLocalField.*`; the source's `isLocallyConstant_addChar` is the Library's
  `isLocallyConstant_of_continuous_addChar`.
- Hypotheses dropped: `[CharZero F]`; in `exists_setIntegral_setOf_valuation_le_eq_zero`, Haar
  measure is weakened to a left-invariant measure and the continuity and modulus of `ψ` are not
  assumed. The ball condition `s₀ ∈ cball s` is stated as `v s₀ ≤ v s`. Types in any universe.

## Declarations

- `CompactOpenExhaustion`, `CompactOpenExhaustion.of_addEquiv`, instance `compactOpenExhaustion_pi`
- `finiteDimensionalCoordinates`, `compactOpenExhaustion_of_finiteDimensional`,
  `t2Space_of_finiteDimensional`, `locallyCompactSpace_of_finiteDimensional`,
  `secondCountableTopology_of_finiteDimensional`
- `IsFiniteDimensionalOverLocalField` and its instances `.compactOpenExhaustion`, `.t2Space`,
  `.locallyCompactSpace`, `.secondCountableTopology`, `.pi`, `.matrix`
- `isOpen_setOf_valuation_le`, `exists_setOf_valuation_le_subset`,
  `exists_setIntegral_setOf_valuation_le_eq_zero`
- `IsSelfDualBicharacter`, `.ne_zero`, `.map_add_right`, `.map_zero_right`, `.map_zero_left`,
  `.conj_apply`, `.continuous`, `.annihilator`, `.mem_annihilator`, `.isOpen_annihilator`
- `isSelfDualBicharacter_of_symm`

All in the namespace `Langlands.HarmonicAnalysis`.

## Dependencies

`Langlands.HarmonicAnalysis.AdditiveCharacterExists` (local constancy of continuous characters,
nonarchimedean additive structure of `F`, and through it `Langlands.HarmonicAnalysis.Basic`),
`Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof` (`GeneralLocalField.*`); Mathlib:
`MeasureTheory.Integral.Bochner.Set`, `MeasureTheory.Group.Integral`,
`Topology.Algebra.Module.ModuleTopology`, `Topology.Algebra.Module.FiniteDimension`,
`LinearAlgebra.Matrix.DotProduct`.
