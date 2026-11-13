# Reduction of the tempered-untwist selection (Renard VII.4.2 (iii))

Worker 5295, Task 5295. This module defines the closed proposition
`OppositeUntwistTemperedCriterionStatement`, a temperedness criterion for a
unitary untwist ("T" below). It imports the closed proposition
`OppositeStandardExponentRestrictionStatement` from the module
`OppositeStandardExponentRestrictionStatement`, on restriction of exponents
to a larger standard Levi ("R1" below; recalled here, not restated).

It proves `oppositeJacquetUntwistSelection_of_inputs`: R1, T, Langlands'
combinatorial lemma V.3.18, admissibility of irreducible representations and
finite length of Levi Jacquet modules imply the published internal proposition
`OppositeJacquetUntwistSelectionStatement`. It does not prove any of these five
inputs. It does not prove part (iii) of VII.4.2 or the classification
unconditionally.

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026. The main locator is VII.4.2, Theorem (iii) and
its proof, printed pp.243–244 / PDF pp.249–250. The proof also uses Lemma
VII.1.1 (printed p.220 / PDF p.226), the definition of temperedness VII.2.1
(printed p.227 / PDF p.233) and Langlands' combinatorial lemma V.3.18 (printed
pp.114–115 / PDF pp.120–121). Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Notation

Throughout, `k` is a nonarchimedean local field (`Field`, `ValuativeRel`,
topology, `IsNonarchimedeanLocalField`, `T2Space`). `G` is a connected reductive
group scheme over `k`, and its rational points carry the canonical point
topology and are locally compact and a nonarchimedean group. Further:

- `i : T → G` is a maximal split torus (a monomorphism).
- `ν` is a generic cocharacter whose dynamic parabolic is minimal, so that it
  fixes the positive and simple relative roots `Δ`.
- `D` is integral root-reflection data supplying the coroots `α̌`.

For a smooth representation `π` of `G(k)`,
`OppositeStandardJacquetFamily.exponents i ν hG hi hν π` is the published
family of pairs `(J, χ)`. Here `J ⊆ Δ` is a standard label and `χ` is an actual
normalized Jacquet exponent of `π` along the opposite `P̄_J` of the standard
parabolic `P_J`, a character of the chosen split component `A_J` of the standard
Levi `M_J`. Its full real parameter
`v_x = OppositeStandardJacquetFamily.fullRealPart … D x` is the unique vector of
`𝔞*_∅ = Vstar T = ℝ ⊗ X*(T)` that annihilates the coroots of `J` and restricts
on `A_J` to the normalized real part of `χ` (published, in
`OppositeStandardExponentParameters`). For a set `S` of characters, `⟨S⟩`
denotes the real span of the vectors `1 ⊗ α`, `α ∈ S`, and `hull(S)` their
nonnegative cone (`PointedCone.hull ℝ`).

## R1 (imported): restriction of exponents to a larger standard Levi

`OppositeStandardExponentRestrictionStatement`, defined and documented in its
own module, quantifies over the data above and an admissible
finite-length smooth `π` on a carrier in universe `v`. For every exponent `z` on
a label `J`, every standard label `K` with `J ⊆ K`, and every `w ∈ Vstar T`:

- if `⟨w, α̌⟩ = 0` for every relative root `α ∈ K`,
- and `v_z − w ∈ ⟨K⟩`,

then there is an exponent `x` with label `x.1 = K` and `v_x = w`.

This is the step of the proof of (iii) (printed p.244) in which Lemma VII.1.1
and the transitivity of parabolic restriction give
`μ|_{A_L} = μ⁺ + μ_G ∈ ℜ(Exp(A_L, r^G_{Q̄}(V)))`. Its correspondence with the
source and its provenance are explained in the Markdown of its own module.

## T: temperedness of a unitary untwist from ambient exponents

`OppositeUntwistTemperedCriterionStatement` quantifies over the same data and an
arbitrary smooth `π`. It also quantifies over an exponent `x` of `π` and a
published `UnitaryUntwist` `W` of `x`. Such a `W` consists of an irreducible
subrepresentation `ρ` of the opposite Levi Jacquet module on the label `x.1`,
its irreducible admissible untwist `W.untwist = ρ ⊗ ψ_x⁻¹` by the positive
unramified character realizing the real part of `x`, and the unitary scalar
action of `A_{x.1}` on the untwist.

Assume that every exponent `y` with `y.1 ⊆ x.1` and `v_y − v_x ∈ ⟨x.1⟩`
satisfies `−(v_y − v_x) ∈ hull(Δ)`, so that `v_y − v_x` is a nonpositive
combination of simple roots. Then `W.untwist` is tempered on the standard Levi
`M_{x.1}`, in the sense `IsNormalizedExponentTempered`. That is the library's
normalized-exponent formulation of VII.2.1, which includes admissibility. The
Levi carries its canonical point topology, local compactness and
nonarchimedean group instances, written exactly as in
`OppositeJacquetUntwistSelectionStatement`.

**Correspondence.** On printed p.244, Renard sets `σ = ρ ⊗ ψ⁻¹` and fixes a
standard `P₁ = M₁N₁ ⊆ Q`. He then uses the following:

- `r^L_{P̄₁∩L}(ρ) ↪ r^L_{P̄₁∩L} ∘ r^G_{Q̄}(π) = r^G_{P̄₁}(π)`. Hence every
  exponent of `σ` along `P̄₁ ∩ L` has real part `λ` with
  `λ + ℜ(ψ) ∈ ℜ(Exp(A_{M₁}, r^G_{P̄₁}(V)))`.
- `λ|_{𝔞_L} = 0` by Lemma VII.1.1 (ii).

After the norm argument, which this module proves (see below), he concludes
`λ ∈ ⁺[𝔞*_{M₁}]^G_{P̄₁}`. Changing `Δ^L` to its opposite, so that the
`P̄₁ ∩ L` become the standard parabolics of `L`, he states that `σ` satisfies
the conditions of the definition of temperedness.

T isolates exactly this last step. Its hypothesis ranges over all exponents `y`
on labels inside `x.1` whose full parameter agrees with `v_x` on `A_{x.1}`,
which is the condition `v_y − v_x ∈ ⟨x.1⟩`. The exponents that actually come
from `ρ` form a subset of these, so quantifying over the larger family weakens
the proposition and does not strengthen it. A vector of `⟨x.1⟩` lies in
`−hull(Δ)` exactly when it is a nonpositive combination of the simple roots of
`x.1`, which is Renard's cone for the opposite parabolics. The remaining content
is the following: the exponents of the untwist along `P̄₁ ∩ L` have full real
parameters `v_y − v_x`, and checking the cone condition of VII.2.1 on the
opposite standard parabolics of `L` suffices. No admissibility of `π` is
assumed. The untwist is irreducible and admissible by the fields of
`UnitaryUntwist`, and its Jacquet exponents are generalized weights inside
those of `π` by exactness and transitivity. Provenance: derived, an
intermediate claim of the source proof.

## The reduction

`oppositeJacquetUntwistSelection_of_inputs` proves
`OppositeJacquetUntwistSelectionStatement.{u, v}` from

- `Langlands.GroupScheme.LanglandsCombinatorialDecompositionStatement.{u}`
  (V.3.18, a published statement by Worker 24, unproved);
- `RationalPointsIrreducibleAdmissibleStatement.{u, v}` (irreducible smooth
  representations are admissible; unproved);
- `LeviJacquetFiniteLengthStatement.{u, v}` (Levi Jacquet functors preserve
  finite length; unproved);
- `OppositeStandardExponentRestrictionStatement.{u, v}` (R1, unproved);
- `OppositeUntwistTemperedCriterionStatement.{u, v}` (T, unproved).

### Auxiliary lemmas (namespace `UntwistSelection`)

These lemmas fix a field `k`, a group scheme `G` with affine structure map, a
torus monomorphism `i : T → G`, reflection data `D`, and a real bilinear form
`B` on `Vstar T` with `IsWeylInvariantInnerProduct i B`: symmetric, positive
definite and invariant under the full real relative Weyl action.

- `pair_coroot_mul_form_root`: `⟨y, α̌⟩ · B(α, α) = 2 · B(y, α)` for every
  relative root `α` and every `y`. Proof: apply invariance to the reflection
  representative of `α`, whose real action is `y ↦ y − ⟨y, α̌⟩ α`
  (`RelativeRootReflectionData.fullRealAction_representative`), and use
  `⟨α, α̌⟩ = 2`.
- `tmul_root_ne_zero`: `1 ⊗ α ≠ 0`, since it pairs to `2` with `α̌`.
- `relativeWeylFullRealAction_restrictReal`: the full real Weyl action fixes
  the image of `rationalCharacterRestrictReal i` (restriction of real rational
  characters of `G`). This is tensor induction from the published fixedness of
  restricted characters, the real analogue of
  `relativeWeylFullRatAction_restrictionRange`.
- `pair_coroot_eq_zero_of_mem_range`: such central vectors annihilate every
  coroot, because the reflection of `α` fixes them and `1 ⊗ α ≠ 0`.
- `form_eq_zero_of_pair_eq_zero`: a vector annihilating the coroots of a set
  `K` of roots is `B`-orthogonal to `⟨K⟩`, by the coroot formula on generators.
- `form_eq_zero_of_mem_range_of_mem_rootSpan`: central vectors are
  `B`-orthogonal to the real root span `relativeRootSpanReal i`.
- `form_nonneg_of_mem_hull`: if `S ⊆ Δ`, `z ∈ hull(S)` and `c` lies in the
  closed coroot face of `∅` (`closedCorootFace i ν D ∅`, nonnegative pairing
  with every simple coroot), then `B(z, c) ≥ 0`. The proof is cone induction
  with the coroot formula.
- `neg_mem_hull_of_positivePart_le` (the Euclidean core). Let `G` be connected
  reductive with maximal split `i`. Suppose:
  - `K ⊆ Δ`, `m_G` is central, and `m_p` lies in the open coroot face of `K`;
  - `(K_y, y_G, y_p, y_m)` is a `P_∅` Langlands decomposition of a vector
    `v_y`;
  - `v_y − (m_G + m_p) ∈ ⟨K⟩`;
  - `B(y_p, y_p) ≤ B(m_p, m_p)`.

  Then `−(v_y − (m_G + m_p)) ∈ hull(Δ)`.

### Implemented proof of the core lemma

Let `λ = v_y − (m_G + m_p)`.

1. The decomposition gives `−y_m ∈ hull(K_y)`: its projected cone for the
   empty label has zero span correction.
2. `m_p` lies in the closed coroot face of `∅`, because its pairings with
   simple coroots are `0` on `K` and positive off `K`.
3. Three facts follow from the auxiliary lemmas:
   - `B(m_p, λ) = 0`, since `m_p` annihilates the coroots of `K`;
   - `B(y_G − m_G, m_p) = 0`, since `y_G − m_G` is central and `m_p` lies in
     the root span;
   - `B(−y_m, m_p) ≥ 0`.
4. Write `λ = (y_G − m_G) + (y_p − m_p) + y_m`. Then
   `B(y_p, m_p) ≥ B(m_p, m_p)`. With `B(y_p, y_p) ≤ B(m_p, m_p)` this gives
   `B(y_p − m_p, y_p − m_p) ≤ 0`, so positive definiteness forces
   `y_p = m_p`.
5. Hence `λ = (y_G − m_G) + y_m`. Here `λ ∈ ⟨K⟩` and `y_m ∈ ⟨K_y⟩` both lie
   in the root span, so `y_G − m_G` is a central vector in the root span. The
   published `relativeCharacterRootComplement` (the root span meets the
   central range only in `0`) gives `y_G = m_G`.
6. So `−λ = −y_m ∈ hull(K_y) ⊆ hull(Δ)`.

This is the inner-product form of Renard's chain
`|λ⁻| ≤ |λ| ≤ |(λ + μ⁺)⁻| ≤ |λ⁻|`. Step 4 replaces the norm comparison: the
residual `(y_G − m_G) + y_m` pairs nonpositively with the closed chamber.

### Implemented proof of the reduction

Fix the data and an irreducible `π`.

1. `π` is admissible (`RationalPointsIrreducibleAdmissibleStatement`), has
   finite length (`SmoothRep.hasFiniteLength_of_isIrreducible`) and is
   nontrivial (an irreducible representation is a simple module).
2. The relative Weyl group is finite (`IsConnectedReductive.finite_relativeWeylGroup`).
   `B = relativeWeylInvariantForm i` (the published Weyl average of a
   coordinate inner product) satisfies `IsWeylInvariantInnerProduct i B` by
   its published symmetry, positivity and invariance lemmas.
3. For each exponent `y`, `v_y` annihilates the coroots of `y.1`
   (`pair_fullRealPart_selectedCoroot`). V.3.18 applied to the published
   compatible standard presentation `rootPresentation … y.1` (with its split
   component `A_{y.1}`, the standard parabolic and Levi, and the factor
   `Additive.ofMul g`) gives a decomposition of `v_y` relative to `y.1`. By
   its final clause, the `P_∅` decompositions of `v_y` are exactly this tuple.
   Let `pos y` be the positive part of the `P_∅` decomposition, chosen by
   `Classical.choose`. Every `P_∅` decomposition of `v_y` has positive part
   `pos y`.
4. The exponents form a finite nonempty type (`finite_exponents`,
   `nonempty_exponents`). Choose `x₀` maximizing `B(pos y, pos y)`
   (`Finite.exists_max`).
5. Let `(K, m_G, m_p, m_m)` be the decomposition of `v_{x₀}` relative to `x₀.1`.
   Then `x₀.1 ⊆ K ⊆ Δ` and `pos x₀ = m_p`. Moreover `v_{x₀} − (m_G + m_p) = m_m`
   lies in `⟨K⟩`, because `−m_m` is a nonnegative combination of `K ∖ x₀.1`
   modulo `⟨x₀.1⟩`. Also `m_G + m_p` annihilates the coroots of `K`.
6. R1 with `w = m_G + m_p` gives an exponent `x` with label `K` and
   `v_x = m_G + m_p`.
7. `LeviJacquetFiniteLengthStatement` gives finite length of the opposite
   Levi Jacquet module on `K`. The published `irreducibleUnitaryUntwist` then
   gives a unitary untwist `W` of `x`.
8. Temperedness: apply T. For an exponent `y` with
   `v_y − v_x ∈ ⟨K⟩`, take its `P_∅` decomposition. Maximality gives
   `B(pos y, pos y) ≤ B(m_p, m_p)`, and the core lemma gives
   `−(v_y − v_x) ∈ hull(Δ)`.
9. Chamber: `v_x` restricts to `realPart x` (`restrict_fullRealPart`) and
   annihilates the coroots of `K`. For a simple `α ∉ K`,
   `⟨v_x, α̌⟩ = ⟨m_G, α̌⟩ + ⟨m_p, α̌⟩ = 0 + ⟨m_p, α̌⟩ > 0`, by
   `pair_coroot_eq_zero_of_mem_range` and the open face. So
   `realPart x ∈ restrictedCorootChamber i ν K (Additive.ofMul g) D`.

The pair `(x, W)` satisfies both conjuncts of the selection statement. No
universe is identified with another. The published statement's Lean/Markdown
pair and its imports are unchanged. The proof uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.
