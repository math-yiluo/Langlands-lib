# Modular characters of the actual rational-point group and its standard parabolics

Authors: Worker 1415 and Worker 1423.

`Langlands.Aubert.General.RationalPointFamily.RationalParabolicModulusStatement`
is a proposition definition awaiting proof. It states two facts about the
actual rational-point group `G(k)` and its actual standard parabolics:
unimodularity of `G(k)`, and the identification of Mathlib's modular character
of a standard parabolic `P = M ⋉ U` with the Library's Haar modulus of the
conjugation action of `P` on `U`. It proves neither fact and adds no axiom.

## Hypotheses

The field `k : Type u` is every nonarchimedean local field, given by the
instances `Field k`, `ValuativeRel k`, `TopologicalSpace k` and
`IsNonarchimedeanLocalField k`. There is no restriction on the characteristic
or on the residue field.

`G` is every group scheme over `Spec k` with `IsConnectedReductive G`. This
includes nonsplit and non-quasisplit groups. `T` is a commutative group scheme
over `Spec k` and `i : T.toGrp ⟶ G` is an actual homomorphism with
`IsMaximalSplitTorus i`. The two local `haveI` binders only extract instances
from these hypotheses: affineness of the structure morphism of `G` from
`hG.isAffineHom`, and the monomorphism property of `i` from
`hi.isSplitSubtorus.mono`. The published root-indexed subgroup families need
both.

The carrier `RationalPoint k G.X` is the actual group of `k`-points, with the
canonical topology `RationalPointFamily.pointTopology`. Local compactness, the
nonarchimedean group property and Hausdorffness of this topology are displayed
instance hypotheses. `NonarchimedeanGroup` includes `IsTopologicalGroup`, so
continuity of the group operations is part of this premise, not a separate
one. Every subgroup carries the subspace topology.

`ν` is a cocharacter of `T` with `IsGenericCocharacter i ν`. `I` is every finite
subset of the actual simple-root labels `SimpleRoot i ν`, including the empty
subset; there is no nonemptiness condition. `parabolic i ν I`, `levi i ν I` and
`unipotent i ν I` are the published standard parabolic, Levi and unipotent
point subgroups at `rootSet i ν I`. The explicit hypothesis
`hStandard : StandardCocharacterStatement.{u}` is the published universal
standard-cocharacter assertion, which remains unproved. The target is
conditional on that assertion. The published theorem
`isSemidirectDecomposition_of_standardCocharacterStatement` uses it to prove
the actual decomposition `P = M ⋉ U` of these three subgroups. That
decomposition provides `le_normalizer : P ≤ normalizer U` and the actual Levi
projection `projection : P →* M`.

`hU` and `hP` assert that `U` and `P` are closed in `G(k)`. `hU` is used in the
conclusion through `HaarModulus.closedRestrictCharacter`, which takes the local
compactness of `U` from closedness. `hP` gives local compactness of `P` through
the binder `haveI : LocallyCompactSpace (parabolic i ν I) := hP.locallyCompactSpace`.
Mathlib's modular character of `P` needs this. The last premise is continuity of
the actual Levi projection. It does not enter the expression of either
conclusion.

These outer premises are exactly those of the published
`RationalNaturalInductionDualityStatement`. The statement's intended consumer
can therefore apply it directly. No other premise is assumed: in particular no
compactness of `P\G`, good maximal compact subgroup, Iwasawa or Cartan
decomposition, second countability, Iwahori factorization or modular-character
identity. Every such input is a proof obligation.

## Conclusions

1. For every `g : RationalPoint k G.X`,
   `MeasureTheory.Measure.modularCharacter g = 1`. That is, `G(k)` with its
   point topology is unimodular.
2. For every `p : parabolic i ν I`,
   `MeasureTheory.Measure.modularCharacter p` (the modular character of the
   locally compact group `P` itself, with its subspace topology) equals
   the value at `p` of
   `HaarModulus.closedRestrictCharacter (unipotent i ν I) hU (parabolic i ν I) h.le_normalizer`,
   coerced from `ℝ≥0ˣ` to `ℝ≥0`. Here `h` is the decomposition above. By
   definition this value is `mulEquivHaarChar` of the conjugation
   `u ↦ p u p⁻¹` on `U`, that is, `normalizerCharacter U` at `p` regarded as an
   element of the normalizer of `U`.

Mathlib's `modularCharacter` uses the Borel σ-algebra internally, so neither
conclusion depends on a measurable-space instance chosen here.

## Three conventions

Write `Δ_H` for Mathlib's `modularCharacter` on a locally compact group `H`,
`mod_U` for the Library `normalizerCharacter U`, and `δ` for Renard's modular
functions.

- **Mathlib.** For an inner-regular left Haar measure `μ` on `H`,
  `map (· * g) μ = modularCharacter g • μ`
  (`map_right_mul_eq_modularCharacterFun_smul`). Since
  `(map (· * g) μ)(S) = μ(S g⁻¹)`, this gives `μ(S g⁻¹) = Δ_H(g) μ(S)` and
  `μ(S g) = Δ_H(g)⁻¹ μ(S)`.
- **Library.** `HaarModulus.normalizerCharacter_smul_map` states
  `normalizerCharacter g • μ_U.map (u ↦ g u g⁻¹) = μ_U` for a Haar measure
  `μ_U` on `U`. Since `(μ_U.map (u ↦ g u g⁻¹))(S) = μ_U(g⁻¹ S g)`, this gives
  `μ_U(g⁻¹ S g) = mod_U(g)⁻¹ μ_U(S)`. Equivalently,
  `∫ f(g⁻¹ u g) dμ_U = mod_U(g) ∫ f dμ_U` (`integral_normalizerConj_symm`).
- **Renard.** In the proof of the Lemma of V.5.4, `δ_P` is given by
  `∫_P χ(a p a⁻¹) dμ_P(p) = δ_P(a) ∫_P χ(p) dμ_P(p)` for a left Haar measure
  `μ_P`. That is, `μ_P(a⁻¹ K a) = δ_P(a) μ_P(K)`. By left invariance,
  `μ_P(a⁻¹ K a) = μ_P(K a) = Δ_P(a)⁻¹ μ_P(K)`. Hence Renard's `δ_P` is the
  inverse of Mathlib's `Δ_P`. This agrees with II.3.7, where right translation
  satisfies `μ(S h) = δ(h) μ(S)`. For the unipotent radical, Renard's index
  formula
  `δ_P(a) = [a⁻¹ K_N a : K_{1,N}] / [K_N : K_{1,N}] = μ_N(a⁻¹ K_N a) / μ_N(K_N)`
  is the Library's `mod_U(a)⁻¹`. The same holds for the modulus `δ_N(a)` of
  the automorphism `Int(a)` of `N` in the sense of II.3.7.1.

These comparisons are derived here from the displayed formulas; the source
does not state them.

## Source correspondence

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, source ID
`renard-2026-representations-groupes-reductifs-padiques`, file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Section V.5.4, "Calculs de fonctions modulaires", printed pp. 126–127 (PDF
pp. 132–133), was read and visually checked. The modular-function definitions
in II.3.7–II.3.8 (printed pp. 47–48, PDF pp. 53–54) were also read.

- *Proposition. Le groupe G est unimodulaire.* This is conclusion 1. Renard's
  proof uses the Cartan decomposition and Iwahori decompositions of compact
  open subgroups. Neither is a premise here.
- *Lemme.* For `m ∈ M`,
  `δ_{P\G}(m) = δ_G(m)/δ_P(m) = δ_P(m)⁻¹ = δ_N(m)⁻¹ = δ_{N̄}(m)`, and for
  `a ∈ A`, `δ_{P\G}(a) = ∏_{γ∈Σ(P)} |γ(a)^{m_γ+2m_{2γ}}|`. The proof
  establishes `δ_P(a) = δ_N(a) = δ_{N̄}(a)⁻¹` for `a ∈ A` and extends the
  equalities to `m ∈ M` by the Cartan decomposition of `M`. By the
  conventions above, `δ_P(m) = δ_N(m)` on `M` says exactly
  `Δ_P(m) = δ_P(m)⁻¹ = δ_N(m)⁻¹ = mod_U(m)`. This is conclusion 2 restricted
  to `M`.

The Lemma is printed "avec les notations ci-dessus", after a proof that
abbreviates `P = P_∅ = MN`. Its statement and proof nevertheless use `Σ(P)`,
the group `A` and the Iwahori factor `K_M K_N`. The Lean target asserts
the identity for every standard parabolic `parabolic i ν I`, which is the
reading adopted here; a proof must establish it for every `I`. The Lean target
omits the root-product formula and the quotient modulus `δ_{P\G}`.

The supplementary errata for the 2010 edition
(`renard-2010-corrections-complements`, PDF p. 9) correct the 2010 Lemme V.5.4:
all equalities hold for elements of `M` except the last, which needs `A`. The
2026 statement above is already split this way.

### Extension from `M` to all of `P`

The Lean equality holds for every `p` in `P`, whereas the source formula is
stated for `m ∈ M`. Given the source formula, both sides are trivial on `U`:

- `Δ_P` is a continuous homomorphism into the positive reals, so it is trivial
  on every compact subgroup (Renard II.3.7). `U(k)` is a union of compact open
  subgroups, for example the conjugates of `K_N` by the powers of a suitable
  element of `A`. So every `u ∈ U` lies in a compact subgroup of `P` and
  `Δ_P(u) = 1`. The same argument appears in the 2010 errata (PDF
  p. 12): "N étant réunion filtrante de ses sous-groupes ouverts compacts,
  les caractères modulaires sont triviaux sur N".
- For `u ∈ U`, conjugation by `u` is an inner automorphism of `U`, so its
  modulus is the modular function of `U` at `u` (II.3.7.1). `U` is unimodular
  because it is a union of compact open subgroups (II.3.7, Example 3). Hence
  `mod_U(u) = 1`.

Both sides are homomorphisms on `P`, and every `p ∈ P` is `m u` with `m ∈ M`
and `u ∈ U`. Hence `Δ_P(p) = Δ_P(m) = mod_U(m) = mod_U(p)`. So the
all-of-`P` statement is equivalent to the source formula on `M`, given these
trivialities. They are explanation for a proof and are not premises of the
statement. That `U(k)` is a union of compact open subgroups remains a proof
obligation. Continuity of Mathlib's modular character also remains a
formal proof obligation; its file lists continuity as a TODO.

### Sanity check

Take the upper triangular `B = TU` in `SL₂(k)` and `t = diag(c, c⁻¹)`. Then
`t u(x) t⁻¹ = u(c² x)`, so `mod_U(t) = |c|²`. In the coordinates `t(c) u(x)`,
`d^×c dx` is a left Haar measure on `B`, and right translation by `t(c₀)`
scales `x` by `c₀⁻²`. So `Δ_B(t) = |c|²`. Renard's root formula gives
`δ_B(t) = |c|⁻²`, whose inverse is again `|c|²`.

## Intended use

The proof of `RationalNaturalInductionDualityStatement` (task
`2137e0ce-8d32-43f5-b4ed-79824b68585f`) needs this identity. The Library's
normalized induction twists by `HaarModulus.closedHalfCharacter`, whose square
is `closedRestrictCharacter`. The duality pairing of `Ind(σ)` with `Ind(σ̃)`
gives functions transforming under this square. For unimodular `G(k)`, the
quotient integral formula `∫_G f = ∫_{P\G} ∫_P f(p g) dμ_P(p)` defines the
`G(k)`-invariant functional on functions with `φ(p g) = Δ_P(p) φ(g)`; the
orientation follows from the Mathlib convention above. Conclusion 2 equates
the two characters, and conclusion 1 supplies unimodularity. Compactness of `P\G`, also
needed by that proof, is not part of this statement.

The rational-point formulation and translation between conventions are
internal. The Library ledger `notes/renard/chapter-v-structural-inputs.md`
records the source results as item D07, a retained in-book proof obligation.
This statement does not establish the root-product formula, continuity of
the modular character, or assertions about non-standard parabolics.
