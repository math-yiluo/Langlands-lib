# The operators `π(p)` of Waldspurger, Proposition III.7.1, and Corollary III.7.2

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitPolynomialOperator`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.TraceFamilyScalar` (Worker 249):
  `quotientCharacter`, `quotientCharacter_apply`, `finsuppCharacterSum`, `contragredientRep`,
  `conj_mk_ker`, `hasCompactSupport_kerLiftFun`, `exists_character_comp_eq`,
  `traceFamily_operator_eq_smul` (`π[φ] = P_φ(π) • id` with a chosen `χ₀`) and
  `traceFamily_operator_eval_eq_zero`; through its imports `traceFamily`,
  `IdempotentFamily.operator`, `IdempotentFamily.comp_operator`,
  `exists_compactOpenSubgroup_fixed`, `ext_smoothDual`, `formalDegree`, `formalDegree_pos`,
  `norm_character_eq_one` (`SchurOrthogonality`), `twist`, `twistEquiv`, `twist_one`,
  `twist_twist`, `twist_twist_inv`;
- `Langlands.Representation.Category.Twist` (`equivOfRepresentationEq`);
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.AdmissibleFitting` (Worker 249):
  `fittingRange`, `fittingKernel`, `mem_fittingKernel_iff`, `isCompl_fittingRange_fittingKernel`,
  `bijOn_fittingRange` (the decomposition `V = ⋂ₙ Tⁿ V ⊕ ⋃ₙ Ker Tⁿ` for an intertwiner `T` of an
  admissible representation);
- `Langlands.Representation.Smooth.Admissibility.EmbeddingProof` (`isAdmissible_of_injective`),
  `Langlands.Representation.Unramified.SphericalConstituentExistenceProof`
  (`SphericalExistence.isAdmissible_of_surjective`; through it
  `Langlands.Compact.fixedVectorSurjectivity`: a surjective intertwiner of smooth representations
  is surjective on the vectors fixed by a compact open subgroup; and
  `Langlands.Representation.Smooth.Transfer.SubquotientProof`: `isSmooth_of_injective`,
  `isSmooth_of_surjective`),
  `Langlands.Representation.Smooth.Contragredient.ExactProof`
  (`contragredientMap_surjective_of_injective_of_compact_cofinal`: smooth functionals extend
  from subrepresentations), with `fixedVectorsMap`;
- `Langlands.Representation.Smooth.RenardIrreducibleExistenceProof`
  (`SmoothRep.RenardIrreducibleExistence.exists_irreducible_subquotient`: a nonzero smooth
  representation has an irreducible subquotient), with `SmoothRep.subrepresentation`,
  `SmoothRep.subtype`, `SmoothRep.mkQ`, `SmoothRep.equivOfIso`;
- `Langlands.Representation.Smooth.Factorization.MultiplicityDefinitions`
  (`ProductFactorization.subrepresentationInclusion`, the inclusion of a subrepresentation as an
  intertwining map, and `ProductFactorization.subrepresentationInclusion_injective`);
- through the imports above, `fixedVectors_twist_eq_of_le_ker`
  (`Langlands.Representation.Twist.AdmissibilityProof`: a twist by a character trivial on `H`
  has the same `H`-fixed vectors);
- from Mathlib `AddChar.norm_apply` (characters of a finite group are unitary),
  `pow_card_eq_one`, `linearIndependent_monoidHom` (Dedekind's independence of characters),
  `LinearMap.dualMap_injective_iff`, `Submodule.finrank_lt_finrank_of_lt`,
  `Submodule.finiteDimensional_of_le`, `Finset.card_insert_of_notMem` and `Nat.sSup_mem`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234. The quoted text carries no overline in the printed text (checked on the
rendered PDF pages 39, 41 and 42).

- III.7, printed p. 273 (PDF p. 39): "On note `E₂(G)` l'ensemble des classes de représentations
  admissibles irréductibles de carré intégrable de `G`. Le groupe `Im X(G)` agit sur `E₂(G)` par
  `(χ, ω) ↦ ω ⊗ χ`. Soit `O` une orbite pour cette action. Si l'on choisit un point base
  `ω ∈ O`, on a une bijection `Im X(G)/Stab_{X(G)}(ω) → O`, `χ ↦ ω ⊗ χ`, où
  `Stab_{X(G)}(ω) = {χ ∈ X(G); ω ⊗ χ ≃ ω}` (c'est un groupe fini). On appelle polynôme sur `O`
  une fonction `p : O → ℂ` telle qu'il existe un polynôme `p'` sur `X(G)` de sorte que
  `p(ω ⊗ χ) = p'(χ)` pour tout `χ ∈ Im X(G)`."
- Proposition III.7.1, printed p. 273: "Soient `O ⊂ E₂(G)` une orbite pour l'action de
  `Im X(G)` et `p` un polynôme sur `O`. Pour toute représentation admissible tempérée `(π, V)` de
  `G`, il existe un opérateur `π(p) ∈ End_G V` de sorte que les propriétés suivantes soient
  vérifiées: (i) si `(π₁, V₁)` et `(π₂, V₂)` sont deux représentations admissibles tempérées de
  `G` et `f ∈ Hom_G(V₁, V₂)`, `π₂(p) ∘ f = f ∘ π₁(p)`; (ii) si `π` est irréductible et
  `π ∉ O`, `π(p) = 0`; (iii) si `π ∈ O`, `π(p)` est l'homothétie de rapport `p(π)`."
- Corollary III.7.2, printed p. 275 (PDF p. 41): "Soient `ω ∈ E₂(G)` et `(π, V)` une
  représentation admissible tempérée de `G`. Alors il existe une unique décomposition en somme
  directe: `(π, V) = (π₁, V₁) ⊕ (π₂, V₂)` telle que (i) tous les sous-quotients irréductibles de
  `π₁` sont isomorphes à `ω`; (ii) aucun sous-quotient irréductible de `π₂` n'est isomorphe à
  `ω`."
- Its proof, printed pp. 275–276 (PDF pp. 41–42): "Soit `O` l'orbite de `ω`. Pour `ω' ∈ O`,
  `ω'|_K ≃ ω|_K`. Comme `π` est admissible, l'ensemble `Σ` des `ω' ∈ O` intervenant comme
  sous-quotient de `π` est fini. Soit `p` un polynôme sur `O` s'annulant en tout point de
  `Σ - {ω}` et tel que `p(ω) = 1`. Posons `V₁ = ⋂_{n ∈ ℕ} π(p)ⁿ V`,
  `V₂ = ⋃_{n ∈ ℕ} Ker π(p)ⁿ`. Ces sous-espaces sont invariants par `G`. [...] En faisant varier
  `H`, on obtient `V = V₁ ⊕ V₂`. On déduit de (3) et (4) que l'opérateur `π₁(p)` est bijectif
  tandis que `π₂(p)` est nilpotent. Mais alors `π₁(p)`, resp. `π₂(p)`, agit sur tout
  sous-quotient irréductible de `V₁`, resp. `V₂`, par un scalaire non nul, resp. par `0`. Or
  `ω(p) ≠ 0` et, d'après la définition de `p`, tout sous-quotient irréductible `π'` de `π` pour
  lequel `π'(p) ≠ 0` est isomorphe à `ω`. On en déduit les propriétés (i) et (ii) de l'énoncé."
- End of the proof of Proposition III.7.1, printed p. 275 (PDF p. 41): "Comme `π` est tempérée, `S(π) ⊂ Im X(G)`. On a
  `S(π) ≠ ∅` si et seulement si `π ∈ O`. D'autre part `P_φ|_O` est un polynôme et en faisant
  varier `φ`, on obtient ainsi tous les polynômes sur `O`. Revenons alors au polynôme `p` de
  l'énoncé. On choisit `φ` tel que `P_φ|_O = p` et l'on pose `π(p) = π[φ]`. Les propriétés (ii)
  et (iii) de l'énoncé résultent du calcul ci-dessus. La propriété (i) est immédiate."

## Correspondence and generalizations

- Setting. As in `TraceFamilyScalar`: a surjective `p : G →* Λ` onto a commutative group with
  open kernel in place of `G → G / G¹`, a central subgroup `A` in place of `A_G` with
  `Λ / p(A)` finite, characters of `Λ` (composed with `p`) in place of `X(G)`, the unitary ones
  (`‖χ(λ)‖ = 1` for all `λ`) in place of `Im X(G)`, and the measure compatibility `hcompat`
  with constant `m`.
- The orbit `O` of `ω` is not formed as a set of classes. Membership `π ∈ O` is the existence of
  a unitary `χ₁` with `π ≃ ω ⊗ (χ₁ ∘ p)` (`e` in `orbitPolynomialOperator_eq_smul_of_equiv`), and
  `π ∉ O` is `hnot`: no such `χ` exists.
- A polynomial `p'` on `X(G)` is given by a finitely supported `b : Λ →₀ ℂ`, through
  `p'(χ) = b̂(χ) = Σ_λ b(λ) χ(λ)` (`finsuppCharacterSum b χ`), the regular functions on the
  torus of characters of a lattice being the linear combinations of the evaluations
  `χ ↦ χ(λ)`. That `p'` defines a function `p` on `O` is the hypothesis `hb`: `b̂(χ) = b̂(χ')`
  whenever `χ, χ'` are unitary and `ω ⊗ (χ ∘ p) ≃ ω ⊗ (χ' ∘ p)`; then `p(ω ⊗ χ) = b̂(χ)`.
- `Stab_{X(G)}(ω)` is represented by `orbitStabilizer p A ω`, the characters `η` of the finite
  group `Λ / p(A)` with `ω ⊗ (η ∘ p)⁻¹ ≃ ω`. The comparison with the set of all unramified
  `χ` with `ω ⊗ χ ≃ ω` is not made.
- The source's `φ` with `P_φ|_O = p` is `orbitPolynomialTestFunction … m b = c⁻¹ b` with
  `c = orbitPolynomialConstant … m = m |Q|⁻¹ d(ω)⁻¹ |Stab|`, and `π(p)` is
  `orbitPolynomialOperator … b π = π[φ_b]`.
- (ii) needs that the central character `cπ` of `π` on `A` is unitary (`hπu`); in the source
  this comes from the temperedness of `π` ("Comme `π` est tempérée, `S(π) ⊂ Im X(G)`").
- (iii) holds for every irreducible admissible tempered `π` with `π ≃ ω ⊗ (χ₁ ∘ p)`; the source's
  `p(π)` is `b̂(χ₁)`. It needs `m ≠ 0` (`hm0`), so that `c ≠ 0`.
- Corollary III.7.2. A subquotient of `π` is given by an injective intertwiner `i : τ → π` and a
  surjective intertwiner `q : τ → π'`; it is a subquotient of `V₁` (resp. `V₂`) when the image
  of `i` lies in `V₁` (resp. `V₂`). Irreducibility is `π'.IsIrreducible`, isomorphism is
  `Nonempty (π'.Equiv ω)`. In `exists_isCompl_orbitIsotypic`, a finite set `F` of
  characters `χ` with `ω ⊗ (χ ∘ p) ≄ ω` stands for `Σ - {ω}`, and the polynomial vanishes on it
  (`exists_orbit_separating`). Accordingly (i) states that every irreducible subquotient of `V₁`
  is equivalent to some `ω ⊗ (χ ∘ p)`, `χ` unitary, and to no `ω ⊗ (χ₀ ∘ p)` with `χ₀ ∈ F`; when
  `F` meets every class of `Σ - {ω}`, this is the source's (i). To apply Proposition III.7.1 to
  an irreducible subquotient `π'`, (i) assumes the central character of `π'` on `A` and its
  unitarity, and both (i) and (ii) assume the integrability hypothesis `hint` for `π'` (all of
  them consequences of the temperedness of `π` in the source); admissibility and temperedness of
  the subquotients are proved (`hasTemperedCoefficients_of_injective`,
  `hasTemperedCoefficients_of_surjective`). In the source form
  `exists_orbitIsotypic_decomposition`, the covering of `Σ - {ω}` by `F` is the hypothesis
  `hcover` (every irreducible subquotient of `π` equivalent to some `ω ⊗ (χ ∘ p)`, `χ` unitary, is
  equivalent to `ω` or to some `ω ⊗ (χ₀ ∘ p)` with `χ₀ ∈ F`) and the hypotheses of
  Proposition III.7.1 for all irreducible subquotients of `π` are the hypothesis `hsub`; (i) then
  reads "equivalent to `ω`". The uniqueness `orbitIsotypic_decomposition_unique` is proved under
  the same two hypotheses, by comparing any decomposition with properties (i) and (ii) with the
  Fitting decomposition of `π(p)` (`eq_fitting_of_orbitIsotypic`). The source's proof derives
  only (i) and (ii) for the Fitting decomposition and gives no argument for uniqueness; the
  argument of `eq_fitting_of_orbitIsotypic` is derived.
- The finiteness of `Σ`. The source argues "Pour `ω' ∈ O`, `ω'|_K ≃ ω|_K`. Comme `π` est
  admissible, l'ensemble `Σ` [...] est fini." Here `exists_orbit_covering` proves `hcover` for
  some finite `F` from `hsub` alone. The counterpart of `ω'|_K ≃ ω|_K` is that every twist
  `ω ⊗ (χ ∘ p)` has the same vectors fixed by a compact open `H ≤ ker p`
  (`fixedVectors_twist_eq_of_le_ker`), and admissibility enters through `dim V^H < ∞`: pairwise
  inequivalent twists occurring in `π` number at most `dim V^H`
  (`card_le_finrank_of_hasSubquotientIn`). This counting argument is derived; it uses the
  operators `π(p)` themselves. `existsUnique_orbitIsotypic_decomposition` is then Corollary
  III.7.2 (existence and uniqueness) under `hsub` only.
- Derived results, not statements of the paper: the interpolation and stabilizer lemmas
  `exists_finsuppCharacterSum_eq`, `finsuppTwist`, `finsuppCharacterSum_add`,
  `finsuppCharacterSum_single`, `finsuppCharacterSum_sum`, `finsuppCharacterSum_finsuppTwist`,
  `quotientCharacter_add`, `quotientCharacter_neg`, `quotientCharacter_injective`,
  `exists_quotientCharacter_eq`, `mem_orbitStabilizer_iff`, `nonempty_twist_inv_equiv_iff`,
  `nonempty_twist_mul_equiv_self`, `add_mem_orbitStabilizer`, `neg_mem_orbitStabilizer`,
  `exists_mem_orbitStabilizer_of_equiv`, `finsuppCharacterSum_eq_of_equiv`,
  `pow_apply_of_comm`, `exists_irreducible_subquotient_le`,
  `eq_of_le_of_isCompl`, `exists_orbit_separating_of_covering`, `eq_fitting_of_orbitIsotypic`,
  `HasSubquotientIn`, `exists_ne_zero_fixed_of_hasSubquotientIn`,
  `hasSubquotientIn_fitting`, `card_le_finrank_of_hasSubquotientIn`, `exists_orbit_covering`,
  the twist lemmas
  `nonempty_twist_equiv_iff`, `nonempty_twist_mul_equiv`, `nonempty_equiv_twist_of_twist_inv`,
  the unitarity lemmas `norm_quotientCharacter`, `norm_eq_one_of_norm_eq_one_on`,
  `finsuppCharacterSum_smul`, `one_mem_orbitStabilizer` and `orbitPolynomialConstant_ne_zero`.

## Scope and hypotheses

The section `Operator` has the variables of `TraceFamilyScalar`'s main section:
`G : Type u` with `[Group G] [TopologicalSpace G] [IsTopologicalGroup G]
[Nonempty (CompactOpenSubgroup G)]`, weights `Ξ σ : G → ℝ`, `[MeasurableSpace G] [BorelSpace G]
[SecondCountableTopology G]`, `μ` with `[μ.IsHaarMeasure] [SFinite μ] [μ.IsMulRightInvariant]`,
a subgroup `K` with `[CompactSpace K]`, a commutative group `Λ` and `p : G →* Λ`, a normal
subgroup `A` with `hA : A ≤ Subgroup.center G`, `[MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]`,
`ν` with `[ν.IsHaarMeasure] [ν.IsInvInvariant]`, `hcof` (compact open subgroups are cofinal), a
representation `ω : Representation ℂ G W` (`W : Type v`) with a character `cω : A →* ℂˣ` and
`hω : ∀ a x, ω a x = cω a • x`, `hsq : IsSquareIntegrableModCentralSubgroup A hA ω ν`,
`hiω : ω.IsIrreducible`, and `[Fintype (Λ ⧸ A.map p)]`. Representations `π` act on
`V : Type w`.

- `orbitPolynomialOperator` and `orbitPolynomialOperator_comp` take
  `hN : IsOpen (p.ker : Set G)`, `hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker`,
  `hc : ConvolutionWeights μ K Ξ σ`, `ht : TranslationWeights Ξ σ`, `hw : L2Weights μ Ξ σ`,
  `hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation`,
  `m : ℝ≥0∞`, `b : Λ →₀ ℂ`, and, for each representation, `IsAdmissible` and
  `HasTemperedCoefficients Ξ σ`.
- `orbitPolynomialOperator_eq_smul_of_equiv` takes in addition `hp : Function.Surjective p`,
  `hm : m ≠ ∞`, `hm0 : m ≠ 0`, `hcompat`, `hb`, `hiπ : π.IsIrreducible`, the integrability
  hypothesis `hint` of `TraceFamilyScalar` for `π`, a unitary `χ₁ : Λ →* ℂˣ` (`hχ₁`) and
  `e : π.Equiv (twist (χ₁.comp p) ω)`.
- `orbitPolynomialOperator_eq_zero` takes `hp`, `hm`, `hcompat`, `hiπ`, a character
  `cπ : A →* ℂˣ` with `hπc : ∀ a x, π a x = cπ a • x` and `hπu : ∀ a, ‖cπ a‖ = 1`, `hint`, and
  `hnot : ∀ χ : Λ →* ℂˣ, (∀ l, ‖χ l‖ = 1) → IsEmpty (π.Equiv (twist (χ.comp p) ω))`.

- `exists_equiv_twist_of_subquotient_fittingRange` and
  `isEmpty_equiv_of_subquotient_fittingKernel` take the hypotheses of
  `orbitPolynomialOperator_eq_smul_of_equiv` except `hb`, `π` irreducible and `e`, together with a
  polynomial `b` invariant under the stabilizer (`hbSt`), for the second also `b̂(1) = 1`
  (`hb1`), the subquotient data `i`, `hi`, `hiR` (resp. `hiK`), `q`, `hq`,
  `hiπ' : π'.IsIrreducible`, `hint'` for `π'`, and for the first a character `cπ'` with
  `hπ'c` and `hπ'u`. `exists_isCompl_orbitIsotypic` takes `hp`, `hN`, `hHN`, `hm`, `hm0`,
  `hcompat`, `hc`, `ht`, `hw`, `hD`, `F` with `hF : ∀ χ ∈ F, IsEmpty ((twist (χ.comp p) ω).Equiv ω)`
  and an admissible tempered `π`; the subquotient hypotheses appear inside its conclusion. All
  subquotients act on types in the universe of `V`.
- `exists_orbitIsotypic_decomposition` and `orbitIsotypic_decomposition_unique` take the
  hypotheses of `exists_isCompl_orbitIsotypic` together with `hcover` and `hsub` (for every
  irreducible subquotient `π'` of `π`: a character `cπ'` of `A` by which `A` acts, unitary, and the
  integrability hypothesis `hint` for `π'`); the uniqueness also takes two decompositions with
  properties (i), (ii). `eq_fitting_of_orbitIsotypic` takes, instead of `F`, a polynomial `b` with
  `hbSt`, `hb1` and the detection property `hO` (an irreducible subquotient of `π` equivalent to
  `ω ⊗ (χ ∘ p)` with `χ` unitary and `b̂(χ) ≠ 0` is equivalent to `ω`), `hsub`, and one
  decomposition with (i), (ii). `exists_orbit_separating_of_covering` takes only `F`, `hF` and
  `hcover` (with `hω`, `hiω`).
- `HasSubquotientIn ρ W' σ'` and `exists_ne_zero_fixed_of_hasSubquotientIn` (`ρ` smooth, `H` an
  open subgroup with `IsCompact H`, `u ≠ 0` fixed by `H` under `σ'`) are stated for an arbitrary
  topological group `G`, `V : Type w`, a subspace `W'` and `σ'` on any type.
- `hasSubquotientIn_fitting` takes the hypotheses of `exists_equiv_twist_of_subquotient_fittingRange`
  up to the subquotient data, with `hsub` instead, a subspace `W'`, a unitary `χ` and
  `HasSubquotientIn π W' (ω ⊗ (χ ∘ p))`. `card_le_finrank_of_hasSubquotientIn` takes `hp`, `hN`,
  `hHN`, `hm`, `hm0`, `hcompat`, `hc`, `ht`, `hw`, `hD`, an admissible tempered `π`, `hsub`, a
  compact open `H` with a nonzero `u ∈ ω^H`, a finite set `F` of unitary characters (`hFu`) with
  pairwise inequivalent twists (`hFi`), and `W'` with `HasSubquotientIn π W' (ω ⊗ (χ ∘ p))` for
  `χ ∈ F`. `exists_orbit_covering` and `existsUnique_orbitIsotypic_decomposition` take the
  hypotheses of `card_le_finrank_of_hasSubquotientIn` up to `hsub`.

## Definitions

- `orbitStabilizer p A ω : Finset (AddChar (Additive (Λ ⧸ A.map p)) ℂ)`, the `η` with
  `Nonempty ((twist ((quotientCharacter (A.map p) η).comp p)⁻¹ ω).Equiv ω)`.
- `orbitPolynomialConstant … m : ℂ`, `m.toReal * |Λ ⧸ A.map p|⁻¹ * d(ω)⁻¹ * |orbitStabilizer|`,
  with `d(ω) = formalDegree A hA ν hω hcof hsq hiω`.
- `orbitPolynomialTestFunction … m b = (orbitPolynomialConstant … m)⁻¹ • b`.
- `finsuppTwist s b`, the coefficients of `b` multiplied by the character `s`.
- `HasSubquotientIn ρ W' σ'`: some irreducible subquotient of `ρ` lying in the subspace `W'` (an
  injective `i : τ → ρ` with image in `W'` and a surjective `q : τ → π'`, `π'` irreducible, all on
  types in the universe of `V`) is equivalent to `σ'`.
- `orbitPolynomialOperator … m b π hπa hT : π.IntertwiningMap π`, the operator
  `(traceFamily (contragredientRep ω) … (hasCompactSupport_kerLiftFun p hN φ_b)).operator hw hπa hT`
  with `φ_b = orbitPolynomialTestFunction … m b`; Waldspurger's `π(p) = π[φ]`.

## Results

- `nonempty_twist_equiv_iff`: if `π ≃ ω ⊗ (χ₁ ∘ p)`, then `π ⊗ ((χ₁ θ) ∘ p)⁻¹ ≃ ω` iff
  `ω ⊗ (θ ∘ p)⁻¹ ≃ ω`.
- `nonempty_twist_mul_equiv`: `ω ⊗ (θ ∘ p)⁻¹ ≃ ω` implies
  `ω ⊗ ((χ₁ θ) ∘ p) ≃ ω ⊗ (χ₁ ∘ p)`.
- `nonempty_equiv_twist_of_twist_inv`: `π ⊗ (χ ∘ p)⁻¹ ≃ ω` implies `π ≃ ω ⊗ (χ ∘ p)`.
- `norm_quotientCharacter`: characters of the finite group `Λ / B` are unitary;
  `norm_eq_one_of_norm_eq_one_on`: a character of `Λ` unitary on `B` is unitary when `Λ / B` is
  finite; `finsuppCharacterSum_smul`: `(c • φ)^ = c φ̂`.
- `one_mem_orbitStabilizer`, `orbitPolynomialConstant_ne_zero` (for `m ≠ 0, ∞`).
- `orbitPolynomialOperator_comp` (**Proposition III.7.1 (i)**):
  `T ∘ π₁(p) = π₂(p) ∘ T` for every intertwiner `T : π₁ → π₂` of admissible tempered
  representations.
- `orbitPolynomialOperator_eq_smul_of_equiv` (**Proposition III.7.1 (iii)**): if
  `π ≃ ω ⊗ (χ₁ ∘ p)` with `χ₁` unitary, then `π(p) v = b̂(χ₁) v` for every `v`.
- `orbitPolynomialOperator_eq_zero` (**Proposition III.7.1 (ii)**): if `π` is irreducible with
  unitary central character on `A` and `π ≄ ω ⊗ (χ ∘ p)` for every unitary `χ`, then
  `π(p) v = 0` for every `v`.

- `exists_finsuppCharacterSum_eq`: polynomials interpolate arbitrary values on a finite set of
  characters.
- `exists_mem_orbitStabilizer_of_equiv`: if `ω ⊗ (χ ∘ p) ≃ ω ⊗ (χ' ∘ p)`, then `χ' = χ η` with
  `η ∈ orbitStabilizer`; `finsuppCharacterSum_eq_of_equiv`: a polynomial invariant under the
  stabilizer is constant on the classes of the orbit (it satisfies `hb`).
- `exists_orbit_separating` (**the polynomial of the proof of Corollary III.7.2**): for a finite
  `F` of characters `χ` with `ω ⊗ (χ ∘ p) ≄ ω`, a `b` invariant under the stabilizer with
  `b̂(1) = 1` and `b̂ = 0` on `F`.
- `hasTemperedCoefficients_of_injective`, `hasTemperedCoefficients_of_surjective`:
  subrepresentations and quotients of a representation with tempered coefficients have tempered
  coefficients.
- `exists_equiv_twist_of_subquotient_fittingRange`: an irreducible subquotient of
  `V₁ = fittingRange π(p)` is equivalent to some `ω ⊗ (χ ∘ p)`, `χ` unitary, with `b̂(χ) ≠ 0`.
- `isEmpty_equiv_of_subquotient_fittingKernel`: if `b̂(1) = 1`, no irreducible subquotient of
  `V₂ = fittingKernel π(p)` is equivalent to `ω`.
- `exists_isCompl_orbitIsotypic` (**Corollary III.7.2, existence**): subrepresentations
  `V₁, V₂` of `π` with `V₁ ⊕ V₂ = V` (`IsCompl` of the submodules) such that (i) every
  irreducible subquotient of `V₁` (with its hypotheses) is equivalent to some `ω ⊗ (χ ∘ p)`,
  `χ` unitary, and to no `ω ⊗ (χ₀ ∘ p)` with `χ₀ ∈ F`, and (ii) no irreducible subquotient of
  `V₂` (with `hint'`) is equivalent to `ω`.

- `exists_irreducible_subquotient_le`: a nonzero subrepresentation `W` of a smooth `ρ` contains an
  irreducible subquotient (`i : C → ρ` injective with image in `W`, `q : C → B` surjective, `B`
  irreducible), from `SmoothRep.RenardIrreducibleExistence.exists_irreducible_subquotient` (the
  first assertion at the end of Renard III.1.4, proved in the Library).
- `eq_of_le_of_isCompl`: in the submodule lattice, `a ≤ c`, `b ≤ d`, `a ⊕ b = c ⊕ d` force `a = c`,
  `b = d`.
- `exists_orbit_separating_of_covering`: under `hcover`, the polynomial of
  `exists_orbit_separating` has the detection property `hO`.
- `eq_fitting_of_orbitIsotypic`: a decomposition with (i) and (ii) is the Fitting decomposition
  of `π(p)`.
- `exists_orbitIsotypic_decomposition` (**Corollary III.7.2, existence, source form**): under
  `hcover` and `hsub`, `V = V₁ ⊕ V₂` with every irreducible subquotient of `V₁` equivalent to `ω`
  and none of `V₂`.
- `orbitIsotypic_decomposition_unique` (**Corollary III.7.2, uniqueness**): under `hcover` and
  `hsub`, two such decompositions coincide.
- `exists_ne_zero_fixed_of_hasSubquotientIn`: if `HasSubquotientIn ρ W' σ'` and `σ'` has a
  nonzero `H`-fixed vector, then `W'` contains a nonzero `H`-fixed vector of `ρ`.
- `hasSubquotientIn_fitting`: if `HasSubquotientIn π W' (ω ⊗ (χ ∘ p))` with `χ` unitary and `b`
  invariant under the stabilizer, then `HasSubquotientIn π (W' ∩ V₁) (ω ⊗ (χ ∘ p))` if
  `b̂(χ) ≠ 0` and `HasSubquotientIn π (W' ∩ V₂) (ω ⊗ (χ ∘ p))` if `b̂(χ) = 0`, with `V₁`, `V₂` the
  Fitting range and kernel of `π(p)`.
- `card_le_finrank_of_hasSubquotientIn`: `|F| ≤ dim (W' ∩ V^H)`.
- `exists_orbit_covering` (**finiteness of `Σ`**): a finite `F` with `hF` and `hcover`.
- `existsUnique_orbitIsotypic_decomposition` (**Corollary III.7.2**): under `hsub`, there are
  subrepresentations `V₁`, `V₂` with `V = V₁ ⊕ V₂`, (i) and (ii), and every other pair with these
  properties equals `(V₁, V₂)`.

## Proof notes

1. (i) is `IdempotentFamily.comp_operator`.
2. (iii): the central character of `π` is `cπ = (χ₁ ∘ p) cω`, read off through `e`.
   `traceFamily_operator_eq_smul` with `χ₀ = χ₁` gives `π[φ_b] = m |Q|⁻¹ Σ_η c_η • id`. By
   `nonempty_twist_equiv_iff`, the condition in `c_η` is `η ∈ orbitStabilizer`, and then
   `φ̂_b(χ₁ η) = c⁻¹ b̂(χ₁ η) = c⁻¹ b̂(χ₁)` by `hb` (`χ₁ η` is unitary by
   `norm_quotientCharacter`, and `ω ⊗ (χ₁ η ∘ p) ≃ ω ⊗ (χ₁ ∘ p)` by `nonempty_twist_mul_equiv`).
   The sum is `|Stab| d(ω)⁻¹ c⁻¹ b̂(χ₁)` and the scalar is `c c⁻¹ b̂(χ₁) = b̂(χ₁)`.
3. (ii): if `cπ ≠ cω` at some `a ∈ A ∩ ker p`, `traceFamily_operator_eval_eq_zero` and
   `ext_smoothDual` give `π(p) = 0`. Otherwise `exists_character_comp_eq` gives `χ₀` with
   `χ₀(p(a)) cω(a) = cπ(a)`; `χ₀` is unitary on `p(A)` (`hπu`, `norm_character_eq_one`), hence
   unitary (`norm_eq_one_of_norm_eq_one_on`), and every `χ₀ η` is unitary. A nonzero term of
   `traceFamily_operator_eq_smul` would give `π ≃ ω ⊗ (χ₀ η ∘ p)`
   (`nonempty_equiv_twist_of_twist_inv`), contradicting `hnot`.
4. `exists_finsuppCharacterSum_eq`: the evaluation map `b ↦ (b̂(χ))_{χ ∈ S}` is surjective since
   its dual map is injective: a linear form `y` killing its range gives
   `Σ_χ y_χ χ(λ) = 0` for all `λ`, hence `y = 0` by `linearIndependent_monoidHom`.
5. `exists_orbit_separating`: interpolate `1` on the stabilizer characters `T` and `0` on
   `F · T` (disjoint from `T` by `hF` and the subgroup property of the stabilizer), then average
   `finsuppTwist` over the stabilizer; the average is stabilizer-invariant (reindexing
   `η ↦ η₀ + η`), equal to `1` at `1` and `0` on `F`.
6. `exists_mem_orbitStabilizer_of_equiv`: `ω ≃ ω ⊗ (θ ∘ p)` for `θ = χ⁻¹ χ'`; comparing the
   actions of `a ∈ A` on a nonzero vector gives `θ(p(a)) = 1`, so `θ` comes from a character of
   `Λ / p(A)` (`exists_quotientCharacter_eq`) lying in the stabilizer.
7. `exists_equiv_twist_of_subquotient_fittingRange`: `τ` and `π'` are admissible with tempered
   coefficients; by (i), `i ∘ τ(p) = π(p) ∘ i` and `q ∘ τ(p) = π'(p) ∘ q`. `π(p)` is injective on
   `V₁` (`bijOn_fittingRange`), so `τ(p)` is injective, hence bijective on each
   finite-dimensional `X^H`, hence surjective, and `π'(p) ≠ 0`. By (iii) and (ii) of
   Proposition III.7.1, `π'(p)` is `b̂(χ)` if `π' ≃ ω ⊗ (χ ∘ p)` with `χ` unitary and `0` otherwise;
   so the first case holds with `b̂(χ) ≠ 0`.
8. `isEmpty_equiv_of_subquotient_fittingKernel`: if `π' ≃ ω`, then `π'(p) = b̂(1) = 1` by (iii).
   For `x` with `q(x) ≠ 0`, some `π(p)ⁿ` kills `i(x)` (`mem_fittingKernel_iff`), hence
   `τ(p)ⁿ x = 0` and `q(x) = π'(p)ⁿ q(x) = q(τ(p)ⁿ x) = 0` (`pow_apply_of_comm`), a contradiction.
9. `exists_isCompl_orbitIsotypic`: `b` from `exists_orbit_separating`, `V₁`, `V₂` the Fitting
   range and kernel of `π(p) = orbitPolynomialOperator … b π` (`isCompl_fittingRange_fittingKernel`);
   (i) follows from step 7 and `b̂ = 0` on `F` (with `finsuppCharacterSum_eq_of_equiv`), (ii) from
   step 8.
10. `exists_orbitIsotypic_decomposition`: `exists_isCompl_orbitIsotypic`, with `hsub` supplying
    the hypotheses on the subquotients and `hcover` excluding the classes of `F`.
11. `eq_fitting_of_orbitIsotypic`: let `T = π(p)`. On `V₁` (an admissible tempered
    subrepresentation, with operator `T₁ = V₁(p)` intertwined with `T` by the inclusion), `T₁` is
    injective: otherwise its kernel, a nonzero subrepresentation, contains an irreducible
    subquotient `B` (`exists_irreducible_subquotient_le`), which is a subquotient of `V₁`, hence
    equivalent to `ω`, so `B(p) = b̂(1) = 1`; but `B(p)` is induced by the zero map on the kernel,
    a contradiction. So the Fitting kernel of `T₁` is `0`, its Fitting range is `V₁`, and
    `V₁ ≤ fittingRange T`. On `V₂`, the Fitting range of `T₂ = V₂(p)` is `0`: otherwise it contains
    an irreducible subquotient `B`, a subquotient of `V₂` lying in `fittingRange T`, so by step 7
    and `hO` equivalent to `ω`, contradicting (ii). So `V₂ ≤ fittingKernel T`, and
    `eq_of_le_of_isCompl` gives equality.
12. `orbitIsotypic_decomposition_unique`: both decompositions equal the Fitting decomposition of
    `π(p)` for the polynomial of `exists_orbit_separating_of_covering`.
13. `exists_ne_zero_fixed_of_hasSubquotientIn`: transport the fixed vector to `π'` along the
    equivalence, lift it to an `H`-fixed `y` of `τ` (`Langlands.Compact.fixedVectorSurjectivity`;
    `τ` and `π'` are smooth by `isSmooth_of_injective`, `isSmooth_of_surjective`), and take
    `i(y)`.
14. `hasSubquotientIn_fitting`: let `(τ, i, q, π')` be the subquotient. `τ`, `π'` are admissible
    with tempered coefficients, `π'(p) = b̂(χ)` by Proposition III.7.1 (iii) (with `hint` from
    `hsub`), and `i`, `q` intertwine `τ(p)` with `π(p)`, `π'(p)`. Write `x = r + k` in the Fitting
    decomposition of `τ(p)`. If `b̂(χ) ≠ 0`, then `q(k) = 0` (`b̂(χ)ⁿ q(k) = q(τ(p)ⁿ k) = 0`), so
    `q` restricted to the Fitting range `τ₁` of `τ(p)` is surjective, and `i(τ₁)` lies in the
    Fitting range of `π(p)` (`mem_fittingRange_iff`). If `b̂(χ) = 0`, then `q(r) = 0` (`r = τ(p) y`,
    `q(r) = b̂(χ) q(y)`), so `q` restricted to the Fitting kernel `τ₂` is surjective, and `i(τ₂)`
    lies in the Fitting kernel of `π(p)`.
15. `card_le_finrank_of_hasSubquotientIn`: induction on `F`, generalizing `W'`. For
    `F ∪ {χ₁}`, `exists_orbit_separating` applied to `{χ χ₁⁻¹ : χ ∈ F}` (whose twists are not
    equivalent to `ω` since `hFi`) gives `b₀`; `b = finsuppTwist χ₁⁻¹ b₀` has `b̂(χ) = b̂₀(χ χ₁⁻¹)`,
    so it is invariant under the stabilizer, `b̂(χ₁) = 1` and `b̂ = 0` on `F`. By step 14, `ω ⊗ χ₁`
    occurs in `W' ∩ V₁`, so by step 13 (with `fixedVectors_twist_eq_of_le_ker` and `H ≤ ker p`) there is
    a nonzero `x ∈ W' ∩ V₁ ∩ V^H`; and every `χ ∈ F` occurs in `W' ∩ V₂`, so the induction
    hypothesis bounds `|F|` by `dim (W' ∩ V₂ ∩ V^H)`. Since `V₁ ∩ V₂ = 0`, `x ∉ W' ∩ V₂ ∩ V^H`,
    which is therefore a proper subspace of the finite-dimensional `W' ∩ V^H`
    (`Submodule.finrank_lt_finrank_of_lt`).
16. `exists_orbit_covering`: `H` is a compact open subgroup fixing a nonzero vector of `ω`
    (`exists_compactOpenSubgroup_fixed`, `ω` admissible by `hsq`). The sizes of the finite sets
    `F` of unitary characters with pairwise inequivalent twists, none equivalent to `ω`, all
    occurring in `π`, are bounded by `dim V^H` (step 15); take `F` of maximal size
    (`Nat.sSup_mem`). If an irreducible subquotient equivalent to `ω ⊗ (χ ∘ p)` were equivalent
    neither to `ω` nor to a twist by an element of `F`, then `F ∪ {χ}` would be a larger such
    set.
17. `existsUnique_orbitIsotypic_decomposition`: `exists_orbitIsotypic_decomposition` and
    `orbitIsotypic_decomposition_unique` with the `F` of step 16.
