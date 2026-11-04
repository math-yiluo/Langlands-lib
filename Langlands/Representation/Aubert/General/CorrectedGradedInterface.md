# Interface data for the surviving graded transitions

Module: `Langlands.Representation.Aubert.General.CorrectedGradedInterface`.

This module holds definitions only; it asserts nothing. It names the explicit
inputs of a conditional (helper) proof of the generic target
`Langlands.Aubert.General.CorrectedFiltration.CorrectedGradedTransitionTarget`
(`CorrectedFiltrationStatements.lean`). That target specializes to the task
target `RationalPointFamily.RationalCorrectedGradedTransitionStatement`. The
intended proof has three parts:

* Part A (support layer). Restrict the functions of `E_J` supported in
  `G_{θ_{i+1}'}` to the cell `P_J m⁻¹ P_I`. This gives a surjection onto the
  actual orbit piece with kernel the functions supported in `G_{θ_i'}`.
* Part B (orbit Jacquet layer). The data `OrbitJacquetData` below.
* Part C (assembly). Compose the maps of A and B and descend through the
  Jacquet exactness `Jacquet.Localization.map_injective_of_smooth`. This gives
  the maps `β_s` of the target, with their surjectivity, kernel and transition
  laws.

Provenance: the declarations are internal interface data for this proof. They
are not definitions from the literature. The mathematics follows the erratum
proof of the graded transitions (pp. 4688–4690, with the Ban–Jantzen
double-coset correction) cited in the target's Markdown. Part A is the
geometric lemma for the open/closed decomposition of the support
(`G_{θ_i'}` open in `G_{θ_{i+1}'}`, with complement one double coset). Part B is
the orbit computation of the Jacquet module of a compactly induced
representation from a single double coset.

## Conventions

* `J = S \ s` is written `Finset.univ \ s`.
* The Weyl element `w` is the `i`-th length-ordered element, and `m` is a lift
  of `w⁻¹` in `N_G(T)`, as in the target. The Library's orbit piece
  `Geometric.orbitPiece (P J) (P I) m` uses the double coset
  `cosetOrbit (P J) (P I) m = P_J m⁻¹ P_I`. It uses the stabilizer
  `orbitStabilizer (P J) (P I) m = P_I ∩ m P_J m⁻¹`, and the stabilizer map
  `q ↦ m⁻¹ q m` into `P_J`. So the cell of `w` in the target's support sets is
  `P_J m⁻¹ P_I`, and the orbit restriction of Part A is
  `f ↦ (q ↦ f(m⁻¹ q))` on `P_I`.
* `K` is a standard index set with `M K = m⁻¹ (M I) m`, recorded by
  `hK : ∀ x, x ∈ M I ↔ m⁻¹ x m ∈ M K` as in the target.

## Declarations

### `inducingObject P M U h E J`

The smooth `P_J`-representation on the actual coinvariants
`E_{U_J} = Jacquet.Localization.Coinvariants E.representation (U J) 1` with the
unnormalized quotient action `p · [v] = [p v]`. It is
`Jacquet.Localization.smoothObject (U J) 1 (P J) …` applied to `E`. The term
`E_J = term … E s` of the complex uses the normalized inducing representation
`inducingRepresentation (h J) (hclosed J) (r_J E)`. Under the unimodularity
hypothesis `hδ J` this has the same underlying action, by the Library theorem
`inducingRepresentation_jacquet_eq`. Part A uses that theorem to move functions
between the two coefficient representations; on functions the move is the
identity. The coefficient of the orbit piece in `OrbitJacquetData` is
`inducingObject` because the orbit piece needs a smooth `P_J`-representation.

### `SurvivingSupportHypotheses P T cs I s i m`

A `Prop` structure with four fields, for the grade `i` of `r_I(E_J)`:

* `isOpen_lower`: `G_{θ_i'} = groupSupport P T cs I s i` is open in `G`;
* `isOpen_upper`: `G_{θ_{i+1}'} = groupSupport P T cs I s (i + 1)` is open in `G`;
* `left_upper`: `G_{θ_{i+1}'}` is stable under left multiplication by `P_J`;
* `sdiff_eq`: `G_{θ_{i+1}'} \ G_{θ_i'} = {p m⁻¹ q | p ∈ P_J, q ∈ P_I}`.

These are the support facts Part A needs to apply the generic open/closed orbit
quotient (`Geometric.OpenOrbitSupportPair`, `smoothQuotientIso`) on
`P_J \ G`. For actual rational points they follow from the Bruhat cell
disjointness and covering, the left `P_J`-invariance of the modified supports,
and the openness of the length-ordered cell unions. Those facts are not in the
Library and are not premises of the task target. Only grades with `w` minimal in
`W_J w W_I` are used; at the other grades `step_succ_eq` already gives
`step (i + 1) = step i`.

### `OrbitJacquetData P M U h hclosed hU T cs I E w m K hK`

A structure (data and laws) for fixed `I`, `E`, `w`, `m`, `K`, `hK`. For every
surviving `J = S \ s` (`K ⊆ J` and `w` minimal in `W_J w W_I`):

* `Θ s hKs hs` is a `ℂ`-linear map from the actual orbit piece
  `c-Ind_{P_I ∩ m P_J m⁻¹}^{P_I}(E_{U_J} ∘ Ad(m⁻¹))`, i.e.
  `(Geometric.orbitPiece (P J) (P I) m).obj (inducingObject … J)`, to
  `Ad(w⁻¹)(r_K E) = (conjugationFunctor m hK).obj (r_K E)`;
* `unipotent_invariant`: `Θ (u · φ) = Θ φ` for `u ∈ U_I`;
* `levi_equivariant`: for `l ∈ M_I`, `δ_{U_I}^{-1/2}(l) · Θ (l · φ)` equals
  the action of `l` on `Θ φ` in `Ad(w⁻¹)(r_K E)`. The factor
  `HaarModulus.closedInverseHalfCharacter (U I) …` is the normalization of the
  actual Jacquet functor `jacquetFunctor (h I) (hclosed I)` along `P_I`;
* `surjective`: `Θ` is surjective;
* `ker_le`: the kernel of `Θ` is contained in the actual `U_I`-relations
  `Jacquet.Localization.relations … ((U I).subgroupOf (P I)) 1` of the orbit
  piece. Together with `unipotent_invariant` (which gives the reverse
  inclusion), the kernel is exactly the span of the `u φ - φ`;
* `transition`: for surviving `s ⊆ t`, if `ψ(q)` is the pointwise coinvariant
  transition `E_{U_J} → E_{U_{J'}}` (`Jacquet.Localization.transitionLinear`) of
  `φ(q)` for all `q ∈ P_I`, then `Θ_t ψ = Θ_s φ`.

The intended construction (Part B) is
`Θ_s φ = ∫_{H_U \ U_I} [φ(u)]_{U_K} du`. Here `H_U = U_I ∩ (P_I ∩ m P_J m⁻¹)`,
and `[·]_{U_K}` is the coinvariant transition `E_{U_J} → E_{U_K}` (`U_J ≤ U_K`
since `K ⊆ J`). Its inputs are not part of this interface: the decomposition of
the stabilizer, the coinvariant identification `(E_{U_J})_{H_U} = E_{U_K}`, the
modulus identity (erratum D07, `δ_I^{-1/2}(l) · c(l) = δ_K^{-1/2}(m⁻¹ l m)`),
and the equality of the stabilizers for surviving `s ⊆ t`.

## Status

Definitions only; nothing is asserted or proved here. The module compiles with
no errors or warnings. Parts A and C (the conditional reduction) and Part B
(a construction of `OrbitJacquetData` from explicit structural hypotheses) are
separate modules that import this one.
