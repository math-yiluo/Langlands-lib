# Renard's compact-support description of `F̃^{<1̄}_{PQ}`: proof

Author: Worker 48. Module
`Langlands.Representation.Intertwining.PQBoundaryVanishingCompactSupportProof`, namespace
`Langlands.Aubert.General.RepresentedParabolic`. Universe parameters `u, v`.

This module proves `PQBoundaryVanishingCompactSupportStatement` (module
`Langlands.Representation.Intertwining.PQIntertwiningCompositionReduction`, unchanged)
unconditionally. That statement is the first of the four inputs of the Library reduction of
Renard VII.3.5 (i) (`pqIntertwiningComposition_of_reductions`). The proved theorem is
`pqBoundaryVanishingCompactSupport : PQBoundaryVanishingCompactSupportStatement.{u, v}`.

The module contains:

- `isOpen_setOf_mem_of_openSubgroup` and `IsSemidirectDecomposition.eq_one_of_mem_of_mem`, two
  small lemmas;
- `boundaryVanishing_iff_compactSupport`, an abstract topological theorem about a group `Γ` and
  subgroups `P, Q, V`;
- `pointImage_radical_eq_mul`, Renard's decomposition `U = (U ∩ N)(U ∩ N̄)` on rational points
  over a nonarchimedean local field;
- `pqBoundaryVanishingCompactSupport`, the target theorem.

None of them has a hypothesis that is still open in the Library.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026. Literature ID `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

- VII.3.4, proof, printed p.236 / PDF p.242. Renard writes the morphism `F̃^{<1̄}_{PQ} → E`,
  `f ↦ ∫_{U∩N\U} f(u) dν(u) = ∫_{U∩N̄} f(u) du`. He says that the equality of the two integrals
  "provient de la décomposition `U = (U ∩ N)(U ∩ N̄)`". He also says the integrals converge
  because `Supp(f) ∩ PQ` is compact modulo `P` for `f ∈ F̃^{<1̄}_{PQ}`, "donc `Supp(f|_U)` est
  compact modulo `P ∩ U = N ∩ U`". `pointImage_radical_eq_mul` is this decomposition on
  rational points.
- VII.3.5, proof of (i), printed p.239 / PDF p.245. For `P₁, P₃`, Renard characterizes
  `F̃^{<1̄}_{P₁P₃}(E)` as the `f ∈ i_{P₁}^G(E)` such that `Supp f ∩ (N̄₁ ∩ N₃)` is compact. He
  justifies this by the map `N̄₁ ∩ N₃ → P₁\P₁P₃` being a homeomorphism.
  `PQBoundaryVanishingCompactSupportStatement` is this characterization for a general pair
  `(P, Q)` with common Levi `M`.

The proof below does not use that homeomorphism. It uses only the set inclusion `Q ⊆ P V`,
where `V = N̄(F) ∩ U(F)`, which follows from the decomposition of `U`. The topology comes from
the Library's orbit homeomorphism `Geometric.cosetOrbitHomeomorph` (a Baire category argument)
and from compactness of `P(F)\G(F)`.

## Small lemmas

- `isOpen_setOf_mem_of_openSubgroup`: let `Γ` be a topological group, `K₀` an open subgroup,
  and `φ : Γ → X` a function with `φ(xk) = φ(x)` for `k ∈ K₀`. Then `{x | φ(x) ∈ s}` is open for
  every set `s ⊆ X`. Each `x` in it has the neighbourhood `x K₀` inside it.
- `IsSemidirectDecomposition.eq_one_of_mem_of_mem`: if `P = M ⋉ U` is a semidirect
  decomposition (`IsSemidirectDecomposition P M U`), then `M ∩ U = 1`. The Levi projection is
  the identity on `M` and is trivial exactly on `U`.

## The abstract theorem `boundaryVanishing_iff_compactSupport`

Setting: a locally compact, σ-compact topological group `Γ`, and subgroups `P, Q, V` with:

- `P` and `V` closed;
- `P\Γ` compact (`CompactSpace (Induction.LeftQuotient P)`);
- the orbit `P\PQ` of the identity coset under `Q` locally closed in `P\Γ`
  (`IsLocallyClosed (Geometric.cosetOrbit P Q 1)`);
- `V ≤ Q`, `V ∩ P = 1`, and `Q ⊆ P V`, stated as: for every `x ∈ Q` there is `v ∈ V` with
  `x v⁻¹ ∈ P`.

Let `φ : Γ → X` be a function to a type with zero such that:

- its zero set is left `P`-invariant: `φ(x) = 0` implies `φ(px) = 0` for `p ∈ P`;
- `φ` is right-invariant under some open subgroup `K₀`.

Conclusion: `φ` vanishes on `closure(PQ) \ PQ` if and only if there is a compact `K ⊆ V` with
`φ(v) = 0` for all `v ∈ V \ K`. Here `PQ` is written as `DoubleCoset.quotToDoubleCoset P Q`
of the class of `1`.

Proof. Let `S = {φ ≠ 0}`. It is open and closed by `isOpen_setOf_mem_of_openSubgroup`.
Let `π : Γ → P\Γ` be the quotient map.

Forward direction. Assume `φ = 0` on `closure(PQ) \ PQ`.

1. `Z = closure(PQ) ∩ S` is left `P`-invariant, because `closure(PQ)` and `S` are. So
   `π⁻¹(π(Z)) = Z`, and `π(Z)` is closed because `π` is a quotient map. Since `P\Γ` is compact,
   `π(Z)` is compact.
2. `Z ⊆ PQ` by the hypothesis. Hence `π(Z)` lies in the `Q`-orbit of the identity coset. By
   `Q ⊆ PV` the `Q`-orbit equals the `V`-orbit, which is therefore also locally closed.
3. `Geometric.cosetOrbitHomeomorph P V 1` is a homeomorphism from `V/Stab` onto the `V`-orbit,
   where `Stab = {v ∈ V | v ∈ P}`. `Stab` is trivial because `V ∩ P = 1`, so
   `Quotient.lift id` is a continuous map `V/Stab → V`.
4. The preimage of `π(Z)` in the orbit is compact. Its image in `V` under the inverse
   homeomorphism followed by `Quotient.lift id` is the required compact `K`. If `v ∈ V` has
   `φ(v) ≠ 0`, then `v ∈ Z`, because `v ∈ PQ ⊆ closure(PQ)`. The identity
   `Geometric.cosetOrbitHomeomorph_symm_map` then shows `v ∈ K`.

Reverse direction. Assume `φ = 0` on `V \ K` with `K` compact, and let
`x ∈ closure(PQ) \ PQ` with `φ(x) ≠ 0`.

1. `C = P K` is closed, as the product of a closed set and a compact set. It lies in `PQ`
   because `K ⊆ V ⊆ Q`, so `x ∉ C`.
2. `S ∩ Cᶜ` is an open neighbourhood of `x`, so it meets `PQ` in some `y = pq`.
3. Write `q = (q b⁻¹) b` with `b ∈ V` and `q b⁻¹ ∈ P`. The zero set of `φ` is left
   `P`-invariant and `φ(y) ≠ 0`, so `φ(b) ≠ 0` and therefore `b ∈ K`.
4. Then `y = (p q b⁻¹) b ∈ P K = C`, a contradiction.

## The decomposition `pointImage_radical_eq_mul`

The data: a nonarchimedean local field `k` (`[ValuativeRel k] [TopologicalSpace k]
[IsNonarchimedeanLocalField k]`), a connected reductive group scheme `G` over `k`, and three
represented parabolic subgroups with a common Levi `M`, each given by a Levi subgroup and a
geometric unipotent radical:

- `P = MN`, with `p : P ⟶ G`, `l : M ⟶ P`, `r : N ⟶ P`;
- `Q = MU`, with `q`, `lQ`, `rQ`, and with the multiplication map `M ⋊ U → Q` an isomorphism
  (`hmulQ`);
- `P̄ = MN̄`, with `pb`, `lb`, `rb`.

The hypotheses are:

- `l ≫ p = lQ ≫ q` (the same embedded Levi);
- `lb ≫ pb = l ≫ p`;
- `P(F) ∩ P̄(F) = M(F)`, which says that `P̄` is opposite to `P`.

The conclusion is an equality of subsets of `G(F)`:
`U(F) = (N(F) ∩ U(F)) · (N̄(F) ∩ U(F))`.
Here `X(F)` stands for `pointImage` of the composite embedding into `G` (for instance
`U(F) = pointImage (rQ ≫ q)`), and `·` is the pointwise product of sets.

Proof. Write `Z(χ)`, `P(χ)`, `U(χ)` for the dynamic centralizer, parabolic and unipotent
subgroups (`Dynamic.centralizer`, `Dynamic.parabolic`, `Dynamic.unipotent`) of a cocharacter
`χ : 𝔾_m → G`.

1. `M` has a split component `a : A → M` (`splitComponentStatement`). With this common `a`,
   `parabolicRootPresentationExistence` gives root presentations of `(P, M)`, `(Q, M)` and
   `(P̄, M)`. Each presentation has a split-component cocharacter; composed into `G` they give
   cocharacters `χ` (for `P`), `ξ` (for `Q`) and `χ̄` (for `P̄`).
2. By `parabolic_eq_splitComponentCocharacter`, `levi_eq_splitComponentCocharacter` and
   `range_comp_radical_eq`, as subgroup functors: `P = P(χ)`, `M = Z(χ)`, `N = U(χ)`,
   `U = U(ξ)`, `P̄ = P(χ̄)`, `M = Z(χ̄)` (using `lb ≫ pb = l ≫ p`) and `N̄ = U(χ̄)`.
3. `Z(χ̄) = Z(χ)`, and the opposite hypothesis reads `P(χ)(F) ∩ P(χ̄)(F) = Z(χ)(F)`. So
   `oppositeDynamicParabolicUniqueness` gives `U(χ̄) = U(χ⁻¹)`, where `χ⁻¹` is `χ` composed with
   the inversion of `𝔾_m`. Hence `N̄(F) = U(χ⁻¹)(F)`.
4. `BruhatTits.DynamicUnipotentContainment.exists_unit_tendsto_pow_zero` gives `t ∈ kˣ` with
   `tⁿ → 0`. The point `ξ(t)` lies in `M(F) = Z(χ)(F)`, because `ξ` factors through `a`, hence
   through `M`, and `l ≫ p = lQ ≫ q`.
5. `Z(χ)(F) ∩ U(ξ)(F) = 1`: this is `M(F) ∩ U(F) = 1`, by
   `IsSemidirectDecomposition.eq_one_of_mem_of_mem` for the decomposition
   `Q(F) = M(F) ⋉ U(F)` (`isSemidirectDecomposition_pointImage`, which uses `hmulQ`).
6. With these inputs, `MatrixRepresentation.unipotentIntersectionProduct k χ ξ t …` is a
   homeomorphism `(U(χ)(F) ∩ U(ξ)(F)) × (U(χ⁻¹)(F) ∩ U(ξ)(F)) ≃ₜ U(ξ)(F)`. By
   `unipotentIntersectionProduct_apply` it is the product map `(a, b) ↦ a b`. The topology on
   `G(F)` needed to state it is `PointTopology.rationalPointTopology k G.X`; the conclusion of
   this theorem is a set equality and does not involve it.
7. After rewriting with steps 2 and 3, surjectivity of this map gives the inclusion `⊆`. The
   inclusion `⊇` holds because both factors lie in the subgroup `U(ξ)(F)`.

## The theorem `pqBoundaryVanishingCompactSupport`

Conclusion: exactly `PQBoundaryVanishingCompactSupportStatement.{u, v}`.

Proof. Introduce the binders and let `V = N̄(F) ∩ U(F)`. Fix `σ` and `f ∈ i_P^G(σ)`, and let
`φ = Induction.eval … f`, the function `G(F) → σ` underlying `f`. The hypotheses of
`boundaryVanishing_iff_compactSupport` with `Γ = G(F)`, `P(F)`, `Q(F)`, `V` are obtained as
follows.

- `G(F)` is Hausdorff (`PointTopology.rationalPoint_t2Space`) and second countable
  (`RationalPointFamily.reductiveRationalPoint_secondCountable`). It is locally compact (an
  instance binder of the statement), hence σ-compact.
- `P(F)\G(F)` is compact: `arbitraryParabolicQuotientCompact`.
- Local closedness of the orbit `P(F)\P(F)Q(F)`. There are finitely many double cosets
  `P(F)\G(F)/Q(F)`, by `representedGeometricLemma` (it supplies an equivalence with some
  `Fin m`). `Geometric.closedSubgroupOrbitOrdering` then gives a Bruhat ordering of the double
  cosets. For it, `Geometric.boundaryVanishingSupportPair … 1` gives the support pair whose
  difference is the orbit of `1`, and `orbit_isLocallyClosed` gives that the orbit is locally
  closed.
- `P(F)` is closed (`isClosed_pointImage`). `V` is closed as an intersection of two closed
  subgroups (`isClosed_pointImage_comp`). `V ≤ U(F) ≤ Q(F)`.
- `V ∩ P(F) = 1`. If `v ∈ V ∩ P(F)`, then `v ∈ P(F) ∩ P̄(F) = M(F)`, using the opposite
  hypothesis and `lb ≫ pb = l ≫ p`. Also `v ∈ N̄(F)`. By
  `IsSemidirectDecomposition.eq_one_of_mem_of_mem` for the decomposition
  `P̄(F) = M(F) ⋉ N̄(F)` (`isSemidirectDecomposition_pointImage`), `v = 1`.
- `Q(F) ⊆ P(F) V`. Let `x ∈ Q(F)`, and let `m ∈ M(F)` be its Levi projection for
  `Q(F) = M(F) ⋉ U(F)`, so that `m⁻¹ x ∈ U(F)` (`projection_inv_mul_mem`).
  `pointImage_radical_eq_mul` writes `m⁻¹ x = a b` with `a ∈ N(F) ∩ U(F)` and `b ∈ V`. Then
  `x b⁻¹ = m a`, which lies in `P(F)` because `M(F) ≤ P(F)` (by `l ≫ p = lQ ≫ q`) and
  `N(F) ≤ P(F)`.
- The zero set of `φ` is left `P(F)`-invariant. The covariance of `f` gives
  `φ(p x) = σ'(p)(φ(x))` for `p ∈ P(F)`, where `σ'` is the inducing representation, and
  `σ'(p)` is linear.
- `φ` is right-invariant under the open subgroup that fixes `f`, by smoothness of `f`.

`boundaryVanishing_iff_compactSupport` rewrites the right-hand side of the goal as vanishing of
`φ` on `closure(P(F)Q(F)) \ P(F)Q(F)`. The left-hand side,
`f ∈ F̃^{<1̄}_{PQ}(σ)` (`boundaryVanishingSubfunctor … (identityParabolicDoubleCoset p q)`), is
equivalent to it by `Geometric.mem_rawSmoothVanishingSubfunctor_iff`.

## Provenance

The abstract theorem, the small lemmas, the decomposition proof and the final assembly are
internal. They make Renard's argument (Source section) explicit, with one change of route: a
set inclusion plus the Library's orbit homeomorphism replaces Renard's homeomorphism
`V → P\PQ`. `pointImage_radical_eq_mul` is Renard's decomposition `U = (U ∩ N)(U ∩ N̄)`,
stated on rational points for parabolics given as represented subgroups with a common Levi. Its
proof identifies the subgroups with dynamic subgroups of cocharacters and applies the Library's
`MatrixRepresentation.unipotentIntersectionProduct`, which proves the same decomposition for
dynamic unipotent subgroups (Waldspurger 2003, IV.1, uses it there).

The semidirect-intersection theorem is imported from `Langlands.Representation.Aubert.General.SemidirectIntersection` with its original name and statement.
