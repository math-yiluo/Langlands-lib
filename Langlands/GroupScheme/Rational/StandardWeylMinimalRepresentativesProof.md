# Minimal representatives of standard Weyl double cosets (Renard V.4.6, Lemma): proof

Module `Langlands.GroupScheme.Rational.StandardWeylMinimalRepresentativesProof`.
Universe parameter `u`. Author: Worker 165.

The main theorem `Langlands.GroupScheme.standardWeylMinimalRepresentatives` has exactly
the type `Langlands.GroupScheme.StandardWeylMinimalRepresentativesStatement.{u}`, the
published statement in
[`StandardWeylMinimalRepresentativesStatement`](StandardWeylMinimalRepresentativesStatement.md).
It adds no hypothesis. The statement's Lean/Markdown pair and its imports are unchanged.
The statement is Renard, *Représentations des groupes réductifs p-adiques* (2026), V.4.6,
Lemma (printed pp.120–121 / PDF pp.126–127). That Markdown file gives its source,
notation and dictionary. This file describes the Lean proof, whose route differs from
Renard's.

Notation below: `P_I = parabolic i ν I`, `L_I = levi i ν I`, `U_I = unipotent i ν I`
(rational points). `N = normalizerPoints i`, `Z = centralizerPoints i`, and
`W = relativeWeylGroup i = N/Z`. `Q = P_{IL} = L U` and `P = P_{IM} = M N'`. For
`n ∈ N`, `n·H = H.map (MulAut.conj n)`.

The proof uses only published Library results, plus the helper lemmas proved in this
module. It does not use the nonarchimedean local-field instances of the statement. Every
helper lemma below holds over an arbitrary field `k : Type u`.

## Global inputs

The main proof fixes two things:

- one Coxeter system `cs` with `IsRelativeWeylCoxeterRealization i ν cs`, from
  `relativeWeylCoxeter` (`HasRelativeWeylCoxeterSystem`);
- the relative Tits system `hT : HasRelativeTitsSystem i ν`, from `relativeTitsSystem`.
  This gives the Tits system `(G(k), P_∅(k), N, S)` with
  `P_∅(k) ⊓ N = Z` (`HasRelativeTitsSystem.inf_eq`).

The last field of a realization, `standardSubgroup cs I =
standardRelativeWeylGroup i ν (rootSet i ν I)`, identifies the statement's `W_I` with the
Coxeter parabolic subgroup. `mem_standardRelativeWeylGroup_iff` says that `w ∈ W_J` iff
`w` has a lift `n ∈ N` with `n ∈ L_J`.

## Helper lemmas

### Product decompositions (part (ii), last four equalities), for every `n ∈ N`

- `Dynamic.parabolic_inf_parabolic_eq_mul`: for two cocharacters `α, β` of a common
  commutative group mapping to an affine separated `G`, on every test scheme,
  `P(α) ∩ P(β) = (P(α) ∩ Z(β)) · (P(α) ∩ U(β))` as sets. It is a near copy of the
  published `Dynamic.centralizer_inf_parabolic_eq_mul`. It applies
  `inf_parabolic_eq_mul_of_isStable` to the stability of `P(α)` under the conjugation
  action through `β` (`parabolic_isStable_conjugation`, `restrict_conjugation`).
- `map_conj_eq_rationalPoints_comap`: `F(k).map (conj n)` is the rational-point set of
  `F.comap (G.innerIso n⁻¹).hom` (from `SubgroupFunctor.rationalPoints_comap_innerIso_inv`).
- `exists_map_conj_eq_dynamic` and `exists_eq_dynamic`. `standardCocharacter` gives a
  cocharacter `ζ` for which `P_I`, `L_I`, `U_I` are the dynamic parabolic, centralizer and
  unipotent functors of `ζ ≫ i`. Transporting along `n` gives these lemmas
  (`dynamicParabolic_comap_innerIso`, `dynamicCentralizer_comap_innerIso_hom`,
  `dynamicUnipotent_comap_innerIso`). The result: `n·P_I`, `n·L_I`, `n·U_I` are the dynamic
  subgroups of one torus cocharacter `η`, and `P_J`, `L_J`, `U_J` those of one `μ`.
- `parabolic_inf_map_parabolic_eq_mul`: `P_J ∩ n·P_I = (P_J ∩ n·L_I)(P_J ∩ n·U_I)`,
  using the first lemma.
- `unipotent_inf_map_parabolic_eq_mul`: `U_J ∩ n·P_I = (U_J ∩ n·L_I)(U_J ∩ n·U_I)`,
  using the published `Dynamic.unipotent_inf_parabolic_eq_mul`. Affineness comes from
  `isAffine_of_isAffineHom`, separatedness from `IsConnectedReductive.isSeparated`.

These hold for every `n ∈ N`, not only for lifts of elements of `W^{L,M}`. The main proof
applies them with `(I, J, n) = (IL, IM, n)` and `(IM, IL, n⁻¹)`.

### Minimality and the `P_∅`-conditions

- `intersectionSubset_empty`: `intersectionSubset cs ∅ J w = ∅`. A simple reflection is
  never `1`, since it has length one.
- `isMinimal_mono`: `IsMinimal cs I J w` implies `IsMinimal cs I' J' w` for `I' ⊆ I`,
  `J' ⊆ J`.
- `conj_mem_parabolic_empty_iff` (lemma S). Let `x` be minimal in `x W_J`
  (`IsMinimal cs ∅ J x`), `m` a lift of `x`, and `y ∈ L_J`. Then
  `m y m⁻¹ ∈ P_∅ ↔ y ∈ P_∅`. This is `standardSourceTwistedIntersection` with
  `I = ∅`, read at rational points through
  `standardSourcePoints_twistedIntersection_of_functor_eq`:
  `L_J ∩ m⁻¹ P_∅ m = L_J ∩ P_K` with `K = intersectionSubset cs ∅ J x = ∅`.
- `isMinimal_empty_of_conj_le` (lemma R, from the Tits system). Suppose
  `n (L_J ∩ P_∅) n⁻¹ ⊆ P_∅` for some `n ∈ N`. Then `IsMinimal cs ∅ J (mk n)`. Proof:
  1. `exists_minimal_in_doubleCoset_unrestricted` gives a minimal `x = mk n · b` in the
     coset `mk n · W_J`, and `b` has a lift `n_b ∈ N ∩ L_J`.
  2. Lemma S for the lift `n n_b` of `x` gives `n_b⁻¹ (L_J ∩ P_∅) n_b ⊆ P_∅`.
  3. Write `p ∈ P_∅ ⊆ P_J` as `p = l u` with `l ∈ L_J` and `u ∈ U_J`
     (`Dynamic.exists_centralizer_mul_unipotent`). Then `u ∈ U_J ⊆ U_∅ ⊆ P_∅`
     (`standardParabolicOrder`, `unipotent_le_parabolic`), so `l ∈ L_J ∩ P_∅`. Also
     `n_b⁻¹ u n_b ∈ U_J`, because `n_b⁻¹ ∈ L_J ⊆ P_J` normalizes `U_J`
     (`Dynamic.conj_mem_unipotent`). Hence `n_b⁻¹ P_∅ n_b ⊆ P_∅`.
  4. `IsTitsSystem.mem_of_conjugate_le` gives `n_b ∈ P_∅`, hence
     `n_b ∈ P_∅ ⊓ N = Z`. So `b = 1` and `mk n = x` is minimal.
- `conj_le_iff_isMinimal` (key lemma K). For every `n ∈ N`, the two conditions of
  (V.4.6.1), `n (L ∩ P_∅) n⁻¹ ⊆ P_∅` and `n⁻¹ (M ∩ P_∅) n ⊆ P_∅`, hold iff
  `IsMinimal cs IM IL (mk n)`.
  - (⟹) Lemma R for `n` and `IL`, and for `n⁻¹` and `IM` with `isMinimal_inv`, gives
    right minimality in `mk n · W_L` and left minimality in `W_M · mk n`.
    `minimalityLengthCriterion_proof` combines them.
  - (⟸) Lemma S for `IsMinimal cs ∅ IL (mk n)` and for
    `IsMinimal cs ∅ IM (mk n)⁻¹`, both from `isMinimal_mono` and `isMinimal_inv`.
- `exists_conj_le_iff_isMinimal`. The statement's `v ∈ Wmin IL IM` holds iff
  `IsMinimal cs IM IL v`, for every realization `cs`. Lemma K applies to any lift of `v`,
  obtained from `QuotientGroup.mk_surjective`.

### Standard intersections (part (ii), first two clauses)

- `exists_levi_inf_map_conj_eq` (side of `M`). Let `IsMinimal cs IM IL (mk n)` and
  `K = intersectionSubset cs IL IM (mk n)⁻¹ ⊆ IM`. Then `M ∩ n·Q = M ∩ P_K`,
  `M ∩ n·L = L_K` and `M ∩ n·U = M ∩ U_K`. These are `standardSourceTwistedIntersection`
  and `standardLeviTwistedIntersection` for `I = IL`, `J = IM`, the minimal element
  `(mk n)⁻¹` and its lift `n⁻¹`. They are read at points by
  `standardSourcePoints_twistedIntersection_of_functor_eq` and
  `standardLeviPoints_twistedIntersection_of_functor_eq`.
- `exists_levi_inf_map_conj_inv_eq` (side of `L`). With
  `K' = intersectionSubset cs IM IL (mk n) ⊆ IL`: `L ∩ n⁻¹·P = L ∩ P_{K'}`,
  `L ∩ n⁻¹·M = L_{K'}` and `L ∩ n⁻¹·N' = L ∩ U_{K'}`. These are the same results for
  `I = IM`, `J = IL`, `mk n` and its lift `n`.

### Group-theoretic helpers

- `map_conj_eq_of_mem`: `H.map (conj m) = H` for `m ∈ H`.
- `map_conj_mul`: `H.map (conj (n m)) = (H.map (conj m)).map (conj n)`.

## Assembly of the main theorem

After introducing the data, the proof sets `hWmin`, which is
`exists_conj_le_iff_isMinimal` for an arbitrary realization. It sets `hD`, which identifies
the statement's `∃ a ∈ W_M, ∃ b ∈ W_L, v = a w b` with `v ∈ doubleCoset cs' IM IL w`
through the realization field.

- **(i), existence and uniqueness.** `exists_minimal_in_doubleCoset_unrestricted` gives a
  minimal `x` in `W_M w W_L`. Then `x ∈ Wmin` by `hWmin`. Any other `y ∈ Wmin` in the same
  double coset is minimal, so `y = x` by `minimalRepresentativeUnique_proof`.
- **(i), strict length.** Take any realization `cs'`, `v ∈ Wmin`, `a ∈ W_M`, `b ∈ W_L`
  with `a v b ≠ v`. `hWmin` for `cs'` gives `ℓ(v) ≤ ℓ(a v b)`. If the lengths were
  equal, `a v b` would also be minimal in the double coset. `minimalRepresentativeUnique_proof`
  would then give `a v b = v`, a contradiction.
- **(ii).** For a lift `n` with `mk n ∈ Wmin`, `hWmin` gives `IsMinimal cs IM IL (mk n)`.
  The two standard-intersection lemmas and the four product lemmas then give the six
  clauses.
- **(iii).** Let `w = mk n` with `n·L = M`.
  - For `a = mk m ∈ W_M` with `m ∈ M = n·L`, write `m = n y n⁻¹` with `y ∈ L`. Then
    `n⁻¹ m n = y ∈ L ∩ N`, so `b = mk (n⁻¹ m n) ∈ W_L` and `a w = w b`.
  - So `W_M w W_L = w W_L`. The unique `x ∈ Wmin` of (i) for this double coset has the
    form `w b''` with `b'' = mk m'`, `m' ∈ L ∩ N`. It lies in `W(L, M)` through the lift
    `n m'`, because `(n m')·L = n·(m'·L) = n·L = M` (`map_conj_mul`,
    `map_conj_eq_of_mem`).
  - Any `v ∈ Wmin ∩ W(L, M)` with `v ∈ w W_L` lies in `W_M w W_L`, so `v = x` by the
    uniqueness in (i).

## Checks

`lean_check` with a full Lake build of this module succeeds. The axioms of
`standardWeylMinimalRepresentatives` are only `propext`, `Classical.choice` and
`Quot.sound`. The module contains no `sorry`, no new axioms and no new `Prop`-valued
statement definitions. Its helper declarations are theorems used by the main proof.
