# Opposite unipotent products fixing an apartment point, without apartment axioms

Module `Langlands.Geometry.Building.GenericOppositeUnipotentFixer`, namespace
`Langlands.Geometry.Building.KPApartmentData`.

## Setting

`k : Type u` is any field, `i : S.toGrp ⟶ G` is a homomorphism from a commutative group
scheme into an affine group scheme with monomorphic underlying scheme map, `ω : kˣ → ℝ` is
arbitrary, and `D : KPApartmentData i ω` is supplied apartment data. The main results assume
`hG : IsConnectedReductive G`, `hi : IsMaximalSplitTorus i` and a generic cocharacter `ν`
(`IsGenericCocharacter i ν`). No apartment axiom (AS 1–AS 5, V 7) is assumed. `U(±ν)(k)`
denotes the rational points of `Dynamic.unipotent (CommGroupScheme.groupHom (±ν) ≫ i)`, and
"fixes `x`" means fixing `D.apartmentMap x` in the reduced building `D.ReducedBuilding`.

## Declarations

- `cocharacterRootForm i ν`: the linear form
  `v ↦ ∑_α ⟨α, ν⟩ · α(v)` on `TranslationSpace i`, summed over all relative roots
  (requires `[Fintype (relativeRoots i)]`).
- `cocharacterRootForm_translationAction_sub_lt`: if a normalizer point `m` satisfies
  `weylAction i m⁻¹ c = -c` for a relative root `c` with `⟨c, ν⟩ ≠ 0`, and `s > 0`, then the
  form is negative on `m·(s ⊗ ν) - s ⊗ ν`.
- `exists_fold` (rank-one fold): for a relative root `c` with `⟨c, ν⟩ < 0` and
  `e ∈ U_c(k)` outside `D.filtration x c 0`, there are `p ∈ U_{-c}(k)` and a normalizer
  point `m` with `e · x = p · (m · x)` in the building and
  `cocharacterRootForm i ν (m · x -ᵥ x) < 0`.
- `exists_iwasawa_fold`: let `cs` be a Coxeter system on `relativeWeylGroup i` with
  `IsRelativeWeylCoxeterRealization i ν cs`, and assume `HasSimpleRootUnipotentFactorization i ν`.
  For every `N`, every normalizer point `n` whose class has length `N`, every
  `c ∈ n U(ν)(k) n⁻¹` and every apartment point `x`, there are `v ∈ U(ν)(k)` and an apartment
  point `y` with `c · x = v · y`. In addition, either `cocharacterRootForm i ν (y -ᵥ x) < 0`,
  or `y = x` and `c = v e` with `e ∈ U(-ν)(k)` fixing `x`.
- `pairing_weylAction_neg_of_length_max`: a normalizer point whose class has maximal Coxeter
  length sends every positive relative root of `ν` to a root negative on `ν`.
- `smul_apartmentMap_eq_of_mul_smul_apartmentMap_eq`: if `u⁻ ∈ U(-ν)(k)`, `u⁺ ∈ U(ν)(k)`
  and `u⁻ u⁺` fixes `x`, then `u⁻` and `u⁺` both fix `x`.
- `mem_filtration_of_orderedProduct_mul_smul_apartmentMap_eq`: let `bn`, `bp` be injective
  enumerations of `RelativeRoot.indivisiblePositiveRoots i (-ν)` and
  `RelativeRoot.indivisiblePositiveRoots i ν`. Let `gn j ∈ U_{bn j}(k)` and
  `gp j ∈ U_{bp j}(k)`, and let `t` be a normalizer point with `weylAction i t = 1` and
  `t · x = x`. If `(∏ gn) · t · (∏ gp)` (ordered products) fixes `x`, then every `gn j` lies
  in `D.filtration x (bn j) 0` and every `gp j` lies in `D.filtration x (bp j) 0`.

## Implemented proofs

**The form.** `rootForm_translationAction` (module `ValuationApartmentMetric`) shows that the
linear part of a normalizer point permutes the root coordinates by
`π = relativeWeylRootPermutation i (mk m⁻¹)`. With `f α = ⟨α, ν⟩`, the value of the form on
`m·(s ⊗ ν) - s ⊗ ν` is `s (∑ f α f (π α) - ∑ f α²)`. Expanding
`0 < ∑ (f α - f (π α))²`, with `∑ f (π α)² = ∑ f α²` (reindexing by `π`), gives the strict
inequality. The term of `α = c` is positive because `π c = -c` and `f c ≠ 0`.

**The fold.** `rootRankOneFactorization` gives an opposite pair `(p₁, p₂)` in `U_{-c}(k)` with
`m = p₁ e p₂` in the normalizer; `weylAction_eq_neg` gives `m · c = -c`. Write
`t₀ = x.val c e < 0`. Valuation axiom V 5, in the form `opposite_snd`, gives
`x.val (-c) p₂ = -t₀ > 0`, so `p₂` fixes `x` (`filtration_le_sharpFixer`,
`sharpFixer_le_reducedFixer`). Hence `e · x = p₁⁻¹ · m · x`. Put `s = t₀/⟨c, ν⟩ > 0` and
`z = (-(s ⊗ ν)) +ᵥ x`. Then `z.val c e = 0`, so the published axiom-free AS 1
(`smul_eq_self_of_val_eq_zero`) shows that `m` fixes `z`. Since `x = (s ⊗ ν) +ᵥ z`,
`smul_vadd` gives `m · x -ᵥ x = m·(s ⊗ ν) - s ⊗ ν`. The form lemma applies because
`weylAction i m⁻¹ c = -c`.

**The induction (`exists_iwasawa_fold`).** Induction on `N`. If `N = 0`, the class of `n` is
trivial, so `n` lies in the centralizer and hence in the dynamic parabolic
(`centralizerPoints_le_dynamicParabolic`). Then `c ∈ U(ν)(k)` (`Dynamic.conj_mem_unipotent`),
and `v = c`, `y = x`, `e = 1` work. If `N > 0`, choose a right descent `a`
(`CoxeterSystem.exists_rightDescent_of_ne_one`). Property (3) of the realization shows
`c' := weylAction i n a ∉ Φ⁺(ν)`, and genericity gives `⟨c', ν⟩ < 0`. Lift `cs.simple a` to
`n_a`; by `isRelativeReflection_simple` it is a relative reflection in `a`, and property (1)
gives `weylAction i n_a a = -a`. `HasSimpleRootUnipotentFactorization` writes
`n⁻¹ c n = q x₀` with `q, n_a q n_a⁻¹ ∈ U(ν)(k)` and `x₀ ∈ U_a(k)`. Then `c = f e` with
`f = n q n⁻¹` and `e = n x₀ n⁻¹ ∈ U_{c'}(k) ⊆ U(-ν)(k)`. The point `n' = n n_a⁻¹` has length
`N - 1`, and `n'⁻¹ f n' = n_a q n_a⁻¹ ∈ U(ν)(k)`.
- If `e` fixes `x`, apply the induction hypothesis to `f` at `x`. In the second alternative,
  `c = v (e₁ e)` with `e₁ e ∈ U(-ν)(k)` fixing `x`.
- Otherwise `e ∉ D.filtration x c' 0`, and `exists_fold` gives `e · x = p · (m · x)` with
  `p ∈ U_{-c'}(k)`. Since `weylAction i n'⁻¹ (-c') = a`, `n'⁻¹ p n' ∈ U_a(k) ⊆ U(ν)(k)`.
  Apply the induction hypothesis to `f p` at `m · x` and add the two negative values of the
  form (`vsub_add_vsub_cancel`).

**Maximal length.** If `w₀` has maximal length, then `ℓ(w₀ s_a) ≤ ℓ(w₀)` for every simple `a`.
Realization property (3) shows that `w₀ a` is not positive, so `⟨w₀ a, ν⟩ ≤ 0`. Every positive
root is a sum of simple roots (`positiveRelativeRoots_subset_closure_simpleRelativeRoots`), so
`⟨w₀ β, ν⟩ ≤ 0` for every positive root `β`. Genericity makes it strictly negative.

**The core statement.** Finiteness of the relative roots, the root system
(`relativeRootSystem`), the Coxeter realization (`relativeWeylCoxeter`) and the ordered root
factorization (`dynamicRootOrderedProduct` through
`hasOrderedRootPointFactorization_of_statement`) give the hypotheses of
`exists_iwasawa_fold` (via `hasSimpleRootUnipotentFactorization_of_orderedRootPoints`). Choose a
lift `n₀` of a maximal-length element (`Finite.exists_max`). Every root factor of an element of
`U(-ν)(k)` is moved into `U(ν)(k)` by conjugation with `n₀⁻¹`, by the previous lemma. Hence
`n₀⁻¹ u⁻⁻¹ n₀ ∈ U(ν)(k)`. Apply `exists_iwasawa_fold` to `c = u⁻⁻¹`, which satisfies
`c · x = u⁺ · x`. In the first alternative, `(v⁻¹ u⁺) · x = y` with `v⁻¹ u⁺ ∈ U(ν)(k)`. The
published `eq_of_unipotent_smul_apartmentMap_eq` (a `U(ν)`-orbit meets the apartment in at
most one point) gives `y = x`, contradicting the strict inequality. In the second alternative,
`v = u⁻⁻¹ e⁻¹ ∈ U(ν)(k) ∩ U(-ν)(k)`, so `v = 1` by
`Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic`. Then `u⁻⁻¹ = e` fixes `x`, and
so does `u⁺ = u⁻⁻¹ (u⁻ u⁺)`.

**Ordered factors.** Conjugate the positive block by `t`; its factors stay in `U_{bp j}(k)`
because `weylAction i t = 1`. Since `t` fixes `x`, `(∏ gn)(t (∏ gp) t⁻¹)` fixes `x`. The core
statement shows that both blocks fix `x`. The published single-sign theorem
`mem_filtration_of_orderedProduct_smul_apartmentMap_eq` (module `GenericOrderedFixerFactors`),
applied with `-ν` and with `ν`, places each factor in its depth-zero filtration. Conjugating
back by `t⁻¹` (`conj_mem_filtration`, with `t⁻¹ · x = x`) recovers `gp j`.

## Provenance

Internal derived unit. The core statement is the algebraic form of the fact that
`U⁺ x ∩ U⁻ x = {x}` in the Bruhat–Tits building, used in the displayed equation in the proof of
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Proposition 8.4.15 (printed p. 307 /
PDF p. 338; source `kaletha-prasad-2023-bruhat-tits-new-approach`). The rank-one fold is the
Schiffmann formula of Bruhat–Tits, *Groupes réductifs sur un corps local I* (1972),
Proposition 7.3.3 (printed p. 165 / PDF p. 162; source
`bruhat-tits-1972-reductive-local-groups-i`). The length induction follows the idea of
Bruhat–Tits Lemma 7.3.6 and 7.3.8 (printed pp. 166–170), but replaces their reductive-quotient
argument with the strictly decreasing root form above. KP and BT state these facts for
building data satisfying their axioms. This unit proves the core statement for every supplied
`KPApartmentData` of a maximal split torus of a connected reductive group over any field.
