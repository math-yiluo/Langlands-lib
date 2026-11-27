# Weyl conjugations between the standard parabolics of a family

Module `Langlands.Global.AdelicStandardWeylSteps`. It is a helper module for the proof
`Langlands.Global.intertwiningElementaryChain` and has no statement of its own.

## Group-scheme lemmas (namespace `Langlands.GroupScheme`)

For a field `k`, a torus map `i : T → G` with monic underlying morphism and a cocharacter `ν`:

* `weylAction_image_rootSet_of_simple_bijection`: let `cs` be a Coxeter system on the relative
  Weyl group realizing the root action (`IsRelativeWeylCoxeterRealization`), and let `g` raise
  the length on the simple reflections of `L` and conjugate them bijectively onto those of `L'`.
  Then every normalizer lift `n` of `g` satisfies `weylAction i n '' rootSet L = rootSet L'`.
  Positivity of `g(α_a)` comes from the length criterion of the realization, and
  `IsRelativeWeylCoxeterRealization.root_eq_of_conj_simple` gives `g(α_a) = α_b`; this is the
  argument of `exists_levi_map_conj_of_simple_bijection`.
* `rootSet_insert`: `rootSet (insert a L) = insert a (rootSet L)`.

## Subgroup functors and parameters (namespace `Langlands.Global`)

* `range_comp_iso_hom_eq_comap_inv`: the range of `j ≫ e.hom` for an automorphism `e` of `G` is
  the preimage of the range of `j` under `e.inv`.
* `AdelicGroupPoints.weylParameter_retraction_eq`: for a rational Levi `l' : M' → Q` and two
  retractions `π₁`, `π₂` of `l'`, `weylParameter l c π₁ = weylParameter l c π₂`. The characters
  `χ ∘ l ∘ c ∘ πᵢ` of `Q` restrict to the same character of `M'`, and restriction to `M'` is
  injective (`IsRationalLeviSubgroup.characterRestrict_bijective`).

## The family (namespace `Langlands.Global.StandardParabolicFamily`)

`fam` is a standard parabolic family over a number field `F`.

* `mono_levi_comp`, `mono_levi_comp_grp`, `mono_p_left`: the maps `l_J ≫ p_J` and `p_J` are
  monomorphisms.
* `mem_standardLeviPoints_iff`: the rational points of the standard Levi of `J` are the
  images of the rational points of `M_J` (`levi_eq` of the compatibility).
* `exists_rootSet_eq`: with finitely many simple roots, every standard index is the `rootSet` of
  a finite set of simple roots.
* `exists_normalizerPoints_mul_levi`: a Weyl conjugation `(w, c)` from `P_I` to `P_I'` has a
  rational point `z` of `M_I` with `w z` in the normalizer of `T`. The Library's
  `weylTorusAlignment` gives `z` and an isomorphism `e` of `T` with
  `i ≫ Int(w z)⁻¹ = e ≫ i`, so `(w z)⁻¹` normalizes `T` through
  `CommGroupScheme.isoOfGroupIso e`.
* `mem_standardLeviPoints_iff_of_isWeylConjugation`: if `(n, c)` presents a Weyl conjugation
  from `P_K` to `P_K'`, then `x ∈ M_K(F)` if and only if `n x n⁻¹ ∈ M_K'(F)`. The range of
  `l_K ≫ p_K` equals that of `c ≫ l_K ≫ p_K = l_K' ≫ p_K' ≫ Int(n)⁻¹` (`c` is an isomorphism),
  which is the preimage of the range of `l_K' ≫ p_K'` under `Int(n)`.
* `mem_standardRelativeWeylGroup_iff_of_isWeylConjugation`: for such `(n, c)` with `n` a
  normalizer point, `g ∈ W_K'` if and only if `[n]⁻¹ g [n] ∈ W_K`, for the standard relative
  Weyl subgroups `standardRelativeWeylGroup` (as in `mem_standardRelativeWeylGroup_conj_iff`).
* `exists_isWeylConjugation_of_image`: a normalizer point `n` with
  `weylAction n '' K = K'` presents a Weyl conjugation `(n, c)` from `P_K` to `P_K'`. The
  Library's `standardLeviConjugation` (with `relativeRootSubset_image_of_character_image`)
  identifies the standard Levi of `K` with the preimage under `Int(n)` of that of `K'`, so
  `l_K' ≫ p_K' ≫ Int(n)⁻¹` and `l_K ≫ p_K` have equal ranges; `c` is the factor
  `SubgroupFunctor.rangeFactor`, an isomorphism by `SubgroupFunctor.isIso_factor_of_range_eq`.
* `intertwiningOperator_add_of_rootFunctional_eq_zero`: let `a` be a simple root, `S`, `L`,
  `L'` standard indices with `S = L ∪ {a}` and `L' ⊆ S`, and `(n, c)` a Weyl conjugation from
  `P_L` to `P_L'` with `n ∈ M_S(F)`. If the root form of `a ∘ f_L` vanishes at `ν`, then the
  operator `(hK L).intertwiningOperator (hK L') … c π' n` takes the same value at `μ + ν` and
  at `μ`, for every `μ`, `ψ`, `g` and every retraction `π'`. By
  `exists_parameterRestrict_of_rootFunctional_eq_zero`, `ν` is restricted from `P_S`; the
  inclusions `P_L, P_L' → P_S` are range factors (`le_iff_range_le`); `n` is the image of a
  rational point of `M_S`; and `IsIwasawaCompact.intertwiningOperator_add_parameterRestrict`
  applies, the radical `U_L'` being unipotent.
* `intertwiningOperator_eq_of_eq_mul_levi`: let `(w, c)` and `(w', c')` be Weyl conjugations
  from `P_I` to `P_Q` and to `P_Q'` with `Q = Q'`, `π`, `π'` retractions, and
  `w' = w (z ≫ l_I ≫ p_I)` for a rational point `z` of `M_I`. Then the two operators agree at
  every `μ` and `g` on every `ψ` left invariant under `U_I(𝔸)M_I(F)`. After identifying `Q'`
  with `Q`, `c' = c ≫ Int(z)⁻¹` because `l_I ≫ p_I` is a monomorphism and both satisfy the Weyl
  conjugation identity for `w'` (`IsWeylConjugation.mul_right_levi`); the Library's
  `intertwiningRightLeviRepresentative` gives the equality for `π'`, and
  `weylParameter_retraction_eq` replaces `π'` by `π` in the normalizing factor.

## Provenance

Derived. The normalizing representative, the conjugation of standard Levis and the change of
representative are the facts used in Mœglin–Waldspurger, *Spectral decomposition and
Eisenstein series* (1995), registered as `moeglin-waldspurger-1995-spectral-decomposition`,
II.1.6, pp. 87–90, and Bernstein–Lapid (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §8.6, pp. 225–226, written for
the Library's standard parabolic families.
