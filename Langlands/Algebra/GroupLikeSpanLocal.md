# Group-like spanned flat Hopf algebras over local rings

Module `Langlands.Algebra.GroupLikeSpanLocal`, namespace `Langlands.GroupLikeSpan`.

This is an internal module. It supplies the local algebra input for the proof of
`Langlands.GroupScheme.RelativeMultiplicativeTypeClosedSubgroupStatement`.
In particular it is what the reduction
`FlatGroupLikeHopfMultiplicativeTypeStatement` (module
`Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeSubgroupReduction`) needs over a local base. It cites no
external source. The statement is the local form of the standard fact that, over a
local ring, a flat finitely presented commutative Hopf algebra spanned by group-like
elements is a group algebra. The proof below was written for this development. It
never reduces to a noetherian base.

## Main results

Throughout, `R : Type u` is a local commutative ring and `A : Type v` is a commutative
Hopf `R`-algebra. `A` is flat as an `R`-module and finitely presented as an
`R`-algebra. Every main result assumes
`hspan : Submodule.span R {a : A | IsGroupLikeElem R a} = ⊤`.

- `linearIndependent_groupLike_of_isLocalRing`: the family
  `fun g : GroupLike R A => (g : A)` is `R`-linearly independent.
- `groupFG`: `Group.FG (GroupLike R A)`.
- `linearIndependent_and_groupFG`: both statements together.
- `basisGroupLike hspan : Module.Basis (GroupLike R A) R A`, the basis formed by the
  group-like elements. `basisGroupLike_apply` says that it sends `g` to `(g : A)`.
- `eq_one_of_sub_one_mem`: if `u` is group-like and
  `u - 1 ∈ (maximalIdeal R).map (algebraMap R A)`, then `u = 1`.
- `liftGroupLikeBialgHom_injective`: Mathlib's evaluation
  `MonoidAlgebra.liftGroupLikeBialgHom : R[GroupLike R A] →ₐc[R] A` is injective.
- `bialgEquiv hspan : MonoidAlgebra R (GroupLike R A) ≃ₐc[R] A` is this evaluation as
  a bialgebra equivalence. Surjectivity is the published
  `Langlands.MonoidAlgebra.liftGroupLikeBialgHom_surjective`. `bialgEquiv_single`
  says that it sends `single g r` to `r • (g : A)`.

## Auxiliary definitions and lemmas

Let `Γ` be a commutative group and `y : Γ →* B` a monoid homomorphism into a
commutative ring.

- `congrKer y I` is the subgroup `{γ | y γ - 1 ∈ I}` for an ideal `I` of `B`. The
  lemma `congrKer_mk_eq_mk_iff` says that `γ` and `δ` have the same coset exactly when
  `y γ - y δ ∈ I`. `congrKer_mono` says the subgroup grows with `I`.
- For an `R`-algebra `A` and `x : Γ →* A`, `charKer x I := congrKer x (I.map
  (algebraMap R A))` for an ideal `I` of `R`. Its API is `mem_charKer`,
  `mk_eq_mk_iff` and `charKer_mono`.

The tensor product lemmas are as follows.

- `one_tmul_eq_zero_iff`: `(1 : R ⧸ I) ⊗ₜ a = 0` iff `a ∈ I.map (algebraMap R A)`.
- `mem_smul_top_iff_mem_map`: `I • ⊤ = I.map (algebraMap R A)` as sets.
- `basis_repr_mem_of_mem_smul_top`: every basis coordinate of an element of `I • ⊤`
  lies in `I`.
- `span_one_tmul_eq_top`: a spanning family stays spanning after scalar extension.
- `isGroupLikeElem_one_tmul`: group-like elements stay group-like after scalar
  extension.
- `one_tmul_mem_map`: `1 ⊗ₜ a` lies in the extension of `J.map (algebraMap R S)`
  whenever `a ∈ J.map (algebraMap R A)`.

For the fibre statements, `A` is an `R`-bialgebra that is flat over `R`. The map
`x : Γ →* A` takes group-like values (`hx`) and its range spans `A` (`hspan`).

- `coeff_mem_of_mem_map`. Let `q` be prime and `q ≤ J`. Write `H` for
  `charKer x q`. Suppose `Finsupp.linearCombination R x a` lies in
  `J.map (algebraMap R A)`. Then every coset sum `Finsupp.mapDomain mk a c`, for
  `c : Γ ⧸ H`, lies in `J`.
- `charKer_eq_of_isPrime_le`: `charKer x J = charKer x q` for every proper `J ≥ q`.
- `charKer_eq_maximalIdeal`: over a local ring, `charKer x q = charKer x 𝔪` for every
  prime `q`.
- `coeff_mem_nilradical`: over a local ring, the coset sums modulo `charKer x 𝔪` of
  any linear relation `Finsupp.linearCombination R x a = 0` are nilpotent.

The remaining auxiliary results are these.

- `eq_one_of_forall_isPrime` is an abstract Nakayama statement. Take an `S`-algebra `B`
  and `y : Γ →* B` whose range spans `B` over `S`. Let `K ≤ Γ` be finitely generated,
  and let `π : B →ₗ[S] (Γ ⧸ K →₀ S)` be linear with `π (y γ) = single [γ] 1`. Suppose
  that for every prime `P` of `S` and every `κ ∈ K`, `y κ - 1 ∈ P.map (algebraMap S B)`.
  Then `y κ = 1` for all `κ ∈ K`.
- `ker_fg_of_finiteType`: a surjective `R`-algebra map from a finite-type algebra
  onto a finitely presented algebra has finitely generated kernel.
- `subgroup_fg`: every subgroup of a finitely generated commutative group is
  finitely generated.
- `lift_eq_linearCombination`: evaluating `R[Γ]` along `x` is the linear combination
  of the coefficients. `lift_surjective`: this evaluation is surjective when the range
  of `x` spans.
- `exists_isNilpotent_sub_one_mem`. Over a local ring, with `A` flat and finitely
  presented and `Γ` finitely generated, there is a nilpotent ideal `N` of `R` such that
  `x κ - 1 ∈ N.map (algebraMap R A)` for every `κ ∈ charKer x 𝔪`.
- `span_out_eq_top`, `linearIndependent_one_tmul_out` and `exists_basis`. Under the
  same hypotheses, the representatives `x c.out` for `c : Γ ⧸ charKer x 𝔪` form a basis
  of `A`. Modulo any prime `q`, the elements `1 ⊗ x c.out` for
  `c : Γ ⧸ charKer x q` are linearly independent.
- `exists_eq_basis_of_isGroupLikeElem`: over a local ring, if a basis consists of
  group-like elements, every group-like element is one of its vectors.

## Proof outline

1. **Prime fibres.** Let `q` be a prime of `R`. The base change `(R ⧸ q) ⊗ A` is
   torsion-free over the domain `R ⧸ q`, because `A` is flat. It is spanned by the
   group-like elements `1 ⊗ x γ`, so Mathlib's `linearIndep_groupLikeVal` makes the
   distinct ones a basis. Two of them agree exactly when the cosets modulo
   `charKer x q` agree, by `one_tmul_eq_zero_iff`. Hence the basis coordinates of
   `1 ⊗ Σ a_γ x γ` are the reduced coset sums of `a`. This gives
   `coeff_mem_of_mem_map`. Take `γ ∈ charKer x J` outside `charKer x q`. The relation
   `x γ - x 1` has a coset sum equal to `1` at the coset of `γ`, so `1 ∈ J`. This
   gives `charKer_eq_of_isPrime_le`. On a local ring every prime lies in `𝔪`, so all
   the subgroups `charKer x q` equal `K := charKer x 𝔪`. The coset sums modulo `K` of a
   relation therefore lie in every prime, which is `coeff_mem_nilradical`.
2. **A nilpotent ideal.** Let `ψ : R[Γ] → A` be evaluation along `x`. It is
   surjective. `R[Γ]` has finite type because `Γ` is finitely generated, and `A` is
   finitely presented, so `ker ψ` is generated by a finite set `F`. Let `N` be the
   ideal generated by the finitely many coset sums modulo `K` of the elements of `F`.
   It is finitely generated and contained in the nilradical, so it is nilpotent
   (`Ideal.FG.isNilpotent_iff_le_nilradical`). Let `Θ : R[Γ] → (R ⧸ N)[Γ ⧸ K]` be the
   algebra map that sends `single γ r` to `single [γ] [r]`. It kills `F`, so it
   factors through `A` (`AlgHom.liftOfSurjective`). Extending scalars to `R ⧸ N`
   gives an `(R ⧸ N)`-linear map
   `π : (R ⧸ N) ⊗ A → (Γ ⧸ K →₀ R ⧸ N)` with `π (1 ⊗ x γ) = single [γ] 1`.
3. **Nakayama.** Apply `eq_one_of_forall_isPrime` with `S = R ⧸ N`,
   `B = (R ⧸ N) ⊗ A` and `y γ = 1 ⊗ x γ`. `K` is finitely generated by `subgroup_fg`.
   Every prime `P` of `R ⧸ N` pulls back to a prime `q` of `R`, and
   `charKer x q = K`, which gives the fibre hypothesis. Inside that lemma, let `𝔞` be
   the ideal generated by the `y κ - 1` for generators `κ` of `K`. The map
   `ρ = id - σ ∘ π` sends `B` into `𝔞`, where `σ` sends `single c s` to `s • y c.out`.
   It fixes each `y κ - 1`. So each generator of `𝔞` lies in `Q • 𝔞` for every maximal
   ideal `Q` of `B`. The determinant trick
   (`Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`) then shows that
   `𝔞` has annihilator `⊤`, so `𝔞 = 0`. Hence `1 ⊗ x κ = 1`, that is,
   `x κ - 1 ∈ N.map (algebraMap R A)` (`exists_isNilpotent_sub_one_mem`).
4. **Basis.** Each `x γ` is congruent to `x [γ].out` modulo `N • A`. So the
   representatives span `A` modulo `N • A`, and because `N` is nilpotent they span `A`
   (`Langlands.Algebra.eq_top_of_sup_smul_eq_top_of_nilpotent`). In the residue fibre
   `k ⊗ A`, their images are distinct group-like elements and hence linearly
   independent (step 1 with `q = 𝔪`). Flatness lifts this independence to `A`
   (`Module.IsLocalRing.linearIndependent_of_flat`). This is `exists_basis`.
5. **Classification.** Let `g = Σ a_i b_i` be group-like, where `(b_i)` is a basis of
   group-like elements. Compose the comultiplication with the coordinate pairing
   `u ⊗ v ↦ b.coord i u * b.coord j v`, and compare the result with `b.coord i`, or
   with `0` when `i ≠ j`, on the basis. This gives `a_i a_i = a_i` and `a_i a_j = 0`
   for `i ≠ j`. The counit gives `Σ a_i = 1`. Some `a_i` lies outside `𝔪`, so it is a
   unit idempotent and equals `1`, and all other coordinates vanish. Hence `g = b_i`
   (`exists_eq_basis_of_isGroupLikeElem`).
6. **Main theorem.** `A` has finite type, so finitely many elements generate it. Each
   is a combination of finitely many group-like elements. Let `Γ` be the subgroup of
   `GroupLike R A` that these group-like elements generate. It is finitely generated,
   and the span of its values is the subalgebra they generate, which is `A`. Step 4
   gives a basis `x c.out`. By step 5 every group-like element is one of these basis
   vectors. Hence the group-like elements are linearly independent, every group-like
   element lies in `Γ` (so `Γ = ⊤` and the group is finitely generated), and they form
   a basis. For `eq_one_of_sub_one_mem`, write `u - 1` in this basis. If `u ≠ 1`, its
   `u`-coordinate is `1`, and `1 ∈ 𝔪` by `basis_repr_mem_of_mem_smul_top`, which is a
   contradiction. Injectivity of the evaluation is linear independence read through
   coefficients, as in `Langlands.MonoidAlgebra.liftGroupLikeBialgHom_injective`.

## Scope

All results are local: `R` is assumed local where stated. Spreading from local rings
to a Zariski cover, and identifying `hopfSpec A` with a group of multiplicative type,
are not part of this module.
