# Field-valued detection for flat formally smooth cut-out subgroups

This helper module holds the commutative-algebra core of the proof of
`Langlands.GroupScheme.RelativeSelfNormalizerStatement`. See
`Langlands/GroupScheme/RelativeSelfNormalizerProof.md`. Everything lives in the
namespace `Langlands.GroupScheme.Corepresented`.

## Setting

Fix a commutative ring `R` and a functor `F` from commutative `R`-algebras to
groups. `F` is corepresented by an `R`-algebra `B` through
`e : (F ⋙ forget GrpCat).CorepresentableBy B`. Let `H A ≤ F A` be a family of
subgroups cut out by an ideal `I` of `B`. This is the Library predicate
`IsCutOutBy e H I`: a point `x ∈ F A` lies in `H A` exactly when its
classifying map `B → A` vanishes on `I`. `normalizerFamily H` is the Library's
algebra-level normalizer: `g ∈ F A` normalizes `H` when, after every algebra
map `A ⟶ A'`, conjugation by the image of `g` and by its inverse preserve
`H A'`.

## Definitions and auxiliary results

- `map_mem_normalizerFamily`, `le_normalizerFamily`: the normalizer family is
  stable under algebra maps, and a cut-out family lies in its own normalizer
  family.
- `tensorQuotientMapOf` with `tensorQuotientMapOf_apply`,
  `tensorQuotientLeft_comp_mapOf`, `map_universalCutPoint_mapOf`,
  `map_conjugate_mapOf` and `map_invConjugate_mapOf`. An algebra map
  `f : A ⟶ A'` induces `A ⊗[R] (B ⧸ I) ⟶ A' ⊗[R] (B ⧸ I)`. This map sends the
  universal cut point to the universal cut point, and it sends the two
  conjugates of the universal point that occur in the Library criterion
  `mem_normalizerFamily_iff` to the corresponding conjugates by `F.map f g`.
- `congruencePairs J`: the `R`-subalgebra `P = A ×_{A/J} A` of `A × A`, made of
  the pairs that are congruent modulo an ideal `J`. Its projections are
  `pairFst` and `pairSnd`. `pairMap η γ h : B ⟶ P` is the map defined by two
  classifying maps that agree modulo `J`.
- `tensor_eq_zero_of_pair`: if `B ⧸ I` is flat over `R`, then an element of
  `P ⊗[R] (B ⧸ I)` that vanishes under both projections is zero. The proof
  uses injectivity of `P ⊗ (B ⧸ I) → (A × A) ⊗ (B ⧸ I)`, which holds by
  flatness, together with `TensorProduct.prodLeft`.
- `diagonalIdeal m J hmJ`: for ideals with `m * J = 0`, the ideal of `P`
  consisting of the diagonal pairs `(a, a)` with `a ∈ m`. Write `K` for it.
  `residueMap` is the ring map `A ⧸ m → P ⧸ K` induced by the diagonal. It is
  compatible with the structure maps from `R` (`residueMap_comp_algebraMap`).
  So when `m` is maximal, `P ⧸ K` is an `R`-algebra whose structure map
  factors through the field `A ⧸ m`.
- `eq_bot_of_le_mul_maximal`: a global form of Nakayama's lemma. A finitely
  generated ideal `J` with `J ≤ m * J` for every maximal ideal `m` is zero.
  The proof uses Mathlib's
  `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul` and shows
  that the annihilator of `J` is not contained in any maximal ideal.
- `isMaximal_map_mk`, `map_mk_mul_map_eq_bot`: elementary facts about images
  of ideals in `A ⧸ m * J`.
- `FieldNormalizerCondition H` is a `Prop`-valued definition used as a
  hypothesis. It says that `normalizerFamily H E ≤ H E` for every `R`-algebra
  `E` whose structure map factors as `R → k → E` through a field `k : Type u`.

## Main results

Assume `B ⧸ I` is flat and formally smooth over `R`.

- `mem_of_mul_eq_bot` (the square-zero step). Let `g ∈ normalizerFamily H A`
  with classifying map `γ`, let `J = I.map γ`, and let `m` be a maximal ideal
  with `m * J = 0`. Then `g ∈ H A`. The proof:
  1. The residue-field test `A → A ⧸ m` and the field hypothesis give `J ≤ m`.
     Hence `J ^ 2 ≤ m * J = 0`.
  2. Formal smoothness lifts `B ⧸ I → A ⧸ J` (induced by `γ`) along the
     square-zero quotient `A → A ⧸ J` (`Algebra.FormallySmooth.lift`). This
     gives a classifying map `η` that kills `I` and agrees with `γ` modulo `J`.
     So `e.homEquiv η ∈ H A`.
  3. The point `pt` classified by `pairMap η γ` over `P` maps to
     `e.homEquiv η` and to `g` under the two projections. Both of these
     normalize `H`. By `tensor_eq_zero_of_pair`, membership in `H` over
     `P ⊗[R] (B ⧸ I)` can be checked after the two projections. The criterion
     `mem_normalizerFamily_iff` then shows that `pt` normalizes `H`.
  4. Push `pt` to `P ⧸ K`, which is an algebra over the field `A ⧸ m`. The
     field hypothesis puts its image in `H`. So for `b ∈ I` the pair
     `(η b, γ b)` lies in `K`, and in particular `γ b = η b = 0`.
- `le_mul_of_isMaximal`: for a normalizing point `g` and a maximal ideal `m`,
  `J ≤ m * J`. This applies `mem_of_mul_eq_bot` to the image of `g` over
  `A ⧸ m * J` and the maximal ideal `m.map π`.
- `normalizerFamily_le_of_field`: if, in addition, `I` is finitely generated
  and `FieldNormalizerCondition H` holds, then `normalizerFamily H A ≤ H A`
  for every `R`-algebra `A`. Here `J = I.map γ` is finitely generated, so
  `eq_bot_of_le_mul_maximal` and `le_mul_of_isMaximal` give `J = 0`. That is,
  `γ` kills `I`.

## Provenance

This module is internal to the proof. The theorem is a derived algebraic form
of the field-fibre detection in Brian Conrad, *Reductive group schemes*
(2014), Proposition 2.1.6 and Lemma B.3.1 (source
`conrad-2014-reductive-group-schemes`), which the target statement cites. The
route differs from Conrad's. Conrad represents the normalizer by a closed
subgroup scheme and applies a fibrewise isomorphism criterion. This module
never represents the normalizer. It works directly with a normalizing point
and the ideal `J`, and uses formal smoothness, flatness and Nakayama's lemma.
