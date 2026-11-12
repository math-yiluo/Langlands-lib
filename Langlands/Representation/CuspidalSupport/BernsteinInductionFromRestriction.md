# Bernstein induction of arbitrary fibred inputs, from restriction

Module `Langlands.Representation.CuspidalSupport.BernsteinInductionFromRestriction`.
Namespace `Langlands.CuspidalSupport`.

Worker 4822 wrote this module under Task 5420
(`064bce40-ce18-46d6-bd56-51926d1a2791`), whose target is the published
`BernsteinInductionRestrictionStatement`. The module does not prove that target.
It defines one generic categorical isomorphism, `cofanInjIsoOfIsZero`, and proves
conditional helper theorems for the target's induction clause 1, for arbitrary
smooth inputs of a standard Levi. Every unproved input is an explicit hypothesis.

## Source and provenance

This is a derived reduction for Renard, *Représentations des groupes réductifs
p-adiques* (9 July 2026), registered as
`renard-2026-representations-groupes-reductifs-padiques`, VI.7.3, Proposition,
printed p.185 / PDF p.191: if `ρ ∈ M(M)_𝔰` then `i_P^G(ρ) ∈ M(G)_{i_{MG}(𝔰)}`.
Renard deduces it from the characterizations in VI.7.2. This module uses a
different route, which needs only `G`-level data. It combines the decomposition
of `M(G)` (Theorem of VI.7.2, printed p.182 / PDF p.188), uniqueness of the
inertial support, first adjointness, and the restriction clause 2 of the same
Proposition. The route is the author's, not Renard's.

The definition `cofanInjIsoOfIsZero` is internal: a standard fact about
coproducts, needed in the proof below. It has no literature source.

## Definition

`cofanInjIsoOfIsZero hc j hzero`. Let `C` be a category with zero morphisms,
`I` a type with decidable equality, `Y : I → C`, and `hc` a proof that the cofan
`Cofan.mk X ιs`, with legs `ιs k : Y k ⟶ X`, is a colimit (a coproduct).
Suppose every `Y k` with `k ≠ j` is a zero object (`hzero`). Then the leg
`ιs j : Y j ⟶ X` is an isomorphism `Y j ≅ X`:

- `hom` is the leg `ιs j`;
- `inv` is the map `X ⟶ Y j` out of the coproduct (`Cofan.IsColimit.desc`)
  whose component at `k` is `eqToHom` for `k = j` and `0` otherwise;
- `hom ≫ inv = 𝟙` is the factorization property `Cofan.IsColimit.fac` at `j`;
- `inv ≫ hom = 𝟙` is checked on each leg (`Cofan.IsColimit.hom_ext`): at `j`
  by the factorization property, and at `k ≠ j` because `Y k` is zero.

## Setting

As in `BernsteinInductionRestrictionStatement`: `F`, `G`, `T`, `i`, `ν` and
`family : BernsteinStandardFamily i ν` are the actual standard family, with the
same structural instance hypotheses. `J : Finset (SimpleRoot i ν)` gives
`P_J = M_J ⋉ N_J`. All carriers are in the saturated universe `max uF uV`.
`ind` is `normalizedInductionFunctor (family.decomposition J)
(family.closedUnipotent J)` and `jac` is `normalizedJacquetFunctor (unipotent i ν J)
(levi i ν J) (family.closedUnipotent J) (family.decomposition J).levi_le_normalizer`.
`M(G)_𝔱` is `bernsteinSaturatedBlockProperty i ν family 𝔱`.

## Statements

1. `bernsteinInertialClass_eq_of_induction_mem_blocks`. Assume
   `huniq : BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family`.
   Let `τ` be an irreducible smooth representation of `M_J(F)` and `a`, `c`
   cuspidal data. If `ind τ` lies in the saturated blocks of both
   `[a] = bernsteinInertialClass i ν family a` and `[c]`, then `[a] = [c]`.

2. `bernsteinInduction_mem_block_of_restriction`. Fix `J` and an arbitrary
   predicate `Q c τ` on cuspidal data `c` of `G` and smooth representations `τ`
   of `M_J(F)`. Assume:
   - `hdec`: `Renard.IsCategoryDecomposition` of the family of block properties
     `fun s => bernsteinBlockProperty.{uF, max uF uV} i ν family s`, indexed by the
     inertial classes `BernsteinInertialClass.{uF, max uF uV} i ν family`;
   - `huniq`: as in 1;
   - `hirr`: for every `c` and every irreducible `τ` with `Q c τ`, `ind τ` lies in
     the saturated block of `[c]`;
   - `hres`: for every `c` and every `V` in the saturated block of `[c]`, every
     irreducible subquotient `τ` of `jac V` satisfies `Q c τ`.

   Then for every cuspidal datum `a` and every smooth `ρ` of `M_J(F)` all of
   whose irreducible subquotients `τ` satisfy `Q a τ`, `ind ρ` lies in the
   saturated block of `[a]`.

3. `bernsteinInduction_mem_block_of_decompositionStatement`. The same as 2,
   with `hdec` replaced by the published `BernsteinDecompositionStatement`
   instantiated at the carrier universe `max uF uV`, that is
   `BernsteinDecompositionStatement.{uF, max uF uV}`. Its instance at the given
   family is exactly the `hdec` of 2.

## Intended use

For the target, take `Q c τ` to be the fibre condition of
`BernsteinInductionRestrictionStatement` for the datum `c`: there are
`I : Finset J`, a datum `b` with `leviIndex J I = b.roots` and
`IsBernsteinInertiaRelated i ν family c b`, and `τ` is a subquotient of the
induction from `M_K` (`K = leviIndex J I`) to `M_J` of the transported `σ_b`.
Then `hρ` is the fibre hypothesis of clause 1 and `hres` is clause 2 of the
target for every datum. `hirr` is clause 1 for irreducible inputs, and `hdec`
and `huniq` are the decomposition (VI.7.2) and uniqueness of the inertial
support. None of these is proved here.

## Proof

1. `τ` is nonzero, since it is irreducible, so `ind τ` is nonzero by the
   published `nontrivial_normalizedInduction`. By
   `SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial` it has an
   irreducible subquotient `π`. By the saturated block hypotheses, `π` has
   inertial support `[a]` and `[c]`, and `huniq` gives `[a] = [c]`.

2. Put `X = ind ρ`. `hdec` gives a coproduct cofan `(Y_s, ι_s)` of `X` with each
   `Y_s` in the block of `s`.
   - Every `Y_s` with `s ≠ [a]` is zero. Otherwise choose a representative `c`
     of `s` (`Quotient.exists_rep`). The leg `ι_s` is a monomorphism
     (`Renard.CategoryDecompositionSimpleClassesProof.cofan_leg_mono`), hence
     injective (`SmoothRep.mono_iff_injective`), hence nonzero. First adjointness
     (`FirstAdjointness.equiv`, with the unimodularity of `N_J` from
     `standardUnipotent_isUnimodular_of_standardCocharacterStatement` and the
     published `standardCocharacter`) is a linear equivalence, so the adjoint
     map `φ : jac Y_s → ρ` is nonzero. Its image `W` is a nonzero
     subrepresentation of `ρ` and a quotient of `jac Y_s`. Let `τ` be an
     irreducible subquotient of `W`. By transitivity of subquotients
     (`smoothSubquotientTransitivity`), `τ` is a subquotient of `ρ`, so
     `Q a τ` holds, and of `jac Y_s`, so `Q c τ` holds by `hres`, because `Y_s`
     is in the block of `[c]` (`bernsteinBlockProperty_iff_saturated`).
     Applying `hirr` twice, `ind τ` lies in the saturated blocks of `[a]` and
     `[c]`, so 1 gives `[a] = [c] = s`, a contradiction.
   - So `ι_[a] : Y_[a] ≅ X` is an isomorphism, `cofanInjIsoOfIsZero`.
   - The block property is stable under isomorphism
     (`bernsteinBlockProperty_of_iso`), so `X` is in the block of `[a]`, and
     `bernsteinBlockProperty_iff_saturated` converts this to the saturated
     block.

3. Apply 2 with `hdec` the instance of the decomposition statement at the given
   data.

## Scope

Apart from `cofanInjIsoOfIsZero`, these are conditional helper theorems. The
hypotheses `hdec`, `huniq`, `hirr`
and `hres` remain separate proof obligations. The theorems do not prove
`BernsteinInductionRestrictionStatement` and add no hypothesis to it. The
predicate `Q` is generic, so this module imports only published Library modules
(environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`).
