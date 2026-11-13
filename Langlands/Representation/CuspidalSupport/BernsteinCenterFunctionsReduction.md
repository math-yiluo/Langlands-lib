# Renard VI.10.4, Theorem (second sentence) with Remark 1, from the first sentence

Worker 117. Derived conditional reduction for Renard, *Représentations des
groupes réductifs p-adiques*, French version dated 9 July 2026
(`renard-2026-representations-groupes-reductifs-padiques`), VI.10.4, Theorem
and Remark 1, printed p.212 / PDF p.218. It also uses VI.7.2, Theorem
(printed pp.181–184 / PDF pp.187–190), and VI.5.4 (printed pp.173–175 / PDF
pp.179–181) in their published forms.

## Statement

`BernsteinCenterFunctionsReductionStatement.{uF, uV}` is the implication

> `BernsteinBlockCenterFunctionsStatement.{uF, uV}` →
> `BernsteinDecompositionStatement.{uF, max uF uV}` →
> (for all `F, G, T, i, ν`, the topology `pointTopology` on `G(F)`, instances
> `LocallyCompactSpace G(F)`, `NonarchimedeanGroup G(F)` and every standard family
> `family`: `BernsteinAssociatedSupportInvarianceStatement.{uF, uV} i ν family`) →
> `BernsteinCenterFunctionsStatement.{uF, uV}`.

All four statements are unchanged published statements:

- `BernsteinBlockCenterFunctionsStatement` (VI.10.4, Theorem, first sentence,
  with Remark 1): for each cuspidal datum `a = (M, ρ)` with carriers in
  `Type (max uF uV)`, every `ind ω = i_P^G(ρ ⊗ ω)`, `ω ∈ X(M)`, lies in the
  saturated block of `a`, and there is a ring isomorphism `e` from the centre of
  that block onto the subalgebra of `ℂ[X(M)]` of association-invariant
  functions with `z` acting on `ind ω` by `e z ω`.
- `BernsteinDecompositionStatement` (VI.7.2, Theorem): the Bernstein blocks
  decompose the category of smooth representations in the sense of A.IX
  (`Renard.IsCategoryDecomposition`). It is used at carrier universe
  `max uF uV`, the universe of the target.
- `BernsteinAssociatedSupportInvarianceStatement i ν family` (VI.5.4): associated
  cuspidal data have the same irreducible induction-subquotients. The published
  definition has `F, G, T, i, ν, family` as section variables, so the premise
  quantifies over them, with the same instance context as the other statements.
- `BernsteinCenterFunctionsStatement` (VI.10.4, Theorem, second sentence, with
  Remark 1), the target: every central `z` acts on every
  `i_{P_a}^G(ρ_a ⊗ ω)` by a scalar `f a ω`, with `f` a family of polynomial
  functions compatible with association; `z` is determined by these actions;
  every such family arises from some `z`.

`bernsteinCenterFunctions_reduction` proves the implication.

## Provenance

The statement is internal: it is not a translation of a single assertion of
Renard. Renard deduces the second sentence of the Theorem from the first and
the decomposition `M(G) = ∏_Ω M(G)_Ω`. This record isolates the published
inputs that deduction needs. The compatibility of the scalars across distinct
data of one class uses VI.5.4, applied to twisted data. No premise is proved
here, and the unit does not prove `BernsteinCenterFunctionsStatement`
unconditionally.

## Helper lemmas (section `Helpers`, unconditional unless stated)

The usual standard-Levi instances are local instances, as in the statement
module.

- `bernsteinSaturatedBlockProperty_of_isSubquotient`: the saturated block is
  closed under subquotients (via `bernsteinBlockProperty_iff_saturated` and the
  Library's `bernsteinBlockProperty_of_isSubquotient`).
- `exists_bernsteinInertialClass_eq`: every inertial class is the class of a
  datum (`Quotient.exists_rep`).
- `nontrivial_twistInduction`: every `i_P^G(ρ ⊗ ω)` is nonzero.
  `nontrivial_bernsteinInduction` (module `BernsteinCenterFunctionsBasics`)
  applied to the twisted datum `a.unramifiedTwist ω`, rewritten with
  `bernsteinInduction_unramifiedTwist`.
- `exists_twist_association`: if `a₀` and `a` are inertially related
  (`IsBernsteinInertiaRelated a₀ a`: a conjugacy `c` of the Levis, a character
  `χ ∈ X(M_{a₀})` and `c^*ρ_a ≅ ρ_{a₀} ⊗ χ`), then for every `ω ∈ X(M_a)` the twist
  `ρ_a ⊗ ω` is associated (via the same `c`) to `ρ_{a₀} ⊗ ω₀` with
  `ω₀ = (restriction of ω along c) · χ`. The isomorphism is the inverse of the
  composite of `rationalIsoPullbackTwistIso`, `SmoothRep.twistIso` and
  `rationalUnramifiedTwistMulIso`.
- `areAssociated_unramifiedTwist`: associated twists give associated twisted
  data (`AreBernsteinCuspidalDataAssociated` unfolds to the same proposition).
- `exists_common_irreducible_subquotient` (uses VI.5.4): the inductions of two
  associated twists share an irreducible subquotient. Take an irreducible
  subquotient `π` of the first (nonzero, so
  `SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial` applies), then
  VI.5.4 for the associated twisted data.
- `scalar_eq_of_twistAssociated` (uses VI.5.4): a central `z` acting by `p` and
  `q` on the inductions of two associated twists has `p = q`. `z` acts by both
  on the common irreducible subquotient (`centerScalar_of_isSubquotient`), which
  is nonzero (`scalar_unique`).
- `exists_twistInduction_scalars` (uses the first sentence): every central `z`
  acts on the `i_P^G(ρ_a ⊗ ω)` by `g ω` for some `g ∈ ℂ[X(M_a)]`. Take
  `g = e (catCenterRestrict z)`, where `catCenterRestrict` (module
  `DecompositionCenterAssembly`) restricts `z` to the saturated block.
- `center_app_eq_of_twistInduction` (uses the first sentence): if `z`, `z'`
  agree on every `i_P^G(ρ_a ⊗ ω)`, they agree on every object of the saturated
  block of `a`. The two restrictions have the same image under `e` (their
  scalars on each nonzero `ind ω` coincide, `scalar_unique`), so they are equal
  by injectivity of `e`. Conclude with `catCenterRestrict_app_eq`.
- `exists_blockCenter_of_function` (uses the first sentence): a function
  `g ∈ ℂ[X(M_{a₀})]` invariant under association is the family of scalars of
  `e⁻¹ g` on the inductions of `a₀`.
- `blockCenter_scalar_of_related` (uses the first sentence and VI.5.4): let `zs`
  be central in the block of `s` and act on the inductions of a datum `a₀` of
  `s` by `f a₀`, where `f` is compatible with association. Then `zs` acts on the
  inductions of every datum `a` of `s` by `f a`. Given `ω ∈ X(M_a)`,
  `exists_twist_association` gives an associated `ω₀ ∈ X(M_{a₀})`, so
  `f a₀ ω₀ = f a ω`. The two inductions share an irreducible subquotient `π`,
  which lies in the block (closure under subquotients). By the first sentence
  for `a`, `zs` acts on `ind_a ω` by some scalar. By
  `fullSubcategory_centerScalar_of_isSubquotient`, `zs` acts on `π` by that
  scalar and by `f a₀ ω₀`, so they are equal.
- `exists_blockCenter` (uses the first sentence and VI.5.4): for every class
  `s`, a representative `a₀` and `exists_blockCenter_of_function` give a
  block-central `zs`, and `blockCenter_scalar_of_related` extends its scalars to
  all data of `s`.
- `extendUnramified a g`: the extension by `0` (`Function.extend`) of
  `g : X(M_a) → ℂ` to all characters `M_a(F) →* ℂˣ`, along the injective map
  `ω ↦ ω.val.toMonoidHom`. `extendUnramified_apply`: on `ω ∈ X(M_a)` it is `g ω`.

## Proof of the reduction

Fix `F, G, T, i, ν`, the instances and a standard family. Let `hD` be the
decomposition and `hI` the support invariance for this family.

1. **Scalars.** For central `z`, `exists_twistInduction_scalars` and `choose`
   give `g a ∈ ℂ[X(M_a)]` with `z` acting on `i_{P_a}^G(ρ_a ⊗ ω)` by `g a ω`. Set
   `f a = extendUnramified a (g a)`. On `X(M_a)` it is `g a`, which is regular.
   The compatibility `f a ω = f b ω'` for associated twists is
   `scalar_eq_of_twistAssociated`.
2. **Injectivity.** By `catCenter_ext_of_everyObjectIsCoproduct` with the first
   conjunct of `hD`, it suffices that `z`, `z'` agree on every object `X` of every
   block `s`. Choose a datum `a` with class `s`, convert block membership to the
   saturated form, and apply `center_app_eq_of_twistInduction`.
3. **Surjectivity.** Given a compatible family `f`, `exists_blockCenter` and
   `choose` give block-central elements `zs s`. Their components `w s X hX`
   (with block membership converted to the saturated form) are natural inside
   each block, by naturality of `zs s` on `ObjectProperty.homMk g`.
   `SmoothRep.assembledCenter hD w hw` is central, and on
   `i_{P_a}^G(ρ_a ⊗ ω)`, which lies in the block of `a`
   (`twistInduction_mem_saturatedBlock`), its component is
   `w (class of a) …` (`assembledCenter_app_of_mem`). That component acts by
   `f a ω`.

Lemmas are applied one step at a time in let-heavy contexts
(`have h' := lemma i ν family a; have h := h' ω`). Passing `ω` directly as an
argument of a lemma with pending instance arguments made elaboration time out.
The module uses `backward.isDefEq.respectTransparency.types false`, like the
statement module, and no heartbeat options.
