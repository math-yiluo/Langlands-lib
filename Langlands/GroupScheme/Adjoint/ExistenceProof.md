# Existence of the actual adjoint quotient: proof

Author: Worker 4030.

This module proves the published Library statement
`Langlands.GroupScheme.AdjointQuotientExistenceStatement` (module
`Langlands.GroupScheme.Adjoint.ExistenceStatement`). It adds no hypotheses and
no new definitions.

## `adjointQuotientExistence`

`theorem Langlands.GroupScheme.adjointQuotientExistence :
AdjointQuotientExistenceStatement.{u}`.

For every universe `u`, every field `k : Type u` and every group scheme `G`
over `Spec k` with `IsConnectedReductive G`, there are a group scheme `A` over
`Spec k` and a homomorphism `q : G ⟶ A` with `IsAdjointQuotient q`. The field
is arbitrary: any characteristic, not necessarily perfect or infinite. Tori
and groups with nonsmooth centre are included: no step below assumes
anything about the centre beyond its all-test definition. `q` is not
required to be finite.

`IsAdjointQuotient q` is used unchanged, so the theorem gives all of its
fields: `G` connected reductive, `A` adjoint (connected reductive with a
finite closed centre representative and centre functor `⊥`), `q` flat,
surjective and locally of finite presentation, the actual kernel of `q` is a
closed subgroup whose range is the full all-test centre `center G`, and both
universal properties, for every group scheme `H` over `Spec k` and every
`Y : Over (Spec k)`.

## Proof

The proof composes published Library theorems; it proves no new lemma.

1. **Centre representative.** `schemeTheoreticCenterExistence`
   (module `Reductive.CenterExistenceProof`) gives a group scheme `Z` and
   `z : Z ⟶ G` with `IsSchemeTheoreticCenter z`: `z` is a closed subgroup
   and `SubgroupFunctor.range z = center G`. That theorem obtains `z` as the
   closed fixed subgroup of the conjugation action of `G` on itself.
2. **Quotient.** The range of `z` is normal (`IsSchemeTheoreticCenter.isNormal`,
   module `Adjoint.Assembly`, since the full centre is normal). `G.X.hom` is
   affine (`hG.isAffineHom`) and locally of finite type (it is smooth, and
   the Mathlib instance chain from smoothness supplies local finite type).
   So `normalSubgroupQuotientExistence` (module
   `NormalQuotientExistenceProof`) gives `Q` and `q : G ⟶ Q` with `Q.X.hom`
   affine and locally of finite type and
   `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q`. Rewriting with
   `range z = center G` turns this into
   `RelativeRoot.IsFppfQuotient (center G) q`: `q` is flat, surjective and
   locally of finite presentation, and `range (kernelι q) = center G`.
3. **Reductivity of the target.** `centerQuotientReductive` (module
   `Adjoint.CenterQuotientReductiveProof`) applied to `q` gives
   `IsConnectedReductive Q`.
4. **Trivial centre of the target.** `reductiveCentralDerivedProduct`
   (module `Reductive.CentralDerivedProductProof`) is the published proof of
   `ReductiveCentralDerivedProductStatement`. With it,
   `SecondCenter.secondCenterTrivial_of_centralDerivedProduct` (module
   `Adjoint.SecondCenterReductive`) gives `SecondCenterTrivial G`: a point of
   `G` all of whose commutators are central is central. Then
   `CenterQuotientCenter.center_eq_bot_of_secondCenterTrivial` (module
   `Adjoint.CenterQuotientDescent`) applied to the fppf quotient `q` gives
   `center Q = ⊥`.
5. **Assembly.** `isAdjointQuotient_of_fppf_kernel_range` (module
   `Adjoint.Assembly`) takes `IsConnectedReductive G`,
   `IsConnectedReductive Q`, `center Q = ⊥`, flatness, surjectivity and
   local finite presentation of `q`, and `range (kernelι q) = center G`, and
   returns `IsAdjointQuotient q`. Inside it, the unit of the separated group
   `Q` is a finite closed centre representative, so `Q` is adjoint; the
   actual kernel of `q` is a closed immersion into `G` because `Q` is
   separated; and the group and scheme universal properties are proved by
   fppf descent along `q` (`isAdjointQuotient_of_fppf`, module
   `Adjoint.QuotientDescent`).

The witness is `A := Q` with this `q`.

## Sources

The statement's Markdown gives the literature (Milne, *Algebraic Groups*,
Corollary 17.62(e), Remark 17.63, Theorem 5.14, Proposition 5.18; Conrad–Gabber–Prasad,
A.1.10–A.1.12). The Lean proof route follows the same outline (quotient by
the normal centre, reductivity of the quotient, triviality of its centre,
fppf descent for the universal properties), with each step supplied by the
published Library theorems named above.
