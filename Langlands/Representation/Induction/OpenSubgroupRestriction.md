# Restriction of smooth induction to an open subgroup

This module constructs restriction and its inverse on actual smooth induced
functions. Let `G` be a topological group, `P` an actual subgroup, and `K` an
open subgroup. Suppose

\[
  \forall g\in G,\quad g=pk\quad\text{for some }p\in P,\ k\in K.
\]

For a representation `σ` of `P` over a commutative ring `R`,
`Langlands.Induction.openSubgroupInductionEquiv` is an equivalence of
representations of `K`:

\[
  \left.\operatorname{Ind}^{G,\mathrm{sm}}_P(\sigma)\right|_K
  \simeq
  \operatorname{Ind}^{K,\mathrm{sm}}_{P\cap K}
      \left(\left.\sigma\right|_{P\cap K}\right).
\]

Both sides are the existing `SmoothFunctions` carriers. Their functions satisfy
left covariance `f(p*g) = σ(p)(f(g))` and have a common open right stabilizer.
Both group actions are actual right translation. The intersection is the literal
subgroup `P.comap K.toSubgroup.subtype` of `K`, and
`openSubgroupInducingRepresentation` is the restriction of `σ` along its
canonical homomorphism into `P`. No abstract model, inverse, or smoothness
conclusion is assumed.

## Provenance and scope

The construction is a derived subgroup-level prerequisite for Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*,
VI.1, printed pp.295–296, especially p.296 (PDF pp.61–62). That passage identifies
the twisted product-induced spaces with a fixed compact picture by restriction.
The generic single-group equivalence here supplies the actual restriction
step and proves its inverse. Its proof is given below; this more general
formulation and its naturality assertion are derived content.

The ring, ambient group, coefficient module, and the second coefficient module
in the naturality theorem have independent universes. The coefficient modules
are additive commutative groups with `R`-module structures. No smoothness
hypothesis on `σ`, compactness of `K`, closedness of `P`, reductive realization,
measure, or admissibility is needed. The structural factorization hypothesis is
explicit. In a reductive application its existence remains a separate
Iwasawa-decomposition obligation. Application to normalized induction,
removal of the half-modulus character on the compact intersection, unramified
twist independence, product comparison, and the smooth families of VI.1 are
separate steps.

## The maps and the inverse proof

`openSubgroupInductionRestrict` sends `f` to the function `k ↦ f(k)`. It reuses
`smoothSplitQuotientRestrict`, whose construction works for any continuous
group homomorphism: the preimage of a global open stabilizer proves smoothness.
`openSubgroupInductionRestrict_eval` records literal evaluation.

For the inverse, choose one factorization `g = p*k` and set

\[
  \widetilde f(g)=\sigma(p)f(k).
\]

The private lemma `factorization_value` proves independence of this choice.
If `p*k = q*l`, then `q⁻¹*p = l*k⁻¹` belongs to both subgroups. Covariance of
`f` on the actual intersection gives
`f(l) = σ(q⁻¹*p)(f(k))`, and the representation law gives
`σ(q)(f(l)) = σ(p)(f(k))`. The private function `extensionValue` chooses
factorizations, and `extensionValue_mul` proves the stated formula for every
factorization.

`openSubgroupInductionExtend` proves covariance by replacing `p*(q*k)` with
`(p*q)*k` and applying the representation law. It also proves global
smoothness. Choose an open subgroup `H` of `K` fixing `f` under right
translation. Its image in `G` is an open subgroup because `K` is open and its
subtype inclusion is an open map. For `h∈H` and `g=p*k`, the extension formula
gives

\[
  \widetilde f(gh)=\sigma(p)f(kh)
    =\sigma(p)f(k)=\widetilde f(g).
\]

Thus the image of `H` is a common open right stabilizer for the extension.
This supplies the actual `SmoothFunctions` value.
`openSubgroupInductionExtend_mul` exposes its evaluation at every `p*k`.

The bundled `openSubgroupInductionEquiv` uses restriction as its linear forward
map and this extension as its inverse. Covariance of a global function proves
extension after restriction is the identity. Taking `p=1` in the extension
formula proves restriction after extension is the identity. Restriction commutes
pointwise with right translation by each element of `K`, giving the bundled
intertwining law. The evaluation theorems
`openSubgroupInductionEquiv_eval` and
`openSubgroupInductionEquiv_symm_mul` record both directions.

## Naturality

`openSubgroupInductionEquiv_natural` states that for any actual coefficient
intertwiner `T : σ.IntertwiningMap τ` and every global smooth induced `f`,
restricting `smoothInducedMap P T f` equals applying the induced restricted
coefficient map to the restriction of `f`. Both sides evaluate to `T(f(k))`
at every `k∈K`, so subtype and function extensionality prove the equality.
The source and target coefficient carriers may have different universes.
