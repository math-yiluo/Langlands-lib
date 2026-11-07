# Point-group isomorphisms over field points from isomorphisms of field fibres

Module `Langlands.GroupScheme.Reductive.LocalSplitFieldPoints`, namespace
`Langlands.GroupScheme.LocalSplitCell`.

## Setting

`R` is a commutative ring, `K` a field with an `R`-algebra structure, and `b = algebraBaseMap R K`.
`G_K` and `H_K` are the base changes of group schemes `G`, `H` over `Spec R`. The Library's
`GroupScheme.baseChangePointsEquiv b G T : G_K(T) ≃* G((Over.map b).obj T)` is the adjunction
on points. `splitTorus.baseChangeHom (K := K) G I i : T_I ⟶ G_K` is the field-fibre torus map.
`LocalSplitBigCell.baseChangeRoot K u : Ga K ⟶ G_K` is the base change of a root map, from the
module `Langlands.GroupScheme.Reductive.LocalSplitBigCellProof`. `fieldPoint R K` and
`weylFamily` are as in the modules `LocalSplitCellIsomorphism` and `LocalSplitWeylFamily`.

## Reused point equivalence

`GroupScheme.isoPointsEquiv Φ T : G(T) ≃* H(T)`, from
`Langlands.GroupScheme.Torus.Split`, is composition with an isomorphism
`Φ : G ≅ H` of group schemes over any base.

## Results

- `exists_fieldPointsEquiv`. The inputs are as follows.
  - An isomorphism `Φ : G_K ≅ H_K` that carries the field-fibre torus map of `i` to that of `i'`.
  - Families `uK`, `uK'` of maps `Ga K ⟶ G_K` and `Ga K ⟶ H_K` whose values correspond to those
    of `u` and `u'` under `baseChangePointsEquiv`, on every test object over `Spec K`.
  - `uK a ≫ Φ.hom = uK' a` for every simple root `a`.
  - `Φ` carries the base point `uK_{-a}(-1)` to `uK'_{-a}(-1)` for every simple `a`. Here `-a`
    is `P.reflectionPerm a a`.
  Then there is an isomorphism `Ψ : G(fieldPoint R K) ≃* H(fieldPoint R K)` with
  `Ψ (t ≫ i) = t ≫ i'` for every torus point `t`. It also carries the value at `c` of
  `weylFamily P W u α` to that of `weylFamily P W u' α`, for every root `α` and every `c`.
- `IsWeylPoint.baseChange`: if `weylPoint u v` is a Weyl point of `i` for `f` over `R`, then
  `weylPoint (baseChangeRoot K u) (baseChangeRoot K v)` is a Weyl point of the field-fibre torus
  map for the same `f`.

## Proof

`exists_fieldPointsEquiv`. Write `pt` for the unit object over `Spec K`, so that
`fieldPoint R K = (Over.map b).obj pt`. Take `Ψ = E_H ∘ (· ≫ Φ) ∘ E_G⁻¹` with
`E = baseChangePointsEquiv b _ pt`.

- Torus points. Write a torus point as `t = E_T t₀`, with `E_T` the adjunction for the torus.
  The base change of `i` is the canonical identification `splitTorus.baseChangeIso` followed by
  the field-fibre torus map (definition of `baseChangeHom`). With the hypothesis on `Φ` this gives
  `Ψ (t ≫ i) = t ≫ i'`, via `baseChangePointsEquiv_comp`.
- Simple roots. `u_a(c)` at `fieldPoint R K` is `E_G (uK_a(c))`. Hence `Ψ (u_a(c))` is
  `E_H (uK_a(c) ≫ Φ) = E_H (uK'_a(c)) = u'_a(c)`, by `rootPoint_comp` and the hypotheses. The
  same argument at `c = -1` handles `u_{-a}(-1)`.
- All roots: `map_rootPoint_weylFamily` (module `LocalSplitWeylFamily`).

`IsWeylPoint.baseChange`. Fix a test object `Z` over `Spec K` and a torus point `t`. Apply the
injective map `E = baseChangePointsEquiv b G Z`.
- The Weyl point pulled back to `Z` is a product of root points (`constantPoint_weylPoint`).
  Under `E` it becomes the corresponding product over `Z' = (Over.map b).obj Z`
  (`baseChangePointsEquiv_rootPoint`), which is the Weyl point of `u`, `v` pulled back to `Z'`.
- Torus points: `baseChangePointsEquiv_torus` (module `LocalSplitBigCellProof`).
- The exponent automorphism commutes with base change (Library
  `splitTorus.exponentIso_baseChange`).
The required equation is then the hypothesis over `R`, applied at `Z'`.

## Provenance

These are internal lemmas for the proof of the Isomorphism Theorem over a reduced local ring
(`LocalSplitReducedIsomorphismTheoremStatement`), written for this project. They pass from an
isomorphism of a field fibre to the point-level data used by the gluing argument
(`nonempty_iso_of_fieldAlgebras`), and from Weyl points over `R` to Weyl points on field fibres.
The base change of root maps is Worker 712's module `LocalSplitBigCellProof`. The proofs follow
no particular printed source.
