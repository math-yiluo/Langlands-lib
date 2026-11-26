# The birational group law on ω-minimal models and its solution

The module `Langlands.AbelianScheme.NeronModelOfWeakNeronModelStatement` states the step
of the construction of Néron models that passes from a weak Néron model of an abelian
variety to an `R`-birational group law whose solution is a Néron model. It follows Bosch,
Lütkebohmert and Raynaud, *Néron Models* (1990), §4.3, Propositions 4 and 5, printed
pp. 106–107, and §4.4, Corollary 4, printed pp. 110–111 (literature ID
`bosch-lutkebohmert-raynaud-1990-neron-models`, file SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`; printed page `p` is
PDF page `p + 7`). The module states a proposition and proves nothing.

## The proposition

`NeronModelOfWeakNeronModelStatement.{u}` quantifies over a discrete valuation ring `R`
with fraction field `K`, an abelian variety `B` over `K` (`AbelianScheme (Spec K)`), and
a scheme `W` over `Spec R` which is smooth, separated, locally of finite type and
quasi-compact, whose generic fibre `(Over.pullback (Spec K ⟶ Spec R)).obj W` is
isomorphic to `B.X` over `Spec K`, and which has the weak Néron mapping property
`WeakNeronMappingProperty R K W.hom`. It asserts a scheme `X` over `Spec R`, an
isomorphism of `B.X` with the generic fibre of `X` over `Spec K`, and a
`BirationalGroupLaw X.hom` `m` such that:

1. `X` is smooth, separated, locally of finite type, quasi-compact and surjective over
   `Spec R`;
2. every point of `X ×_R X` over the generic point of `Spec R` lies in the domain of `m`
   and in the images of both universal translations of `m`;
3. for every solution `σ` of `m` with `σ.domain = ⊤`, the structure morphism of the group
   scheme `σ.group` has the Library's Néron model properties
   `NeronModelInfra.NeronModelPropertyBundle R K` (smooth, separated, locally of finite
   type, quasi-compact, with the Néron mapping property).

The definitions `BirationalGroupLaw`, `BirationalGroupLaw.Solution`, `leftTranslation`
and `rightTranslation` are in `Langlands.AlgebraicGeometry.BirationalGroupLaw`, and
`WeakNeronMappingProperty` is in `Langlands.AbelianScheme.WeakNeronMappingProperty`.

## Correspondence with the source

In BLR §4.3, `X_K` is a smooth `K`-group scheme of finite type with bounded
`K^sh`-points (for instance an abelian variety), `ω` a generating left-invariant
differential form of top degree, and a weak Néron model is given. The `ω`-minimal
`R`-models (4.3/2) are glued along the generic fibre to an `R`-model `X` (4.3/4), which is
smooth, separated, faithfully flat and of finite type with generic fibre `X_K`; by 4.3/5
the group law `m_K` extends to an `R`-birational group law `m` on `X`. By 4.3/6 (proved
as 5.1/5) `m` has a solution `X̄`, and 4.4/4 shows that `X̄` is a Néron model of `X_K`.

- Clause 1 is the list of properties of `X` in 4.3/4; faithful flatness is flatness,
  given by smoothness, together with surjectivity.
- Clause 2 records that `m` extends the group law of the generic fibre: on `X_K`, `m_K`
  is defined everywhere and its universal translations are isomorphisms. This is the
  hypothesis under which BLR 5.1/5 provides a solution containing all of `X`.
- Clause 3 is 4.4/4 for solutions containing all of `X`. Solutions are unique up to
  isomorphism (BLR 5.1/3), so this is the solution of 4.3/6.
- The weak Néron model of the source is replaced by a single model `W` with the weak
  Néron mapping property, which is the property of weak Néron models used in §4.3
  (3.5/3 and 3.5/4).
- The proposition does not state that `m` restricts to the group law of `B` on the
  generic fibre, although the construction gives this. Clause 3 concerns only the
  underlying scheme of the solution, and the group law of a Néron model of `B.X` is
  determined by the Néron mapping property (BLR 1.2/6).
