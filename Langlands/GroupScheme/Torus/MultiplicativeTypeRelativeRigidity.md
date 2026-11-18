# Rigidity of families of homomorphisms between groups of multiplicative type

Worker 5698.

This module extends the diagonalizable rigidity of
[`Torus.RelativeDiagonalizableRigidity`](RelativeDiagonalizableRigidity.md) to groups of
multiplicative type (`RelativeMultiplicativeType.IsMultiplicativeType`, Conrad, *Reductive group
schemes* (2014), Definition B.1.1) over an arbitrary scheme `S`, with a geometrically connected
parameter scheme. All declarations are in the namespace
`Langlands.GroupScheme.MultiplicativeTypeRigidity`. The statement and its proof are internal to
this project. They are the rigidity input for the centrality results of Conrad, Lemma 3.3.1,
whose proof instead classifies the conjugation action by a map to a finite étale Hom scheme.

## The rigidity predicate

`Rigid X D D'`, for `X : Over S` and `D D' : GroupScheme S`, says: every family

`F : ∀ V : Over S, (V ⟶ X) → (V ⟶ D.X) → (V ⟶ D'.X)`

that is multiplicative in the point of `D` (`F V a (t₁ * t₂) = F V a t₁ * F V a t₂`) and natural
in the test scheme (`F W (f ≫ a) (f ≫ t) = f ≫ F V a t`) satisfies `F V a t = F V a' t` for all
parameters `a a' : V ⟶ X` and points `t : V ⟶ D.X`.

## Base change of a family

For `b : S' ⟶ S`, `baseChangeFamily b F` is the family over `S'` with parameter scheme
`(Over.pullback b).obj X` and groups `(baseChange b).obj D`, `(baseChange b).obj D'`. On an
`S'`-scheme `V`, a parameter and a point are turned into a parameter and a point of
`(Over.map b).obj V` (the scheme `V` viewed over `S`) by the adjunction `Over.mapPullbackAdj b`
and `baseChangePointsEquiv b`, the family `F` is evaluated there, and the result is transported
back. `baseChangeFamily_mul` and `baseChangeFamily_naturality` show that it is again
multiplicative and natural; naturality uses `baseChangePointsEquiv_naturality` and
`Adjunction.homEquiv_naturality_left_symm`.

## Locality

`Rigid.of_cover`: let `𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S` be an fppf cover. If
`Rigid` holds for the base changes of `X`, `D`, `D'` along every member `𝒰.f k`, it holds over
`S`. Proof: two morphisms `V ⟶ D'.X` over `S` are equal if their underlying morphisms agree
after composing with the members of the pulled-back cover `𝒰.pullback₁ V.hom`
(`Precoverage.ZeroHypercover.hom_ext`). The `k`-th member is `V ×_S U_k → V`. The base-changed
family evaluated at the restricted parameters and point equals the transport of `F` restricted to
`V ×_S U_k` (by naturality of `F`), so the hypothesis over `U_k` gives the required equality.

## Results

- `geometricallyConnected_pullback` (instance): `GeometricallyConnected` is stable under base
  change of `X`.
- `rigid_of_isDiagonalizable`: if `X.hom` is geometrically connected and `D`, `D'` are
  diagonalizable, `Rigid X D D'`. The fibres of `X.hom` are connected
  (`Scheme.Hom.isConnected_preimage_singleton`), so this is
  `RelativeDiagonalizableRigidity.eq_of_isDiagonalizable`.
- `rigid_of_isDiagonalizable_of_isMultiplicativeType`: `D` diagonalizable and `D'` of
  multiplicative type. `IsMultiplicativeType D'` provides an fppf cover over whose members `D'`
  is diagonalizable; `D` stays diagonalizable (`IsDiagonalizable.baseChange`) and `Rigid.of_cover`
  applies.
- `rigid_of_isMultiplicativeType`: `D` and `D'` of multiplicative type. The same argument with
  the cover of `D`, using `IsMultiplicativeType.baseChange` for `D'`.
- `eq_of_isMultiplicativeType`: the unfolded form. For `X : Over S` with
  `[GeometricallyConnected X.hom]`, `D`, `D'` of multiplicative type and a multiplicative natural
  family `F`, `F V a t = F V a' t` for all `a a' : V ⟶ X` and `t : V ⟶ D.X`.

No finiteness hypothesis is placed on `D`, `D'`, `X` or `S` beyond those contained in the
definitions of the predicates.
