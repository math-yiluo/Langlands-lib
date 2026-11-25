# Factor projections of a group described by a Weil-restriction chart

Namespace `Langlands.GroupScheme.WeilChart`. This internal construction is the first step of
the proof of `AffineWeilPairSingleChartDescentStatement` (descent of a Weil-restriction
presentation along one étale cover). It describes the normal idempotent endomorphisms of a
group `G` over `Spec A` through a chart, using factor rigidity, and compares two
chart maps. The construction works with points only and never base-changes a Weil restriction.

## Setting

Fix an `A`-algebra `A'`, a finite projective `A'`-algebra `C`, a group scheme `G` over `Spec A`,
an affine group scheme `H` locally of finite type over `Spec C`, and a chart
`P : G_{A'} ≅ AffineWeil.groupScheme A' C H`.

- `chartPointsEquiv P X`: for an `A'`-algebra `X` (with compatible `A`-structure), the points of
  `G` on `X` are the points of `H` on `C ⊗[A'] X`. It composes the base-change point
  equivalence `affinePointsBaseChangeMulEquiv`, the chart `P`, and `AffineWeil.pointsEquiv`.
  `chartPointsEquiv_naturality` gives naturality.
- `chartProj P X e`: the factor projection of `G(X)` attached to `e ∈ C ⊗[A'] X`. It is
  `IdempotentPoints.proj H e` transported by `chartPointsEquiv`, and is natural
  (`chartProj_naturality`).

## Chart factor projections over a test algebra

Let `T` be an `A`-algebra and `f : A' →ₐ[A] T` a chart map. `GFun G T` is the group functor of
`G` on `T`-algebras (`Under T`). `chartAlgebra f` makes `T` an `A'`-algebra, and
`underAlgebra f X` does the same for every `T`-algebra `X`. For an idempotent `e` of
`C ⊗[A', f] T`, `chartFactor P f e he : GFun G T ⟶ GFun G T` acts on the `X`-points by
`chartProj` with the image `baseIdem f X e` of `e`. The definition raises `maxRecDepth` for a
definitional unfolding in the naturality proof. Lemmas:

- `chartFactor_comp`: composition corresponds to the product of the idempotents;
  `chartFactor_idem`;
- `gpt_chartFactor_conj`: chart factor projections are normal;
- `grestrict_chartFactor`: restriction along `χ : T ⟶ T₁` gives the chart factor projection of
  the image idempotent for the chart map `χ ∘ f`;
- `gpt_chartFactor_zero`: the projection of `0` is trivial.

## Rigidity through a chart

Rigidity (`WeilFactorIdempotentRigidityStatement`) is stated for the group functor of
`R_{C/A'}(H)` on algebras under `T` regarded as an `A'`-algebra (`chartTest f`). The module
compares the two settings:

- `extObj f` turns a `T`-algebra into an algebra under `chartTest f`. `resObj f`/`resHom f`
  turn an algebra under `chartTest f` into a `T`-algebra, with `A`-structure restricted
  along `A → A'` (`restrictAlgebra`, `resInst`). Round trips are isomorphic to the identity
  (`resExtIso`, `extResIso`), through identity maps of the underlying rings.
- `transportEnd P f ψ` transports an endomorphism of `GFun G T` to the group functor of
  `R_{C/A'}(H)` over `chartTest f`. It is natural, multiplicative (`transportEnd_comp`) and
  preserves normality (`pt_transportEnd_conj`).
- `transportEnd_chartFactor`: the transported chart factor projection is
  `WeilFactor.factorProjection` (module `WeilFactorProjection`). The comparison is definitional on objects of the form
  `extObj f X`, and `app_eq_of_iso` together with `extResIso` extends it to all objects.

From these, with `[Algebra.Etale A' C]`, `IsReductive H` and almost simple geometric fibres of `H`:

- `exists_chartFactor`: every normal idempotent endomorphism of `GFun G T` is a chart factor
  projection. Rigidity gives the idempotent for the transported endomorphism.
  `app_resObj_eq_of_transportEnd` and `resExtIso` transport the equality back.
- `chartFactor_injective`: chart factor projections determine their idempotents, by
  `WeilFactor.factorProjection_injective`.

## Chart transfer

For two chart maps `f₁ f₂ : A' →ₐ[A] T`, `chartTransfer P hR hred hsimple f₁ f₂ e` is the unique
idempotent of `C ⊗[A', f₂] T` whose chart factor projection through `f₂` equals that of `e`
through `f₁` (`chartTransfer_spec`, `chartFactor_chartTransfer`, `chartTransfer_eq`). It
satisfies:

- `chartTransfer_self` (identity for `f₁ = f₂`) and `chartTransfer_trans` (cocycle);
- `chartTransfer_mul` and `chartTransfer_zero` (multiplicativity on idempotents and `0 ↦ 0`);
- `chartTransfer_map` (naturality along `χ : T ⟶ T₁`, for the chart maps `χ ∘ fₖ`).

The cocycle and identity properties hold because every transfer passes through the same
endomorphisms of the functor of `G`. These transfers are the input to the algebra recovery that
produces the descent datum of the coefficient algebra.

## Provenance

This is an internal construction derived from the proof of Proposition 6.4.4 in Conrad,
*Reductive group schemes* (2014): uniqueness of Weil pairs makes the descent data canonical.
It uses only factor rigidity and the published point descriptions of Weil restriction and base
change.
