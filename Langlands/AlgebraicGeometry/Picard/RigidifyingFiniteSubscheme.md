# A finite subscheme detecting global functions after every base change

Module `Langlands.AlgebraicGeometry.Picard.RigidifyingFiniteSubscheme`, namespace
`Langlands.AlgebraicGeometry.Picard.RigidifyingSubscheme`.

This internal module constructs the finite subscheme used in the proof of
`Langlands.AlgebraicGeometry.Picard.FieldEtaleFppfClassSheafStatement`. For a proper scheme
`X` over a field `k`, it produces a scheme `Z`, finite over `k`, and a morphism `z : Z ⟶ X`
such that pulling back global functions along `T ×_k Z ⟶ T ×_k X` is injective for every test
`T`. No hypothesis beyond properness is used: `X` may be nonreduced or disconnected, and `k`
may be imperfect.

## Commutative algebra

Let `C` be a finitely generated algebra over a field `k`.

- `finite_quotient_pow`: for a maximal ideal `m`, every `C ⧸ m ^ n` is finite-dimensional.
  `C ⧸ m` is finite over `k` by Zariski's lemma (Mathlib's
  `finite_of_finite_type_of_isJacobsonRing`). The kernel of `C ⧸ m ^ n → C ⧸ m` is
  finitely generated and nilpotent, so Mathlib's `Module.finite_of_surjective_of_ker_le_nilradical`
  applies.
- `finite_quotient_inf`: if `C ⧸ I` and `C ⧸ J` are finite-dimensional, so is `C ⧸ (I ⊓ J)`,
  since it embeds in `(C ⧸ I) × (C ⧸ J)`.
- `exists_ideal_not_mem`: a nonzero `v` lies outside some ideal of finite codimension. Choose a
  maximal ideal `m` containing the annihilator of `v`. If `v` were in every `m ^ n`, its image
  in the Noetherian local ring `C_m` would lie in every power of the maximal ideal, hence be
  `0` by Krull's intersection theorem (`Ideal.iInf_pow_eq_bot_of_isLocalRing`). Then some
  `s ∉ m` would kill `v`, contradicting the choice of `m`.
- `exists_ideal_inf_eq_bot`: a finite-dimensional subspace `V ⊆ C` meets some ideal `I` with
  `C ⧸ I` finite-dimensional only in `0`. The proof is by induction on the dimension of
  `V ∩ I₀`, starting from `I₀ = C`. If `0 ≠ v ∈ V ∩ I₀`, intersect `I₀` with an ideal of finite
  codimension avoiding `v`; this strictly lowers the dimension.

## Charts

Let `f : X ⟶ Spec k` be proper. `Γ(X, ⊤)` is finite over `k` (the published
`FieldGlobalFunctions.finite_algebra`).

- `exists_chart`: for an affine open `U` there are a scheme `Z` and `z : Z ⟶ X` such that
  `z ≫ f` is finite and every global function `a` with `z.appTop a = 0` restricts to `0` on `U`.
  Let `C = Γ(U, ⊤)`. It is finitely generated over `k` because `U ⟶ Spec k` is locally of
  finite type with affine source and target. Take `V`, the image of the `k`-linear restriction
  `Γ(X, ⊤) → C`, and `I` from `exists_ideal_inf_eq_bot`. Set
  `Z = Spec (C ⧸ I) ⟶ Spec C ≅ U ⟶ X`. Then `z ≫ f` is `Spec` of `k → C ⧸ I` (the published
  `FieldGlobalUnits.toSpecΓ_over`), so it is finite. On global functions `z` is restriction to
  `U` followed by the quotient map, so a function killed by `z` restricts into `V ∩ I = 0`.
- `exists_finset`: finitely many affine opens are handled at once by a finite coproduct of such
  charts (induction on the finite set; Mathlib's instance that `coprod.desc` of finite
  morphisms is finite).
- `exists_finite_injective`: `X` is quasi-compact, so finitely many affine opens cover it. A
  global function vanishing on each of them has all germs zero (stalk maps of open immersions
  are isomorphisms), hence is zero (`TopCat.Presheaf.section_ext`). So the map on global
  functions of the coproduct chart is injective.

## Injectivity after base change

`injective_zRel_appTop`. Let `f : X ⟶ Spec k` and `g : Z ⟶ Spec k` be proper, `z : Z ⟶ X`
with `z ≫ f = g`, and `z.appTop` injective. Then for every `T : Over (Spec k)` the map on
global functions of `(SubschemeRigidification.zRel f g z hz).app T : T ×_k Z ⟶ T ×_k X` is
injective. Here `T` is arbitrary, including non-affine and non-quasi-compact tests.

Proof. The pullback of global functions `Γ(X) → Γ(Z)` (published `FieldGlobalUnits.sectionsMap`)
is an injective map of `k`-vector spaces, so it has a `k`-linear left inverse. Take the
published comparison maps `FieldGlobalFunctions.directImageSheafMap` from the pullback to `T` of
`Γ(X)~` (respectively `Γ(Z)~`) to the direct image of the structure sheaf of `T ×_k X`
(respectively `T ×_k Z`). They are isomorphisms for proper schemes over a field
(`FieldGlobalFunctions.isIso_directImageSheafMap`). By `FieldGlobalUnits.directImageSheafMap_naturality`
they intertwine the pullback of `sectionsMap` with the map of direct images induced by
`zRel.app T` (`FieldGlobalUnits.directImageMap`). That map is therefore split injective as a
morphism of `O_T`-modules, so it is injective on sections over `T`. On these sections it is the
map on global functions of `zRel.app T` (`directImageMap_top`).

## Provenance

Internal. Detecting global functions by finitely many infinitesimal neighbourhoods of closed
points, and flat base change for global functions over a field, are standard. The formalization
uses only published Library results and Mathlib.
