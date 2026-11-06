# The orbit map of a cut-out subscheme into a Grassmannian

The theorem `Langlands.GroupScheme.SelfNormalizingAmbient.exists_proper_orbit_map` works over a
commutative ring `R`. It concerns a group-valued functor `F` on commutative `R`-algebras,
corepresented by `B`, and an ideal `K` of `B` containing a power `I ^ (n + 1)` of the augmentation
ideal. If `B ⧸ I ^ (n + 1)` and `B ⧸ K` are finite projective `R`-modules, it gives a proper,
locally finitely presented scheme `Y` over `Spec R` and a morphism `r` from the group scheme of `F`
to `Y`. Two points `g` and `h` of the group scheme over any `T` have the same image under `r`
exactly when `g⁻¹ * h` stabilizes the subfunctor cut out by `K`. So the fibres of `r` are the
cosets of that stabilizer.

## Provenance

This module is internal supporting content for the task proving
`Langlands.GroupScheme.SelfNormalizingProperAmbientStatement`. It formalizes the orbit map in
Conrad's proof of Theorem 2.3.6(1) (Conrad, *Reductive group schemes*, 2014, source
`conrad-2014-reductive-group-schemes`, printed pp. 73–74). There `H_n ⊂ G_n` are the `n`-th
infinitesimal neighbourhoods of the identity, which are finite locally free over `S`. The group
`G` acts on the Grassmannian `Gr_N(G_n)` of rank-`N` quotient bundles of the coordinate algebra
of `G_n` through its conjugation action on `G_n`. The stabilizer of the point `ξ` given by `H_n`
is `N_G(H_n)`, and the orbit map `G → Gr_N(G_n)` through `ξ` is considered.

The Lean version differs from the source as follows.

- It works over any commutative ring, with no Noetherian reduction.
- `K` is any ideal of `B` with `I ^ (n + 1) ≤ K` and `B ⧸ K` finite projective; it is not
  required to come from a subgroup.
- The rank of `B ⧸ K` need not be constant. A finite projective complement `C`, with
  `(B ⧸ K) × C ≅ R ^ b`, fixes this. The Grassmannian is that of rank-`b` quotients of
  `M = (B ⧸ I ^ (n + 1)) × C`.
- The point attached to `g ∈ F S` is the kernel of `q_g × id`, an `S`-linear map from
  `S ⊗[R] ((B ⧸ I ^ (n + 1)) × C)` to `(S ⊗[R] (B ⧸ K)) × (S ⊗[R] C)`. Here
  `q_g : S ⊗[R] (B ⧸ I ^ (n + 1)) → S ⊗[R] (B ⧸ K)` classifies the conjugate `g u g⁻¹` of the
  universal point `u` of the subscheme cut out by `K`. So the point is the ideal of the conjugate
  of that subscheme by `g`, as in Conrad.
- The fibre statement is proved directly, with the stabilizer defined by the two-sided condition
  `Stabilizes` of the module `SelfNormalizingAmbient.Stabilizer`. No group action on the
  Grassmannian is formalized.

The Grassmannian scheme, its properness and its finite presentation come from
`Module.Grassmannian.exists_scheme_represents_isProper_locallyOfFinitePresentation`
(`Langlands.RingTheory.Grassmannian.ProperFinitePresentation`).

## Conventions

`R : CommRingCat.{u}`, `F : CommAlgCat.{u} R ⥤ GrpCat.{u}`, `B : CommAlgCat.{u} R` and
`e : (F ⋙ forget GrpCat).CorepresentableBy B`. `augIdeal e` is the augmentation ideal `I` of the
module `Stabilizer`, and `VanishesOn e K x` and `Stabilizes e K g` are as defined there. From the
Library module `Langlands.GroupScheme.CorepresentedNormalizer`, `tensorQuotient L S` is
`S ⊗[R] (B ⧸ L)` as an object of `CommAlgCat R`, `tensorQuotientLeft L S` is the inclusion of
`S`, and `universalCutPoint e L S ∈ F (tensorQuotient L S)` is classified by
`B → B ⧸ L → S ⊗[R] (B ⧸ L)`. From `Langlands.GroupScheme.CorepresentedPoints`, `groupScheme F e`
is the group scheme of `F` over `Spec R`, and `pointsEquiv F e T` identifies its `T`-points with
`F` of the global sections of `T`. `G(k, V; S)` is Mathlib's Grassmannian of submodules of `V`
with finite projective quotient of constant rank `k`. In the main section `m` is an exponent with
`hK : augIdeal e ^ m ≤ K`.

## Declarations

### Grassmannian and module lemmas

In the namespace `Module`:

- `Grassmannian.eq_of_le`: two points `N₁ ≤ N₂` of `G(k, V; S)` are equal.
- `Grassmannian.ofKer Φ hΦ eN`: the kernel of a surjective `S`-linear map `Φ : V → N` together
  with `eN : N ≃ₗ[S] (Fin k → S)`, as a point of `G(k, V; S)`.
- `exists_prod_linearEquiv_pi R P`: a finite projective `R`-module `P` has a finite projective
  complement `C ≤ R ^ b` with `P × C ≃ₗ[R] (Fin b → R)`.

### Conjugates of the universal cut point

In the namespace `Langlands.GroupScheme.Corepresented`, for an ideal `L` of `B` and `g ∈ F S`:

- `universalCutConj e L g ∈ F (tensorQuotient L S)` is `g u g⁻¹`, where `u` is
  `universalCutPoint e L S` and `g` is mapped along `tensorQuotientLeft L S`.
- `map_map_eq_map_comp`, `map_universalCutConj` and `universalCutConj_one`: images of these
  conjugates under algebra maps, and the case `g = 1`.
- `tensorQuotient_hom_ext`: two algebra maps out of `tensorQuotient L S` are equal if they agree
  on `S` and send `universalCutPoint e L S` to the same point.
- `conjMap e L₁ L₂ g h`: given `h : VanishesOn e L₁ (universalCutConj e L₂ g)`, the algebra map
  `tensorQuotient L₁ S ⟶ tensorQuotient L₂ S` that is the inclusion on `S` and sends the
  universal cut point to `universalCutConj e L₂ g` (`left_conjMap`, `map_conjMap`).

### Orbit maps

- `tensorQuotientBaseChange L φ` is `φ ⊗ id` for `φ : S ⟶ S'`;
  `left_tensorQuotientBaseChange`, `map_tensorQuotientBaseChange` and
  `tensorQuotientBaseChange_apply` describe it.
- `jetMap e m g`: the endomorphism `conjMap` of `tensorQuotient (augIdeal e ^ m) S` classifying
  `universalCutConj e (augIdeal e ^ m) g`. `left_jetMap` and `map_jetMap` are its defining
  properties.
- `orbitMap e hK g : tensorQuotient (augIdeal e ^ m) S ⟶ tensorQuotient K S`, the `conjMap`
  classifying `universalCutConj e K g`. `left_orbitMap` and `map_orbitMap` are its defining
  properties.
- `jetMap_inv_comp`: `jetMap e m g⁻¹ ≫ jetMap e m g = 𝟙 _`. Also `jetMap_surjective`.
- `orbitMap_eq_jetMap_comp`: `orbitMap e hK g = jetMap e m g ≫ orbitMap e hK 1`.
- `orbitMap_one_tmul`: `orbitMap e hK 1` sends `s ⊗ₜ [b]` to `s ⊗ₜ [b]`.
- `orbitMap_one_surjective` and `orbitMap_surjective`: every orbit map is surjective.
- **`le_ker_orbitMap_iff`**: for an algebra map `χ` out of `tensorQuotient (augIdeal e ^ m) S`,
  the kernel of `orbitMap e hK g` lies in the kernel of `χ` exactly when `x⁻¹ * v * x` vanishes on
  `K`. Here `v` is the image of the universal cut point under `χ` and `x` is the image of `g`.
- **`ker_orbitMap_eq_iff`**: `orbitMap e hK g` and `orbitMap e hK h` have the same kernel exactly
  when `Stabilizes e K (g⁻¹ * h)`.
- `orbitMap_comp_baseChange`: `orbitMap e hK g ≫ tensorQuotientBaseChange K φ` equals
  `tensorQuotientBaseChange _ φ ≫ orbitMap e hK (F.map φ g)`.

### Linear algebra

Fix `C` with `eW : ((B ⧸ K) × C) ≃ₗ[R] (Fin b → R)`.

- `smul_eq_tmul_one_mul`: `s • y = (s ⊗ₜ 1) * y` in `S ⊗[R] A`.
- `orbitLinearMap e hK g`: `orbitMap e hK g` as an `S`-linear map, with `orbitLinearMap_apply`,
  `ker_orbitLinearMap_eq_iff` and the base-change rule `orbitLinearMap_rTensor`.
- `orbitProdMap e hK C g`: the `S`-linear map from `S ⊗[R] ((B ⧸ augIdeal e ^ m) × C)` to
  `(S ⊗[R] (B ⧸ K)) × (S ⊗[R] C)` that is `orbitLinearMap e hK g` on the first factor and the
  identity on the second. It is surjective (`orbitProdMap_surjective`), and
  `orbitProdMap_rTensor` gives its base-change rule.
- `orbitTargetEquiv eW`: the `S`-linear equivalence of that target with `Fin b → S`.
- `orbitPoint e hK S eW g`: `Grassmannian.ofKer` of `orbitProdMap e hK C g`, a point of
  `Module.Grassmannian S (S ⊗[R] ((B ⧸ augIdeal e ^ m) × C)) b`. `orbitPoint_toSubmodule` gives
  its submodule.
- **`orbitPoint_eq_iff`**: `orbitPoint e hK S eW g = orbitPoint e hK S eW h` exactly when
  `Stabilizes e K (g⁻¹ * h)`.
- **`map_orbitPoint`**: for `φ : S ⟶ S'`, `Module.Grassmannian.map φ.hom` sends the orbit point
  of `g` to the orbit point of `F.map φ g`.

### Schemes

Fix a scheme `Gr` over `Spec R` (`p : Gr ⟶ Spec R`) and bijections `pt A` from
`Module.Grassmannian A (A ⊗[R] ((B ⧸ augIdeal e ^ m) × C)) b` to the morphisms
`Spec A ⟶ Gr` over `Spec R`.

- `orbitHom e hK eW pt S x : (algSpec R).obj (op S) ⟶ Over.mk p` classifies
  `orbitPoint e hK S eW x`. `orbitHom_left` gives its underlying morphism.
- `orbitHom_eq_iff`: `orbitHom … S x = orbitHom … S y` exactly when `Stabilizes e K (x⁻¹ * y)`.

The remaining results assume `hpt`, the compatibility of `pt` with base change
(`pt A' (map φ N) = Spec.map φ ≫ pt A N`).

- `map_orbitHom`: `(algSpec R).map φ.op ≫ orbitHom … S x = orbitHom … S' (F.map φ x)`.
- `unit_comp_map_homEquiv_symm`: a morphism `g : T ⟶ (algSpec R).obj (op B)` is the unit of the
  adjunction `algΓAlgSpecAdjunction R` at `T` followed by `algSpec R` applied to the adjoint of
  `g`. This one does not use `hpt`.
- `comp_orbitHom`: for `g : T ⟶ (groupScheme F e).X`, composing `g` with the orbit morphism `r` of
  the universal point `e.homEquiv (𝟙 B)` gives the adjunction unit at `T` followed by
  `orbitHom` of `pointsEquiv F e T g`.
- `comp_orbitHom_eq_iff_of_isIso`: if that adjunction unit is an isomorphism, then
  `g ≫ r = h ≫ r` exactly when `Stabilizes e K (pointsEquiv F e T (g⁻¹ * h))`.
- **`comp_orbitHom_eq_iff`**: the same equivalence for every `T : Over (Spec R)`, assuming
  `B ⧸ K` is a projective `R`-module.

### Export

`Langlands.GroupScheme.SelfNormalizingAmbient.exists_proper_orbit_map F e K n hK` takes
`R : CommRingCat.{u}`, `F`, `B` and `e` as above, `K : Ideal B`, `n : ℕ` and
`hK : Corepresented.augIdeal e ^ (n + 1) ≤ K`. It assumes the instances
`[Module.Finite R (B ⧸ Corepresented.augIdeal e ^ (n + 1))]`,
`[Module.Projective R (B ⧸ Corepresented.augIdeal e ^ (n + 1))]`,
`[Module.Finite R (B ⧸ K)]` and `[Module.Projective R (B ⧸ K)]`, and states

```
∃ (Y : Over (Spec R)) (r : (Corepresented.groupScheme F e).X ⟶ Y),
  IsProper Y.hom ∧ LocallyOfFinitePresentation Y.hom ∧
  ∀ (T : Over (Spec R)) (g h : T ⟶ (Corepresented.groupScheme F e).X),
    g ≫ r = h ≫ r ↔
      Corepresented.Stabilizes e K (Corepresented.pointsEquiv F e T (g⁻¹ * h))
```

## Proof

**Grassmannian lemmas.** For `eq_of_le`, the map `V ⧸ N₁ → V ⧸ N₂` is surjective with projective
target, so it splits. Its kernel is then a finite projective direct summand, and `V ⧸ N₁` is
isomorphic to the product of the kernel and `V ⧸ N₂`. Both quotients have rank `k` at every
prime, so the kernel has rank `0` everywhere and is zero (`rankAtStalk_eq_zero_iff_subsingleton`).
Hence `N₂ ≤ N₁`. For `ofKer`, `V ⧸ ker Φ ≅ N ≅ S ^ k`. For `exists_prod_linearEquiv_pi`, a finite
projective module is a retract of some `R ^ b`, and the kernel of the retraction is the complement.

**Conjugation maps.** `tensorQuotient_hom_ext` holds because a map out of `S ⊗[R] (B ⧸ L)` is
determined on `S` and on `B ⧸ L`, and its value on `B ⧸ L` is read off the image of the
universal cut point through `e`. `conjMap` is `Algebra.TensorProduct.lift` of the inclusion of
`S` and of the classifying map of the conjugate, factored through `B ⧸ L₁`. The vanishing
hypotheses of `jetMap` and `orbitMap` come from `VanishesOn.conj` in `Stabilizer`, applied to the
universal cut point, which vanishes on `augIdeal e ^ m` (by `VanishesOn.mono` and `hK` in the
case of `orbitMap`).

**Surjectivity.** All identities between maps out of `tensorQuotient` are proved by
`tensorQuotient_hom_ext`, computing images of the universal cut point and simplifying in the
group. This gives `jetMap_inv_comp` and `orbitMap_eq_jetMap_comp`. So `jetMap e m g` is
surjective, `orbitMap e hK 1` is the quotient map `id ⊗ (B ⧸ I ^ m → B ⧸ K)`, which is surjective,
and every orbit map is a composite of the two.

**Kernel criterion.** If the kernel of `q = orbitMap e hK g` lies in the kernel of `χ`, then `χ`
factors as `q ≫ ψ`, since `q` is surjective. Then `x⁻¹ * v * x` is the image under `ψ` of the
universal cut point of `K`, which vanishes on `K`. Conversely, if `x⁻¹ * v * x` vanishes on `K`,
`exists_universalCutPoint_of_vanishesOn` gives `ψ` with this image that restricts to `χ` on `S`.
Then `q ≫ ψ = χ` by `tensorQuotient_hom_ext`, so the kernel of `q` lies in the kernel of `χ`.
For `ker_orbitMap_eq_iff`, apply this with `χ` the orbit maps of `h` and of `g` and compare with
`stabilizes_iff_universal` from `Stabilizer`. Both sides then ask that the two conjugates of the
universal cut point by the image of `g⁻¹ * h` vanish on `K`.

**Points of the Grassmannian.** `orbitProdMap` is surjective because each factor is. The kernels
of `orbitProdMap` for `g` and `h` agree exactly when the kernels of the orbit maps agree, since
the second factor is the identity. With `ker_orbitLinearMap_eq_iff` this gives
`orbitPoint_eq_iff`. For `map_orbitPoint`, the base change of a Grassmannian point is the span of
the image of its submodule (`Langlands.Grassmannian.map_toSubmodule_eq_span`). That image lies in
the kernel of the orbit map of `F.map φ g` by `orbitProdMap_rTensor`, which comes from
`orbitMap_comp_baseChange`. Both are points of the same Grassmannian, so `eq_of_le` gives
equality. No exactness of base change is needed.

**Morphisms of schemes.** `orbitHom_eq_iff` follows from the injectivity of `pt S` and
`orbitPoint_eq_iff`. `map_orbitHom` follows from `hpt` and `map_orbitPoint`. In
`comp_orbitHom`, `g` is the adjunction unit followed by `algSpec R` of the adjoint algebra map
`φ : B ⟶ Γ(T)` (`unit_comp_map_homEquiv_symm`). `pointsEquiv F e T g` is `e.homEquiv φ`
(`pointsEquiv_apply`), which is `F.map φ (e.homEquiv (𝟙 B))`. So `map_orbitHom` applies. If the
unit at `T` is an isomorphism, it is an epimorphism and cancels. Then
`comp_orbitHom_eq_iff_of_isIso` reduces to `orbitHom_eq_iff` over `Γ(T)`, using that
`pointsEquiv` is multiplicative.

**General test schemes.** The reverse implication of `comp_orbitHom_eq_iff` follows from
`comp_orbitHom` and `orbitHom_eq_iff` with no hypothesis on `T`. For the forward implication, let
`ψ` classify `pointsEquiv F e T (g⁻¹ * h)`. Since `B ⧸ K` is projective, `stabilizes_iff` from
`Stabilizer` reduces the goal to `ψ a = 0` for `a ∈ subgroupNormalizerIdeal e K`. This is a global
section of `T`, so it suffices that it vanishes on every chart of the affine cover
`T.left.affineCover` (`Scheme.zero_of_zero_cover`). On an affine chart `Tᵢ` the adjunction unit
is an isomorphism (`isIso_unit_app_iff_mem_essImage`, `essImage_algSpec`). The restrictions of
`g` and `h` to `Tᵢ` still have equal images under `r`. So `comp_orbitHom_eq_iff_of_isIso`,
`pointsEquiv_naturality` and `stabilizes_iff` give that the restriction of `ψ a` to `Tᵢ` is `0`.

**Export.** `exists_prod_linearEquiv_pi` gives `C` and `eW` for `B ⧸ K`, with
`(B ⧸ K) × C ≅ R ^ b`. The Grassmannian theorem
`Module.Grassmannian.exists_scheme_represents_isProper_locallyOfFinitePresentation`, applied to
`M = (B ⧸ augIdeal e ^ (n + 1)) × C` and rank `b`, gives `Gr`, `p`, `pt`, `hpt`, properness and
local finite presentation. `M` is finite projective as a product of finite projective modules.
Take `Y = Over.mk p` and `r = orbitHom e hK eW pt B (e.homEquiv (𝟙 B))`. The fibre condition is
`comp_orbitHom_eq_iff`.
