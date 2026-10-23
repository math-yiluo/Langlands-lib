# Semilocal coinduction for the idele group

This module has two parts. The first part is pure group cohomology, in the
namespace `Langlands.Shapiro`. It proves Shapiro's lemma along an injective
group homomorphism `φ : H →* G`, using the explicit map (restriction of
cochains along `φ`, then evaluation at the identity). It also builds a coset
sum out of a coinduced representation. The second part, in the namespace
`Langlands.ClassField.Global`, applies this to the idele group `J_E` and the
published decomposition map `decompositionHom v w : Gal(E_w/F_v) → Gal(E/F)`.
The main result is that the local map
`ideleLocalMap v w n : Hⁿ(Gal(E/F), J_E) → Hⁿ(Gal(E_w/F_v), E_wˣ)` has an
explicit section in every degree `n`. This section is killed by the local
map at every finite place `w'` that is not a Galois conjugate of `w`.

Only finite places are treated. The module does not prove that the semilocal
projection is an isomorphism onto the coinduced module. It does not decompose
`Hⁿ(Gal(E/F), J_E)` into a sum over places and proves no vanishing results.

## Shapiro's lemma along an injective homomorphism

Let `k`, `G` and `H` be in one universe `Type u`, with `k` a commutative ring,
`G` and `H` groups, and `φ : H →* G`. Mathlib's coinduced representation
`Rep.coind φ A` of an `H`-representation `A` consists of the functions
`f : G → A` with `f (φ h * g) = h • f g`. The group `G` acts by
`(g • f) x = f (x * g)`.

- `coindEvalOf φ A : Res_φ (Coind_φ A) ⟶ A` is evaluation at the identity,
  `f ↦ f 1`. `coindEvalOf_hom_apply` gives its value.
- `shapiroMapOf φ A n : Hⁿ(G, Coind_φ A) ⟶ Hⁿ(H, A)` is Mathlib's
  `groupCohomology.map φ (coindEvalOf φ A) n`.

Now let `φ` be injective (`hφ`). Let `H ≃* φ(H)` be Mathlib's
`MonoidHom.ofInjective hφ`.

- `coindToRange hφ A` and `coindOfRange hφ A` are the identity on functions.
  They go between `Coind_φ A` and the module coinduced along the inclusion of
  the subgroup `φ(H)`, where `A` is viewed as a `φ(H)`-representation through
  the inverse of `H ≃* φ(H)`.
- `resRangeHom hφ A` is the identity of `A`. Its source is `A` restricted
  along `H ≃* φ(H)` and then back along the inverse.
- `shapiroMapOf_eq`: `shapiroMapOf φ A n` is the composite of three maps. The
  first is the map induced by `coindToRange`. The second is the published
  Shapiro map `Langlands.Shapiro.shapiroMap` for the subgroup `φ(H)`. The
  third is the map along `H ≃* φ(H)` induced by `resRangeHom`.
- `isIso_shapiroMapOf hφ A n`: `shapiroMapOf φ A n` is an isomorphism for
  every `n`. In the factorization above, the first map is an isomorphism since
  `coindToRange` is one. The second is an isomorphism by the published
  `isIso_shapiroMap`. The third is Mathlib's `groupCohomology.mapIso` for the
  group isomorphism `H ≃* φ(H)` and the identity of `A`.
- `shapiroIsoOf hφ A n` is the resulting isomorphism
  `Hⁿ(G, Coind_φ A) ≅ Hⁿ(H, A)`. `shapiroIsoOf_hom` says its forward map is
  `shapiroMapOf φ A n`.

Let `B` be a `G`-representation and `π : Res_φ B ⟶ A` a morphism of
`H`-representations. Mathlib's `Rep.resCoindToHom φ B A π : B ⟶ Coind_φ A`
is the adjoint morphism `b ↦ (g ↦ π (g • b))`. No injectivity is assumed in
the next two lemmas.

- `res_resCoindToHom_comp_coindEvalOf`: the adjoint morphism, restricted
  along `φ` and followed by `coindEvalOf φ A`, is `π`.
- `map_resCoindToHom_comp_shapiroMapOf`: the map `Hⁿ(G, B) ⟶ Hⁿ(G, Coind_φ A)`
  induced by the adjoint morphism, followed by `shapiroMapOf φ A n`, is the
  map `groupCohomology.map φ π n`.

## The coset sum

Keep `φ : H →* G`, and let `ι : A ⟶ Res_φ B` be a morphism of
`H`-representations.

- `cosetTerm φ ι c` is a `k`-linear map `Coind_φ A → B` for each left coset
  `c = x φ(H)` in `G ⧸ φ(H)`. It sends `f` to `x • ι (f x⁻¹)`. This does not
  depend on the representative `x`: replacing `x` by `x φ(h)` changes
  `f x⁻¹` to `h⁻¹ • f x⁻¹`, and `ι` is `H`-equivariant. `cosetTerm_mk` gives
  the value at the coset of `x`.

The rest of this section assumes `[Fintype (G ⧸ φ(H))]`.

- `coindSum φ ι : Coind_φ A ⟶ B` is the morphism of `G`-representations
  `f ↦ ∑_{x φ(H) ∈ G ⧸ φ(H)} x • ι (f x⁻¹)`. Its `G`-equivariance comes from
  reindexing the sum by left multiplication by `g` on the cosets.
  `coindSum_hom_apply` gives its value.
- `coindSum_comp_resCoindToHom`: assume `π (ι a) = a` for all `a`, and
  `π (g • ι a) = 0` for all `a` and all `g ∉ φ(H)`. Then `coindSum φ ι`
  followed by `Rep.resCoindToHom φ B A π` is the identity of `Coind_φ A`.
  At `g`, only the coset of `g⁻¹` contributes to `π (g • coindSum φ ι f)`,
  and it contributes `f g`.

## The idele group

Let `E / F` be a normal extension of number fields, `v` a finite place of `F`,
and `w` a finite place of `E` over `v`. `J_E` is the published
`relativeIdeleRepresentation F E` of `Gal(E/F)`. `E_wˣ` is the published
`unitsRepresentation` of `Gal(E_w/F_v)`.

- `exists_completionEquiv_of_finitePlaceEquiv_eq`: let `e : K ≃+* L` be a
  ring isomorphism of number fields, and `p`, `q` finite places of `L`, `K`
  with `finitePlaceEquiv e p = q`. Then there is a continuous ring
  isomorphism `K_q ≃+* L_p` that extends `e` on the image of `K`. It is the
  published `finiteCompletionEquiv e p` after substituting the equation.
- `ideleCoordinate_relativeIdeleAut_ofAdicCompletion_of_ne`: let `w`, `w'`
  be finite places of `E`, let `g ∈ Gal(E/F)` with
  `finitePlaceEquiv g.toRingEquiv w' ≠ w`, and let `y ∈ E_wˣ`. Apply `g` to
  Mathlib's idele `IdeleGroup.ofAdicCompletion (𝓞 E) E w y` (coordinate `y`
  at `w`, `1` at every other place). The `w'`-coordinate of the result is
  `1`. This lemma needs no normality and no places of `F`.
- `decompositionHom_injective`: `decompositionHom v w` is injective. Two
  `F_v`-automorphisms of `E_w` with the same restriction to `E` are equal,
  because both are continuous and `E` is dense in `E_w`.
- `mem_range_decompositionHom_iff`: `g ∈ Gal(E/F)` lies in the image of
  `decompositionHom v w` exactly when `finitePlaceEquiv g.toRingEquiv w = w`. That is,
  the image is the stabilizer of `w`. One direction is the published
  `finitePlaceEquiv_decompositionHom`. For the other, a `g` fixing `w`
  extends to a continuous ring automorphism of `E_w` by the previous lemma.
  This automorphism is `F_v`-linear, because it fixes the dense image of `F`
  in `F_v`, and it restricts to `g` on `E`.
- `ideleSemilocalProjection v w : J_E ⟶ Coind(E_wˣ)` is
  `Rep.resCoindToHom` of the published `ideleLocalProjection v w`, with
  coinduction along `decompositionHom v w`. It sends `x` to the function
  `g ↦ (g • x)_w`.
- `ideleLocalMap_eq`: `ideleLocalMap v w n` is the map induced by
  `ideleSemilocalProjection v w` followed by `shapiroMapOf`. This is
  `map_resCoindToHom_comp_shapiroMapOf`.

The rest of this section assumes
`[Fintype (Gal(E/F) ⧸ (decompositionHom v w).range)]`.

- `ideleSemilocalSection v w : Coind(E_wˣ) ⟶ J_E` is `coindSum` of the
  published single-coordinate embedding `ideleLocalEmbedding v w`. It sends
  `f` to `∑_{g D_w} g • ι_w (f g⁻¹)`, where `D_w` is the image of
  `decompositionHom v w`. In terms of places, `g • ι_w (f g⁻¹)` is the idele
  with coordinate `g (f g⁻¹)` at the place `g w` and `1` elsewhere.
- `ideleSemilocalSection_comp_ideleSemilocalProjection`: the semilocal
  section followed by the semilocal projection is the identity of
  `Coind(E_wˣ)`. This is `coindSum_comp_resCoindToHom`. Its first hypothesis
  is the published `ideleCoordinate_ofAdicCompletion_self`. Its second
  hypothesis follows from the coordinate lemma above with `w' = w` and
  `mem_range_decompositionHom_iff`.
- `ideleLocalSection v w n : Hⁿ(Gal(E_w/F_v), E_wˣ) ⟶ Hⁿ(Gal(E/F), J_E)` is
  the inverse of `shapiroIsoOf (decompositionHom_injective v w)` followed by
  the map induced by `ideleSemilocalSection v w`.
- `ideleLocalSection_comp_ideleLocalMap`: `ideleLocalSection v w n` followed
  by `ideleLocalMap v w n` is the identity. So `ideleLocalMap v w n` is a
  split epimorphism in every degree `n`.

## Places that are not conjugate

Now let `v`, `v'` be finite places of `F`, and `w`, `w'` finite places of
`E` over `v`, `v'` respectively. Assume
`[Fintype (Gal(E/F) ⧸ (decompositionHom v w).range)]`. Assume also that no
`g ∈ Gal(E/F)` has `finitePlaceEquiv g.toRingEquiv w' = w` (hypothesis
`h`). Since `g` ranges over all of `Gal(E/F)`, this says that `w'` is not
a Galois conjugate of `w`. Mathematically it holds whenever `v' ≠ v`, but the
module does not prove this, and the lemmas take `h` itself as hypothesis.

- `ideleSemilocalSection_comp_ideleLocalProjection_of_ne`: the semilocal
  section at `w`, restricted along `decompositionHom v' w'` and followed by
  the published `ideleLocalProjection v' w'`, is the zero morphism. Each
  summand `x • ι_w (f x⁻¹)` of the coset sum has `w'`-coordinate `1` by the
  coordinate lemma.
- `ideleLocalSection_comp_ideleLocalMap_of_ne`: `ideleLocalSection v w n`
  followed by `ideleLocalMap v' w' n` is zero, for every `n`. By
  `groupCohomology.map_comp` the composite factors through the map induced
  by the previous zero morphism.

## Sources and provenance

Milne, *Class Field Theory* (v4.03, 2020), Chapter VII §2, printed
pp. 203–204 (PDF pp. 212–213), has the semilocal theory. Lemma 2.1 gives the
Galois action on `∏_{w|v} L_w`. In Proposition 2.2,
`α ↦ f_α`, `f_α(σ) = σ(α(σ⁻¹ w₀))`, is an isomorphism of `G`-modules from
`∏_{w|v} L_w` to `Ind_{G_{w₀}}^G L_{w₀}`, and its inverse is
`f ↦ α_f`, `α_f(σ w₀) = σ(f(σ⁻¹))`. These statements hold also for `L_wˣ` and
`U_w`. Proposition 2.3 combines this with Shapiro's lemma. Milne's
`Ind_H^G` has the same conventions as Mathlib's `Rep.coind`. Milne's `f_α`
is `ideleSemilocalProjection` restricted to the factors over `v`. Milne's
inverse `α_f` is `ideleSemilocalSection`. Artin–Tate, *Class Field Theory*
(AMS Chelsea, 2009), Preliminaries §1, printed pp. 1–2 (PDF pp. 10–11),
describes the same semilocal isomorphism
`Hʳ(G, ∏_{P|p} K_Pˣ) ≅ Hʳ(G_P, K_Pˣ)` through the decomposition group.

The Shapiro map along an injective homomorphism is the map of Serre,
*Local Fields*, Chapter VII §5, exercise, printed pp. 116–117
(PDF pp. 122–123), there stated for a subgroup. The Lean proof is internal.
It reduces to the published subgroup case `Langlands.Shapiro.isIso_shapiroMap`
through the range of `φ`. The coset sum and its section lemma are internal
Lean forms of Milne's inverse `α_f`. Here they are applied to all of `J_E`
rather than to the factors over `v`. Only the one-sided identity
(section followed by projection) is proved. The orthogonality lemmas for
non-conjugate places are internal. They express that `α_f` is supported on
the places over `v`.
