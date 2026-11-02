# Functoriality of the dynamic subgroup functors in the group

This module makes the dynamic subgroup functors `P_G(λ)`, `Z_G(λ)` and `U_G(λ)` of
`Langlands.GroupScheme.Dynamic.Basic` functorial along homomorphisms of group schemes. Fix a
base scheme `S`, group schemes `H` and `G` over `S`, a homomorphism `f : H ⟶ G` and a
cocharacter `λ : 𝔾_{m,S} ⟶ H`. Then `λ ≫ f` is a cocharacter of `G`, and `f` is equivariant
for the conjugation actions of `𝔾_m` through `λ` and through `λ ≫ f`. The module proves that `f`
carries `P_H(λ)`, `Z_H(λ)` and `U_H(λ)` into `P_G(λ ≫ f)`, `Z_G(λ ≫ f)` and `U_G(λ ≫ f)`.
These inclusions are equalities of preimages when `f` is an isomorphism, so conjugation by a
point over the base carries the dynamic subgroups of `λ` onto those of the conjugate
cocharacter. The centralizer inclusion is an equality of preimages whenever `f` is a
monomorphism of schemes.

All statements are about subfunctors of points on every scheme `T` over `S`. `G` and `H` are
arbitrary group schemes over `S`, with no affineness, finiteness or separatedness hypothesis.

## Sources

- Conrad, *Reductive group schemes* (2014), Proposition 4.1.10, pp. 114–115. Part 2: for a
  `𝔾_m`-equivariant map `f : G → G'`, "`f` carries `P_G(λ)` into `P_{G'}(λ')`, `U_G(λ)` into
  `U_{G'}(λ')`, and `Z_G(λ)` into `Z_{G'}(λ')`". Part 1: for a finitely presented closed
  subgroup `H` of `G` stable under the `𝔾_m`-action, `H ∩ P_G(λ) = P_H(λ)`,
  `H ∩ U_G(λ) = U_H(λ)` and `H ∩ Z_G(λ) = Z_H(λ)`. The proof says that both parts are immediate
  from the functorial definitions.
- Conrad, Gabber and Prasad, *Pseudo-reductive groups*, 2nd ed. (2015), p. 49 (PDF page 75),
  in the paragraph after the proof of Lemma 2.1.4: "if `H ⊆ G` is a closed `k`-subgroup scheme through which `λ` factors then
  `H ∩ P_G(λ) = P_H(λ)`". Also p. 51 (PDF page 77): "The equality `H ∩ U_G(λ) = U_H(λ)` holds
  because `H ∩ P_G(λ) = P_H(λ)`".

This module formalizes Conrad's part 2 for the conjugation actions coming from cocharacters,
with `G' = G`, `λ' = λ ≫ f` and the equivariant map a homomorphism. From part 1 it formalizes
only the equalities that hold without a closedness hypothesis. These are the equalities for
isomorphisms, and the centralizer equality for monomorphisms. The equalities
`H ∩ P_G(λ) = P_H(λ)` and `H ∩ U_G(λ) = U_H(λ)` for a closed subgroup `H` are **not** proved
here. They need extensions from `T ×_S 𝔾_{m,S}` to `T ×_S 𝔸¹_S` that land in `G` to land in `H`,
which uses that `T ×_S 𝔾_{m,S}` is schematically dense in `T ×_S 𝔸¹_S`.

## Preimages of subgroup functors

- `SubgroupFunctor.comap f F` is the subgroup functor of `H` whose `T`-points are the points
  `x : T ⟶ H` with `x ≫ f ∈ F(T)`. It is the preimage of `F(T)` under the group homomorphism
  `(yonedaGrp.map f).app (op T)` on points. Restriction along `a : T' ⟶ T` preserves it because
  `(a ≫ x) ≫ f = a ≫ (x ≫ f)`. For a subgroup `H ⊆ G` given by a monomorphism `f`, this is the
  functor `H ∩ F` of the sources.
- `SubgroupFunctor.mem_comap` unfolds membership.
- `comap_id`, `comap_comp`, `comap_mono` (monotone in `F`), `comap_top` and `comap_inf` are the
  formal properties of preimages.
- `range_le_iff_comap_eq_top`: the Library image functor `range f` lies in `F` if and only if
  the preimage of `F` is everything.
- `SubgroupFunctor.IsNormal.comap`: preimages of normal subgroup functors are normal. This holds
  because `x ↦ x ≫ f` is a group homomorphism on points (`MonObj.mul_comp`,
  `GrpObj.inv_comp`).

## Orbits, extensions and limits along a homomorphism

The notions are those of `Dynamic.Basic`. Fix a point `g : T ⟶ H`.

- `Dynamic.orbit_comp_hom`: the orbit map of `g ≫ f` under `λ ≫ f` is the orbit map of `g`
  under `λ`, followed by `f`. In the notation of the sources, `f(t.g) = t.f(g)`. The proof uses
  that composition with `f` preserves products and inverses of points.
- `Dynamic.evalZero_comp`: evaluation at the zero section commutes with composition.
- `Dynamic.IsOrbitExtension.comp_hom`: if `e : T ×_S 𝔸¹_S ⟶ H` extends the orbit map of `g`,
  then `e ≫ f` extends the orbit map of `g ≫ f` under `λ ≫ f`.
- `Dynamic.HasLimit.comp_hom`: if `l` is a limit at zero of the orbit of `g` under `λ`, then
  `l ≫ f` is a limit at zero of the orbit of `g ≫ f` under `λ ≫ f`.

## The inclusions

- `Dynamic.parabolic_le_comap`: `P_H(λ) ≤ f⁻¹ P_G(λ ≫ f)`, by `IsOrbitExtension.comp_hom`.
- `Dynamic.centralizer_le_comap`: `Z_H(λ) ≤ f⁻¹ Z_G(λ ≫ f)`, by `orbit_comp_hom`.
- `Dynamic.unipotent_le_comap`: `U_H(λ) ≤ f⁻¹ U_G(λ ≫ f)`, by `HasLimit.comp_hom` and
  `1 ≫ f = 1` (`MonObj.one_comp`).

## Equalities

- `Dynamic.centralizer_eq_comap_of_mono`: if the underlying morphism `f.hom.hom` of schemes
  over `S` is a monomorphism, then `Z_H(λ) = f⁻¹ Z_G(λ ≫ f)`. If `g ≫ f` is centralized by
  `λ ≫ f`, then `orbit λ g ≫ f = fst ≫ g ≫ f` by `orbit_comp_hom`, and cancelling the
  monomorphism gives `orbit λ g = fst ≫ g`.
- For an isomorphism `e : H ≅ G`:
  - `comp_hom_comp_inv` (`(λ ≫ e) ≫ e⁻¹ = λ`) and `comp_hom_hom_comp_inv_hom`
    (`(g ≫ e) ≫ e⁻¹ = g` on points) are the cancellation rules used below.
  - `Dynamic.parabolic_eq_comap_of_iso`: `P_H(λ) = e⁻¹ P_G(λ ≫ e)`.
  - `Dynamic.centralizer_eq_comap_of_iso`: `Z_H(λ) = e⁻¹ Z_G(λ ≫ e)`.
  - `Dynamic.unipotent_eq_comap_of_iso`: `U_H(λ) = e⁻¹ U_G(λ ≫ e)`.

  In each case one inclusion is the inclusion above for `e`. For the other, apply the inclusion
  for `e⁻¹` to the cocharacter `λ ≫ e` and cancel.

## Conjugation by a point over the base

Let `g : Over.mk (𝟙 S) ⟶ G.X` be a point of `G` over the base `S`. The Library inner automorphism `G.innerIso g` acts on
`T`-points by `x ↦ c x c⁻¹`, where `c = G.constantPoint g T` is the restriction of `g` to `T`
(`comp_innerIso_hom`). The cocharacter `λ ≫ (G.innerIso g).hom` is the conjugate `gλg⁻¹`. The
equalities for isomorphisms give, for every `T` and every point `x : T ⟶ G`:

- `Dynamic.mem_parabolic_conj`: `x ∈ P_G(λ)(T)` if and only if `c x c⁻¹ ∈ P_G(gλg⁻¹)(T)`.
- `Dynamic.mem_centralizer_conj`: the same for `Z_G`.
- `Dynamic.mem_unipotent_conj`: the same for `U_G`.

So `P_G(gλg⁻¹) = g P_G(λ) g⁻¹`, and likewise for `Z_G` and `U_G`. This is part 2 of
Conrad's Proposition 4.1.10 applied to the `𝔾_m`-equivariant automorphism `x ↦ gxg⁻¹` from
`(G, λ)` to `(G, gλg⁻¹)`, together with the same statement for its inverse.
