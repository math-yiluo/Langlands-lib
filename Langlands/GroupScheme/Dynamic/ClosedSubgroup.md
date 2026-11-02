# Dynamic subgroups of closed subgroups

This module proves that the dynamic subgroup functors `P(λ)`, `U(λ)` and `Z(λ)` of
`Langlands.GroupScheme.Dynamic.Basic` are compatible with closed subgroups. Fix a base scheme
`S`, group schemes `H` and `G` over `S`, and a homomorphism `f : H ⟶ G` that is a closed
subgroup in the sense of the Library predicate `IsClosedSubgroup f`, meaning the underlying
morphism of schemes is a closed immersion. Let `λ : 𝔾_{m,S} ⟶ H` be a cocharacter of `H`, so
`λ ≫ f` is a cocharacter of `G` that factors through `H`. The module proves

- `P_H(λ) = f⁻¹ P_G(λ ≫ f)`, `U_H(λ) = f⁻¹ U_G(λ ≫ f)` and `Z_H(λ) = f⁻¹ Z_G(λ ≫ f)`;
- equivalently `H ∩ P_G(λ ≫ f)`, `H ∩ U_G(λ ≫ f)` and `H ∩ Z_G(λ ≫ f)` are the images of
  `P_H(λ)`, `U_H(λ)` and `Z_H(λ)`;
- a limit in `G` of the image of a point of `H` is the image of a limit in `H`.

All statements are about subfunctors of points on every scheme `T` over `S`. `G` and `H` are
arbitrary group schemes over `S`. There is no affineness, finiteness or separatedness
hypothesis, and `f` is not assumed finitely presented.

## Sources

- Conrad, *Reductive group schemes* (2014), Proposition 4.1.10(1), p. 114. For `(G, λ)` as in
  Theorem 4.1.7 (an affine finitely presented group over a ring with a `𝔾_m`-action), "For any
  finitely presented closed subgroup `H` of `G` that is stable under the `𝔾_m`-action, with the
  restricted action on `H` also denoted as `λ`, `H ∩ P_G(λ) = P_H(λ)`, `H ∩ U_G(λ) = U_H(λ)`,
  `H ∩ Z_G(λ) = Z_H(λ)`". The proof on p. 115 says that (1) "is immediate from the functorial
  definitions of these subgroups".
- Conrad, Gabber and Prasad, *Pseudo-reductive groups*, 2nd ed. (2015), p. 49 (PDF page 75),
  after the proof of Lemma 2.1.4: "if `H ⊆ G` is a closed `k`-subgroup scheme through which `λ`
  factors then `H ∩ P_G(λ) = P_H(λ)` (using `λ` to also denote the homomorphism `GL₁ → H`)".
  Lemma 2.1.5, p. 50 (PDF page 76), states `H ∩ U_G(λ) = U_H(λ)`, and its proof on p. 51 (PDF
  page 77) says "The equality `H ∩ U_G(λ) = U_H(λ)` holds because `H ∩ P_G(λ) = P_H(λ)`".

The sources treat conjugation actions on affine groups over a ring (Conrad's statement also
covers general `𝔾_m`-actions). There, the equalities follow from the compatibility of the
representing closed subschemes with `𝔾_m`-stable closed subschemes (CGP Lemma 2.1.4). This
module formalizes the case of a cocharacter of `H` acting by conjugation, over any base and for
arbitrary group schemes. Its proof works directly with points, as described below. Conrad's
`H ∩ P_G(λ)` is formalized in two ways: as the preimage `f⁻¹ P_G(λ ≫ f)`, a subgroup functor
of `H`, and as the intersection `range f ⊓ P_G(λ ≫ f)`, a subgroup functor of `G`.

## Factoring through a closed immersion

The key input is that a morphism from `T ×_S 𝔸¹_S` that lands in a closed subscheme on
`T ×_S 𝔾_{m,S}` lands in it everywhere.

- `exists_lift_of_isSchemeTheoreticallyDominant`: let `i : Y' ⟶ Y` be a closed immersion,
  `f : X ⟶ Y` a morphism and `j : W ⟶ X` a scheme-theoretically dominant morphism (Mathlib
  `IsSchemeTheoreticallyDominant`: its kernel ideal sheaf is `⊥`). If `j ≫ f` factors through
  `i`, then `f` factors through `i`. Proof: `j` factors through the closed immersion
  `pullback.fst f i` (the base change of `i`). So the kernel of `pullback.fst f i` lies in the
  kernel of `j`, which is `⊥` (`Scheme.Hom.le_ker_comp`). A closed immersion with zero kernel is
  an isomorphism (`IsClosedImmersion.isIso_iff_ker_eq_bot`), and its inverse followed by
  `pullback.snd f i` is the factorization.
- `Langlands.AlgebraicGeometry.exists_lift_of_openCover`, imported from
  [the generic gluing module](../../AlgebraicGeometry/Morphisms/OpenCoverLift.md): a morphism `f : X ⟶ Y` factors through a monomorphism `i` if it
  does on each member of an open cover of `X`. The local factorizations agree on overlaps
  after composing with `i`, hence agree, and glue (`Scheme.Cover.glueMorphisms`).
- `AffineLine.exists_lift_of_unitInclusion_affine`: let `Spec A ⟶ S` be a morphism and
  `i : Y' ⟶ Y` a morphism over `S` whose underlying morphism is a closed immersion. If the
  restriction of `e : Spec A ×_S 𝔸¹_S ⟶ Y` to `Spec A ×_S 𝔾_{m,S}` factors through `i`, then
  `e` factors through `i` on underlying schemes. Proof: use the Library identifications from
  `Dynamic.Uniqueness`. These are `polynomialPoint : Spec A[X] ⟶ Spec A ×_S 𝔸¹_S` with its
  section `polynomialPointInv`, and `laurentInclusion_polynomialPoint`, which says that the
  inclusion `Spec A[X, X⁻¹] ⟶ Spec A[X]` followed by `polynomialPoint` factors through
  `Spec A ×_S 𝔾_{m,S}`. The inclusion is `Spec` of the injective map `A[X] ⟶ A[X, X⁻¹]`, so it
  is scheme-theoretically dominant (`isSchemeTheoreticallyDominant_specMap`). The first lemma
  then factors `polynomialPoint ≫ e` through `i`, and composing with `polynomialPointInv`
  factors `e`.
- `AffineLine.exists_lift_of_unitInclusion`: the same for every scheme `T` over `S`, with a
  factorization `e' : T ×_S 𝔸¹_S ⟶ Y'` over `S` and `e' ≫ i = e`. Proof: pull back the affine
  open cover of `T` along the projection `T ×_S 𝔸¹_S ⟶ T`. On the member over `Spec A ⟶ T`, the
  map `pullbackFstToWhiskerRight` of `Dynamic.Uniqueness` identifies the restriction of `e`
  with a map from `Spec A ×_S 𝔸¹_S` (`pullbackFstToWhiskerRight_comp`). The affine case gives
  local factorizations, and `exists_lift_of_openCover` glues them. A closed immersion is a
  monomorphism, so gluing applies. The glued morphism lies over `S` because `i` and `e` do.

## Images of subgroup functors

- `SubgroupFunctor.map f F`: the image of a subgroup functor `F` of `H` under a homomorphism
  `f : H ⟶ G`. Its `T`-points are the points `y ≫ f` with `y ∈ F(T)`. It is the image of the
  subgroup `F(T)` under the group homomorphism `(yonedaGrp.map f).app (op T)` on points, and
  restriction along `a : T' ⟶ T` preserves it because `a ≫ (y ≫ f) = (a ≫ y) ≫ f`. This is the
  functor-of-points image, not a scheme-theoretic image.
- `SubgroupFunctor.mem_map` unfolds membership.
- `map_top`: the image of `⊤` is the Library functor `range f`. `map_le_range`: every image lies
  in `range f`.
- `map_le_iff_le_comap`: `map f` is left adjoint to `comap f` (from `Dynamic.Functoriality`).
- `map_comap`: `(f⁻¹ F).map f = range f ⊓ F`.
- `comap_map_of_mono`: if the underlying morphism of `f` is a monomorphism, then
  `f⁻¹ (F.map f) = F`.

## Orbit extensions and limits in a closed subgroup

The notions are those of `Dynamic.Basic`. Fix a point `g : T ⟶ H`.

- `Dynamic.IsOrbitExtension.exists_of_isClosedSubgroup`: every extension `e : T ×_S 𝔸¹_S ⟶ G`
  of the orbit of `g ≫ f` under `λ ≫ f` is `e' ≫ f` for an extension `e'` of the orbit of `g`
  under `λ`. The orbit of `g ≫ f` is the orbit of `g` followed by `f` (`orbit_comp_hom`). So
  the restriction of `e` to `T ×_S 𝔾_{m,S}` factors through `f`, and
  `AffineLine.exists_lift_of_unitInclusion` gives `e'`. Since `f` is a monomorphism, `e'`
  extends the orbit of `g`.
- `Dynamic.HasLimit.exists_of_isClosedSubgroup`: a limit `l` in `G` of the orbit of `g ≫ f` is
  `l' ≫ f` for a limit `l'` of the orbit of `g` (evaluate `e'` at zero, `evalZero_comp`).
- `Dynamic.hasLimit_comp_hom_iff`: for points `g` and `l` of `H`, `l ≫ f` is a limit of the
  orbit of `g ≫ f` under `λ ≫ f` if and only if `l` is a limit of the orbit of `g` under `λ`.
  One direction is `HasLimit.comp_hom`. For the other, the limit `l'` given by the previous
  lemma satisfies `l' ≫ f = l ≫ f`, hence `l' = l`.

## The equalities

- `Dynamic.parabolic_eq_comap_of_isClosedSubgroup`: `P_H(λ) = f⁻¹ P_G(λ ≫ f)`. The inclusion
  `≤` is `parabolic_le_comap`. For `≥`, an extension of the orbit of `g ≫ f` comes from one of
  the orbit of `g`.
- `Dynamic.unipotent_eq_comap_of_isClosedSubgroup`: `U_H(λ) = f⁻¹ U_G(λ ≫ f)`. If `g ≫ f` has
  limit `1 = 1 ≫ f` (`MonObj.one_comp`), then `g` has limit `1` by `hasLimit_comp_hom_iff`.
- `Dynamic.centralizer_eq_comap_of_isClosedSubgroup`: `Z_H(λ) = f⁻¹ Z_G(λ ≫ f)`. This is
  `centralizer_eq_comap_of_mono`, since closed immersions are monomorphisms.
- `Dynamic.range_inf_parabolic`, `Dynamic.range_inf_unipotent`,
  `Dynamic.range_inf_centralizer`: `range f ⊓ P_G(λ ≫ f) = P_H(λ).map f`, and likewise for `U`
  and `Z`, by the equalities above and `map_comap`. These are the source statements
  `H ∩ P_G(λ) = P_H(λ)` (and likewise for `U` and `Z`) as subfunctors of `G`.
