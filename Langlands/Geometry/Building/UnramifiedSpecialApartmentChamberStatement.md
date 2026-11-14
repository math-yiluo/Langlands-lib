# Ordinary stable chambers in a supplied special apartment

`Langlands.Geometry.Building.UnramifiedSpecialApartmentChamberStatement`
is an unproved proposition. For each universe `u`, it concerns a
nonarchimedean local field `F : Type u`, its maximal unramified field
`K = inertiaFixedField F`, and a connected reductive group `G/F`.
The actual special-torus data are explicit:

- a maximal `F`-split torus `iS : S → G`;
- a commutative group scheme `T/F`, a closed subgroup inclusion
  `iT : T → G`, and a morphism `f : S → T` whose composite with `iT`
  is `iS`;
- maximal splitness of the scalar extension `iT_K : T_K → G_K`.

Thus `T` contains the prescribed maximal base-field split torus as
well as becoming maximal split over `K`. Mere maximal splitness of
`T_K` is not the whole special-torus premise.

For every actual apartment datum
`D : KPApartmentData iT_K
(IntegerValuation.order (MaximalUnramified.valuation F))`, every actual
centralizer datum `C`, full compatibility
`IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C`,
and coefficient stability `hD : KPApartmentData.GaloisStable F K iT D`,
the conclusion gives `x : D.Apartment` such that:

- `AffineRootSystem.GalleryGeometry.IsRegular D.affineRoots x`;
- every `σ : K ≃ₐ[F] K` carries
  `AffineRootSystem.facet D.affineRoots x` onto itself through the
  actual affine coefficient action `KPApartmentData.galoisAffineAction`.

The facet of this regular point is an ordinary `K`-chamber of the
ordinary affine roots. It lies in the supplied apartment, and the
conclusion states ordinary coefficient stability. It does not merely
produce a building-wide stable chamber or a stable facet of smaller
dimension. The point `x` itself need not be fixed. No splitting of
`G_K`, anisotropy of `G`, residue characteristic, or field
characteristic is assumed. The monomorphism instances for `iT_K` are
deduced from maximal splitness.

This statement neither constructs the special torus and compatible
apartment nor proves that such a chamber exists. It supplies an input
distinct from `UnramifiedGaloisFixedApartmentStatement` (a fixed point
may lie on walls) and `UnramifiedTwistedChamberStatement` (the stable
chamber there need not lie in the original apartment). It does not prove
`LocalAnisotropicAffineDiagramStatement`.

## Derived source correspondence

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Proposition 9.3.6 (printed pp.333–334, PDF pp.364–365) puts a
`Γ`-chamber in every special `F`-apartment. Its proof begins with a
coefficient-fixed apartment point and its facet. In the associated
residual group it chooses a minimal parabolic containing the residual
maximal split torus, hence also the residual image of `T`. The inverse
parahoric is `Γ`-stable and contains the maximal bounded subgroup of
`T(K)`. Proposition 9.3.5(3) then places its facet in the original
apartment. A globally chosen chamber followed by transport to another
torus is not the construction used in this proposition.

Proposition 9.10.4 (printed p.382, PDF p.413) gives residual
quasi-splitness when the residue field has dimension at most one; in
particular it applies to the finite residue field here. Proposition
9.10.1(2) (printed p.381, PDF p.412) makes every `Γ`-chamber an
ordinary `K`-chamber. Their combination gives the regular-point
formulation and the stable ordinary facet requested above. This is
exactly the route used at the start of the proof of Theorem 10.3.1
(printed p.392, PDF p.423), before its splitting conclusion.

The source uses the canonical building apartment. This target uses
every full-V6-compatible `D` on the specified special torus. A proof
must identify that class with the canonical one, compare centralizer
representations as needed, and transport its ordinary facets and
coefficient action. The integer-valued uniqueness theorem
`IntegerValuation.IsOmegaCompatible.eq_of_isMaximalSplitTorus`
in `IntegerOmegaApartmentUniqueness` provides the same-centralizer
class comparison. These transports, the integral/residual construction,
and the passage from residual quasi-splitness to a regular facet remain
proof obligations.

The authors' *Corrections and additions* (2024), PDF pp.39–41,
correct §9.2.1's bounded fixed-point argument and portions of §9.3.
They do not alter Proposition 9.3.6 there; the bounded fixed-point
argument must use the correction if invoked. The present target does
not assert any of the subsequently corrected §9.3.13 or §9.3.25
conclusions. The registered sources are
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
and `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
This is a derived combination and compatible-class formulation of the
source results.
