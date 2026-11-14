# Apartments from supplied closed split tori of an integral model

This internal unit combines published Henselian specialization, integral
split-torus conjugacy, and conjugate-apartment realization. Its inputs include
the actual integral model and both closed integral split tori, with maximal
split generic fibres. It constructs a generic conjugator belonging to the
model's actual integral-point subgroup and proves containment in the actual
conjugate-apartment map whenever that subgroup fixes the prescribed subset.

The closed proposition
`Langlands.Geometry.Building.IntegralModelSplitTorusApartmentStatement.{u}`
quantifies over a commutative Henselian local domain `R : Type u` with
algebraically closed residue field, a fraction field `K : Type u`, an affine
group scheme `G` over `K`, and an integral model `M` of `G`. The model is smooth
and its actual special fibre is connected. The specified generic group is
connected reductive. Both supplied commutative group schemes `T₁` and `T₂`
over `R` are split tori; the supplied maps `j₁` and `j₂` into `M.group` are
closed subgroups. Their actual generic maps
`M.genericTorusMap Tᵢ jᵢ`, formed using `M.genericIso`, are maximal split tori
of `G`. No characteristic restriction is imposed.

For every supplied function `ω : Kˣ → ℝ`, apartment datum `D` for the first
generic map and subset `Y` of `D.ReducedBuilding`, assume that `Y` is contained
in the image of `D.apartmentMap` and that `M.integralPoints` is a subgroup of
`D.pointwiseFixer Y`. There is an actual `g : rationalPoints G` in
`M.integralPoints`, an isomorphism `e` between the two actual generic source
tori, and an equality of group-scheme homomorphisms

```text
M.genericTorusMap T₁ j₁ ≫ (G.innerIso g).hom
  = CommGroupScheme.groupHom e.hom ≫ M.genericTorusMap T₂ j₂.
```

Every `y ∈ Y` has a coordinate `x : D.Apartment` with
`y = g • D.apartmentMap x`, and `Y` is contained in the range of
`D.conjugateApartmentMap e g he` for this same homomorphism equality `he`.
The proposition does not require that `Y` be nonempty or bounded. Its exact
proof is `integralModelSplitTorusApartment`.

The supporting theorem
`IntegralModel.exists_integralPoint_genericTorusMap_conjugacy` first applies
`IntegralModel.isMaximalTorus_specialFibre_of_generic` separately to the two
closed split integral tori. That result uses Henselian split-rank specialization;
no equality of the ranks of an arbitrary smooth model and its generic group is
assumed. The actual residue maps are therefore maximal tori.
`Langlands.GroupScheme.exists_henselian_splitTorus_conjugacy` constructs an
integral section and an integral source isomorphism, using smoothness,
affineness and connectedness of the actual residue fibre.
`IntegralModel.genericTorusMap_conjugation` uses base change of
inner automorphisms and their naturality through the supplied `genericIso` to
obtain equality of the actual generic homomorphisms. The conjugator is precisely
the image under `integralPointMap`, so its membership in `integralPoints` is
proved from the actual range definition.

For `exists_integralPoint_conjugateApartment_contains`, the supplied
integral-point inclusion in
`D.pointwiseFixer Y` shows that this same conjugator fixes each point of `Y`.
Each point already has a coordinate in the original apartment. The affine
transport of that coordinate lies in the actual conjugate apartment, whose
realization is `g • D.apartmentMap x` by
`KPApartmentData.conjugateApartmentMap_transport`. Fixation proves this is the
original point. Both the coordinate equation and containment in the range of
the actual transported chart are retained.

The provenance is internal composition of the Henselian specialization and
conjugacy theorems above with
`Langlands.GroupScheme.baseChange_innerIso_hom`,
`Langlands.GroupScheme.innerIso_hom_comp` and the conjugate-apartment
realization from `Langlands.Geometry.Building.ConjugateApartmentRealization`.
There is no claim to transcribe an additional literature statement.

The supplied integral tori, their generic maximal splitness, the original
apartment containment and integral-point fixation remain hypotheses. This
unit constructs no integral model or torus and supplies no Galois descent,
facet or segment comparison, or integral-point fixation theorem. It does not
prove that a supplied torus is Galois stable or special.
`UnramifiedFixedPointSplitTorusStatement` remains open; the four prohibited
unramified building-descent statements are not used.
