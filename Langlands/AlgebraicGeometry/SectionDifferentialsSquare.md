# Differential square maps along compatible sections

This is an internal construction from the Library's canonical relative differential
square maps and Mathlib's module pullback pseudofunctor. It supplies comparisons
needed for base-map coherence of group cotangent and Lie sheaves. No external
literature is translated here.

Work in an arbitrary universe `u`. Let `g : X ⟶ Y` and `b : T ⟶ S`, with
structure maps `fX : X ⟶ T`, `fY : Y ⟶ S` and a commuting square
`w : g ≫ fY = fX ≫ b`. Let `eX : T ⟶ X` and `eY : S ⟶ Y` satisfy
`h : eX ≫ g = b ≫ eY`. These maps can be sections; the construction does
not require right-inverse equations for them.

`Langlands.Scheme.sectionPullbackSquareIso g b eX eY h` is the natural
isomorphism from `eY^*` followed by `b^*` to `g^*` followed by `eX^*`.
It composes the module pullback comparison for `(b,eY)`, transport along
`h` in the inverse direction, and the inverse comparison for `(eX,g)`.
Its component is expressed by `sectionPullbackSquareIso_hom_app` using the
Library's generalized comparison `SchemeModule.RigidifiedModule.compHom`.

`Langlands.Scheme.sectionDifferentialsSquareMap g b w eX eY h` is the
actual morphism

```text
b^*(eY^* Ω_{Y/S}) ⟶ eX^* Ω_{X/T}.
```

It first uses that pullback isomorphism and then pulls back the canonical
`relativeDifferentialsSquareMap g b w` along `eX`. No smoothness, finiteness,
flatness, group structure or invertibility of the differential map is assumed.

For composable squares `(g,b)` and `(h,c)` with compatible maps `eX,eY,eZ`,
`sectionPullbackSquareIso_comp` proves that the successive comparisons agree
with the composite comparison, after the canonical pullback composition
comparisons on the two sides. The proof uses three instances of the published
`compHom_assoc` theorem: one for the two maps on total spaces, one for the
intermediate section, and one for the two base maps. It cancels the terminal
invertible pullback comparisons and then cancels their inverse pairs.

`sectionDifferentialsSquareMap_comp` consequently identifies the successive
differential maps with the differential map of the composite square, preceded
by `(pullbackComp b c).hom` on `eZ^* Ω_{Z/S}`. Its proof moves the second
square's differential through the first section comparison by naturality,
applies the section comparison composition law, and uses the published
`relativeDifferentialsSquareMap_comp` theorem. The `@[reassoc]` attribute
also provides its postcomposition form.

`sectionPullbackSquareIso_id_base` removes the base identity pullback using
`pullbackId`. `sectionDifferentialsSquareMap_id_base` specializes the resulting
formula to the fixed-base differential map `relativeDifferentialsMap`, with
the required transport along `eX ≫ g = eY`. These are specialization formulas;
this module does not state the group cotangent or Lie base-change identity
and composition laws.

This module is a prerequisite toward relative parabolic representability. It does
not prove that representability theorem or construct its polarization.
