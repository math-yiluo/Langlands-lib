# Generic points of fibres and fibre products

The module `Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.FibreGeneric`
describes generic points of fibres by generizations and proves that generizations in a fibre of
one factor of a fibre product lift to the fibre product with the other coordinate fixed. These
are derived results used in the Library's proof
`Langlands.AlgebraicGeometry.strictBirationalGroupLawRestriction` of Bosch, Lütkebohmert and
Raynaud, *Néron Models* (1990), §5.2 Proposition 2 (printed p. 115). They supply the step of
BLR's proof (printed pp. 116–117) where, after base change to a point `a` of `X'`, the generic
points of `a ×_S X` are seen to lie over generic points of the fibres of `X`.

## `IsFibreGeneric`

```lean
def IsFibreGeneric {T B : Type*} [TopologicalSpace T] (p : T → B) (y : T) : Prop :=
  ∀ y' : T, y' ⤳ y → p y' = p y → y' = y
```

For a map `p` out of a topological space, `IsFibreGeneric p y` says that `y` has no proper
generization with the same image. The definition is internal: it is the pointwise form of the
Library's set `fibreGenericPoints` (module `Langlands.AlgebraicGeometry.FibreGenericPoints`).

`mem_fibreGenericPoints_iff g y` proves, for a morphism of schemes `g : Y ⟶ S`, that
`y ∈ fibreGenericPoints g` if and only if `IsFibreGeneric g y`; that is, `y` is the image of the
generic point of an irreducible component of the scheme-theoretic fibre exactly when it has no
proper generization in the same fibre. One direction is
`SmoothDvrFibreGenericPoints.noProperGenerization_in_fibre`; for the other, the Library's
`exists_fibreGenericPoint_specializes` gives a point of `fibreGenericPoints g` in the same fibre
specializing to `y`, which equals `y`.

## Generizations in fibre products

`exists_specializes_of_specializes_snd f g q y'`: for `f : X ⟶ S`, `g : Y ⟶ S`, a point `q` of
`X ×_S Y` and a generization `y'` of `pullback.snd f g q` with
`g y' = g (pullback.snd f g q)`, there is a generization `q'` of `q` with
`pullback.fst f g q' = pullback.fst f g q` and `pullback.snd f g q' = y'`.

Proof. Let `x` be the first projection of `q`, `s = f x`, and let `φ : Spec κ(x) ⟶ Spec κ(s)` be
induced by the residue field map of `f` at `x`
(`Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField`). Put
`W = (fibre of g over s) ×_{Spec κ(s)} Spec κ(x)`. Its first projection `w₁` to the fibre of `g`
is flat, being a base change of a morphism to the spectrum of a field, so it lifts
generizations (`Flat.generalizingMap`). The two projections of `W`, composed with the inclusion
of the fibre of `g` and with `Spec κ(x) ⟶ X`, define `ψ : W ⟶ X ×_S Y`; every point of
`X ×_S Y` over `x` lies in the image of `ψ`, since the fibre of the first projection over `x`
maps to `W` with composite `ψ ∘ χ` equal to the inclusion of that fibre (checked on both
projections with `pullback.hom_ext`). Write `q = ψ w`. The point `y'` lies in the fibre of `g`
over `s`, where it generizes `w₁ w` (the fibre inclusion is an embedding). Lifting along `w₁`
gives `w' ⤳ w`, and `q' = ψ w'` has first projection `x`, because `Spec κ(x)` maps to `x`
(`Scheme.fromSpecResidueField_apply`), and second projection `y'`.

`exists_specializes_of_specializes_fst` is the same statement for generizations of the first
projection, obtained from the previous one through `pullbackSymmetry f g`.

## Consequences for generic points

- `isFibreGeneric_snd f g`: if `q` is generic in its fibre under `pullback.fst f g`, then
  `pullback.snd f g q` is generic in its fibre under `g`.
- `isFibreGeneric_fst f g`: if `q` is generic in its fibre under `pullback.snd f g`, then
  `pullback.fst f g q` is generic in its fibre under `f`.

Both follow at once from the lifting statements: a proper generization of the projection in its
fibre would lift to a proper generization of `q` in its fibre.
