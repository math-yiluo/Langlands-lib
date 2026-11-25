# Affineness of quasi-finite schemes over a finite affine base

`Langlands.AlgebraicGeometry.finiteBaseQuasiFiniteAffineIso` constructs an
actual isomorphism

```
X ≅ Spec Γ(X, ⊤)
```

for every quasi-compact separated locally quasi-finite morphism `f : X ⟶ Y`
which is locally of finite type, where `Y` is affine and has finitely many
underlying points. All schemes lie in an arbitrary common universe `u`.
The source is not supplied with an affineness hypothesis.

The supporting theorems prove that a finite quasi-affine scheme is affine,
that the source of `f` is affine, and that `f` is an affine morphism.
Here “finite” in the first assertion means a finite set of underlying
points, not a finite structure morphism.

The DVR specializations are:

- `isAffineHom_quasiFinite_over_dvr`: every quasi-compact separated locally
  quasi-finite morphism, locally of finite type, to the spectrum of any DVR
  is affine.
- `isAffineHom_etale_over_dvr`: every quasi-compact separated etale morphism
  to the spectrum of any DVR is affine.

The DVR assumptions are exactly `CommRing R`, `IsDomain R`, and
`IsDiscreteValuationRing R`; there is no completeness or henselian hypothesis.
The latter theorem concerns arbitrary schemes, so it applies to the total
scheme of an etale Weyl quotient without assuming that the ambient group
scheme is affine.

## Implemented argument and provenance

This is derived supporting development for the DVR step in the affineness
route for smooth group schemes with connected reductive residue fibres. It combines existing Library results and Mathlib's
Zariski main theorem; it introduces no new literature transcription.

1. Quasi-compact locally quasi-finite morphisms have finite point fibres.
   `Scheme.Hom.finite_preimage` therefore shows that `X` has finitely many
   points when `Y` does.
2. Zariski main theorem makes `f.toNormalization` an open immersion. The
   normalization is affine over the affine `Y`, so
   `Scheme.IsQuasiAffine.of_isImmersion` makes `X` quasi-affine.
3. The published
   `OrbitSaturatedAffineOpen.exists_basicOpen_isAffineOpen_of_finite` puts
   any finite set of points of a quasi-affine scheme in an affine basic
   open. Apply it to every point of `X`: the resulting open is the whole
   scheme, which is therefore affine.
4. `finiteBaseQuasiFiniteAffineIso` is the canonical `X.isoSpec` with this
   proved affine instance. Between affine schemes every morphism is affine.
5. `SmoothDvrFibreGenericPoints.finite_base` says that the spectrum of a
   DVR has only its generic and closed points. This supplies the finite
   base for the DVR specialization. An etale morphism is locally
   quasi-finite and locally of finite type.

The construction does not assert that `f` is finite. For example, the
generic-point open immersion of a DVR is covered by the affineness result.
It supplies only the general scheme-theoretic DVR affineness input; it
does not prove the group-scheme Weyl criterion, finiteness over an arbitrary
base, or the reductive-residue-fibre affineness theorem.
