# Scalar-linear shuffle slant on actual cohomology

This internal construction transports the existing shuffle slant operator
to the scalar-linear ordered Čech complex and then to actual right-derived
structure-sheaf cohomology. It uses the operator and boundary identities from
`CechSlant`, the signed short-complex construction from `CechSlantDescent`,
and the actual ordered resolution comparison from `AllSeqCohomology` and
`AllSeqCup`. The section-scalar identification `cochainSecEquiv` is supplied
by `CanonicalH1Primitive`. These are internal dependencies; no new
literature theorem is asserted here.

The data are a commutative ring `R`, schemes `X`, `Y`, and `P`, structure
morphisms to `Spec R`, and a pullback square with maps `p₁ : P ⟶ X` and
`p₂ : P ⟶ Y`. The composite `p₁ ≫ πX` must equal `πP`. Every section ring
has an `R`-algebra structure whose algebra map is the actual structure-induced
map `secHom`. The open families `U : ι → X.Opens` and `V : κ → Y.Opens`
have finite index types in the same universe as the schemes. Every
two-entry intersection of `U` and every nonempty finite intersection of `V`
must be affine. At this stage neither family is required to cover.

The functional

```text
l : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[R] R
```

is defined on all first-factor one-cochains. The hypothesis `hl` says that
it vanishes on the differential of every zero-cochain.

`slantCochainMap n` is an `R`-linear morphism from degree `n+1` of
`cochainComplex πP (prodCover p₁ p₂ U V) (unitModule P)` to degree `n` of
`cochainComplex πY V (unitModule Y)`. It first uses `cochainSecEquiv` to
identify scalar-linear cochains with raw section families, applies the
existing `LLinearMap`, and uses the inverse identification on the target.
Both identifications are the identity on underlying elements, so
`slantCochainMap_apply` identifies its value with the existing shuffle
operator `L`.

`slantCochainMap_anticomm` and `slantCochainMap_bottom` prove

```text
dP(n+1,n+2) ≫ slantCochainMap(n+1)
  = -(slantCochainMap(n) ≫ dY(n,n+1)),
dP(0,1) ≫ slantCochainMap(0) = 0.
```

They identify `dCochain` with the raw Čech differential and apply `L_d`
and `L_zero_d`, respectively. Thus `slantH n` is the actual signed
short-complex homology map from product-cover homology in degree `n+1`
to second-factor homology in degree `n`, in `ModuleCat R`.
The equation `slantH_π_ι` identifies its composite with the homology
projection and inclusion as cycle inclusion, followed by
`slantCochainMap n`, followed by the opcycle projection.

For a closed cochain `b` in degree `n+2`, the anticommutation identity
proves that `slantCochainMap (n+1) b` is closed in degree `n+1`.
`slantH_classMap` states that applying `slantH (n+1)` to its class gives
the class of this slant cochain. Here `classMap n` denotes a class in
degree `n+1`, so this formula concerns positive target degrees.
The proof uses naturality of the homology projection and the cycle
inclusion formula from `CechSlantDescent`; injectivity of the target
cycle inclusion reduces the formula to equality of the actual cochains.

For the final construction, `πY` and `πP` are separated,
`V` covers `Y` by affine opens, and the product family covers `P` by
affine opens. The definition `slantCanonical n` is the `R`-linear map

```text
H^(n+1)(P, O_P) →ₗ[R] H^n(Y, O_Y)
```

obtained by conjugating `slantH n` by the two actual `cohomologyEquiv`
maps. These cohomology objects are the right-derived functors of relative
global sections evaluated on `unitModule`, the structure sheaf.
`slantCanonical_apply` records this conjugation explicitly.
`slantCanonical_canonicalClass` transports the preceding positive-degree
cocycle-class formula to these actual cohomology objects.

The cover data and the cochain functional remain explicit arguments.
This unit does not construct `l` from an arbitrary cohomology dual, prove
independence of the covers, establish a creation-contraction relation, or
prove alternation, exterior generation, or the host degree-two comparison.
