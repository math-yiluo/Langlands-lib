# Sphericity of the dual cusp form

Module `Langlands.Global.RankinSelberg.ContragredientDualSpherical`.

This module proves one fact and the lemmas it needs. Let `x` be a vector of an actual
cuspidal realization `T` of `GL_n`, `n = r + 1`, with cusp form `φ`. Let `xd` be a vector of
another such realization `Td`, with cusp form `φ̃(g) = φ(w_n ᵗg⁻¹)`. If `x` is fixed by
`GL_n(𝒪_v)` at every finite place `v ∉ S`, then so is `xd`. Every result holds for every
number field `F` in an arbitrary universe `u`. The cusp-function results also assume
`CompactSpace (AdeleQuotient F)`, as `cuspFunction` does. No other hypothesis is used, and no
relation between `T` and `Td` is assumed beyond the equality of cusp functions.

It is a supporting result for `ContragredientDualWhittakerStatement` (published in
`Langlands.Global.RankinSelberg.EqualDualEulerFactorizationReduction`). That statement asks
for a vector `xd` of `Td` that is spherical outside `S` and whose `ψ⁻¹`-Whittaker function is
the dual of the `ψ`-Whittaker function of `x`. In the source `xd` is the cusp form `φ̃`. This
module supplies the sphericity half once `xd` with cusp function `φ̃` is known to exist. It
does not prove `ContragredientDualWhittakerStatement`, and it does not prove that such an
`xd` exists.

Notation: `Points F n` is `GL_n(𝔸)` as the actual adelic points of `Scheme F n`,
`E = GeneralLinearGroupPoints.adelicEquiv F n : Points F n ≃* GL_n(𝔸)`, `IT = GeneralLinear.inverseTranspose n R`
(`g ↦ ᵗg⁻¹` on `GL_n(R)`), `iota F n = E⁻¹ ∘ IT ∘ E`, and `ofFinite = AdelicGL.ofFinite F n`
(the finite factor `d ↦ (1, d)`). `cuspFunction F T x : Points F (r + 1) → ℂ` is the cusp
form of `x`. `dualFunction F n φ g = φ(E⁻¹(w_n · IT(E g)))` is `φ(w_n ᵗg⁻¹)`.
`IsSphericalOutside F T S x` (published in `PartialWhittakerIntegrals`) means that
`T.realization.finiteRepresentation (localInclusion F (r + 1) v k) x = x` for every finite
place `v ∉ S` and every `k ∈ FiniteAdelicGL.localIntegral F (r + 1) v`, that is,
`k ∈ GL_(r+1)(𝒪_v)`.

The two local instances `contragredientDualSchemeAffine` and `contragredientDualSchemeSmooth`
restate, for `Scheme F n`, the published `GroupScheme.GeneralLinear.isAffine_groupScheme` and
`GroupScheme.GeneralLinear.smoothStatement`, exactly as the local instances of
`EqualDualEulerFactorizationReduction` and `UnequalAnalyticProof` do. They provide the group
structure on `Points F n`.

## The packaged statement

`Langlands.Global.RankinSelbergGlobal.ContragredientDualSphericalStatement.{u}` is the
proposition: for every number field `F : Type u` with `CompactSpace (AdeleQuotient F)`,
every `r : ℕ`, all `T Td : Automorphic.CuspidalOperatorRealization F r`, every
`S : Finset (FinitePlace F)`, and all `x : T.Space` and `xd : Td.Space`,

```text
cuspFunction F Td xd = dualFunction F (r + 1) (cuspFunction F T x) →
  IsSphericalOutside F T S x → IsSphericalOutside F Td S xd.
```

The theorem `contragredientDualSpherical` proves it unconditionally from
`isSphericalOutside_of_cuspFunction_eq_dual` below.

**Provenance (internal).** J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in
Bernstein–Gelbart (eds.), *An Introduction to the Langlands Program* (2004), registered as
`cogdell-2004-analytic-theory-gln`. On p.206 (PDF p.209) the outer automorphism
`g ↦ g^ι = ᵗg⁻¹` acts on automorphic forms by `φ̃(g) = φ(g^ι) = φ(w_n g^ι)`. On p.211
(PDF p.214) the dual integral factors as `∏_v Ψ_v(1 − s; W̃_(φ_v), W̃'_(φ'_v), Φ̂_v)`, with the
local data of `φ̃` taken from those of `φ`. This tacitly uses that `φ̃` is unramified at every
place where `φ` is. Cogdell does not state this as a separate fact. The proof below is
internal: `GL_n(𝒪_v)` is stable under `ᵗ(·)⁻¹`, and `ι` turns right translation by `k` into
right translation by `ᵗk⁻¹`.

## Results

All results are in the namespace `Langlands.Global.RankinSelbergGlobal`. The helpers are in
its sub-namespace `ContragredientDual`. `F` is an explicit argument everywhere.

### Transpose inverse on adelic and local matrices

* `ContragredientDual.infinite_inverseTranspose`, `ContragredientDual.finite_inverseTranspose`:
  `AdelicGL.infinite F n (IT g) = IT (AdelicGL.infinite F n g)`, and the same for
  `AdelicGL.finite`. The proof compares entries:
  `inverseTranspose_entry` gives `(IT g) i j = g⁻¹ j i`, and the projection is a ring
  homomorphism on entries, so it commutes with matrix inversion (`map_inv`).
* `ContragredientDual.inverseTranspose_ofFinite`: `IT (ofFinite d) = ofFinite (IT d)` for
  `d ∈ GL_n(𝔸_f)`. Both sides have the same infinite and finite components
  (`AdelicGL.ext_infinite_finite`): the infinite components are `IT 1 = 1` and `1`
  (`AdelicGL.infinite_ofFinite`), and the finite components are both `IT d`
  (`AdelicGL.finite_ofFinite`).
* `ContragredientDual.localProjection_inverseTranspose`: the projection
  `FiniteAdelicGL.localProjection F n v : GL_n(𝔸_f) → GL_n(F_v)` commutes with `IT`, by the
  same entrywise argument.
* `ContragredientDual.inverseTranspose_localInclusion`:
  `IT (localInclusion F n v k) = localInclusion F n v (IT k)` for `k ∈ GL_n(F_v)`. Two elements
  of `GL_n(𝔸_f)` with the same local projections are equal
  (`FiniteAdelicGL.ext_localProjection`). At `w = v` both projections are `IT k`
  (`localProjection_localInclusion`). At `w ≠ v` both are `1`
  (`localProjection_localInclusion_of_ne`, with `IT 1 = 1`).
* `ContragredientDual.inverseTranspose_mem_localIntegral`: if `k ∈ GL_n(𝒪_v)`, then
  `IT k ∈ GL_n(𝒪_v)`. By `FiniteAdelicGL.mem_localIntegral`, membership means that all
  entries of `k` and of `k⁻¹` are integral. The entries of `IT k` are those of `k⁻¹`,
  transposed. The entries of `(IT k)⁻¹ = IT (k⁻¹)` are those of `k`, transposed.
* `ContragredientDual.iota_ofFinite`:
  `iota F n (E⁻¹ (ofFinite d)) = E⁻¹ (ofFinite (IT d))`. This follows by applying `E`, using the
  published `UnequalAnalytic.adelicEquiv_iota` (`E (iota g) = IT (E g)`) and
  `inverseTranspose_ofFinite`.

### Cusp functions

* `ContragredientDual.cuspFunction_finiteRepresentation`: for `d ∈ GL_(r+1)(𝔸_f)`,
  `cuspFunction F T (T.realization.finiteRepresentation d x) p = cuspFunction F T x (p · E⁻¹ (ofFinite d))`.
  The finite action is right translation of cusp forms. By the published
  `UnequalAnalytic.cuspFunction_eq`, the cusp function is the evaluation of
  `T.realization.toContinuous x` at `adelicHomeomorph p`. The published
  `OperatorRealization.evaluate_finiteRepresentation` (true by `rfl`) shows that evaluating
  the translated vector at `a` is the same as evaluating `x` at `a · ofFinite d`. Finally,
  `adelicHomeomorph (p · E⁻¹ q) = adelicHomeomorph p · q` holds because `adelicHomeomorph` is
  multiplicative and has the same underlying map as `E`. The proof composes these equalities
  with `Eq.trans` and `congrArg`, not `rw`: rewriting inside these `Points` terms makes the
  unifier compare `p` with `p · E⁻¹ q` and exhausts the heartbeat limit.
* `ContragredientDual.cuspFunction_injective`: `cuspFunction F T` is injective. The
  continuous function `T.realization.toContinuous x` on `GL_(r+1)(𝔸)` is determined by its
  values `cuspFunction F T x (E⁻¹ g)` (`UnequalAnalytic.cuspFunction_eq`). Both
  `ContinuousRationalFunctions.toContinuousMap` and `T.realization.toContinuous` are
  injective (`ContinuousRationalFunctions.toContinuousMap_injective`,
  `OperatorRealization.toContinuous_injective`).

### Main theorem

`isSphericalOutside_of_cuspFunction_eq_dual F T Td S x xd hxd hx :
IsSphericalOutside F Td S xd`, where
`hxd : cuspFunction F Td xd = dualFunction F (r + 1) (cuspFunction F T x)` and
`hx : IsSphericalOutside F T S x`.

Proof. Let `v ∉ S` and `k ∈ GL_(r+1)(𝒪_v)`, and write `u = localInclusion F (r + 1) v k`. By
`cuspFunction_injective` it suffices to show that the cusp functions of
`Td.realization.finiteRepresentation u xd` and of `xd` agree at every `p`. Put
`φ = cuspFunction F T x`. It is left invariant under the rational points (published
`UnequalAnalytic.cuspFunction_rational_mul`), so the published
`UnequalAnalytic.dualFunction_eq` gives `dualFunction F (r + 1) φ g = φ (iota g)`. The
following chain of rewrites then reduces the left side to the right side:

```text
cusp(Td, π(u) xd)(p) = cusp(Td, xd)(p · E⁻¹(ofFinite u))     cuspFunction_finiteRepresentation
                     = φ(iota(p · E⁻¹(ofFinite u)))          hxd, dualFunction_eq
                     = φ(iota p · E⁻¹(ofFinite (IT u)))       iota_mul, iota_ofFinite
                     = φ(iota p · E⁻¹(ofFinite (localInclusion v (IT k))))
                                                              inverseTranspose_localInclusion
                     = cusp(T, π(localInclusion v (IT k)) x)(iota p)
                                                              cuspFunction_finiteRepresentation
                     = φ(iota p)                              hx, inverseTranspose_mem_localIntegral
                     = cusp(Td, xd)(p)                        hxd, dualFunction_eq
```

The axioms used are `propext`, `Classical.choice` and `Quot.sound`.
