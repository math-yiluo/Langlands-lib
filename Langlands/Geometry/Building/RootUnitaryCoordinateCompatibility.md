# Full V6 on multipliable roots from quadratic unitary coordinates

Author: Worker 1045.

For a multipliable relative root `a` of a quasi-split group, Kaletha–Prasad
identify the root group `U_a` with the restriction of scalars of the quadratic
unitary group of a separable quadratic extension, and define the Chevalley root
functions on `U_a(k)` and `U_{2a}(k)` through these coordinates. This module
packages such coordinates on the actual rational root groups, together with the
action of the whole actual centralizer, as the structure
`RootUnitaryCoordinates`. It proves that the Kaletha–Prasad root functions are
then compatible with that action (V6 at `a` and at `2a`), and combines this with
the published coordinate families on the other roots into the integer
centralizer compatibility and the Omega compatibility of an apartment class. All
statements hold at an arbitrary universe `u`.

## Setting

Let `k` be a field and `v : Valuation k (WithZero (Multiplicative ℤ))`. Let `S`
be a commutative group scheme and `G`, `Z` group schemes over `Spec k`, with
`i : S.toGrp ⟶ G`, `j : Z ⟶ G`, `s : S.toGrp ⟶ Z` and a character
`a : characterLattice S`.

For a commutative ring `A` with an involution `x ↦ x̄`, the Library group
`SU3Root.Parameters` consists of the pairs `(u, v) ∈ A × A` with
`v + v̄ = u ū`, with the product

```text
(u, v) · (u', v') = (u + u', v + v' + u ū'),
```

identity `(0, 0)` and inverse `(-u, v̄)`. Its subgroup
`SU3Root.Parameters.central` is the set of parameters with `u = 0`. For a
separable quadratic extension `L / E` of fields,
`SU3Root.rationalParameters E L` is this group for `A = L` with the nontrivial
automorphism of `L / E` (`SU3Root.fieldInvolution E L`). The scaling
`SU3Root.Parameters.scale λ` sends `(u, v)` to `(λ u, λ λ̄ v)`.

## The structure

An element `R : RootUnitaryCoordinates i j s a` consists of:

- fields `E = R.base` and `L = R.extension` with `L / E` a separable quadratic
  extension, `k → E → L` a scalar tower, and `L` finite and separable over `k`;
- a group isomorphism
  `e = R.equiv : SU3Root.rationalParameters E L ≃* rootGroupPoints i a`
  onto the actual rational root group `U_a(k)`;
- `R.double`: a point `g ∈ G(k)` lies in `rootGroupPoints i (2 • a)` if and only
  if `g = e(p)` for a parameter `p` with first coordinate `0`;
- a rational character `β = R.character` of the base change `Z_L`, with
  `R.restriction`: its restriction along the base change of `s` is the base
  change of the rational character of `S` corresponding to `a`;
- `R.conjugation`: for every `z ∈ Z(k)` and every parameter `p`,

  ```text
  j(z) e(p) j(z)⁻¹ = e(scale (β(z_L)) p),
  ```

  where `z_L` is the image of `z` in `Z(L)`.

The fields and algebra structures of `R` are registered as instances.

## Declarations

In namespace `Langlands.Geometry.Building`:

- `RootUnitaryCoordinates.conj_inv R z p`: for `z ∈ Z(k)`,
  `j(z)⁻¹ e(p) j(z) = e(scale (β(z_L)⁻¹) p)`, the inverse taken in the unit
  group `Lˣ` and coerced to `L`.
- `RootUnitaryCoordinates.conj_eq_multipliable R h hw hbar hφ z hu`: let
  `h : Function.Bijective (Cartan.restrictionEvaluation s)`, let
  `w : AddValuation L (WithTop ℝ)` satisfy
  `hw : IntegerValuation.IsNormCalibrated v w` (that is,
  `w(x) = ord_v(N_{L/k} x) / [L : k]` for `x ∈ Lˣ`) and
  `hbar : w(x̄) = w(x)` for all `x`, and let `φ` be a root function family with
  `hφ : φ_a(e(p)) = SU3Root.Parameters.depthA w p` for every parameter `p`;
  here `depthA w (u, v) = w(v) / 2`, with `⊤ / 2 = ⊤`. Then for every
  `z ∈ Z(k)` and `u ∈ U_a(k)`,

  ```text
  φ_a(j(z)⁻¹ u j(z)) = φ_a(u) + ⟨a, IntegerValuation.centralizerTranslation v s h z⟩.
  ```

- `RootUnitaryCoordinates.conj_eq_double R h hw hbar hφ z hu`: with `h`, `w`,
  `hw`, `hbar` as above and `φ` with `hφ : φ_{2a}(e(p)) = w(p.second)` for every
  parameter `p` with first coordinate `0`, for every `z ∈ Z(k)` and
  `u ∈ U_{2a}(k)`,

  ```text
  φ_{2a}(j(z)⁻¹ u j(z)) = φ_{2a}(u) + ⟨2a, IntegerValuation.centralizerTranslation v s h z⟩.
  ```

- `RootUnitaryCoordinates.conj_eq_multipliable_henselian hH R h hφ z hu` and
  `RootUnitaryCoordinates.conj_eq_double_henselian hH R h hφ z hu`: for
  `hH : HenselianLocalRing v.valuationSubring`, the same conclusions when `φ_a`
  is the published tower depth `SU3Root.towerDepth k E L v hH` on all
  parameters, respectively `φ_{2a}` is the published central tower depth
  `SU3Root.towerCentralDepth k E L v hH` on the zero-first-coordinate
  parameters. Both depths are `depthA`, respectively the valuation of the second
  coordinate, for the induced valuation
  `FieldTheory.henselianSeparableAddValuation v hH L`.

The four V6 lemmas need affine `S` and `Z`.

In namespace `Langlands.Geometry.Building.IntegerValuation`, with `hH` as
above:

- `isCentralizerCompatible_of_rootCoordinateTypes hH hj h hc` (needs
  `IsAffineHom G.X.hom`, affine `S` and `Z`, and `i` a monomorphism): let
  `hj : (torusCentralizer i).IsRepresentedBy j`. Suppose that every
  `a ∈ relativeRoots i` satisfies one of the following:
  1. there is a published coordinate family
     `RootCoordinateFamilyEquivariance v i j s φ a`;
  2. there is `R : RootUnitaryCoordinates i j s a` with
     `φ_a(R.equiv p) = SU3Root.towerDepth k R.base R.extension v hH p` for all
     parameters `p`;
  3. `a = 2 • b` for some `b` and
     `R : RootUnitaryCoordinates i j s b` with
     `φ_a(R.equiv q) = SU3Root.towerCentralDepth k R.base R.extension v hH q`
     for all zero-first-coordinate parameters `q`.

  Then `IsCentralizerCompatible v i j s h φ`.
- `isOmegaCompatible_of_rootCoordinateTypes hH hφ hc` (needs
  `IsAffineHom G.X.hom`, affine `S`, and `i` a monomorphism): for
  `D : KPApartmentData i (order v)`, `C : CentralizerDatum i` and
  `hφ : φ ∈ D.carrier`, if every relative root satisfies one of the three
  conditions above for `C.j` and `C.s`, then `IsOmegaCompatible v D C`.

## Proofs

1. `conj_inv` applies `R.conjugation` to `z⁻¹` and rewrites
   `j(z⁻¹) = j(z)⁻¹`, `(z⁻¹)⁻¹ = z` and `β((z⁻¹)_L) = β(z_L)⁻¹` by `map_inv`.
2. `conj_eq_multipliable`: write `u = e(p)`. By `conj_inv` the left side is
   `depthA w (scale λ⁻¹ p)` with `λ = β(z_L)`. The published
   `SU3Root.Parameters.depthA_scale` (which uses `hbar`) gives
   `depthA w (scale λ⁻¹ p) = w(λ⁻¹) + depthA w p`. By
   `IsNormCalibrated.apply_inv`, `w(λ⁻¹) = -ord_v(N_{L/k} λ) / [L : k]`, the
   negative of the published `characterNormOrder v β z`. The published
   `characterNormOrder_eq_eval` (which uses `R.restriction` and `h`) identifies
   this with `⟨a, centralizerValuation z⟩`, and
   `centralizerTranslation_toAdd` with `map_neg` turns its negative into
   `⟨a, centralizerTranslation z⟩`.
3. `conj_eq_double`: write `u = e(p)` with `p` of first coordinate `0`; the
   scaled parameter `scale λ⁻¹ p` again has first coordinate `0`, so `hφ`
   applies to it. Its second coordinate is `λ⁻¹ λ̄⁻¹ p.second`, of valuation
   `w(λ⁻¹) + w(λ⁻¹) + w(p.second)` by multiplicativity and `hbar`. As in step 2,
   `w(λ⁻¹) = ⟨a, centralizerTranslation z⟩`, and the published
   `eval_nsmul_char` gives `⟨2a, t⟩ = 2 ⟨a, t⟩`.
4. The henselian versions apply steps 2 and 3 to the induced valuation, which
   is norm-calibrated by the published
   `isNormCalibrated_henselianSeparableAddValuation` and invariant under the
   quadratic conjugation by the published
   `SU3Root.henselianSeparableAddValuation_quadratic_bar`.
5. `isCentralizerCompatible_of_rootCoordinateTypes` unfolds the definition and
   treats the three cases by the published
   `RootCoordinateFamilyEquivariance.conj_eq` and by step 4.
   `isOmegaCompatible_of_rootCoordinateTypes` derives the affineness of `G` and
   of `C.Z` from `IsAffineHom G.X.hom` and the closed immersion `C.j`, then uses
   the published `isOmegaCompatible_iff_of_mem`.

## Provenance and scope

The coordinates model Kaletha–Prasad (source
`kaletha-prasad-2023-bruhat-tits-new-approach`). Their (2.7.2) (PDF p. 141,
printed p. 110) defines `U_{ℓ/k}(R) = {(u, v) | v + v̄ = u ū}` with the product
`(u, v) · (u', v') = (u + u', v + v' + u ū')` obtained from the matrices
`u_a(u, v)` of `SU3`; this is the Library law above. For a quasi-split
semisimple simply connected group and a root `a` of type R2, Construction 2.9.16
(isomorphisms (2.9.3), PDF p. 148, printed p. 117) identifies `U_a` with
`R_{k_b/k} U_{k_a/k_b}` and `U_{2a}` with `R_{k_b/k} U⁰_{k_a/k_b}`; on rational
points this is the isomorphism `e` with `E = k_b` and `L = k_a`. Construction
6.1.17 (PDF pp. 236–237, printed pp. 205–206) sets `φ_a((u, v)) = ω(v) / 2` and
`φ_{2a}((0, v)) = ω(v)`, with `ω` the valuation of `k_a` extending that of `k`;
over a henselian base this is the Library's tower depth. The proof of
Proposition 6.1.19 (PDF p. 238, printed p. 207) records the split-torus case
`φ_a(t u t⁻¹) = φ_a(u) + ω(a(t))` for `t ∈ S(k)`.

The structure's scaling field `R.conjugation` is a hypothesis of this module,
not a literature statement: it asserts that the whole centralizer `Z(k)` acts by
`(u, v) ↦ (λ u, λ λ̄ v)` with `λ` the value of a character of `Z_L` restricting
to `a`. For `SU3` with maximal torus `diag(t, t̄ / t, 1 / t̄)` and the matrices
of (2.7.2), conjugation multiplies `u` by `t² / t̄` and `v` by `t t̄`, which is
of this form with `λ = t² / t̄`. The module proves no existence of such
coordinates, defines no root function family, and does not address V0–V5; it
does not prove `QuasiSplitIntegerApartmentExistenceStatement`.
