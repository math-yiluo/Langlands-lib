# Cohomology of the inverse limit of the Hom complexes

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DivisibleSystem.CompatibleHomologyZero`
(`nullHomotopicTowerHoms`, `towerHomQuotientEquivLimitHomologyZero`),
`Langlands.Cohomology.DivisibleSystem.HomSurjective` (`PowTorsionProjective`,
`homComplexSystem_map_f_surjective`, `isMittagLeffler_homComplexSystem_eval`)
and `Langlands.Cohomology.InverseLimit.Statement`
(`FiniteCohomologyInverseLimitStatement`,
`DegreewiseInverseLimitCohomologyStatement`). Through these imports it uses
`DivisibleSystem`, `DivisibleSystem.obj`, `DivisibleSystem.tower` and
`SmoothRepComplexDivisibleSystem` (`Langlands.Cohomology.DivisibleSystem`),
`homComplexSystem` and `homComplexLimit` (`HomSystem`) and
`LinearHomComplex.complex` (`Langlands.Cohomology.LinearHomComplex`). From
Mathlib it uses `Functor.IsMittagLeffler`,
`Functor.isMittagLeffler_of_exists_finite_range`, `Set.toFinite`,
`limit.post`, `limit.post_π`, `HomologicalComplex.homologyFunctor`,
`HomologicalComplex.homologyMap`, `asIso` and `Iso.toLinearEquiv`.

## Conventions

`R` is a ring, `C` an `R`-linear abelian category and `ℓ` a natural number.
`T` and `W` are `ℓ`-divisible systems of cochain complexes in `C`
(`DivisibleSystem (CochainComplex C ℤ) ℓ`), with levels `T m` and `W m`.

`homComplexSystem R T W : ℕᵒᵖ ⥤ CochainComplex (ModuleCat R) ℤ` is the
published inverse system `m ↦ Hom^•(T m, W m)` of the Hom complexes
`LinearHomComplex.complex R (T m) (W m)` of `R`-modules, and
`homComplexLimit R T W` is its limit, a cochain complex of `R`-modules, with
limit projections `limit.π (homComplexSystem R T W) m`.

`PowTorsionProjective ℓ m P` is the published hypothesis that for every
epimorphism `p : X ⟶ Y` such that `X` is killed by `ℓ ^ m`, every morphism
`P ⟶ Y` lifts along `p`. Below it is read as "`P` is projective relative to
objects killed by `ℓ ^ m`". The hypothesis `hT` of the results below is
`∀ m p, PowTorsionProjective ℓ m ((T m).X p)`: every term of every level of
`T` is projective relative to objects killed by `ℓ ^ m`. By the published
`homComplexSystem_map_f_surjective` and
`isMittagLeffler_homComplexSystem_eval`, it makes all degreewise transition
maps of `homComplexSystem R T W` surjective, so that the system satisfies the
Mittag-Leffler condition in every degree.

For a functor `F` to types from a cofiltered category, `F.IsMittagLeffler` is
Mathlib's Mittag-Leffler condition: for every `j` there is a morphism
`f : i ⟶ j` such that the image of `F.map f` lies in the image of
`F.map g` for every morphism `g : k ⟶ j`.

The two inverse-limit statements are published proposition targets, used here
only as hypotheses `hS`; nothing in this module proves them. For every inverse
system `K : ℕᵒᵖ ⥤ CochainComplex (ModuleCat R) ℤ` they concern the morphism
`limit.post K (homologyFunctor q)` from the degree `q` cohomology of the limit
of `K` to the limit of the degree `q` cohomology modules:

- `FiniteCohomologyInverseLimitStatement R`: if all degreewise transition maps
  of `K` are surjective and every cohomology module of every `K i` is finite,
  then this morphism is an isomorphism in every degree.
- `DegreewiseInverseLimitCohomologyStatement R`: if `K` satisfies the
  Mittag-Leffler condition in every degree, then this morphism is surjective in
  every degree `q`, and an isomorphism in degree `q` when the degree `q - 1`
  cohomology modules of `K` satisfy the Mittag-Leffler condition.

## Mittag-Leffler condition for finite systems (namespace `Langlands.Cohomology`)

- `isMittagLeffler_of_finite F hF`: a functor `F` from a cofiltered category
  to types with `hF : ∀ j, Finite (F.obj j)` satisfies the Mittag-Leffler
  condition. The image of `F.map (𝟙 j)` is a subset of the finite set
  `F.obj j`, which is the hypothesis of Mathlib's
  `Functor.isMittagLeffler_of_exists_finite_range`.
- `isMittagLeffler_moduleCat_of_finite F hF`: the same for a functor `F` to
  `ModuleCat R` whose modules have finite underlying sets, composed with the
  forgetful functor to types.

## The comparison morphism (namespace `Langlands.Cohomology.DivisibleSystem`)

- `homComplexLimitHomologyComparison R T W q`: the morphism of `R`-modules
  from the degree `q` cohomology of `homComplexLimit R T W` to the limit of
  the inverse system `m ↦ H^q(Hom^•(T m, W m))`. It is `limit.post` of
  `homComplexSystem R T W` along the degree `q` cohomology functor, so it is
  the canonical morphism induced by the limit projections and is defined
  without any hypothesis.
- `homComplexLimitHomologyComparison_π R T W q m` (`simp`, with a `reassoc`
  form): its composition with the projection to level `m` is the map on degree
  `q` cohomology induced by the limit projection
  `homComplexLimit R T W ⟶ Hom^•(T m, W m)` (Mathlib's `limit.post_π`).

## When the comparison is an isomorphism

All results below take `hT` as above.

- `isIso_homComplexLimitHomologyComparison_of_finite hS hT hfin q`: given
  `hS : FiniteCohomologyInverseLimitStatement R` and
  `hfin : ∀ m q, Finite (H^q(Hom^•(T m, W m)))`, the comparison is an
  isomorphism in every degree `q`. Proof: `hS` applied to
  `homComplexSystem R T W`, with surjectivity of the degreewise transition maps
  from `homComplexSystem_map_f_surjective` and finiteness from `hfin`.
- `homComplexLimitHomologyComparison_surjective hS hT q`: given
  `hS : DegreewiseInverseLimitCohomologyStatement R`, the comparison is
  surjective in every degree. Proof: the first conclusion of `hS`, whose
  hypothesis is `isMittagLeffler_homComplexSystem_eval`.
- `isIso_homComplexLimitHomologyComparison_of_isMittagLeffler hS hT q hML`:
  given `hS : DegreewiseInverseLimitCohomologyStatement R` and the
  Mittag-Leffler condition `hML` for the inverse system
  `m ↦ H^(q - 1)(Hom^•(T m, W m))`, the comparison is an isomorphism in degree
  `q` (the second conclusion of `hS`).
- `isIso_homComplexLimitHomologyComparison_of_finite_sub_one hS hT q hfin`:
  the same with `hML` replaced by finiteness of every
  `H^(q - 1)(Hom^•(T m, W m))`, by `isMittagLeffler_moduleCat_of_finite`.
- `homComplexLimitHomologyIso hS hT hfin q`: under the hypotheses of
  `isIso_homComplexLimitHomologyComparison_of_finite`, the comparison as an
  isomorphism; `homComplexLimitHomologyIso_hom` (`simp`) states that its
  forward morphism is `homComplexLimitHomologyComparison R T W q`.

## Degree zero

The published `towerHomQuotientEquivLimitHomologyZero R T W` is an
`R`-linear equivalence from the morphisms of inverse systems
`T.tower ⟶ W.tower`, modulo the submodule `nullHomotopicTowerHoms R T W` of
those admitting a compatible null-homotopy, to the degree `0` cohomology of
`homComplexLimit R T W`.

- `towerHomQuotientEquivLimitOfHomologyZero hS hT hfin`: given
  `hS : DegreewiseInverseLimitCohomologyStatement R` and
  `hfin : ∀ m, Finite (H^(-1)(Hom^•(T m, W m)))`, an `R`-linear equivalence
  from `(T.tower ⟶ W.tower) ⧸ nullHomotopicTowerHoms R T W` to the limit of
  the inverse system `m ↦ H^0(Hom^•(T m, W m))`. It is
  `towerHomQuotientEquivLimitHomologyZero R T W` followed by the comparison in
  degree `0`, which is an isomorphism by
  `isIso_homComplexLimitHomologyComparison_of_finite_sub_one` with `q = 0`
  (Lean's `0 - 1` is `-1` definitionally).
- `towerHomQuotientEquivLimitOfHomologyZero_apply`: the equivalence sends `x`
  to the image under the degree `0` comparison of
  `towerHomQuotientEquivLimitHomologyZero R T W x`.

## Smooth representations (namespace `Langlands.Cohomology`)

For a commutative ring `R`, a group `G` with a topology and `ℓ`-divisible systems
`T`, `W` of cochain complexes of smooth representations of `G` over `R`
(`SmoothRepComplexDivisibleSystem R G ℓ`), the Hom complexes are complexes of
`R`-modules of equivariant maps, and `hT` is relative projectivity in the
category of smooth representations.

- `isIso_smoothHomComplexLimitHomologyComparison_of_finite hS T W hT hfin q`:
  the specialization of `isIso_homComplexLimitHomologyComparison_of_finite`.
- `isIso_smoothHomComplexLimitHomologyComparison_of_finite_sub_one hS T W hT q
  hfin`: the specialization of
  `isIso_homComplexLimitHomologyComparison_of_finite_sub_one`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), proof of Proposition 4.10, printed p.312
(one-based PDF page 14; Worker 61 read the rendered scanned pages 13 and 14).
The proof begins on printed p.311 (one-based PDF page 13): "We need to check
that the complexes used to obtain the spectral sequences (4.9) satisfy a
Mittag-Leffler condition as `m` varies." The right-hand side of (4.9) is the
cohomology `H^{i+j}(S̄_{K(N)}, 𝓛̃_m)`, where `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m`. After
defining `T_m(j, ẽ)` and the maps (4.10.3) `T_{m+1}(j, ẽ) → T_m(j, ẽ)`,
Harris writes on p.312: "To check the Mittag-Leffler condition, we first need
to study the maps (4.10.3) as `m` varies." He shows that these maps are
surjective for all `m`, and continues: "Since the right-hand side of the
spectral sequence (4.9) is a finite group for all `m`, the complexes in
(4.10.2) satisfy a Mittag-Leffler condition. This and the arguments of [H1]
suffice to complete the proof."

In our reading, the Mittag-Leffler condition serves to pass to the inverse
limit over `m` of the complexes (4.10.2): the cohomology of the limit complex
should be the inverse limit of the cohomology of the complexes at finite
level. This module formalizes that passage for the published Hom complexes of
`ℓ`-divisible systems. The surjectivity of the maps (4.10.3) corresponds to
the degreewise surjectivity of the transition maps (published, from `hT`),
and the finiteness of the right-hand side of (4.9) corresponds to the
hypothesis `hfin` on the cohomology of the Hom complexes. Both correspondences
are our interpretation; the identification of Harris's complexes (4.10.2)
with Hom complexes of `ℓ`-divisible systems is not formalized. The
commutation of cohomology with inverse limits is the published hypothesis
`FiniteCohomologyInverseLimitStatement` or
`DegreewiseInverseLimitCohomologyStatement`, not a theorem.

The displayed formula (4.10.4) on the same page is the stronger integral
spectral sequence with `E_2` terms given by Ext groups and abutment
`H^{i+j}(S̄_{K(N)}, 𝓛̃)`. It is not the comparison morphism of this module and is
not formalized.

That a cofiltered system of finite sets satisfies the Mittag-Leffler
condition is standard. The comparison morphism, the hypotheses and all proofs
are ours; the module is derived.

## Scope

The inverse-limit statements are hypotheses. The module does not prove the
finiteness of the cohomology of any Hom complex, does not treat the spectral
sequences (4.9), (4.10.1) and (4.10.4), and does not identify Harris's
complexes (4.10.2) or `T_m(j, ẽ)` with the published Hom complexes. The
smooth results are specializations of the general ones; no smooth-specific
input is proved.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
