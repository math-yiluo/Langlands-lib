# Hom inverse systems of `ℓ`-divisible systems

Author: Worker 61. Built on `Langlands.Cohomology.DivisibleSystem`
(`DivisibleSystem`, `DivisibleSystem.obj`, `DivisibleSystem.projection`,
`DivisibleSystem.inclusion`, `DivisibleSystem.degree`,
`DivisibleSystem.epi_projection`, `powSMul`, `comp_powSMul`,
`SmoothRepComplexDivisibleSystem`) and on
`Langlands.Cohomology.LinearHomComplex` (`LinearHomComplex.complex`, the Hom
complex of two cochain complexes as a complex of `R`-modules). From Mathlib it
uses `ShortComplex.exact_iff_exact_up_to_refinements`,
`ShortComplex.Exact.gIsCokernel`, `CokernelCofork.IsColimit.desc'`, the
cochain lemmas `δ_ofHom_comp` and `δ_comp_ofHom`, `NatTrans.app_smul` and
`ModuleCat.hasLimitsOfShape`.

Everything is in the namespace `Langlands.Cohomology.DivisibleSystem`, except
`smoothHomComplexSystem`, which is in `Langlands.Cohomology`. Recall that an
`ℓ`-divisible system `T` in an abelian category `C` is an inverse system
`T.tower : ℕᵒᵖ ⥤ C` with objects `T m = T.obj m` and projections
`j = T.projection h : T m ⟶ T m'` for `m' ≤ m`, together with inclusions
`i : T m' ⟶ T m` for `m' < m`, such that `T m` is killed by `ℓ ^ m`, the
sequences `0 → T m' → T m → T (m - m') → 0` are short exact, and the
flatness and torsion conditions hold. `powSMul ℓ a X` is multiplication by
`ℓ ^ a` on `X`.

For two such systems `T` and `W`, this module makes `m ↦ Hom(T m, W m)` an
inverse system of modules, identifies its limit, and does the same for Hom
complexes of `ℓ`-divisible systems of cochain complexes.

## Projections as cokernels

`T` is an `ℓ`-divisible system in an abelian category `C`.

- `projection_comp_projection T h₁ h₂`, `projection_refl T m`: the
  projections compose, and the projection `T m ⟶ T m` is the identity.
- `powSMul_comp_projection T h`: for `m' ≤ m`, multiplication by `ℓ ^ m'` on
  `T m` followed by the projection `T m ⟶ T m'` is zero, because `T m'` is
  killed by `ℓ ^ m'`.
- `exact_powSMul_projection T h`: for `m' ≤ m` the sequence
  `T m ⟶ T m ⟶ T m'` of multiplication by `ℓ ^ m'` and the projection is
  exact. The proof uses refinements. For `m' = 0` multiplication by `ℓ ^ 0`
  is the identity. For `m' > 0` write `m = m' + k`. An element `x` of `T m`
  with zero projection lies, by the short exact sequence
  `0 → T k → T m → T m' → 0`, in the image of the inclusion `T k ⟶ T m`, so
  it is killed by `ℓ ^ k`. The flatness axiom (exactness of
  `T m ⟶ T m ⟶ T m` given by `ℓ ^ m'` and `ℓ ^ k`) then writes `x` as
  `ℓ ^ m'` times an element of `T m`.
- `projectionIsCokernelPowSMul T h`: since the projection is an epimorphism
  (`epi_projection`), it is a cokernel of multiplication by `ℓ ^ m'` on `T m`.
- `descend T h g hg`: a morphism `g : T m ⟶ Z` with
  `powSMul ℓ m' (T.obj m) ≫ g = 0` factors through the projection
  `T m ⟶ T m'`; `descend` is the factored morphism `T m' ⟶ Z`.
  `projection_descend` states `T.projection h ≫ T.descend h g hg = g`, and
  `descend_eq_iff` characterizes `descend` by this equation (uniqueness,
  since the projection is an epimorphism).

## The Hom inverse system

`R` is a ring, `C` an `R`-linear abelian category, and `T`, `W` are
`ℓ`-divisible systems in `C`.

- `powSMul_comp_comp_projection T W h f`: for `f : T m ⟶ W m` and
  `m' ≤ m`, the composite `f ≫ W.projection h` is killed by `ℓ ^ m'`
  (multiplication by `ℓ ^ m'` commutes with `f`, and `W m'` is killed by
  `ℓ ^ m'`).
- `homTransition T W h f : T m' ⟶ W m'`: the morphism `descend` of
  `f ≫ W.projection h` along the projection `T m ⟶ T m'`, that is, the
  unique morphism `g` with `T.projection h ≫ g = f ≫ W.projection h`
  (`projection_comp_homTransition`, `homTransition_eq_iff`).
- `homTransition_refl`, `homTransition_trans`: the transition for `m ≤ m` is
  the identity, and transitions compose.
- `homTransition_app T W α h`: a morphism of inverse systems
  `α : T.tower ⟶ W.tower` is fixed by the transitions:
  `homTransition T W h (α.app (op m)) = α.app (op m')`.
- `homTransitionLinear R T W h`: the transition as an `R`-linear map
  `(T m ⟶ W m) →ₗ[R] (T m' ⟶ W m')`; additivity and `R`-linearity follow
  from `homTransition_eq_iff`.
- `homSystem R T W : ℕᵒᵖ ⥤ ModuleCat R` (with Hom-universe `v` of `C`): the
  inverse system with `m`-th term the `R`-module `T m ⟶ W m` and maps the
  transitions; `homSystem_map_apply` evaluates its maps.
- `towerHomEval R T W m`: evaluation at level `m` of a morphism of inverse
  systems `T.tower ⟶ W.tower`, an `R`-linear map.
- `homSystemCone R T W`: the cone over `homSystem R T W` with apex the
  `R`-module of morphisms of inverse systems `T.tower ⟶ W.tower` (Mathlib's
  linear structure on natural transformations) and projections
  `towerHomEval`; it is a cone by `homTransition_app`.
- `homSystemLift R T W s`: for a cone `s`, the `R`-linear map from its apex
  to `T.tower ⟶ W.tower` sending `x` to the family of its components. The
  components are natural because the cone condition says they are related
  by the transitions, and `projection_comp_homTransition` turns this into
  the naturality square.
- `homSystemIsLimit R T W`: `homSystemCone R T W` is a limit cone. So the
  inverse limit of the modules `Hom(T m, W m)` is the module of morphisms of
  the inverse systems `T.tower ⟶ W.tower`.

A morphism of `ℓ`-divisible systems (`DivisibleSystem.Hom`) is a morphism of
the underlying inverse systems that in addition commutes with the inclusions
`i`. The limit above consists of all morphisms of the inverse systems; the
module says nothing about compatibility with the inclusions.

## Hom complexes

`R` and `C` are as before, and `T`, `W` are `ℓ`-divisible systems in the
category `CochainComplex C ℤ`. For an integer `p`, `T.degree p` is the
`ℓ`-divisible system in `C` of the degree-`p` terms (published in
DivisibleSystem). A cochain of degree `n` from `T m` to `W m`
(`CochainComplex.HomComplex.Cochain`) is a family of morphisms
`T m ^ p ⟶ W m ^ q` for `p + n = q`.

- `cochainTransition T W h z`: for `m' ≤ m` and a cochain `z` of degree `n`
  from `T m` to `W m`, the cochain from `T m'` to `W m'` whose component
  `(p, q)` is `homTransition (T.degree p) (W.degree q) h (z.v p q hpq)`
  (`cochainTransition_v`).
- `cochainTransition_eq_iff T W h z z'`: `cochainTransition T W h z = z'` if
  and only if `ofHom (T.projection h)` composed with `z'` equals `z` composed
  with `ofHom (W.projection h)`, as cochains; it is proved componentwise
  from `homTransition_eq_iff`. `ofHom_comp_cochainTransition` is the
  equation for `z' = cochainTransition T W h z`.
- `cochainTransition_refl`, `cochainTransition_trans`: identity and
  composition, componentwise from the previous section.
- `δ_cochainTransition T W h n n' z`: the transition commutes with the
  differential `δ n n'` of the Hom complexes. By `cochainTransition_eq_iff`
  it suffices that `ofHom (T.projection h)` composed with
  `δ (cochainTransition z)` equals `δ z` composed with
  `ofHom (W.projection h)`. This follows from the Leibniz rule for the
  composition of cochains with chain maps (`δ_ofHom_comp`, `δ_comp_ofHom`)
  and `ofHom_comp_cochainTransition`.
- `cochainTransitionLinear R T W h n`: the transition of degree-`n`
  cochains as an `R`-linear map (`cochainTransitionLinear_apply`).
- `homComplexTransition R T W h`: the chain map
  `LinearHomComplex.complex R (T m) (W m) ⟶ LinearHomComplex.complex R (T m') (W m')`
  with degree-`n` component `cochainTransitionLinear R T W h n`.
- `homComplexSystem R T W : ℕᵒᵖ ⥤ CochainComplex (ModuleCat R) ℤ`: the
  inverse system of Hom complexes `m ↦ Hom^•(T m, W m)` with maps
  `homComplexTransition`.
- `hasLimitsOfShape_natOp_moduleCat`: an instance stating that
  `ModuleCat.{v} R` has limits of shape `ℕᵒᵖ` for every universe `v`
  (Mathlib's `ModuleCat.hasLimitsOfShape`, since `ℕᵒᵖ` is small). It is a
  global instance, so that `homComplexLimit` and its limit API are usable
  downstream; `HasLimitsOfShape` is a proposition, so the instance cannot
  conflict with other instances.
- `homComplexLimit R T W`: the inverse limit `limit (homComplexSystem R T W)`
  in `CochainComplex (ModuleCat R) ℤ` (an abbreviation; nothing about it is
  proved).

## Smooth representations

`R : Type u` is a commutative ring, `G : Type v` a topological group, and
`T`, `W` are `ℓ`-divisible systems of `ℤ`-graded cochain complexes of
smooth representations (`SmoothRepComplexDivisibleSystem.{v, u, w} R G ℓ`,
the systems `C_m` of Harris 1999, p.306).

- `smoothHomComplexSystem R G T W`: `homComplexSystem R T W`, an inverse
  system in `CochainComplex (ModuleCat.{w} R) ℤ`. Its terms are the Hom
  complexes of `G`-equivariant `R`-linear maps.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), proof of Proposition 4.10. Printed p.311
(one-based PDF page 13): "We need to check that the complexes used to obtain
the spectral sequences (4.9) satisfy a Mittag-Leffler condition as m varies.
By (4.4.4) and (4.8), these are of the form [...] which can be rewritten

(4.10.2) ⊕_{i+j=k} ⊕_{(e,δ)∈O_{-i}} Hom_{𝒪/ℓ^m𝒪[S(ẽ)]}(C^j_m(ẽ),
Hom(𝒪_m[C_p/H_p]^M, 𝓛_m))."

Printed p.312 (one-based PDF page 14): "We may replace C^j_m(ẽ) by
C^j_m(ẽ)^{H_p} in (4.10.2). Write T_m(j, ẽ) =
Hom_{𝒪/ℓ^m𝒪[S(ẽ)]}(C^j_m(ẽ)^{H_p}, Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)). To check the
Mittag-Leffler condition, we first need to study the maps (4.10.3)
T_{m+1}(j, ẽ) → T_m(j, ẽ) as m varies. But we have seen in §2 that the maps
C^j_{m+1}(ẽ)^{H_p} → C^j_m(ẽ)^{H_p} are surjective. Since C^j_m(ẽ)^{H_p} and
Hom(𝒪_m[C_p/H_p]^M, 𝓛_m) are both free 𝒪/ℓ^m𝒪[S(ẽ)/H_p]-modules, it
follows that the maps (4.10.3) are surjective for all m." Both pages were
read by Worker 61 in the rendered scanned PDF.

Harris does not write a formula for the maps (4.10.3). We read them as
reduction modulo `ℓ ^ m`: a map `f` between the level-`(m+1)` modules,
followed by the projection of the target, factors through the projection of
the source, because the source projection is reduction modulo `ℓ ^ m`. This
is `homTransition`, and the module proves the facts this reading needs: the
projection `T m ⟶ T m'` is a cokernel of multiplication by `ℓ ^ m'`, which
holds for every `ℓ`-divisible system (`projectionIsCokernelPowSMul`). The
module gives the transitions for all `m' ≤ m`, which compose
(`homTransition_trans`); Harris's maps are those for `m' = m - 1`.

The Hom in `T_m(j, ẽ)` is over `𝒪/ℓ^m𝒪[S(ẽ)]`; the module uses morphisms in
the category `C`. For `C` the smooth representations over `R` (or complexes
of them), as in `smoothHomComplexSystem`, these are the `G`-equivariant
`R`-linear maps. When both objects are killed by `ℓ ^ m`, as the levels `m`
of `ℓ`-divisible systems are, `R`-linear and `R/ℓ^m`-linear maps coincide;
this remark is not formalized.

Harris's complexes (4.10.2) are formed from his double complexes and sums
over cells (4.4.4) and the isomorphism (4.8); their terms are Hom groups out
of the modules `C^j_m(ẽ)` into a fixed module `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)`.
`homComplexSystem` is the general Hom complex construction for two
`ℓ`-divisible systems of cochain complexes, and has the shape of Harris's
inverse system. The module does not identify Harris's complexes with Hom
complexes of this kind (including the degree conventions), and does not
prove that Harris's systems `C^j_m(ẽ)^{H_p}` and
`Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are `ℓ`-divisible systems in the sense of the
DivisibleSystem module. Such identifications are left to the modules that
build these systems.

The construction is ours: the cokernel description of the projections, the
transition maps and their properties, the identification of the limit of
`homSystem` with morphisms of inverse systems, and the degreewise
construction on Hom complexes. The cited passages contain only the modules
`T_m(j, ẽ)`, the complexes (4.10.2) and the existence of the maps (4.10.3).

## Scope

The module proves no surjectivity of the transitions (Harris's surjectivity
of (4.10.3) uses freeness, which is not assumed), no Mittag-Leffler
condition, and nothing about the cohomology of `homComplexLimit` or of the
terms of `homComplexSystem`. It does not compare the limit with Hom or Ext
groups of inverse limits, and does not construct the spectral sequences
(4.9), (4.10.1) or (4.10.4). The limit of the Hom complexes is identified
only in the non-graded case (`homSystemIsLimit`).

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
