# Left exact functors and ℓ-divisible systems

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DivisibleSystem` (ℓ-divisible systems, Harris 1999,
(2.1)), `Langlands.Cohomology.DivisibleSystem.Coaugmented` (the residual and
term systems of Harris's Lemma 2.2),
`Langlands.Sheaf.Equivariant.SmoothSheafCompactSections` (compact sections of
smooth sheaves) and `Langlands.Cohomology.SmoothSheafCohomology` (invariant
compact sections). All names below are in the namespace
`Langlands.Cohomology.DivisibleSystem`, except
`Langlands.Cohomology.shortComplex_map_exact_of_mono`. Write `T m` for
`T.obj m`, `i` for the inclusions `T.inclusion` and `j` for the projections
`T.projection h : T m ⟶ T m'` (`m' ≤ m`), as in the parent module.

On p.305 Harris truncates the resolutions of Lemma 2.2 at degree `D + 1`,
`G_m^• = τ_{≤D+1}(F_m^•)`, and states Lemma 2.2 bis: each `{G_m^q}` is an
`ℓ`-divisible system. He continues: "Indeed, the only point that needs to be
checked is the surjectivity of the projection `G_m^{D+1}(U) → G_{m-1}^{D+1}(U)`
for any m, for an étale morphism `U → U(ẽ)_F̄`. But it follows from Fact 2 that
`G_m^D(U) → G_m^{D+1}(U)` is surjective for all m, so the result follows from
the snake lemma." He then works with the complexes of sections
`G_m^•(U(ẽ)_F̄)` in (2.3).

This module isolates the formal part of that step. If an additive functor
preserves finite limits and maps the projections `j` to epimorphisms, the image
of an `ℓ`-divisible system is again one. The epimorphism condition is the only
additional hypothesis, and it is an explicit hypothesis of every construction
below. It is not derived here from acyclicity, from Harris's Fact 2 or from any
bound on cohomological dimension.

Left exactness alone keeps the rows (2.1) exact except at their last term, and
it keeps the torsion condition (`map_torsion_exact`) and the defining
equations. It does not keep flatness. For example, take `ℓ ≥ 2`, abelian groups,
`T m = ℤ/ℓ^mℤ` with the usual maps, and the left exact functor
`F = Hom(ℤ/ℓℤ, -)`. Then `F(T 2) ≅ ℤ/ℓℤ`, on which multiplication by `ℓ` is
zero, so multiplication by `ℓ` followed by multiplication by `ℓ` on `F(T 2)` is
not exact, and `flat 1 1` fails (as does surjectivity of `F(j)`). Flatness of
the image is derived in `map_flat` below, and that proof uses the epimorphism
hypothesis.

## Left exactness and the factorization of `ℓ^a`

- `Langlands.Cohomology.shortComplex_map_exact_of_mono F S hS`: for an
  additive functor `F` between abelian categories that preserves finite
  limits, and an exact `S : X₁ ⟶ X₂ ⟶ X₃` whose first map is a monomorphism,
  `F(X₁) ⟶ F(X₂) ⟶ F(X₃)` is exact and `F(X₁) ⟶ F(X₂)` is a monomorphism.
  This is one implication of Mathlib's `Functor.preservesFiniteLimits_tfae`.
- `exists_powSMul_eq T ha hb`: for `0 < a` and `0 < b`, there is an
  isomorphism `u : T (a + b - a) ⟶ T b` such that multiplication by `ℓ^a` on
  `T (a + b)` equals `j ≫ u ≫ i`, with `j : T (a + b) ⟶ T (a + b - a)` and
  `i : T b ⟶ T (a + b)`. For a free `ℤ/ℓ^{a+b}ℤ`-module `M` with the
  standard reduction maps and the standard inclusions `x ↦ ℓ^{m-m'} x`, this
  says that `ℓ^a` is reduction modulo `ℓ^b` followed by the identification of
  `M/ℓ^b M` with `ℓ^a M`.

  In general `u` compares two chosen identifications: `j` identifies the
  quotient of `T (a + b)` by the image of `T a` with `T (a + b - a)`, and `i`
  identifies the `ℓ^b`-torsion of `T (a + b)` with `T b`. The axioms of the
  parent module constrain only the images and kernels of the chosen maps, not
  the maps themselves. So even after identifying `a + b - a` with `b`, `u` need
  not be the identity. For example, for `ℓ = 3` and `T m = ℤ/3^mℤ` with the
  usual reductions as projections and `x ↦ -3^{m-m'} x` as the inclusions,
  every axiom holds, because each inclusion has the same image as the standard
  one. At `a = b = 1`, the composite `j ≫ i : ℤ/9ℤ ⟶ ℤ/3ℤ ⟶ ℤ/9ℤ` (that is,
  `u` the identity) sends `1` to `-3 = 6`, whereas multiplication by `3` sends
  it to `3`. So here `u` must be `-1` on `ℤ/3ℤ`. The lemma therefore asserts
  only that some isomorphism `u` exists.

  The proof uses only the axioms of an `ℓ`-divisible system. Multiplication by
  `ℓ^a` vanishes on the image of `i : T a ⟶ T (a + b)`. So it factors through
  `j`, a cokernel of that `i` (`projectionIsCokernel`), as some `g`. Then
  `g ≫ ℓ^b = 0`, so `g` factors through `i : T b ⟶ T (a + b)`, a kernel of
  `ℓ^b` (`inclusionIsKernel`), as `u`. The map `g` is a monomorphism because
  the kernel of `ℓ^a` is the image of `i : T a ⟶ T (a + b)`
  (`torsion_exact`). `u` is an epimorphism because the kernel of `ℓ^b` is the
  image of `ℓ^a` (`flat a b`). Both are checked with refinements.

## The image of an `ℓ`-divisible system

`C` and `D` are abelian categories, `ℓ : ℕ`, `T : DivisibleSystem C ℓ`, and
`F : C ⥤ D` is additive and preserves finite limits. The hypothesis `hF` says
that `F.map (T.projection h)` is an epimorphism for all `m' ≤ m`.

- `map_torsion_exact T F h` (no `hF` needed): for `m' < m`,
  `F(i) : F(T m') ⟶ F(T m)` followed by multiplication by `ℓ^{m'}` on
  `F(T m)` is exact. This is `shortComplex_map_exact_of_mono` applied to the
  parent's `torsion_exact`, with `F(ℓ^{m'}) = ℓ^{m'}` by additivity
  (`map_powSMul`).
- `map_flat T F hF a b`: multiplication by `ℓ^a` then by `ℓ^b` on
  `F(T (a + b))` is exact. If `a = 0` or `b = 0` this is immediate. Otherwise,
  take `x` with `x ≫ ℓ^b = 0`. By `map_torsion_exact`, after a refinement
  `x = y ≫ F(i)` for `i : T b ⟶ T (a + b)`. Because `F(j)` is an epimorphism,
  after a further refinement `y ≫ F(u⁻¹) = z ≫ F(j)`. Then
  `z ≫ ℓ^a = z ≫ F(j) ≫ F(u) ≫ F(i) = y ≫ F(i)` by `exists_powSMul_eq`.
- `mapLeftExact T F hF : DivisibleSystem D ℓ` has tower `T.tower ⋙ F` and
  inclusions `F(i)`. Its short exact rows (2.1) are exact with monic first map
  by `shortComplex_map_exact_of_mono`, and the last map is an epimorphism by
  `hF`. `torsion_exact` and `flat` are the two lemmas above; the equations
  `powSMul_eq_zero` and `inclusion_comp` follow from additivity of `F`.
  `mapLeftExact_tower` and `mapLeftExact_inclusion` record the tower and the
  inclusions.
- `mapLeftExact_eq_map`: if `F` also preserves finite colimits, then
  `mapLeftExact T F hF` is the parent module's `T.map F`, by `rfl`.
- `epi_map_projection_of_succ T F h`: if `F` maps every projection
  `T (m + 1) ⟶ T m` to an epimorphism, then it maps every projection
  `T m ⟶ T m'` (`m' ≤ m`) to an epimorphism. The projections are composites
  of successive ones because `T.tower` is a functor. This is the form of the
  hypothesis that Harris checks: `G_m^{D+1}(U) → G_{m-1}^{D+1}(U)` only. The
  lemma needs only that `F` is a functor.
- `mapLeftExactHom T F hF f hF'`: a morphism `f : T ⟶ T'` of `ℓ`-divisible
  systems, both satisfying the hypothesis, gives a morphism
  `T.mapLeftExact F hF ⟶ T'.mapLeftExact F hF'` with components `F(f)`
  (`mapLeftExactHom_tower`).

## The residual system as the top term of a truncation

`F : C ⥤ C` is additive and preserves finite limits and finite colimits,
`η : 𝟭 C ⟶ F` has monic components and `T : DivisibleSystem C ℓ`, as in the
general section of the Coaugmented module. Write `F^q` for the term system
`T.termSystem F η q`, `R q` for the residual system `T.residualSystem F η q`
and `d^q` for `T.termDifferential F η q : F^q ⟶ F^{q+1}`.

- `residualInclusionIsKernel F η T q m`: at every level `m`, the inclusion
  `R q m ⟶ F^q m` (the level-`m` component of `T.residualInclusion F η q`) is
  a kernel of `d^q` at level `m`. It is the kernel part of the Coaugmented
  module's `residualInclusion_termDifferential_exact`.

  So in degree `q` the truncation `τ_{≤q}` of the level-`m` resolution has the
  term `ker d_m^q`, which is `R q m`. Harris's top term `G^{D+1}` is therefore
  the residual system `R (D + 1)`, which the Coaugmented module already
  proves to be an `ℓ`-divisible system in `C`. In particular, in the category
  of sheaves itself nothing more is needed. What Harris checks is the
  surjectivity of the projections after taking sections, and that is the
  hypothesis `hF` above.
- `mapResidualInclusionIsKernel F η T Φ q m`: for an additive functor
  `Φ : C ⥤ D` preserving finite limits, `Φ(R q m) ⟶ Φ(F^q m)` is a kernel of
  `Φ(d^q)` at level `m`. For a sections functor `Φ`, `Φ(R q m)` is thus the
  module of cycles `Z_m^q = ker d_m^q` of the section complex in Harris's
  (2.3). It is Mathlib's `isLimitForkMapOfIsLimit'`.

## Compact sections of smooth sheaves

`R`, `G` and `X` are as in the published `SmoothTopologicalSheaf R G X`: they
lie in one universe, `G` is a topological group acting on `X` by continuous
translations, and `HasStableNeighbourhoods G X` holds.
`T : SmoothSheafDivisibleSystem R G X ℓ`. The published functors
`smoothSheafCompactSections R G X` (compactly supported sections, as smooth
representations) and `SmoothSheafCohomology.invariantCompactSections R G X`
(their `G`-invariants, as `R`-modules) are additive and preserve finite
limits (published instances), so `mapLeftExact` applies to them.

- `compactSectionsSystem T hT : DivisibleSystem (SmoothRep R G) ℓ` is
  `T.mapLeftExact (smoothSheafCompactSections R G X) hT`. Here `hT` says that
  compact sections of every projection of `T` are epimorphisms.
- `invariantCompactSectionsSystem T hT : DivisibleSystem (ModuleCat R) ℓ` is
  `T.mapLeftExact (SmoothSheafCohomology.invariantCompactSections R G X) hT`,
  with the corresponding hypothesis.

For the smooth Godement systems of the Coaugmented module, the exactness of
the degree-zero smooth Godement functor is not proved in the Library. It is
Worker 3's proposition `SmoothGodementZeroExactStatement R G X`, and the next
three declarations take a proof `h` of it as an explicit argument.

- `smoothGodementTermCompactSectionsSystem h T q hq` is
  `compactSectionsSystem` of the term system `smoothGodementTermSystem h T q`
  (Harris's `{F_m^q}`, so `{G_m^q}` for `q ≤ D`). `hq` says that compact
  sections of its projections are epimorphisms.
- `smoothGodementResidualCompactSectionsSystem h T q hq` is
  `compactSectionsSystem` of the residual system
  `smoothGodementResidualSystem h T q` (for `q = D + 1`, Harris's top term
  `{G_m^{D+1}}`), under the same kind of hypothesis.
- `smoothGodementTermCompactSectionsDifferential h T q hq hq'` is the morphism
  of systems from degree `q` to degree `q + 1` induced by
  `smoothGodementTermDifferential h T q`, via `mapLeftExactHom`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed p.305. Worker 61 read the
page in the scanned original.

1. What Harris proves and what is formalized. Harris obtains the surjectivity
   of `G_m^{D+1}(U) → G_{m-1}^{D+1}(U)` from Fact 2 (vanishing of cohomology
   above degree `D`), which makes `G_m^D(U) → G_m^{D+1}(U)` surjective, and
   the snake lemma. For `q ≤ D` the terms `G_m^q = F_m^q` are `R Γ_c`-acyclic,
   and the surjectivity on their sections is not discussed separately. None of
   this is formalized here. The module proves only the formal consequence:
   given the surjectivity, the sections form `ℓ`-divisible systems. The
   surjectivity is the hypothesis `hF` (or `hT`, `hq`, `hq'`), and nothing in
   the module discharges it.
2. Sections. Harris takes sections over étale `U → U(ẽ)_F̄` of étale sheaves
   on a rigid analytic space, and in (2.3) the complex `G_m^•(U(ẽ)_F̄)`
   computes compactly supported cohomology `H_c^q(U(ẽ)_F̄, ℤ/ℓ^mℤ)`. The
   Library's smooth framework is topological, not étale. The functors used
   here are its compactly supported sections and their `G`-invariants, the
   available counterparts of `Γ_c`. Harris later takes invariants under an
   open normal pro-`p` subgroup `H ⊂ S(ẽ)` (p.305), while
   `invariantCompactSections` takes invariants under the whole group `G`; the
   module does not restrict sheaves to subgroups. The general `mapLeftExact`
   applies to any additive functor preserving finite limits, so a later
   sections functor on another site can use it directly.
3. Truncation. The module identifies the residual system `R q` with the
   cycles `ker d^q` at every level, so `R (D + 1)` plays the role of
   `G^{D+1}`. It does not construct the truncated complexes `G_m^•` or a
   system of truncated complexes.
4. The factorization `exists_powSMul_eq` is not stated by Harris. For free
   `ℤ/ℓ^{a+b}ℤ`-modules with the standard compatible reductions and inclusions
   `x ↦ ℓ^{m-m'} x`, it is the familiar identity `ℓ^a = i ∘ j`. For arbitrary
   maps allowed by the parent axioms it holds only up to the comparison
   isomorphism `u`, which can be nontrivial (see the example above). It is
   derived here from the axioms of the parent module, and used only to prove
   `map_flat`.
5. `epi_map_projection_of_succ` matches the form of Harris's check
   (successive projections only), using that the projections are composites
   of successive ones. That holds because `T.tower` is a functor. The parent
   module explains why it imposes this transitivity.

`mapLeftExact` and the section systems are the `ℓ`-divisible systems of
sections that Harris uses after Lemma 2.2 bis, under the explicit surjectivity
hypothesis. The factorization, the exactness lemmas, the kernel
identifications and the reduction to successive projections are derived. The
smooth declarations are instances of the general construction.

## Scope

The module does not prove Harris's Fact 2, any acyclicity, Lemma 2.2 bis, the
surjectivity of any projection on sections, or any statement about cohomology.
It does not construct the truncated complexes, the free resolutions and the
complexes `C_m^•` of pp.305–306, or the Mittag-Leffler argument of Lemma 2.8.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
