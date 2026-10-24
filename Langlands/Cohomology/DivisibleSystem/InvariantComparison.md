# Comparison of Harris's `C_m^{•,H}` with the underlying complexes

Author: Worker 61. Built on `Langlands.Cohomology.DivisibleSystem.TotalExact`
(`quasiIso_quotientInvariantsTotalSystemToExtend`) and
`Langlands.Cohomology.DivisibleSystem.ProPInvariants` (`IsProPSubgroup`,
`isSmooth_res_subtype`, `epi_smoothQuotientInvariants_map_projection_f`,
`proPQuotientInvariantsComplexesInclusion`). Through them it uses the earlier
modules of the series: from the base module, `DivisibleSystem.map`,
`mapFunctor` and `comp_tower`; from the Invariants module, `smoothQuotientInvariants`,
`quotientInvariantsInclusion`, `toRepComplexes`, `quotientInvariantsComplexes`,
`inflatedQuotientInvariantsComplexes` and `quotientInvariantsComplexesInclusion`;
from the InvariantTotal module, `quotientInvariantsTotalSystem`; and from the
TotalComparison module, `extendSystem`, `isIso_of_isIso_tower_app` and
`quotientInvariantsTotalSystemToExtend`. It
uses the Library's `Langlands.Cohomology.DerivedPlus` (`extendXMapIso`,
`mapExtendIso`) and Worker 3's `Langlands.Cohomology.ProPInvariants.Statement`
(`invariantsInclusion`, `ProPInvariantsExactStatement` and
`ProPInvariantSubcomplexStatement`). From Mathlib it uses extension of complexes
along `ComplexShape.embeddingUpNat` (`HomologicalComplex.extend`, `extendMap`,
`extendXIso`, `isZero_extend_X`, `extendHomologyIso`, `extend_exactAt`,
`quasiIso_extendMap_iff`), `Rep.resFunctor`, `Rep.quotientToInvariantsFunctor`,
`Functor.mapHomologicalComplexCompIso` and
`HomologicalComplex.quasiIso_map_iff_of_preservesHomology`. The first six
sections are in the namespace `Langlands.Cohomology`, so the names written
`Rep.…` below are `Langlands.Cohomology.Rep.…`. The last four sections are in
`Langlands.Cohomology.DivisibleSystem`.

On p.305 Harris takes an open normal pro-`p` subgroup `H ⊂ S(ẽ)` that "acts
trivially on `H_c^q(U(ẽ)_F̄, ℤ/ℓ^mℤ)` for all `q` and all `m`", and continues:
"Since `p` is prime to `ℓ`, the functor `H⁰(H, •)` is exact on `ℓ`-primary
torsion modules, hence the inclusion `G_m^•(U(ẽ)_F̄)^H ↪ G_m^•(U(ẽ)_F̄)` in
(2.3) is a quasi-isomorphism." Here `H_c^q` is compactly supported étale
cohomology. By his isomorphism (2.3) it is the cohomology `H^q(G_m^•(U(ẽ)_F̄))`
of the complex `G_m^•(U(ẽ)_F̄)`, which is formed from the `RΓ_c`-acyclic
resolution `G_m^•` of Lemma 2.2 bis (the compact-section complex). On p.306
he resolves the `H`-invariants by
`C_m^{•,H}`. The earlier modules build `C_m^{•,H}` for a general system `K`
(InvariantTotal) and prove that its map to the `H`-invariants extended to `ℤ` is
a quasi-isomorphism (TotalExact). They also build the inclusion of the inflated
`H`-invariants (Invariants), but do not prove it is a quasi-isomorphism. This
module proves that, given Worker 3's proposition
`ProPInvariantSubcomplexStatement`, and composes the two maps into one
`G`-equivariant comparison at a fixed `H`.

Notation: composition `f ≫ g` is `f` followed by `g`. `e` is Mathlib's
`ComplexShape.embeddingUpNat`, so `L.extend e` is an `ℕ`-graded cochain complex
`L` extended by zero to `ℤ`.

## Extension and functors

`C`, `D` are categories with zero morphisms and zero objects,
`F, G : C ⥤ D` preserve zero morphisms, and `e : c.Embedding c'` is an
embedding of complex shapes. The Library's `DerivedPlus.mapExtendIso F K e` is
an isomorphism from the extension of `F` applied to `K` to `F` applied to the
extension of `K`. Its components `DerivedPlus.extendXMapIso F K i` are the
identity in the degrees coming from `c`, and the unique isomorphism of zero
objects elsewhere.

- `extendMapIso e F K`: the inverse isomorphism
  `(F.mapHomologicalComplex c').obj (K.extend e) ≅
  ((F.mapHomologicalComplex c).obj K).extend e`. By `extendMapIso_hom_f`, its
  component in degree `i'` is the inverse of `DerivedPlus.extendXMapIso F K (e.r i')`.
- `extendXMapIso_inv_mapX` and `extendMapIso_hom_naturality`: `extendMapIso`
  is natural in `K` with respect to Mathlib's `extendMap`. In degrees coming
  from `c` both sides equal `F` of the component. In the other degrees the
  target is zero.
- `extendXMapIso_inv_app` and `extendMapIso_hom_app`: `extendMapIso` is
  natural in the functor. For `α : F ⟶ G`, `α` applied degreewise to `K.extend e`,
  followed by `extendMapIso e G K`, equals `extendMapIso e F K` followed by the
  extension of `α` applied degreewise to `K`. The proof is the same.

## Trivial actions and smoothness under isomorphisms

`k` is a commutative ring and `Γ` a group. `R` is a commutative ring and `H` a
group with a topology.

- `Rep.ρ_eq_id_of_iso i h`: if `g` acts as the identity on `A : Rep k Γ` and
  `i : A ≅ B`, then `g` acts as the identity on `B`. This holds because
  `B.ρ g b = i.hom (A.ρ g (i.inv b)) = b`, by equivariance of `i.hom`.
- `Rep.ρ_eq_id_of_isZero hA g`: every element acts as the identity on a zero
  representation, since its underlying module is a subsingleton (Mathlib's
  `Rep.isZero_iff`).
- `Rep.isSmooth_of_isZero hA`: a zero representation of `H` is smooth, because
  every vector is fixed by the open subgroup `⊤`.
- `Rep.isSmooth_of_iso i hB`: a representation isomorphic to a smooth one is
  smooth. The open subgroup fixing `i.hom v` also fixes `v`, by equivariance of
  `i.inv`.

## The inclusion of invariants is a quasi-isomorphism

`R` is a commutative ring, `G` a topological group, `H` a normal subgroup of
`G` with the subspace topology, and `p : ℕ`.

- `quasiIso_quotientInvariantsInclusion_app hS hH hR L hL htriv` takes
  `hS : ProPInvariantSubcomplexStatement.{uG, uR, uV}`,
  `hH : IsProPSubgroup p H`, `hR : IsUnit (p : R)` and an `ℕ`-graded cochain
  complex `L` of representations of `G` (`Rep.{uV} R G`). It also takes `hL`:
  every degree of `L`, restricted to `H`, is smooth. And it takes `htriv`:
  every `h ∈ H` acts as the identity on every cohomology representation
  `L.homology n`. The conclusion is that the Invariants module's inclusion of
  the inflated `H`-invariants, `quotientInvariantsInclusion R H` applied
  degreewise to `L`, is a quasi-isomorphism.

  Proof. The fields `compactSpace` and `totallyDisconnectedSpace` of `hH`
  become local instances. Let `C'` be `L` restricted to `H` (Mathlib's
  `Rep.resFunctor H.subtype`, which preserves finite limits and colimits).
  Then `C'.extend e` satisfies the hypotheses of `hS`:
  - Its degrees are smooth. In degrees `n : ℕ` it is isomorphic to a degree
    of `C'` (`extendXIso`), so `hL` and `Rep.isSmooth_of_iso` apply. In
    negative degrees it is zero (`isZero_extend_X`), so
    `Rep.isSmooth_of_isZero` applies.
  - `H` acts trivially on its cohomology. In degrees `n : ℕ` that cohomology
    is isomorphic to `L.homology n` restricted to `H`, through Mathlib's
    `extendHomologyIso` and `mapHomologyIso` for the exact functor
    `Rep.resFunctor`. So `htriv` and `Rep.ρ_eq_id_of_iso` apply. In negative
    degrees the extension is exact (`extend_exactAt`), its cohomology is zero,
    and `Rep.ρ_eq_id_of_isZero` applies.

  So `hS` applies, at the prime `hH.prime`, the group `H`, the condition
  `hH.isPGroup`, the ring `R` and `hR`. It gives that Worker 3's
  `invariantsInclusion R H` applied degreewise to `C'.extend e` is a
  quasi-isomorphism of complexes of `R`-modules. By `extendMapIso_hom_app` this
  map is isomorphic, as an arrow, to the extension of `invariantsInclusion R H`
  applied degreewise to `C'`. Hence that map is a quasi-isomorphism before
  extension (`quasiIso_extendMap_iff`). It agrees degreewise with the forgetful
  functor `forget₂ (Rep R G) (ModuleCat R)` applied to the map in the
  conclusion. By Mathlib's definition of `Rep.quotientToInvariantsFunctor`,
  both are the inclusion of the `H`-invariant vectors. The forgetful functor
  preserves homology and reflects isomorphisms, so it reflects
  quasi-isomorphisms (`quasiIso_map_iff_of_preservesHomology`).

## Inflation

- `Rep.quotientInflation R H` (abbreviation), for a normal subgroup `H` of a
  group `G`: inflation `Rep R (G ⧸ H) ⥤ Rep R G` along the quotient map,
  i.e. Mathlib's `Rep.resFunctor (QuotientGroup.mk' H)`. Its two instances say
  that it preserves finite limits and finite colimits (Mathlib's instances for
  `Rep.resFunctor`).

## Mapping a system through an exact functor and extending to `ℤ`

`A`, `B` are abelian categories and `F : A ⥤ B` is additive and preserves
finite limits and finite colimits, as `DivisibleSystem.map` requires.

- `mapHom F f`, for a morphism `f : T ⟶ T'` of `ℓ`-divisible systems in `A`:
  the base module's `mapFunctor` applied to `f`, with source `T.map F` and
  target `T'.map F`. By `mapHom_tower_app`, its level-`m` component is
  `F.map (f.tower.app m)`.
- `extendSystemMapHom F T`, for `T : DivisibleSystem (CochainComplex A ℕ) ℓ`:
  the morphism from `T.extendSystem`, mapped by `F` applied degreewise, to the
  extension of `T.map (F applied degreewise)`. At each level it is
  `extendMapIso e F`, and it commutes with the inclusions by
  `extendMapIso_hom_naturality`. The instance `isIso_extendSystemMapHom` says
  it is an isomorphism, because every level is one
  (`isIso_of_isIso_tower_app`). `extendSystemMapIso F T` is this isomorphism.
  `extendSystemMapHom_tower_app` records the level-`m` component.
- `extendSystemComparison F f g`, for systems
  `T₀ : DivisibleSystem (CochainComplex A ℤ) ℓ`,
  `T : DivisibleSystem (CochainComplex A ℕ) ℓ`,
  `T' : DivisibleSystem (CochainComplex B ℕ) ℓ` and morphisms
  `f : T₀ ⟶ T.extendSystem`,
  `g : T.map (F applied degreewise) ⟶ T'`, is the composite morphism
  `T₀.map (F applied degreewise) ⟶ T'.extendSystem` of three maps: `f`
  mapped by `F` (`mapHom`), then `extendSystemMapHom F T`, then the extension
  of `g` to `ℤ`. `extendSystemComparison_tower_app` writes its level-`m`
  component as this composite of complexes, with Mathlib's `extendMap` for the
  last factor.
- `quasiIso_extendSystemComparison_tower_app F f g m hf hg`: the level-`m`
  component of `extendSystemComparison F f g` is a quasi-isomorphism if those
  of `f` and `g` are. An exact functor preserves homology (Mathlib's
  `Functor.preservesHomology_of_preservesEpis_and_kernels`), so it keeps
  quasi-isomorphisms. `extendMapIso` is an isomorphism. Extension keeps
  quasi-isomorphisms (`quasiIso_extendMap_iff`). Composites of
  quasi-isomorphisms are quasi-isomorphisms.

## The inclusion of invariants for systems

`R` is a commutative ring, `G` a group with a topology, `H` a normal subgroup,
and `K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, uV} R G) ℕ) ℓ`.
`hK` is the Invariants module's hypothesis that every degree of every
projection of `K` stays an epimorphism on `H`-invariants.

- `quotientInvariantsComplexesInclusion_tower_app_eq K H hK m`: the level-`m`
  component of the Invariants module's `K.quotientInvariantsComplexesInclusion
  H hK` is `quotientInvariantsInclusion R H` applied degreewise to the
  underlying complex of representations `K.toRepComplexes.obj m`.
- `quasiIso_quotientInvariantsComplexesInclusion K hS hH hR hK m htriv`: for
  `G` a topological group, `hS`, `hH` and `hR` as above, and `htriv` saying
  that every `h ∈ H` acts as the identity on the cohomology of
  `K.toRepComplexes.obj m`, that level-`m` component is a quasi-isomorphism.
  This is `quasiIso_quotientInvariantsInclusion_app` together with the
  previous lemma. The hypothesis `hL` holds by `isSmooth_res_subtype`.

## The comparison from `C_m^{•,H}`

Now `K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, max w uR uG} R G) ℕ) ℓ`
and `N : ℕ`, in the universes of the InvariantTotal module.

- `inflateQuotientInvariantsComplexesHom K H hK`: a morphism of `ℓ`-divisible
  systems of complexes of representations of `G`. Its source is the
  `H`-invariants system `K.quotientInvariantsComplexes H hK` mapped by
  `Rep.quotientInflation R H` applied degreewise. Its target is
  `K.inflatedQuotientInvariantsComplexes H hK`, which applies the composite
  functor in one step. The two agree degreewise but are not definitionally
  equal as systems at reasonable cost. The components are Mathlib's
  `Functor.mapHomologicalComplexCompIso` for the identity isomorphism, the
  identity in every degree. The instance
  `isIso_inflateQuotientInvariantsComplexesHom_tower_app` says that every
  level is an isomorphism.

From now on `H` also has finite index (`[H.FiniteIndex]`), as in the
InvariantTotal module.

- `inflatedQuotientInvariantsTotalSystem N K H hK` (abbreviation): the
  InvariantTotal module's `quotientInvariantsTotalSystem N K H hK` (Harris's
  `C_m^{•,H}`, rows `q < N`), mapped by `Rep.quotientInflation R H` applied
  degreewise. It is an `ℓ`-divisible system of `ℤ`-graded complexes of
  representations of `G`.
- `quotientInvariantsTotalSystemToRepExtend N K H hK hN` (abbreviation), for
  `hN : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)`: the morphism
  `inflatedQuotientInvariantsTotalSystem N K H hK ⟶ K.toRepComplexes.extendSystem`
  given by `extendSystemComparison` for `F = Rep.quotientInflation R H`. Its
  `f` is the TotalComparison module's `quotientInvariantsTotalSystemToExtend N K H hK hN`.
  Its `g` is `inflateQuotientInvariantsComplexesHom K H hK` followed by
  `K.quotientInvariantsComplexesInclusion H hK`. At level `m` it is the
  inflation of the map from `C_m^{•,H}` to the `H`-invariants of `K m`
  extended to `ℤ`, followed by the extension of the inclusion of those
  invariants into `K m`.
- `quasiIso_quotientInvariantsTotalSystemToRepExtend N K hS hH hR hK hN m htriv`:
  for `G` a topological group, `hS : ProPInvariantSubcomplexStatement.{uG, uR, max w uR uG}`,
  `hH`, `hR` as above, and `htriv` the trivial action of `H` on the cohomology
  of `K.toRepComplexes.obj m`, the level-`m` component of this comparison is a
  quasi-isomorphism. Its `f` part is one by the TotalExact module's
  `quasiIso_quotientInvariantsTotalSystemToExtend`. Its `g` part is one by
  `quasiIso_quotientInvariantsComplexesInclusion`, since the components of
  `inflateQuotientInvariantsComplexesHom` are isomorphisms. The proof then
  follows that of `quasiIso_extendSystemComparison_tower_app`.

## Pro-`p` subgroups

`G` is a topological group, `H` a normal subgroup, `hH : IsProPSubgroup p H`
and `hR : IsUnit (p : R)`. Here `hP` is a proof of Worker 3's
`ProPInvariantsExactStatement`. From `hP`, the ProPInvariants module's
`epi_smoothQuotientInvariants_map_projection_f hP hH hR K` gives the
hypothesis `hK`.

- `quasiIso_proPQuotientInvariantsComplexesInclusion hP hS hH hR K m htriv`:
  for `K` in `SmoothRep.{uR, uG, uV} R G` and `hP`, `hS` in the universes
  `{uG, uR, uV}`, the level-`m` component of the ProPInvariants module's
  `K.proPQuotientInvariantsComplexesInclusion hP hH hR` is a
  quasi-isomorphism, given `htriv` at level `m`.
- `proPQuotientInvariantsTotalSystemToRepExtend N hP hH hR K hN`
  (abbreviation): for `H` of finite index, `K` in
  `SmoothRep.{uR, uG, max w uR uG} R G` and
  `hP : ProPInvariantsExactStatement.{uG, uR, max w uR uG}`, this is
  `quotientInvariantsTotalSystemToRepExtend N K H hK hN` with the derived `hK`.
- `quasiIso_proPQuotientInvariantsTotalSystemToRepExtend N hP hH hR K hS hN m htriv`:
  its level-`m` component is a quasi-isomorphism.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed pp.305–306. Worker 61
read both pages in the scanned original.

1. The inclusion of invariants. Harris derives the quasi-isomorphism
   `G_m^•(U(ẽ)_F̄)^H ↪ G_m^•(U(ẽ)_F̄)` from the trivial action of `H` on the
   cohomology and the exactness of `H⁰(H, •)`. Worker 3's
   `ProPInvariantSubcomplexStatement` states this step for `ℤ`-graded
   complexes of smooth representations of a pro-`p` group, with `p`
   invertible in the coefficients. It is not proved, here or (as of this
   module) anywhere in the Library. Every quasi-isomorphism in this module
   except `quasiIso_extendSystemComparison_tower_app` depends on the
   hypothesis `hS`. The transfer to `ℕ`-graded complexes of representations of
   `G`, restricted to `H`, is derived. So are the inflation and the
   comparisons of extensions.
2. The trivial action. Harris uses one `H` acting trivially on the cohomology
   for all `q` and `m`. He obtains it from the finiteness of the cohomology
   (Fact 1 bis and Lemma 2.2). Here the trivial action is the hypothesis
   `htriv`, at the single level `m` of the conclusion, on the cohomology
   `H^q` of the abstract complex of representations `K.toRepComplexes.obj m`.
   Harris's hypothesis concerns the compactly supported cohomology
   `H_c^q(U(ẽ)_F̄, ℤ/ℓ^mℤ)`, not the ordinary cohomology of the space. When
   `K` is the system of compact-section complexes `G_m^•(U(ẽ)_F̄)`, the
   cohomology of `K.toRepComplexes.obj m` is identified with
   `H_c^q(U(ẽ)_F̄, ℤ/ℓ^mℤ)` only through his isomorphism (2.3), which is not
   formalized. Nothing here identifies the abstract cohomology with a
   geometric one. The existence of such an `H` is not addressed.
3. The hypotheses on `H`. Harris's `H` is open, normal and pro-`p` in `S(ẽ)`.
   Here `H` is normal and pro-`p` (`IsProPSubgroup`), and of finite index for
   the comparison from `C_m^{•,H}`, as in the InvariantTotal module (Harris
   notes on p.305 that `S(ẽ)/H` is a finite group). Openness is not used.
   Harris's "`p` prime to `ℓ`", for the coefficients `ℤ/ℓ^mℤ`, is the
   hypothesis `hR` that `p` is a unit in `R`. The surjectivity on
   `H`-invariants is the explicit hypothesis `hK`, or follows from `hP` (see
   the ProPInvariants module).
4. The comparison. Harris states (2.6), the `S(ẽ)`-equivariant
   quasi-isomorphism `C_m^• → G_m^•(U(ẽ)_F̄)`, after the direct limit over `H`.
   He does not write the comparison at a fixed `H`. Reading
   `quotientInvariantsTotalSystemToRepExtend` as that comparison is our
   interpretation. It is the map `C_m^{•,H} → M_m^{•,H}` of the TotalExact
   module, inflated to `G` so that its source is a complex of representations of
   `G`, followed by the inclusion `M_m^{•,H} = G_m^{•,H} ↪ G_m^•`. A
   `ℤ/ℓ^mℤ[S(ẽ)/H]`-module is a representation of `S(ẽ)` through the quotient
   map, which is the inflation used here. The generic construction
   `extendSystemComparison` and its quasi-isomorphism theorem are derived.
5. Grading. Harris's complexes are bounded and start in degree `0`. The
   Library's systems `K` are `ℕ`-graded, and the total complexes are
   `ℤ`-graded. The comparison therefore targets `K` extended by zero to `ℤ`
   and needs `hN`, the vanishing of `K` in degrees `q ≥ N` (TotalComparison
   module).

## Scope

The module proves quasi-isomorphisms level by level, at a fixed `H`, under
the hypotheses `hS` (and `hP` in the pro-`p` corollaries), `hK`, `hN` and
`htriv`. It does not prove `ProPInvariantSubcomplexStatement` or
`ProPInvariantsExactStatement`, or construct a subgroup `H` acting trivially
on the cohomology. It does not compare the systems for different `H`
(`C_m^{•,H} = [C_m^{•,H'}]^H`) or take the direct limit over `H`. Nor does it
construct (2.6), (2.7) or Lemma 2.8, or prove any freeness or projectivity.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
