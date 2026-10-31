# Global sections of Harris's étale coefficient sheaves over split torsors

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DivisibleSystem` (`DivisibleSystem` with `tower`,
`projection` and `epi_projection`),
`Langlands.Cohomology.DivisibleSystem.LeftExact` (`mapLeftExact`),
`Langlands.Cohomology.DivisibleSystem.HarrisEtale` (`EquivariantStructure`
with `diagram` and `etaleSystem`, `harrisEquivariantStructure`,
`harrisEtaleDivisibleSystem`, `harrisEtaleSectionsDivisibleSystem`), and
Worker 13's `Langlands.Shimura.Coefficients.VaryingCoverLocalTrivialization`
(`etaleAssociatedTrivializationAlong`, whose forward map is
`etaleAssociatedEvaluationAlong`, and
`etaleAssociatedTransition_evaluationAlong`). Through their imports it uses
Worker 13's `etaleAssociatedTransition`
(`Langlands.Shimura.Coefficients.VaryingCoverInverse`),
`harrisEtaleSectionsSystem`
(`Langlands.Shimura.Coefficients.HarrisEtaleCoefficients`) and
`ModuleSheaf`, `sections` and `sectionsIso`
(`Langlands.Geometry.EtaleDerivedSections`), and Worker 57's
`IsFiniteGeometricTorsor` (`Langlands.Shimura.Coefficients.Etale`) and
`harrisCongruenceGroups`. From Mathlib it uses `constantSheaf`,
`presheafToSheaf`, `sheafCompose`, `sheafComposeNatIso`,
`GrothendieckTopology.PreservesSheafification`,
`GrothendieckTopology.W_iff_isLocallyBijective`, `GrothendieckTopology.W.isLocallyInjective`,
`GrothendieckTopology.W.isLocallySurjective`,
`Presheaf.isLocallyInjective_forget`,
`Presheaf.isLocallySurjective_iff_whisker_forget`, the instance
`Scheme.smallEtaleTopology.WEqualsLocallyBijective` (from
`Mathlib.AlgebraicGeometry.Sites.AffineEtale`), `Function.surjInv`,
`ModuleCat.epi_iff_surjective`, `epi_comp_iff_of_isIso` and
`NatIso.naturality_1`.

## Conventions

As in the published `HarrisEtale`, an `ℓ`-divisible system `T` in an abelian
category is an inverse system `T.tower : ℕᵒᵖ ⥤ C` with objects `T m`, maps
`j : T m ⟶ T m'` for `m' ≤ m` (`T.projection`, epimorphisms by the published
`epi_projection`) and maps `i`, satisfying Harris's (2.1) and the published
torsion and flatness axioms. For an additive functor `F` preserving finite
limits, the published `T.mapLeftExact F hF` is the `ℓ`-divisible system with
tower `T.tower ⋙ F`, given the hypothesis `hF` that every `F.map j` is an
epimorphism.

`X : Scheme.{u}`, `R : Type u` is a commutative ring, and `X.Etale` is the
small étale site of `X`; its terminal object `⊤_ X.Etale` is `X` itself.
`ModuleSheaf X R` is the category of sheaves of `R`-modules on it, and
`sections X R : ModuleSheaf X R ⥤ ModuleCat R` is global sections
(`Γ(X, -)`, Mathlib's `Sheaf.Γ`), additive and preserving finite limits.
`sectionsIso` identifies it with evaluation at `⊤_ X.Etale`.

For `D : I ⥤ GrpCat.{u}` and `Y : EquivariantDiagram D X.Etale` with
`hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i)`, and an equivariant
coefficient diagram `M : EquivariantDiagram D (ModuleCat R)`, write
`F_i = Assoc_{Y i}(M i)` for the sheaf associated to the representation
`M i` of `D i` and the torsor `Y i`, and
`τ_f = (etaleAssociatedTransition X Y hY f).app M : F_i ⟶ F_j` for
`f : i ⟶ j` (the maps of the published `etaleAssociatedVaryingSystem`).
A global section of `Y i` is a morphism `s : ⊤_ X.Etale ⟶ Y i` of the étale
site, that is, a section of the structure morphism `Y i ⟶ X`.

## Constant sheaves of surjections

`C` is a category with a Grothendieck topology `J`, and `R : Type w` is a
ring. For a linear map `π : M ⟶ M'` let `c = (Functor.const Cᵒᵖ).map π` be
the map of constant presheaves.

- `constantForgetSection π hπ`: for surjective `π`, the map of constant
  presheaves of sets `M' ⟶ M` given at every object by `Function.surjInv hπ`.
  `constantForgetSection_comp`: it is a section of the map of underlying sets
  of `c`.
- `iso_conj_section_comp`: if `s ≫ p = 𝟙` and `X ≅ X'`, `Y ≅ Y'`, the maps
  conjugated by these isomorphisms again compose to the identity.
- `surjective_constantSheaf_map_app π hπ U`: assume that `J` has weak
  sheafification for `ModuleCat R` and for types, that the forgetful functor
  `forget : ModuleCat R ⥤ Type w` preserves sheaves (`HasSheafCompose`) and
  sheafification (`PreservesSheafification`). Then for surjective `π`, the
  map of sections over `U` of `constantSheaf J (ModuleCat R)` applied to `π`
  is surjective.

  Proof. Sheafifying `constantForgetSection` gives a section `s` of the
  sheafification of `c ⋙ forget` in sheaves of sets. Mathlib's
  `sheafComposeNatIso` identifies the sheafification of a presheaf of modules
  followed by `forget` with the sheafification of its underlying presheaf of
  sets, naturally; its naturality square at `c` (`NatIso.naturality_1`)
  writes `forget` applied to the constant-sheaf map of `π` as the
  sheafification of `c ⋙ forget` conjugated by this isomorphism. By
  `iso_conj_section_comp`, the conjugate of `s` is a section of it. A map of
  sheaves of sets with a section is surjective on sections over `U`.

## The small étale site

- `smallEtaleTopology_preservesSheafification X R`: an instance that the
  forgetful functor `ModuleCat R ⥤ Type u` preserves sheafification on the
  small étale site. Mathlib proves that on this site the morphisms of
  presheaves inverted by sheafification are exactly the locally bijective
  ones, for modules and for sets
  (`Scheme.smallEtaleTopology.WEqualsLocallyBijective`). A map of presheaves
  of modules in `J.W` is therefore locally injective and locally surjective;
  its underlying map of presheaves of sets is then locally injective
  (`Presheaf.isLocallyInjective_forget`) and locally surjective
  (`Presheaf.isLocallySurjective_iff_whisker_forget`), hence lies in `J.W`
  for sets (`W_iff_isLocallyBijective`).
- `epi_sections_map_of_surjective X R φ hφ`: a morphism `φ` of étale sheaves
  of modules whose map of sections over `⊤_ X.Etale` is surjective has an
  epimorphism `Γ(X, φ)`, by the naturality of `sectionsIso`.
- `epi_sections_constantSheaf_map X R π hπ`: for surjective `π`, the global
  sections of the constant étale sheaf map of `π` form an epimorphism.
- `surjective_etaleAssociatedTransition_app_top Y hY M f s hf`: let
  `f : i ⟶ j`, let `s : ⊤_ X.Etale ⟶ Y i` be a global section, and assume
  that `M.obj.map f : M i ⟶ M j` is surjective. Then the map of sections
  over `⊤_ X.Etale` of `τ_f : F_i ⟶ F_j` is surjective.

  Proof. Worker 13's `etaleAssociatedTrivializationAlong` restricts `F_i` to
  the slice site over a given `Z` and, for a map `a : Z ⟶ Y i`, identifies it
  with the restricted constant sheaf of `M i`; invertibility is proved there
  from `hY i`. Take `Z = ⊤_ X.Etale` and evaluate at the object `𝟙 Z` of the
  slice site: along `s` this gives an isomorphism
  `e_i : F_i(X) ≅ (constant M i)(X)`, and along `s ≫ Y.map f` an isomorphism
  `e_j : F_j(X) ≅ (constant M j)(X)`. Worker 13's
  `etaleAssociatedTransition_evaluationAlong` gives
  `τ_f(X) ≫ e_j = e_i ≫ (constant (M.obj.map f))(X)`. The right side is
  surjective by `surjective_constantSheaf_map_app`, so `τ_f(X)` is
  surjective.

## Split torsors and the `ℓ`-divisible system of sections

`D : ℕᵒᵖ ⥤ GrpCat.{u}`, `Y : EquivariantDiagram D X.Etale` with `hY`, `T` an
`ℓ`-divisible system of `R`-modules and `A : T.EquivariantStructure D`
(published), so that `A.etaleSystem X Y hY` is the published `ℓ`-divisible
system of the sheaves `Assoc_{Y m}(T m)`. The hypothesis
`hs : ∀ n : ℕ, Nonempty (⊤_ X.Etale ⟶ Y.obj.obj (op n))` says that every
torsor `Y n` has a global section.

- `A.epi_sections_etaleSystem_projection Y hY hs h`: for `m' ≤ m`, the global
  sections of the map `j` of `A.etaleSystem X Y hY` form an epimorphism.
  Choose a section of `Y m` by `hs m` and apply
  `surjective_etaleAssociatedTransition_app_top` to `f = (homOfLE h).op`,
  whose coefficient map is the epimorphism `T.projection h`, then
  `epi_sections_map_of_surjective`. Only the section at the larger index `m`
  is used.
- `A.etaleSplitSectionsSystem Y hY hs`: the published
  `(A.etaleSystem X Y hY).mapLeftExact (sections X R)` with this hypothesis,
  an `ℓ`-divisible system of `R`-modules.
  `A.etaleSplitSectionsSystem_tower Y hY hs`: its tower is, by definition
  (`rfl`), `etaleAssociatedVaryingSystem X Y hY A.diagram ⋙ sections X R`,
  the global sections of the published inverse system of the sheaves `F_m`.

## Harris's case

The variables are those of the published `HarrisEtale`: `ℓ` a nonzero
natural number, `ρ` an algebraic representation, `p` a finite place of `ℚ`,
`U` a compact open level, `R = HarrisCoefficientIntegers L p`, `X` a scheme,
`Y : EquivariantDiagram (harrisCongruenceGroups ρ p U ℓ) X.Etale` with `hY`,
and in addition `hs` as above.

- `epi_sections_harrisEtaleDivisibleSystem_projection ℓ ρ p U X Y hY hs h`:
  the hypothesis `hΓ` of the published `harrisEtaleSectionsDivisibleSystem`
  holds: the global sections of every map `j` of
  `harrisEtaleDivisibleSystem ℓ ρ p U X Y hY` are epimorphisms. It is the
  general lemma for `harrisEquivariantStructure ℓ ρ p U`.
- `harrisEtaleSplitSectionsDivisibleSystem ℓ ρ p U X Y hY hs`: the published
  `harrisEtaleSectionsDivisibleSystem ℓ ρ p U X Y hY hΓ` with `hΓ` proved by
  the previous lemma. `harrisEtaleSplitSectionsDivisibleSystem_tower`: its
  tower is, by definition, the published
  `harrisEtaleSectionsSystem ρ p U ℓ X Y hY`, the global sections
  `Γ(X, 𝓛̃_m)` of the published model of Harris's sheaves.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §4, printed p.311 (one-based PDF page 13),
quoted in the published `HarrisEtale`: "let `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m` for any `m`.
Then `𝓛_m` forms an inverse system of `𝒪`-modules, and the inverse system
`{𝓛̃_m}` defines a lisse `ℓ`-adic sheaf `W̃ = lim 𝓛̃_m ⊗_𝒪 L_ℓ` on
`S̄_{K(N)}`." The published `harrisEtaleDivisibleSystem` models `{𝓛̃_m}` as
an `ℓ`-divisible system of étale sheaves (the published `HarrisEtale`
explains the reading), and the published `harrisEtaleSectionsDivisibleSystem`
needs the hypothesis `hΓ` because `Γ(X, -)` is only left exact.

Harris makes no splitness assumption on his covers of level `K(N, m)`, and
he does not state the surjectivity `hΓ`. The split case, the statements and
all proofs are ours; the module is derived from the published modules named
above and Mathlib. Worker 13 (first executor of task 23471a9e) approved this
scope as a proved special case of `hΓ`.

`hs` is a genuine restriction: finite geometric torsors alone do not force
`hΓ`. Worker 13 pointed out the elementary obstruction: for `C₂` acting by
negation on `ℤ / 4 ⟶ ℤ / 2`, the fixed elements `{0, 2}` of `ℤ / 4` both
reduce to `0`, while `C₂` acts trivially on `ℤ / 2`. A geometric realization
(a remark, not formalized): `X = Spec ℝ`, the constant system of groups `C₂`
acting on `Y = Spec ℂ` by complex conjugation, `ℓ = 2` and `T m = ℤ / 2 ^ m`
with the generator acting by `-1`. Since `Spec ℂ` is connected, the global
sections of `Assoc_Y(T m)` are the invariants of `T m`, and the map from
level 2 to level 1 is the non-surjective map above. Here `Y` has no global
section.

## Scope

The module proves `hΓ` only under `hs`. It does not prove `hΓ` for non-split
torsors, does not identify `X`, `Y` or `hY` with Harris's Shimura varieties
and covers (they are inputs, as in the published `HarrisEtaleCoefficients`),
and does not show that the sheaves `F_i` are constant or compute their global
sections beyond the surjectivity above. It does not construct the lisse
`ℓ`-adic sheaf `W̃`, higher or compactly supported cohomology, spectral
sequences or Mittag-Leffler arguments. `ℓ` and `p` are unrelated inputs, as
in the published `HarrisEtale`.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
