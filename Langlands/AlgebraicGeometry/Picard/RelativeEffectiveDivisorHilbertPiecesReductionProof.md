# Proof: reduction of relative effective divisors to the Hilbert scheme and the Cartier locus

This module proves the proposition
`Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesReductionStatement`
(module of the same name).

The main theorem is

```lean
theorem Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesReduction.relativeEffectiveDivisorHilbertPiecesReduction :
    RelativeEffectiveDivisorHilbertPiecesReductionStatement.{u}
```

Its type is the target proposition exactly, for an arbitrary universe `u`. The
proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## What is proved

The implication HGP ⟹ (CLO ⟹ (a)), where

- HGP is `Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyStatement`:
  the Hilbert scheme `πH : H ⟶ Spec A` of a flat, locally finitely presented
  `f : X ⟶ Spec A` with `ClosedImmersionBySections 𝓛X f`, with its universal
  ideal `W` on `X ×_A H`, classifying flat locally finitely presented closed
  subschemes on all tests, and with H-projective pieces `U θ`;
- CLO is `Langlands.AlgebraicGeometry.Picard.RelativeEffectiveCartierLocusStatement`:
  for a proper flat `q : Y ⟶ B` over a locally noetherian `B` and an ideal `Z`
  on `Y` with `B`-flat closed subscheme, there is an open `U ⊆ B` such that
  `Z.comap gY` is relative effective Cartier for `qT` exactly when `g` lands in
  `U`, for every pullback square `IsPullback gY qT q g`;
- (a) is `Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesStatement`:
  over a noetherian `A`, relative effective divisors of `f` are represented by
  a separated, locally finitely presented `d : D ⟶ Spec A` with universal
  divisor, and `D` has H-quasi-projective pieces with the same
  Hilbert-function characterization.

## Source

The argument follows the proof of Theorem 3.7 of S. L. Kleiman, *The Picard
scheme* (`kleiman-2005-picard-scheme-arxiv-math0504020v1`, p.24) and the remark
on quasi-projectivity in the proof of Theorem 4.8 (p.30). The construction
of the open locus and the fibre argument are packaged in CLO, so only the
assembly is formalized here.

## Helper lemmas

All declarations are in the namespace
`Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesReduction`.

### Section `Cartier`: effective Cartier divisors are locally of finite presentation

Let `I : X.IdealSheafData` be an effective Cartier ideal
(`IsEffectiveCartierIdeal I`, Library `Picard.RelativeEffectiveDivisor`): the
kernel module of `I.subschemeι` is locally isomorphic to the structure sheaf.

- `hasFiniteAffineSections_kernelModule`: the kernel module has finitely
  generated sections over every affine open. It is quasi-coherent
  (`StructureKernelModule.kernelModule_isQuasicoherent`). Near every point it
  is isomorphic to the structure sheaf of an open `O`, whose sections over
  affines of `O` are finite (rank one). The Library lemmas
  `HasLocallyFiniteSections.of_locally_finiteAffineSections` and
  `HasLocallyFiniteSections.finiteAffineSections` (module
  `Modules.CoherentLineBundle`) turn this local finiteness of a
  quasi-coherent module into finiteness over every affine open.
- `ideal_fg`: the ideal `I.ideal U` is finitely generated over every affine
  open `U`. Its sections are the kernel of `I.subschemeι.app U`
  (`IdealSheafData.ker_subschemeι_app`), which are the sections of the kernel
  module.
- `locallyOfFinitePresentation_subschemeι`: if all `I.ideal U` over affine
  `U` are finitely generated, then `I.subschemeι` is locally of finite
  presentation. It is checked on Mathlib's affine open cover
  `I.subschemeCover` of the closed subscheme, since the property is local at
  the source. The instance `IsZariskiLocalAtSource` is supplied explicitly
  because instance search does not find it. On the piece over `U` the
  composite is `Spec (Γ(X, U) ⧸ I(U)) ⟶ Spec Γ(X, U) ≅ U ⟶ X`
  (`subschemeCover_map_subschemeι`, `glueDataObjι`). The first map is of
  finite presentation because the quotient by a finitely generated ideal is
  finitely presented (`RingHom.FinitePresentation.of_surjective`). The other
  two are an isomorphism and an open immersion.
- `locallyOfFinitePresentation_of_isEffectiveCartierIdeal`: the two lemmas
  combined.

### Section `Families`: base change maps of the family

- `mapX f h w`: for `h : T' ⟶ T` with `h ≫ s = s'`, the map
  `X ×_{f,s'} T' ⟶ X ×_{f,s} T` given by `pullback.map` with `𝟙 X`, `h`. It
  is the map used in the three statements (with `T = H` or `T = U` and
  `h = g`).
- `mapX_fst`, `mapX_snd`: its two projections.
- `isPullback_mapX`: the square of `mapX f h w`, the two second projections
  and `h` is a pullback square. This follows from the pasting lemma
  `IsPullback.of_right` and the chosen pullback squares.
- `mapX_comp`, `mapX_id`, `mapX_congr`: functoriality of `mapX`, and
  independence of the proof of `h ≫ s = s'`.

### Two topological lemmas

- `disjoint_preimage`: preimages of disjoint opens are disjoint.
- `range_comp_ι_subset`: for `g : T ⟶ U` into an open subscheme, the range
  of `g ≫ U.ι` lies in `U` (`Scheme.Opens.range_ι`).

## Main theorem

`relativeEffectiveDivisorHilbertPiecesReduction` takes HGP as `hHGP`, CLO as
`hCLO`, and the data `A`, `X`, `f`, `𝓛X` and hypotheses of (a).

1. **`f` is proper and locally of finite presentation.** The hypothesis
   `ClosedImmersionBySections 𝓛X f` gives a morphism `𝔓` to projective space
   `ProjSpace A N` whose composite with the structure map is `f`
   (`𝔓.toProj_π`) and which is a closed immersion. Projective space is proper
   over `Spec A` (Library `projectiveSpaceToSpec_isProper`), so `f` is
   proper, hence locally of finite type. Over the noetherian `Spec A`, `f` is
   then locally of finite presentation (instance search, through Mathlib's
   comparison for locally noetherian targets).
2. **The Hilbert scheme.** `hHGP` gives `H`, `πH`, the ideal `W` on
   `X ×_A H`, `πH` locally of finite presentation and separated, the
   classification `hrep`, and the pieces `UH θ`. `H` is locally noetherian
   (`LocallyOfFiniteType.isLocallyNoetherian πH`).
3. **The universal subscheme is flat.** Applying the first part of `hrep` to
   `T = H`, `g = 𝟙 H` and rewriting with `mapX_id` and
   `IdealSheafData.comap_id` shows that the closed subscheme of `W` is flat
   over `H`.
4. **The Cartier locus.** `hCLO` applied to `q := pullback.snd f πH` (proper
   and flat, base change of `f`) and `W` gives `U : H.Opens` and the
   equivalence `hU`. Put `d := U.ι ≫ πH` and
   `W_D := W.comap (mapX f U.ι rfl)`. By `hU` on the square
   `isPullback_mapX f U.ι rfl` and `Set.range U.ι.base = U`, `W_D` is a
   relative effective Cartier ideal for `pullback.snd f d`; this is the
   divisor `⟨_, hWD⟩`. The morphism `d` is separated and locally of finite
   presentation by instance search (open immersion followed by `πH`).
5. **Pulled-back divisors.** `hcomap` records that for `g : T ⟶ U`, pulling
   back `W_D` along `mapX f g hg` is pulling back `W` along
   `mapX f (g ≫ U.ι) _` (`IdealSheafData.comap_comp` and `mapX_comp`). With
   `hU` on `isPullback_mapX f (g ≫ U.ι) _` and `range_comp_ι_subset`, every
   pullback of `W_D` is relative effective Cartier.
6. **Classification.** Let `I` be a relative effective Cartier ideal on
   `X ×_A T` over `T`. By the section `Cartier`, `I.subschemeι` is locally of
   finite presentation. Composed with the base change `pullback.snd f s` of
   `f`, the closed subscheme is locally of finite presentation over `T`, and
   it is flat by assumption. The second part of `hrep` gives a unique
   `g : T ⟶ H` over `Spec A` with `W.comap (mapX f g hg) = I`. By `hU`
   (direction ⟹) on `isPullback_mapX f g hg`, `g` lands in `U`. So
   `g' := IsOpenImmersion.lift U.ι g _` satisfies `g' ≫ U.ι = g` and
   `g' ≫ d = s`, and `hcomap` with `mapX_congr` shows that `g'` classifies
   `I`. Uniqueness: if `g''` classifies `I`, then by `hcomap` so does
   `g'' ≫ U.ι`, so `g'' ≫ U.ι = g = g' ≫ U.ι` by uniqueness in `hrep`, and
   `g'' = g'` because `U.ι` is a monomorphism.
7. **Pieces.** The pieces of `D = U` are `U.ι ⁻¹ᵁ UH θ`. They are pairwise
   disjoint by `disjoint_preimage`, and their supremum is `⊤` because
   preimage commutes with suprema (`Scheme.Hom.preimage_iSup`) and the
   `UH θ` cover `H`.
   - *H-quasi-projectivity.* `(hUH θ).1` gives a closed immersion
     `c : UH θ ⟶ ProjSpace A n` over `Spec A`. The composite
     `U.ι⁻¹(UH θ) ⟶ U ⟶ H` lands in `UH θ`, so it lifts to
     `j : U.ι⁻¹(UH θ) ⟶ UH θ` (`IsOpenImmersion.lift`), and `j` is an open
     immersion (`IsOpenImmersion.of_comp`). `UH θ` is proper over `Spec A`
     (`IsHProjective.isProper`), hence quasi-compact. Since it is also
     locally noetherian (as an open of `H`), it is a noetherian scheme. Its
     open subspace `U.ι⁻¹(UH θ)` is then a noetherian space
     (`Topology.IsInducing.noetherianSpace`). This gives quasi-compactness
     of `j ≫ c`, which is an immersion (open immersion followed by a closed
     immersion). The composite with the structure map of projective space is
     `(U.ι⁻¹(UH θ)).ι ≫ d`, so the piece is H-quasi-projective.
   - *Hilbert-function characterization.* For an affine point
     `g : Spec B ⟶ U` over `s` classifying `I`, the composite `g ≫ U.ι`
     classifies `I` for `W` (by `hcomap`). So the characterization of
     `(hUH θ).2` applies to `g ≫ U.ι`. It remains to show that
     `Set.range g.base ⊆ U.ι⁻¹(UH θ)` is equivalent to
     `Set.range (g ≫ U.ι).base ⊆ UH θ`. Both directions are checked
     pointwise with `Scheme.Hom.comp_apply`.

## Dependencies

The module imports the statement module
`Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesReductionStatement`
(which imports HGP, CLO and (a)), `Langlands.AlgebraicGeometry.Modules.CoherentLineBundle`
(for `HasLocallyFiniteSections` and `HasFiniteAffineSections`),
`Langlands.AlgebraicGeometry.ProjectiveSpace.Structure` (for
`projectiveSpaceToSpec_isProper`) and
`Langlands.AlgebraicGeometry.ProjectiveSpace.BaseChange` (for
`IsHProjective.isProper`). It adds no axioms and no new definitions other than
the abbreviation `mapX` and the lemmas listed above.
