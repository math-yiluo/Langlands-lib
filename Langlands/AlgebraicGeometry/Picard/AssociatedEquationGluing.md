# Line bundles from locally associated local equations

This module proves the helper theorem
`Langlands.AlgebraicGeometry.Picard.exists_lineBundle_of_associated_equations`. It is
internal infrastructure for the proof of
`Langlands.AlgebraicGeometry.Picard.PrimeGermDivisorSectionStatement`. It is the gluing
step of the standard passage from local equations to the invertible sheaf `𝒪_X(D)` of an
effective Cartier divisor, with its canonical section (Stacks Project, Tag 01WX and
Tags 0AGA, 0BE8, 0BE9).

## Statement proved

Let `X` be an integral scheme, `T : ι → X.Opens` an open cover (`⨆ i, T i = ⊤`) and
`a i : Γ(X, T i)` local equations such that

- `hreg`: the germ of `a i` at every point of `T i` is nonzero, and
- `hassoc`: at every point `x ∈ T i ⊓ T j`, the germs of `a i` and `a j` are associated
  (they differ by a unit of the stalk).

Then there are a line bundle `L` on `X` and a global section `s` of `L.obj` such that

- for every `i`, `T i ⊓ trivializationOpen L.obj s = X.basicOpen (a i)`, and
- for every `i` and every morphism `f : Y ⟶ X` with `f⁻¹(T i) = Y`
  (hypothesis `hf : ⊤ ≤ f ⁻¹ᵁ T i`), `VanishesAlong L f s` holds exactly when the
  pulled-back function `f.appLE (T i) ⊤ hf (a i)` is zero.

The universe of the index type `ι` is the universe of `X`.

## Helper lemmas (namespace `AssociatedGluing`)

- `eq_of_germ_eq`: two sections over `V` with equal germs at every point of `V` are equal
  (`TopCat.Presheaf.section_ext`).
- `exists_unit_ratio`: on an integral scheme, if `c : Γ(X, V)` has nonzero germs on `V`
  and the germs of `b` and `c` are associated at every point of `V`, then `b = u * c` for
  a unit `u` of `Γ(X, V)`. Proof:
  1. (`hloc`) At each `x ∈ V`, write the stalk unit relating the germs as the germ of a
     section `p` on a neighbourhood (`TopCat.Presheaf.exists_le_germ_eq`); equal germs
     give a smaller neighbourhood `W x ≤ V` on which `b = p x * c`
     (`TopCat.Presheaf.germ_eq`).
  2. (`hcompat`) The local ratios `p x` agree on overlaps: on `W x ⊓ W y` both
     `p x * c` and `p y * c` restrict `b`, and the germs of `c` are nonzero in the stalks,
     which are domains because `X` is integral, so the germs of `p x` and `p y` agree
     (`mul_right_cancel₀`), hence the restrictions agree (`eq_of_germ_eq`).
  3. The sheaf condition (`TopCat.Sheaf.existsUnique_gluing'`) glues the `p x` to
     `v : Γ(X, V)`, and `b = v * c` because the germs agree everywhere (`hbvc`).
  4. `v` is a unit: at each point, `germ b = germ v * germ c` and `germ b * w = germ c`
     for a stalk unit `w`, so cancelling the nonzero `germ c` gives
     `germ v * w = 1`; hence every germ of `v` is a unit and `v` is a unit
     (`RingedSpace.isUnit_of_isUnit_germ`).

## Proof of the main theorem

1. (`hex`) For each pair `i, j`, `exists_unit_ratio` on `T i ⊓ T j`, applied to the
   restrictions of `a i` and `a j`, gives a unit `u i j` with
   `a i|_{T i ⊓ T j} = u i j * a j|_{T i ⊓ T j}`. Let `g i j` be the corresponding unit
   of `Γ(X, T i ⊓ T j)`.
2. (`hgerm`) Taking germs, `germ (a i) = germ (u i j) * germ (a j)` at every point of
   `T i ⊓ T j`.
3. (`hg`) The family `g` is a cocycle in the sense of
   `Langlands.AlgebraicGeometry.Picard.CocycleGluing.IsCocycle`: on a triple overlap,
   the germs of `g i j * g j k` and `g i k` both send the nonzero germ of `a k` to the
   germ of `a i`, so they are equal by cancellation in the domain stalk, and
   `eq_of_germ_eq` gives the identity of sections.
4. (`ha`) By construction `a` is a compatible family for `g`
   (`CocycleGluing.IsCompatibleFamily`).
5. The line bundle is the glued module `CocycleGluing.glued g`, locally free of rank one
   by `CocycleGluing.isLocallyFreeRankOne_glued`, and the section is
   `CocycleGluing.globalSec g ha`. The first conclusion is
   `CocycleGluing.inf_trivializationOpen_globalSec`.
6. For the vanishing criterion, apply the frame vanishing criterion
   `Langlands.SchemeModule.frameVanishingCriterion` with the open `T i`, the frame
   `CocycleGluing.genSec g hg i le_rfl` and the coefficient `a i`:
   - the frame condition on each `W ≤ T i` follows from
     `CocycleGluing.map_genSec` (the restriction of the generator is the generator on
     `W`) and `CocycleGluing.smul_genSec_bijective`;
   - the identity `s|_{T i} = a i • genSec` is `CocycleGluing.map_globalSec` combined
     with `CocycleGluing.res_self`.

## Dependencies

- `Langlands.AlgebraicGeometry.Modules.FrameVanishingCriterionProof` (the frame
  vanishing criterion).
- `Langlands.AlgebraicGeometry.Picard.CocycleLineBundleProof` (the `CocycleGluing`
  construction and its lemmas).
- `Langlands.AlgebraicGeometry.Picard.PointTangentSeparation` (for `LineBundle`,
  `trivializationOpen` and `VanishesAlong`).
