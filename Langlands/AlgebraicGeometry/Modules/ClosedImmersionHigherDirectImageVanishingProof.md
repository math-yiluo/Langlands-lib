# Higher direct images along a closed immersion vanish: proof

Author: Worker 727.

This module proves the published proposition
`Langlands.AlgebraicGeometry.Modules.ClosedImmersionHigherDirectImageVanishingStatement.{u}`
from `Langlands.AlgebraicGeometry.Modules.ClosedImmersionHigherDirectImageVanishingStatement`,
which it imports unchanged.

## Main result

`Langlands.AlgebraicGeometry.Modules.closedImmersionHigherDirectImageVanishing` is the theorem

```lean
theorem closedImmersionHigherDirectImageVanishing :
    ClosedImmersionHigherDirectImageVanishingStatement.{u}
```

for an arbitrary universe `u`. Unfolded, it says: for all schemes `X Y : Scheme.{u}`, every
morphism `i : X ⟶ Y` with `IsClosedImmersion i`, every `M : X.Modules` (not necessarily
quasi-coherent) and every `q : ℕ`,

```lean
IsZero ((DerivedSections.higherDirectImage i (q + 1)).obj M)
```

where `DerivedSections.higherDirectImage i m` is the Library's
`(Scheme.Modules.pushforward i).rightDerived m`. The theorem uses no hypothesis beyond the
statement's. Its axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Route of the proof

The Stacks proof (tag 02UV, via 01AX, 01AG and 015F) checks exactness of `i_*` on stalks.
The Lean proof avoids stalks. It checks exactness through local surjectivity of sections,
using that every open subset of `X` is the preimage of an open subset of `Y` when `i` is an
embedding. The steps are:

1. The forgetful functor `SheafOfModules.toSheaf` from sheaves of modules to sheaves of
   abelian groups preserves finite colimits. Hence it preserves epimorphisms.
2. For sheaves of abelian groups on a topological space, a morphism is an epimorphism if and
   only if it is locally surjective (Mathlib's `TopCat.Sheaf.isLocallySurjective_iff_epi`).
   With step 1 and faithfulness of `toSheaf`, a morphism `φ` of `𝒪_X`-modules is an
   epimorphism if and only if its underlying presheaf map `φ.mapPresheaf` is locally
   surjective.
3. Pushforward along a closed immersion preserves local surjectivity, so
   `Scheme.Modules.pushforward i` preserves epimorphisms.
4. `Scheme.Modules.pushforward i` is a right adjoint, so it preserves kernels. A functor
   between abelian categories that preserves epimorphisms and kernels preserves homology
   (Mathlib's `Functor.preservesHomology_of_preservesEpis_and_kernels`).
5. The Library's `DerivedSections.higherDirectImageIsoOfResolution i I (q + 1)` identifies
   `R^{q+1} i_* M` with the homology in degree `q + 1` of `i_*` applied to the chosen
   injective resolution `I` of `M`. The cocomplex of `I` is exact in degree `q + 1`
   (Mathlib's `InjectiveResolution.cocomplex_exactAt_succ`). A homology-preserving functor
   maps that exact short complex to an exact one (`ShortComplex.Exact.map`), so the homology
   is zero.

Steps 4 and 5 prove, for this functor, the case of Stacks 015F that is needed: an exact
functor sends an injective resolution to a complex that is exact in positive degrees.

## Auxiliary results

All helpers are in namespace
`Langlands.AlgebraicGeometry.Modules.ClosedImmersionHigherDirectImageVanishing`.

- `toSheaf_preservesColimit R F` (public lemma): for a site `(C, J)`, a sheaf of rings
  `R : Sheaf J RingCat.{u}` with `[HasSheafify J AddCommGrpCat.{v}]` and
  `[J.WEqualsLocallyBijective AddCommGrpCat.{v}]`, a shape `K` with
  `[HasColimitsOfShape K AddCommGrpCat.{v}]` and a diagram `F : K ⥤ SheafOfModules.{v} R`,
  the functor `SheafOfModules.toSheaf R` preserves the colimit of `F`. Proof: let `S` be
  sheafification of presheaves of modules. The counit of the sheafification adjunction is an
  isomorphism, so `F ≅ (F ⋙ forget) ⋙ S`, and it suffices to treat the latter diagram
  (`preservesColimit_of_iso_diagram`). The composite `S ⋙ toSheaf R` is, by definition,
  `PresheafOfModules.toPresheaf ⋙ presheafToSheaf J AddCommGrpCat`, and both factors
  preserve colimits of shape `K`. Take the colimit cocone of `F ⋙ forget` in presheaves of
  modules. Its image under `S` is a colimit because `S` is a left adjoint. Its image under
  `S ⋙ toSheaf R` is a colimit too, and `Functor.mapCoconeMapCocone` identifies that with
  the image under `toSheaf R` of the image under `S`. Then
  `preservesColimit_of_preserves_colimit_cocone` concludes.
- `toSheaf_preservesFiniteColimits R` (instance): `PreservesFiniteColimits (toSheaf R)`,
  from the previous lemma.
- `isLocallySurjective_of_epi φ` (public lemma): an epimorphism `φ : M ⟶ N` in
  `X.Modules` has locally surjective `φ.mapPresheaf`. Proof: `toSheaf` preserves the pushout
  of `span φ φ`, so it preserves the epimorphism `φ`
  (`preserves_epi_of_preservesColimit`). Then apply
  `TopCat.Sheaf.isLocallySurjective_iff_epi`.
- `epi_of_isLocallySurjective φ h` (public lemma): the converse. The map
  `toSheaf.map φ` is an epimorphism by `TopCat.Sheaf.isLocallySurjective_iff_epi`, and the
  faithful functor `toSheaf` reflects epimorphisms (`Functor.epi_of_epi_map`).
- `subsingleton_sections_of_eq_bot M hU` (public lemma): sections of `M : X.Modules` over an
  open `U = ⊥` form a subsingleton. By the sheaf condition the sections over the empty open
  are terminal (`TopCat.Sheaf.isTerminalOfEqEmpty`), hence a zero object of `AddCommGrpCat`,
  hence a subsingleton (`AddCommGrpCat.subsingleton_of_isZero`).
- `isLocallySurjective_pushforward i φ h` (public lemma): if `IsClosedImmersion i` and
  `φ.mapPresheaf` is locally surjective, then so is the presheaf map of
  `(Scheme.Modules.pushforward i).map φ`. Use Mathlib's
  `TopCat.Presheaf.isLocallySurjective_iff`. Take an open `W ⊆ Y`, a section `t` of `i_* N`
  over `W` (a section of `N` over `i ⁻¹ᵁ W`) and a point `y ∈ W`. There are two cases.
  - If `y = i x`, local surjectivity of `φ` gives an open `V ≤ i ⁻¹ᵁ W` with `x ∈ V` and a
    section `s` over `V` with `φ(s) = t|_V`. Since `i` is an embedding, `V = i⁻¹(W₀)` for an
    open `W₀ ⊆ Y` (`isInducing.isOpen_iff`). Then `W ⊓ W₀` contains `y`, and its preimage is
    exactly `V`, so `s` is a lift of `t` on it.
  - If `y ∉ range i`, take `W' = W ⊓ (Y \ range i)`. It is open because the range of a
    closed immersion is closed. It contains `y`, and `i ⁻¹ᵁ W' = ⊥`. Sections over the empty
    open form a subsingleton, so `0` lifts the restriction of `t` to `W'`.
- `pushforward_preservesEpimorphisms i` (public lemma): for `IsClosedImmersion i`,
  `(Scheme.Modules.pushforward i).PreservesEpimorphisms`. Combine the three previous
  lemmas.

Only the closed-embedding part of `IsClosedImmersion` is used (`i.isClosedEmbedding`). The
surjectivity of `i^#` on stalks is not needed.

## Original source

The Stacks Project at git commit `a04446e57ec1fbc252a871afcec7752fb2807b14`, from the
registered sources `stacks-closed-immersion-exactness-a04446e5` (folder SHA-256
`a35bfda718ee774de875160239072d121d9d0acd5c43fbc792f2b03a77f64691`; `modules.tex`,
`derived.tex`) and `stacks-flasque-affine-vanishing-kunneth-a04446e5` (folder SHA-256
`af02e6f0aff875e216f1e0fde58f6baad3eedeb6b82799a8d6c91ff68cccaa3a`; `cohomology.tex`):

- Lemma 02UV (`lemma-cohomology-and-closed-immersions`, `cohomology.tex` lines 3446-3459):
  its proof shows `R^p i_* = 0` from exactness of `i_*`.
- Lemma 01AX (`lemma-i-star-exact`, `modules.tex` line 557): `i_*` is exact for a closed
  embedding. The Lean proof shows the same exactness for modules by the local-surjectivity
  route above instead of the stalk formula 00AE and Lemma 01AG.
- Lemma 015F (`lemma-right-derived-exact-functor`, `derived.tex` line 5884): an exact
  functor has vanishing higher right-derived functors. The Lean proof uses only the
  injective-resolution computation of step 5.

The statement's Markdown records the errata check for these sources. No comment changes a
statement used here.
