# Lifting primitive line bundles from obstruction naturality and ideal-H² injectivity

This module reduces the published proposition
`Langlands.AbelianScheme.ArtinianPrimitiveLineBundleLiftingStatement.{u}` to two Library
statements that had no published proof when it was written. It does **not** prove the
target outright. It imports the shared proposition and entry theorem from
[ArtinianPrimitiveLineBundleLiftingFromPrerequisites](ArtinianPrimitiveLineBundleLiftingFromPrerequisites.md):

```lean
def Langlands.AbelianScheme.ArtinianPrimitiveLineBundleLiftingReductionStatement : Prop :=
  Langlands.AlgebraicGeometry.Picard.SquareZeroObstructionMorphismNaturalityStatement.{u} →
    ArtinianH2PrimitiveInjectivityStatement.{u} →
      ArtinianPrimitiveLineBundleLiftingStatement.{u}

theorem Langlands.AbelianScheme.artinianPrimitiveLineBundleLiftingReduction :
    ArtinianPrimitiveLineBundleLiftingReductionStatement.{u}
```

This module retains the explicit-premise proof

```lean
theorem Langlands.AbelianScheme.ArtinianPrimitiveLineBundleLiftingReduction.artinianPrimitiveLineBundleLifting_of
    (naturality : SquareZeroObstructionMorphismNaturalityStatement.{u})
    (injectivity : ArtinianH2PrimitiveInjectivityStatement.{u}) :
    ArtinianPrimitiveLineBundleLiftingStatement.{u}
```

Its two hypotheses are the same premises as those of the shared implication.
The shared named entry has a separate proof in the imported module; there is
one definition of the reduction proposition. All three propositions in the
implication are published Library statements, imported unchanged:

- `Langlands.AlgebraicGeometry.Picard.SquareZeroObstructionMorphismNaturalityStatement`
  (module `…Picard.SquareZeroObstructionMorphismNaturalityStatement`): the square-zero
  Picard obstruction `SquareZeroPicardObstruction.obstructionMap` is natural under an
  arbitrary commutative square of square-zero closed immersions `i' ≫ f.left = g ≫ i`
  over a base `Spec R`, once absolute ideal cohomology is identified with relative
  cohomology (`relativeIdealCohomologyAddEquiv`) and the kernel ideals are related by a
  morphism `k` compatible with the structure maps;
- `Langlands.AbelianScheme.ArtinianH2PrimitiveInjectivityStatement` (module
  `…Picard.ArtinianH2PrimitiveInjectivityStatement`): for an abelian scheme `A` over a
  local Artinian ring `B'` and an elementary thickening `φ : B' → B`, the reduced coproduct
  `μ^* − p₁^* − p₂^*`, built from `relativeCohomologyPullback` and the coefficient maps
  `k`, is injective on the relative H² of the ideal of `A ×_{B'} Spec B ⟶ A`;
- the target `Langlands.AbelianScheme.ArtinianPrimitiveLineBundleLiftingStatement`.

Once proofs of the first two are published, applying
`artinianPrimitiveLineBundleLifting_of` to them proves the target exactly, with no further
hypothesis. The module uses no `sorry` and adds no axiom. It does not use
`PicardZeroArtinianLiftingStatement`, `FiniteTypeDualSchemeGeometryStatement`,
`RelativeDualSchemeGeometryStatement`, `FiniteTypeSmoothFamilyAbelianRepresentabilityStatement`,
`SmoothFamilyAbelianRepresentabilityStatement` or anything proved from them.

The approved Lean service compiled the module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` with zero errors and zero warnings. Inspection of
`ArtinianPrimitiveLineBundleLiftingReductionStatement` reported
`statement_returns_prop: true`, the sole universe parameter `u`, and only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

The file sets `backward.isDefEq.respectTransparency false` and
`backward.isDefEq.respectTransparency.types false` for the whole module. They let the
elaborator unfold the `let`-bound data of the two imported statements and the
`Over.pullback` instances when it matches them with the local terms. They change
no statement.

## Source and provenance

The route is the proof of Proposition 6.7 of Mumford–Fogarty–Kirwan, *Geometric Invariant
Theory*, 3rd edition, Chapter 6, printed pp. 117–118 (PDF pp. 130–131 of the registered
file `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`).
There, `L₀` on `X × Spec(A/I)` with `m·I = 0` has a lifting obstruction in
`H²(X_k, 𝒪) ⊗ I`. The bundle `q(L₀)` for `q = μ^* − p₁^* − p₂^*` lifts trivially, so
its obstruction is zero. The two obstructions "are related by the homomorphism"
`H²(X, 𝒪) ⊗ I → H²(X × X, 𝒪) ⊗ I`, and that homomorphism is injective. Hence the
obstruction of `L₀` vanishes.

This module formalizes only this deduction. The source's "related by the homomorphism"
is the hypothesis `naturality`. Its injectivity claim, which the source derives from the
Künneth formula and the cohomology of abelian varieties, is the hypothesis `injectivity`.
The source states the injectivity with residue-field coefficients `H²(X_k, 𝒪) ⊗ I`. The
Library statement `ArtinianH2PrimitiveInjectivityStatement` instead uses the actual ideal
sheaf of the thickening. Both statements' Markdown files document that dictionary. Two
steps are derived content, not quoted from the source: the triviality of
`m^*L ⊗ p₁^*L⁻¹ ⊗ p₂^*L⁻¹` becomes the additive identity
`m₀^*[L] = p₁₀^*[L] + p₂₀^*[L]` in the Picard group, and the special fibre of
`A ×_{B'} A` is compared with `A₀ ×_B A₀`.

## `pullback_classOf_eq_add`

The proof reuses
`Langlands.AbelianScheme.ArtinianPrimitiveLineBundleLifting.pullback_classOf_eq_add`
from `ArtinianPrimitiveLineBundleLiftingFromPrerequisites`. For morphisms
`m p q : W ⟶ Z`, a line bundle `L` and an isomorphism
`m^*L ≅ p^*L ⊗ q^*L`, it gives the same additive Picard-class identity used here.
Its implementation is documented in that module's paired Markdown.

## `artinianPrimitiveLineBundleLifting_of`

Fix `φ : B' → B`, surjective with `maximalIdeal B' * ker φ = ⊥`, an abelian scheme `A`
over `Spec B'`, `j := Spec.map φ`, `A₀ := (baseChange j).obj A`, a line bundle `L` on
`A₀.X.left` and, from the hypothesis, an isomorphism `e : m₀^*L ≅ p₁₀^*L ⊗ p₂₀^*L` on
`A₀ ×_B A₀`. Here `p₁₀`, `p₂₀` are the projections and `m₀ = p₁₀ * p₂₀`.

**The thickening of `A`.** Let `i := pullback.fst A.X.hom j : A₀.X.left ⟶ A.X.left`. By
definition of `baseChange`, `A₀.X.left` is `pullback A.X.hom j`. The published
`AffineBaseChangeKernel.isClosedImmersion` shows that `i` is a closed immersion, and
`AffineBaseChangeKernel.ker_sq` (from `maximalIdeal B' * ker φ = ⊥`) that
`i.ker ^ 2 = ⊥`. `A.X.left` is compact because `A.X.hom` is quasi-compact over the affine
`Spec B'`. `A₀.X.left` is compact because `i` is quasi-compact
(`QuasiCompact.compactSpace_of_compactSpace`).

**Reduction to the obstruction.** By `SquareZeroPicardObstruction.lineBundle_lift_iff`,
it suffices to show `obstructionMap i hi L.classOf = 0`. That theorem then gives a line
bundle `M` on `A.X.left` with an isomorphism of underlying modules
`(LineBundle.pullback i M).obj ≅ L.obj`. `ObjectProperty.isoMk` makes it an isomorphism of
line bundles, which is the conclusion of the target.

**The thickening of `A ×_{B'} A`.** Let `P := A.X ⨯ A.X` in `Over (Spec B')`, with
projections `p1`, `p2` and `m := p1 * p2`, the group law of `A` on `P`-points. Let
`iP := pullback.fst P.hom j : pullback P.hom j ⟶ P.left`. The same two lemmas show that
`iP` is a closed immersion with `iP.ker ^ 2 = ⊥`. `P.left` is compact via
`Over.prodLeftIsoPullback`, which identifies it with `pullback A.X.hom A.X.hom`.
`((Over.pullback j).obj P).left = pullback P.hom j` is compact via `pullback.fst P.hom j`.

**The three squares and their ideal maps.** For `f : P ⟶ A.X`, set
`g f := ((Over.pullback j).map f).left : pullback P.hom j ⟶ A₀.X.left`. Then
`iP ≫ f.left = g f ≫ i` holds by `Over.pullback_map_left` and `pullback.lift_fst`. The
published `StructureKernelMorphism.kernelModuleMap f.left i iP (g f) (w f)` gives
`k f : kernelModule i ⟶ f_* kernelModule iP`, and `kernelModuleMap_ι` proves the
compatibility
`k f ≫ f_*(kernelModuleι iP) = kernelModuleι i ≫ unitToPushforwardUnit f.left` that both
hypotheses require.

**Naturality.** The hypothesis `naturality` is applied with `R = B'`, `X = A.X`, `X' = P`,
`Y = A₀.X.left`, `Y' = pullback P.hom j`, the immersions `i`, `iP`, the morphism `g f`
and the map `k f`, for each `f ∈ {m, p1, p2}`. With `ρ`, `ρP` the
`relativeIdealCohomologyAddEquiv` of `(A.X.hom, i)` and `(P.hom, iP)` in degree 2, and
`pull f κ := H²(adjoint of κ) ∘ relativeCohomologyPullback f (kernelModule i) 2`, this
gives

```text
pull f (k f) (ρ (o_i [L])) = ρP (o_{iP} ((g f)^* [L]))      (f = m, p1, p2).
```

**Primitivity on the special fibre of `P`.** Let
`E := prod.lift ((Over.pullback j).map p1) ((Over.pullback j).map p2) :
(Over.pullback j).obj P ⟶ A₀.X ⨯ A₀.X`. Then `E ≫ fst = (Over.pullback j).map p1` and
`E ≫ snd = (Over.pullback j).map p2` (`prod.lift_fst`, `prod.lift_snd`). The group law
of `A₀` is the image of that of `A` under the monoidal functor `Over.pullback j`.
Therefore `MonObj.comp_mul` and `Functor.map_mul` give
`E ≫ (fst * snd) = (Over.pullback j).map m`. Taking underlying morphisms,
`g p1 = E.left ≫ p₁₀.left`, `g p2 = E.left ≫ p₂₀.left` and `g m = E.left ≫ m₀.left`.
`Group.pullback_comp` and `pullback_classOf_eq_add` applied to `e` then give

```text
(g m)^* [L] = (g p1)^* [L] + (g p2)^* [L]      in Group (pullback P.hom j).
```

**Injectivity.** The hypothesis `injectivity` is applied with `B'`, `B`, `φ`, `A` and the
maps `k m`, `k p1`, `k p2` with their compatibilities. Its `let`-bound `P`, `p1`, `p2`,
`m`, `i`, `iP` and `pull` agree definitionally with the ones above. It gives injectivity
of `pull m (k m) − pull p1 (k p1) − pull p2 (k p2)` on
`(relativeCohomology A.X.hom 2).obj (kernelModule i)`. Since `ρ` is injective, it suffices
that this difference kills `ρ (o_i [L])`. By the three naturality identities, the
primitivity identity and additivity of `obstructionMap iP hiP` and `ρP`, the value is

```text
ρP(o(p1^*)) + ρP(o(p2^*)) − ρP(o(p1^*)) − ρP(o(p2^*)) = 0,
```

which `abel` closes. Hence `o_i [L] = 0` and `L` lifts.

## `artinianPrimitiveLineBundleLiftingReduction`

The named statement and entry theorem are imported from
`ArtinianPrimitiveLineBundleLiftingFromPrerequisites`. The explicit-premise theorem
above proves the same implication and retains this module's obstruction argument.
