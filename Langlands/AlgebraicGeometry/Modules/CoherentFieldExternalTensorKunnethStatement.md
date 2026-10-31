# Coherent Künneth over a field for external tensor products of line bundles

`Langlands.AlgebraicGeometry.Modules.CoherentFieldExternalTensorKunnethStatement`
is a universe-polymorphic `Prop`-valued definition. It states the coherent
Künneth formula over a field, in every degree, for the external tensor
product of two actual line bundles on smooth proper schemes. The formula
is stated for the Library's right-derived cohomology. The module states the
proposition only. It supplies no proof and adds no axiom.

## Statement

For every universe `u`, every field `K : Type u`, every pair
`X Y : Over (Spec (CommRingCat.of K))` whose structure morphisms `X.hom` and
`Y.hom` are smooth and proper, every `L : LineBundle X.left`, every
`M : LineBundle Y.left` and every `n : ℕ`, put `P := X ⨯ Y`,
`p₁ := (prod.fst : P ⟶ X).left` and `p₂ := (prod.snd : P ⟶ Y).left`. The
proposition says that an isomorphism in `ModuleCat K` exists:

```text
Hⁿ(P, p₁^*L ⊗ p₂^*M)  ≅  ModuleCat.of K (⨁_{(a,b) : a + b = n} Hᵃ(X, L) ⊗_K Hᵇ(Y, M)).
```

Here `Hᵠ(Z, N)` means exactly
`(DerivedSections.relativeCohomology Z.hom q).obj N` for `Z` among `P`, `X`
and `Y`. The coefficient on `P.left` is exactly

```text
Langlands.Scheme.Modules.tensorObj
  ((AlgebraicGeometry.Scheme.Modules.pullback p₁).obj L.obj)
  ((AlgebraicGeometry.Scheme.Modules.pullback p₂).obj M.obj).
```

The proposition asserts only that such an isomorphism exists, as
`Nonempty (_ ≅ _)`. It does not name a comparison map and claims no
naturality.

## Complete checked type

The source declaration is

```lean
def CoherentFieldExternalTensorKunnethStatement : Prop :=
  ∀ (K : Type u) [Field K] (X Y : Over (Spec (CommRingCat.of K)))
    [Smooth X.hom] [IsProper X.hom] [Smooth Y.hom] [IsProper Y.hom]
    (L : LineBundle X.left) (M : LineBundle Y.left) (n : ℕ),
      let P : Over (Spec (CommRingCat.of K)) := X ⨯ Y
      Nonempty ((DerivedSections.relativeCohomology P.hom n).obj
          (Langlands.Scheme.Modules.tensorObj
            ((AlgebraicGeometry.Scheme.Modules.pullback (Limits.prod.fst : P ⟶ X).left).obj L.obj)
            ((AlgebraicGeometry.Scheme.Modules.pullback (Limits.prod.snd : P ⟶ Y).left).obj
              M.obj)) ≅
        ModuleCat.of K (DirectSum {ab : ℕ × ℕ // ab.1 + ab.2 = n} fun ab =>
          TensorProduct K ((DerivedSections.relativeCohomology X.hom ab.1.1).obj L.obj)
            ((DerivedSections.relativeCohomology Y.hom ab.1.2).obj M.obj)))
```

inside `namespace Langlands.AlgebraicGeometry.Modules`, with
`open CategoryTheory CategoryTheory.Limits AlgebraicGeometry` and
`open Langlands.AlgebraicGeometry.Picard`. The module imports
`Langlands.AlgebraicGeometry.Modules.DerivedSections`,
`Langlands.AlgebraicGeometry.Modules.Tensor`,
`Langlands.AlgebraicGeometry.Picard.LineBundle`,
`Mathlib.AlgebraicGeometry.Morphisms.Proper`,
`Mathlib.AlgebraicGeometry.Morphisms.Smooth` and
`Mathlib.Algebra.DirectSum.Module`. With `pp.fullNames true`,
`pp.fieldNotation false`, `pp.proofs true` and `pp.funBinderTypes true`,
`#print` in the approved environment reports:

```text
def Langlands.AlgebraicGeometry.Modules.CoherentFieldExternalTensorKunnethStatement.{u} : Prop :=
∀ (K : Type u) [inst : Field K] (X Y : CategoryTheory.Over (AlgebraicGeometry.Spec ↧K))
  [AlgebraicGeometry.Smooth (CategoryTheory.Over.hom X)] [AlgebraicGeometry.IsProper (CategoryTheory.Over.hom X)]
  [AlgebraicGeometry.Smooth (CategoryTheory.Over.hom Y)] [AlgebraicGeometry.IsProper (CategoryTheory.Over.hom Y)]
  (L : Langlands.AlgebraicGeometry.Picard.LineBundle (CategoryTheory.Over.left X))
  (M : Langlands.AlgebraicGeometry.Picard.LineBundle (CategoryTheory.Over.left Y)) (n : ℕ),
  let P := X ⨯ Y;
  Nonempty
    (CategoryTheory.Functor.obj
        (Langlands.AlgebraicGeometry.Modules.DerivedSections.relativeCohomology (CategoryTheory.Over.hom P) n)
        (Langlands.Scheme.Modules.tensorObj
          (CategoryTheory.Functor.obj
            (AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Over.Hom.left CategoryTheory.Limits.prod.fst))
            (CategoryTheory.ObjectProperty.FullSubcategory.obj L))
          (CategoryTheory.Functor.obj
            (AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Over.Hom.left CategoryTheory.Limits.prod.snd))
            (CategoryTheory.ObjectProperty.FullSubcategory.obj M))) ≅
      ↧(DirectSum { ab : ℕ × ℕ // Prod.fst ab + Prod.snd ab = n }
          fun (ab : { ab : ℕ × ℕ // Prod.fst ab + Prod.snd ab = n }) =>
          TensorProduct K
            ↑(CategoryTheory.Functor.obj
                (Langlands.AlgebraicGeometry.Modules.DerivedSections.relativeCohomology (CategoryTheory.Over.hom X)
                  (Prod.fst ↑ab))
                (CategoryTheory.ObjectProperty.FullSubcategory.obj L))
            ↑(CategoryTheory.Functor.obj
                (Langlands.AlgebraicGeometry.Modules.DerivedSections.relativeCohomology (CategoryTheory.Over.hom Y)
                  (Prod.snd ↑ab))
                (CategoryTheory.ObjectProperty.FullSubcategory.obj M))))
```

and `#check` reports type `Prop`. Here `↧K` is `CommRingCat.of K`. The
outer `↧(…)` on the right is `ModuleCat.of K`. The printed `prod.fst` and
`prod.snd` are the projections `P ⟶ X` and `P ⟶ Y` of the displayed source.
`let P := X ⨯ Y` is a genuine `let`, so `P` unfolds definitionally to the
chosen product. The projections are written inline rather than bound by
`let`, so they stay transparent.

## Indexing of the right side

The direct sum is indexed by the subtype
`{ab : ℕ × ℕ // ab.1 + ab.2 = n}`. An index `ab` is a pair `ab.1 = (a, b)`
of natural numbers with a proof of `a + b = n`. The summand at `ab` is the
`K`-module tensor product

```text
TensorProduct K (H^{ab.1.1}(X, L)) (H^{ab.1.2}(Y, M)),
```

that is `Hᵃ(X, L) ⊗_K Hᵇ(Y, M)` with `a = ab.1.1` and `b = ab.1.2`. The
index set has exactly `n + 1` elements, `(0, n), (1, n - 1), …, (n, 0)`, so
the sum is finite. In degree `0` the only index is `(0, 0)`. Each
`Hᵠ(Z, N)` is a `ModuleCat K` object and is coerced to its carrier for
`TensorProduct K` and `DirectSum`. `DirectSum` is Mathlib's direct sum of
`K`-modules, and `ModuleCat.of K` turns it back into an object of
`ModuleCat K`. Since the index set is finite, this module is the finite
biproduct in `ModuleCat K` of the summands.

## Library objects used

The statement uses only published definitions. It introduces no data,
structure, certificate, cohomology model or axiom.

- `X Y : Over (Spec (CommRingCat.of K))` are actual `K`-schemes `X.left`
  and `Y.left` with structure morphisms `X.hom` and `Y.hom`. The instance
  binders `[Smooth X.hom]`, `[IsProper X.hom]`, `[Smooth Y.hom]` and
  `[IsProper Y.hom]` are Mathlib's smoothness and properness of morphisms
  of schemes. `IsProper` means separated, universally closed and locally
  of finite type. Universally closed morphisms are quasi-compact in
  Mathlib.
- `P := X ⨯ Y` is the chosen categorical binary product in
  `Over (Spec K)`. A binary product in an over category is a fibre product
  over the base, so `P.left` is the fibre product `X.left ×_{Spec K} Y.left`.
  The projections are `p₁ = (prod.fst : P ⟶ X).left` and
  `p₂ = (prod.snd : P ⟶ Y).left`, and `P.hom` is the structure morphism of
  the product.
- `LineBundle Z` is the full subcategory of actual `Z.Modules` that are
  isomorphic to the structure sheaf on an open neighbourhood of each point
  (`IsLocallyFreeRankOne`). `L.obj` is the underlying sheaf of modules.
  The published `IsLocallyFreeRankOne.isQuasicoherent` shows that it is
  quasi-coherent; the statement does not use this lemma.
- `AlgebraicGeometry.Scheme.Modules.pullback f` is Mathlib's pullback of
  sheaves of modules along `f`. It is the left adjoint of the pushforward
  (`Scheme.Modules.pullbackPushforwardAdjunction`), so it is the usual
  `f^*` of `𝒪`-modules.
- `Langlands.Scheme.Modules.tensorObj M N` is the published tensor product
  of module sheaves. It is the sheafification of the sectionwise tensor
  product of the underlying presheaves of modules. This is the usual
  `M ⊗_{𝒪} N`.
- `DerivedSections.relativeCohomology f q`, for `f : Z ⟶ Spec R`, is by
  definition `(relativeGlobalSections f).rightDerived q`, where
  `relativeGlobalSections f = Scheme.Modules.pushforward f ⋙ moduleSpecΓFunctor`.
  It is computed with injective resolutions in the abelian category
  `Z.Modules`. Here `R = CommRingCat.of K`, whose carrier is `K`, so each
  `H` is an actual `K`-module. The published
  `relativeCohomologyRestrictScalarsIso` identifies it with the
  `Γ(Z, ⊤)`-module cohomology with scalars restricted along `K → Γ(Z, ⊤)`.
  In degree zero `relativeCohomologyZeroIso` identifies it with global
  sections.
- `TensorProduct K`, `DirectSum` and `ModuleCat.of K` are Mathlib's.

No cohomology module, comparison, Čech complex, cover or Künneth map is
supplied as a hypothesis.

## Original sources

### General formula: Stacks Project, tag 0BED

The general source is the Stacks Project at commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`, registered as
`stacks-flasque-affine-vanishing-kunneth-a04446e5` with folder SHA256
`af02e6f0aff875e216f1e0fde58f6baad3eedeb6b82799a8d6c91ff68cccaa3a` and
retained as
`literature/Stacks Project - Flasque sheaves, affine vanishing and Kunneth over a field (source at a04446e5)`.
Chapter "Varieties", Section "Künneth formula, I" (tag 0BEC), Lemma
`lemma-kunneth` (tag 0BED; `varieties.tex`, SHA256
`53d0af48818d22ae85675eff76b79fcad4335fda0b4574ec09f5c9e73cc93995`,
lines 5441-5456) reads:

> Let `k` be a field. Let `X` and `Y` be schemes over `k` and let `𝓕`,
> resp. `𝓖` be a quasi-coherent `𝒪_X`-module, resp. `𝒪_Y`-module. Then we
> have a canonical isomorphism
> `Hⁿ(X ×_{Spec(k)} Y, pr₁^*𝓕 ⊗_{𝒪_{X ×_{Spec(k)} Y}} pr₂^*𝓖) = ⨁_{p+q=n} Hᵖ(X, 𝓕) ⊗_k H^q(Y, 𝓖)`
> provided `X` and `Y` are quasi-compact and have affine diagonal (for
> example if `X` and `Y` are separated).

In the same commit, `cohomology.tex` lines 61-76 define `Hⁱ(X, 𝓕)` for an
`𝒪_X`-module as `Hⁱ(Γ(X, 𝓘^•))` for an injective resolution in the category
of `𝒪_X`-modules, a `Γ(X, 𝒪_X)`-module. This is the same construction as the
Library's right-derived functors in `Z.Modules`, viewed as `k`-modules
through `k → Γ(X, 𝒪_X)`. So no comparison with sheaf cohomology of abelian
sheaves is involved in reading the source. The retained `tag-0BED.html`
page has no comments, and the retained README records that no comment on
the retained tags changes a statement. No Stacks-specific errata file was
present in the project or Library `notes` locations checked on 2026-10-31.

### The use in EVM Lemma (7.19)

The use is in B. Edixhoven, G. van der Geer and B. Moonen, *Abelian
Varieties*, preliminary version of the first chapters, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`,
retained as
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
Printed page numbers are PDF page numbers minus four. In the proof of
Lemma (7.19), printed p.105 / PDF p.109, the authors write that, since
`m^*L ≅ p₁^*L ⊗ p₂^*L`, "the Künneth formula gives
`Hⁱ(X × X, m^*L) ≅ Hⁱ(X × X, p₁^*L ⊗ p₂^*L) ≅ ∑_{a+b=i} Hᵃ(X, L) ⊗ Hᵇ(X, L)`."
Here `X` is an abelian variety over a field and `L` a line bundle on it.
EVM uses only this self-product case with the same line bundle on both
factors, and gives no separate statement of the Künneth formula. The
two-factor formulation here is the general Stacks lemma specialized as
below; it is not attributed to EVM. The errata and version audit for this
manuscript is recorded in the published
`TranslationInvariantCohomologyVanishingStatement.md`. No source-specific
errata file was found in the checked project or Library `notes/errata`
locations.

## Specialization from tag 0BED

The proposition is a derived special case of tag 0BED, read with the
Library's cohomology.

- Base. `k = K` and `X ×_{Spec(k)} Y` is `P.left`, the chosen fibre product.
- Quasi-compact. `X.hom` is proper, hence quasi-compact, and `Spec K` is
  quasi-compact, so `X.left` is quasi-compact; likewise `Y.left`.
- Affine diagonal. `X.hom` is proper, hence separated, and `Spec K` is
  affine, hence separated, so `X.left` is a separated scheme. Its diagonal
  is a closed immersion, hence affine. Likewise `Y.left`.
- Coefficients. Locally free rank-one modules are quasi-coherent, so
  `𝓕 = L.obj` and `𝓖 = M.obj` are allowed.
- Operations. `pr₁^*`, `pr₂^*` and `⊗_{𝒪}` are the module-sheaf pullbacks
  along `p₁`, `p₂` and `tensorObj`, as explained above. Every `H` is the
  derived-functor cohomology of the source convention, as a `K`-module.
- Conclusion. The source's "canonical isomorphism" of `k`-vector spaces is
  weakened to `Nonempty` of an isomorphism in `ModuleCat K`, and `⨁_{p+q=n}`
  is the subtype-indexed direct sum described above.

Smoothness is an additional hypothesis that the source lemma does not need.
It is kept because the contract fixes the smooth proper interface used for
abelian schemes. It makes the proposition weaker, not stronger, than the
source specialization.

## Application to abelian schemes

For a Library `A : AbelianScheme (Spec (CommRingCat.of K))` the structure
morphism `A.X.hom` carries the instances `A.smooth : Smooth A.X.hom` and
`A.proper : IsProper A.X.hom`. A private check in the approved environment
confirmed that, for any field `K` with `IsAlgClosed K`, any such `A`, any
`L : LineBundle A.X.left` and any `n`, the term
`h K A.X A.X L L n` has the self-product type, where `h` is a proof of this
proposition. This is the case used in EVM Lemma (7.19), with the same line
bundle on both factors and no translation-invariance or nontriviality
condition on `L`.

## Scope

The statement covers every universe `u`, every field `K` of every
characteristic, all degrees `n : ℕ` including `0`, and every dimension. In
dimension zero, `Over.mk (𝟙 (Spec K))` is smooth and proper; the same
private check confirmed both instances. The empty scheme over `Spec K` is
also allowed; then both sides are zero.

The only geometric hypotheses are smoothness and properness of `X.hom` and
`Y.hom`. There is no connectedness, geometric integrality, positivity,
line-bundle triviality or translation-invariance condition, and no
supplied cohomology, affine cover, acyclicity, Čech-to-derived comparison,
perfectness or Künneth premise.

## Proof obligations for the later exact proof

After independent acceptance and publication, a separate exact-target proof
must have this entire named proposition as its type, with no extra outer
hypotheses. The Stacks proof of tag 0BED (`varieties.tex` lines 5459-5630)
suggests the following obligations. None is proved here.

1. All-degree derived comparison. For a separated quasi-compact scheme over
   `Spec K` with a finite affine open cover, identify the published
   `relativeCohomology` of a quasi-coherent module with the cohomology of
   the alternating Čech complex in every degree. This is Stacks tag 01XD
   (`coherent.tex`, `lemma-cech-cohomology-quasi-coherent`) together with
   affine vanishing (tag 01XB). It is needed for `X.left`, `Y.left` and,
   on the source route, for `P.left`, which is proper over `Spec K` and
   hence also separated and quasi-compact. Worker 958 owns an in-progress
   all-degree Čech-to-derived comparison (AB2) under task
   `5056e5fc-5861-489e-adae-be84a23164c5`. The proof should reuse that
   comparison once it is published, and must not duplicate it. This
   statement does not assume it.
2. Affine section calculation. For affine opens `U ⊆ X.left` and
   `V ⊆ Y.left`, identify the sections of `p₁^*L ⊗ p₂^*M` over the affine
   open `U × V` of `P.left` with `L(U) ⊗_K M(V)`. This uses the Library
   pullback, `tensorObj` and the quasi-coherence of the pulled-back line
   bundles. It is the affine case of the formula, which the source obtains
   from affine vanishing and the definitions (lines 5479-5483). Because
   `X.left` and `Y.left` are separated, it applies to every finite
   intersection `U_{i₀…i_p} × V_{j₀…j_q}` of members of a product cover.
   This calculation does not by itself identify Čech complexes of the
   product cover; see item 3.
3. Cohomological comparison of Čech complexes. Choose finite affine open
   covers `𝒰 = (U_i)_{i ∈ I}` of `X.left` and `𝒱 = (V_j)_{j ∈ J}` of
   `Y.left`, and let `𝒲 = (U_i × V_j)_{(i, j) ∈ I × J}` be the product cover
   of `P.left`. The cover `𝒲` refines `p₁⁻¹𝒰` and `p₂⁻¹𝒱`. The induced
   pullback maps of Čech complexes, followed by the Čech cup product, give
   a map of complexes
   `Tot(Č(𝒰, L) ⊗_K Č(𝒱, M)) → Č(𝒲, p₁^*L ⊗ p₂^*M)`
   (`varieties.tex` lines 5486-5527). This map is **not** an isomorphism of
   complexes; the source warns of this at lines 5528-5529. For example,
   take `X = Y = Spec K`, both line bundles trivial, and on each factor the
   cover by two copies of `Spec K`. Then the degree-one terms of the
   alternating complexes have dimension `4` on the left and `6` on the
   right. The obligation is to prove that this map induces isomorphisms on
   cohomology in every degree. The source proves this as follows.
   - Two-out-of-three (lines 5538-5577). The map is functorial in the first
     coefficient, and the Čech complexes are exact in it because they take
     sections over affine opens. So, for a short exact sequence of
     quasi-coherent modules on `X`, if the comparison is a quasi-isomorphism
     for two of the three terms, it is one for the third.
   - Dimension shifting (lines 5578-5599). Quasi-coherent cohomology on `X`
     vanishes above a finite degree. Induction on the top degree with
     nonzero cohomology, using an embedding into a quasi-coherent module
     with vanishing higher cohomology, reduces to coefficients on `X` and on
     `Y` with cohomology only in degree zero.
   - Base case (lines 5600-5629). Over an affine `V ⊆ Y`, the source states
     the equality of complexes
     `Č(𝒰, 𝓕) ⊗_K 𝓖(V) = Č(𝒰_V, pr₁^*𝓕 ⊗ pr₂^*𝓖)` for the cover
     `𝒰_V = (U_i × V)_i` of `X × V`. With commutation of cohomology with
     direct sums and the Leray spectral sequence for `pr₂`, this gives the
     formula when both coefficients have cohomology only in degree zero.
     The source omits the check that this isomorphism is the one induced
     by the cup product (lines 5627-5629). The two-out-of-three step
     compares the specific map, so on this route that check is part of the
     obligation.

   The source route leaves the class of line bundles. Its induction needs
   the comparison for quasi-coherent modules that are not line bundles,
   and it needs the Leray spectral sequence. A proof may instead use the
   double Čech complex with terms
   `Γ(U_{i₀…i_p} × V_{j₀…j_q}, p₁^*L ⊗ p₂^*M)`. By item 2 and finiteness of
   the covers, its total complex is isomorphic to
   `Tot(Č(𝒰, L) ⊗_K Č(𝒱, M))`, with matching sign conventions. But this
   double complex is not the ordinary Čech complex `Č(𝒲, p₁^*L ⊗ p₂^*M)`
   of the product cover. That route therefore still needs a separate proof
   that its total complex computes `Hⁿ(P, p₁^*L ⊗ p₂^*M)`. Such a proof
   could compare it with `Č(𝒲, …)` or give a direct Čech-to-derived
   argument for the double cover.
4. Algebraic Künneth over a field. For cochain complexes of `K`-vector
   spaces, the cohomology of the total tensor complex in degree `n` is
   `⨁_{a+b=n} Hᵃ ⊗_K Hᵇ`.
5. Assembly. On the source route, item 1 for `P.left` and item 3 identify
   `Hⁿ(P, p₁^*L ⊗ p₂^*M)` with `Hⁿ(Tot(Č(𝒰, L) ⊗_K Č(𝒱, M)))`. On the
   double-complex route, the separate comparison of item 3 gives the same
   identification. Item 4 and item 1 for `X.left` and `Y.left` identify
   this with
   `⨁_{a+b=n} Hᵃ(X, L) ⊗_K Hᵇ(Y, M)`. The assembly must work with the
   products, pullbacks and direct sums of the published statement,
   including in degree zero and for empty schemes, where the covers may be
   empty.

The existing degree-one results
`Langlands.AlgebraicGeometry.Picard.fieldTwoAxisH1Injectivity`, for `H¹` of
structure sheaves, and the abstract degree-one
`Langlands.Algebra.TensorDegreeOneKunneth` may be reused where they apply.
They are not proofs of this all-degree statement. Substantial missing
inputs need separate definitions, statements and unconditional proofs, in
dependency order.

## Role and authorship

This is a focused prerequisite of the exact proof task
`a45129b4-368e-4cd9-813b-e2e884897b35`, which proves
`Langlands.AbelianScheme.AlgClosedFieldTranslationInvariantCohomologyVanishingStatement`
(EVM Lemma (7.19)). That host target, the parent translation-difference
lifting statement and any downstream dual or Picard existence result are
neither used nor cited as justification here.

Worker 1137 implemented the Lean declaration and this Markdown, following
the task specification.
