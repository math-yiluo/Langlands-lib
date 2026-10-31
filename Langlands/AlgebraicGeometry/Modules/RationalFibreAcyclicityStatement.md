# Open-local vanishing of higher direct images from rational-fibre acyclicity

Authors: Worker 310 and Worker 1013. Worker 1013 supplied the Lean statement
and initial geometric design; Worker 310 verified the original references and
completed this account of the derived provenance.

This module defines the universe-polymorphic proposition
`Langlands.AlgebraicGeometry.Modules.RationalFibreAcyclicityStatement.{u}`.
It states a geometric implication; it does not prove that implication. The
statement is a derived specialization and local consequence of the original
results below, rather than a verbatim transcription of a single source.

## Complete declaration

With `universe u`, and with `CategoryTheory`, `CategoryTheory.Limits`,
`AlgebraicGeometry`, and
`Langlands.AlgebraicGeometry.Modules.DerivedSections` open, its complete
type and defining value are:

```lean
def Langlands.AlgebraicGeometry.Modules.RationalFibreAcyclicityStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (X Y : Scheme.{u}) (g : Y ⟶ Spec (CommRingCat.of K)),
    LocallyOfFiniteType g →
    ∀ f : X ⟶ Y, Smooth f → IsProper f →
    ∀ (Q : Langlands.AlgebraicGeometry.Picard.LineBundle X) (U : Y.Opens),
      (∀ (x : Spec (CommRingCat.of K) ⟶ U.toScheme),
        x ≫ U.ι ≫ g = 𝟙 (Spec (CommRingCat.of K)) →
        ∀ n : ℕ,
          IsZero ((relativeCohomology (pullback.snd f (x ≫ U.ι)) n).obj
            ((Scheme.Modules.pullback (pullback.fst f (x ≫ U.ι))).obj Q.obj))) →
      ∀ n : ℕ,
        IsZero ((Scheme.Modules.pullback U.ι).obj ((higherDirectImage f n).obj Q.obj))
```

All field structures and hypotheses are universally quantified inside the
proposition. The schemes, field, and actual module categories use the arbitrary
universe `u`. There is no additional comparison, chosen perfect complex,
coherence, or vanishing hypothesis outside the displayed fibre condition.

## Meaning of the actual objects

The structure morphism `g` makes `Y` a scheme locally of finite type over the
algebraically closed field `K`. The morphism `f : X ⟶ Y` is smooth and proper.
The object `Q` is an actual locally free rank-one sheaf of modules, with
underlying module `Q.obj : X.Modules`, as defined in
`Langlands.AlgebraicGeometry.Picard.LineBundle`.

The open immersion is `U.ι : U.toScheme ⟶ Y`. A point quantified in the
hypothesis is a morphism `x : Spec (CommRingCat.of K) ⟶ U.toScheme` over `K`:
the displayed equation says that its composite with `U.ι` and `g` is the
identity of `Spec (CommRingCat.of K)`. Thus these are rational points over
the specified field structure, not all scheme morphisms from `Spec K`.

For such an `x`, the scheme fibre is the existing categorical pullback
`pullback f (x ≫ U.ι)`. Its first projection maps to `X`; its second
projection maps to `Spec (CommRingCat.of K)`. Ordinary module pullback
along the first projection gives the actual coefficient on that fibre.
The imported `LineBundlePullback` theory proves that this coefficient is
again locally free of rank one.

For a morphism `h : Z ⟶ Spec R`, `relativeCohomology h n` is the
`n`-th right-derived functor of
`Scheme.Modules.pushforward h ⋙ moduleSpecΓFunctor`, valued in
`ModuleCat R`. Consequently the hypothesis says that the actual `K`-module
of cohomology of each displayed fibre coefficient is a zero object for
every `n : ℕ`. This includes its global sections in degree zero.

The functor `higherDirectImage f n` is
`(Scheme.Modules.pushforward f).rightDerived n : X.Modules ⥤ Y.Modules`.
The conclusion is that its value at `Q.obj`, pulled back along `U.ι`, is a
zero object of `U.toScheme.Modules` for every `n : ℕ`. Pullback along this
open immersion is naturally isomorphic to restriction. Thus the conclusion
is vanishing of the restricted sheaf `Rⁿf_*Q`, including `f_*Q` in degree
zero. It is not merely a statement about global sections of that sheaf.
`IsZero` is the categorical zero-object predicate.

The open `U` is arbitrary; in particular it need not be affine or
quasi-compact. The proposition imposes no group law, projectivity,
reducedness, connectedness, characteristic, or dimension restriction and
adds no global finite-type or noetherian hypothesis on `Y`.

## Original sources and derived provenance

The following registered originals are retained at Stacks Project source
commit `a04446e57ec1fbc252a871afcec7752fb2807b14`. Both folder fingerprints
refer to the complete registered folders, and the locators identify the
actual files and statements used.

- Literature ID `stacks-perfect-complexes-a04446e5`, folder
  `literature/Stacks Project - Perfect complexes and proper direct images (source at a04446e5)`,
  SHA-256 `54c831042614714cdb007a024d45dca7f60709efe2c307389ca2ad848b0ccbed`:
  `perfect.tex`, Lemma 36.30.4, tag [0B91](https://stacks.math.columbia.edu/tag/0B91),
  label `lemma-flat-proper-perfect-direct-image-general`, lines 7524–7544;
  Remark 36.30.2, tag [0A1I](https://stacks.math.columbia.edu/tag/0A1I),
  label `remark-explain-perfect-direct-image`, lines 7443–7455; and
  `more-algebra.tex`, Lemma 15.79.2, tag [068V](https://stacks.math.columbia.edu/tag/068V),
  label `lemma-check-perfect-pointwise`, lines 20031–20061.
  The actual chapter title of `perfect.tex` is *Derived Categories of Schemes*;
  the source registration's description as *More on Flatness* is inaccurate.
- Literature ID `stacks-flasque-affine-vanishing-kunneth-a04446e5`, folder
  `literature/Stacks Project - Flasque sheaves, affine vanishing and Kunneth over a field (source at a04446e5)`,
  SHA-256 `af02e6f0aff875e216f1e0fde58f6baad3eedeb6b82799a8d6c91ff68cccaa3a`:
  `varieties.tex`, Lemma 33.14.1, tag [0478](https://stacks.math.columbia.edu/tag/0478),
  label `lemma-locally-finite-type-Jacobson`, lines 2669–2693; and
  `cohomology.tex`, Lemma 20.7.3, tag [01E4](https://stacks.math.columbia.edu/tag/01E4),
  label `lemma-describe-higher-direct-images`, lines 591–627, and Lemma 20.7.4,
  tag [01E5](https://stacks.math.columbia.edu/tag/01E5),
  label `lemma-localize-higher-direct-images`, lines 629–651.

Worker 310 read the complete cited statements and proofs (and the complete
remark) in the retained originals and checked the corresponding live tag
pages and comments. No project errata file for either source was present
at this reading.

Here is the mathematical deduction that motivates the proposition. These
steps explain the provenance and the specializations required; they are not
Lean proofs supplied by this module.

1. Work on a basis of finite-type affine `K`-opens `V = Spec A` contained
   in `U`. Such a basis exists because `g` is locally of finite type; one
   may refine its affine neighbourhoods by distinguished affine opens.
   No finite cover of `U` is needed. The base-changed family `f_V` remains
   smooth and proper. Smoothness gives flatness and local finite
   presentation, and properness gives quasi-compactness and
   quasi-separatedness, so `f_V` has finite presentation. The pulled-back
   line bundle `Q_V` is perfect in degree zero and finitely presented; it
   is flat over `V` since it is locally free and `f_V` is flat.
2. Tag 0B91 applies to the proper, flat, finitely presented morphism
   `f_V` and the perfect coefficient `Q_V`. It gives a perfect derived
   direct image and compatibility with arbitrary base change. Over
   `Spec A`, one obtains a bounded complex `P` of finite projective
   `A`-modules computing derived sections and their base changes.
   Tag 0A1I also states this finite-projective-complex description for a
   finitely presented coefficient flat over the affine base and with
   proper support, conditions satisfied here. Since `P` is bounded
   projective, ordinary termwise scalar extension computes its derived
   tensor product.
3. For each maximal ideal `m` of `A`, tag 0478 makes the residue field
   `κ(m)` algebraic over `K`; algebraic closedness identifies this
   extension with `K` compatibly with its `K`-algebra structure. Apply
   this result to the finite-type affine `V` itself; closedness in all
   of `Y` is unnecessary. The resulting `K`-point of `V` factors through
   `U` and satisfies the equation in the hypothesis. Canonical
   iterated-pullback and coefficient-pullback comparisons identify its
   fibre of `f_V` with the displayed fibre of `f`. Arbitrary base change
   from step 2 therefore identifies the cohomology of
   `P ⊗_A κ(m)` with the fibre cohomology in the hypothesis. It vanishes
   in all nonnegative degrees, including zero; negative cohomology is
   already zero because the coefficient is a sheaf in degree zero and
   sections are right-derived.
4. Tag 068V is a criterion for a pseudo-coherent complex to have Tor
   amplitude in an interval `[a,b]`, tested on maximal-ideal residue
   fibres. It does not literally state acyclicity detection. Apply it
   to the perfect `P` twice, using `[0,0]` and `[1,1]`. Acyclic residue
   fibres satisfy both tests, so `P` has both Tor-amplitude bounds and
   hence has zero cohomology in every integer degree. It follows that
   all `Hⁿ(X_V,Q_V)` vanish.
5. Tag 01E4 describes higher direct images as sheafifications of the
   presheaves `V ↦ Hⁿ(f⁻¹(V),Q)`. Vanishing on the affine basis from
   step 1 thus makes the associated sheaves zero over `U`; this uses
   the sheafification description, not an equality of higher direct
   image sections with that presheaf on every open. Tag 01E5 supplies
   compatibility with restriction to target opens. Together with the
   natural comparison between ordinary module pullback along `U.ι`
   and restriction, this gives precisely the displayed conclusion in
   `U.toScheme.Modules`.

## Remaining formal proof obligations

The Lean file supplies only the proposition definition. A proof must implement
the proper perfect-direct-image and arbitrary-base-change results for this
geometry, compare their derived sections and scalar structures with the
actual `DerivedSections.relativeCohomology` functors, and compare the derived
pullbacks with the ordinary pullbacks of these line bundles. It must also
construct the rational-point/residue-field and iterated-fibre identifications,
apply an appropriate perfect-complex acyclicity detection theorem, and prove
the open-local higher-direct-image and sheaf zero-detection comparisons for
the actual module functors used here. Existing line-bundle pullback and
right-derived functor definitions provide the objects in the statement;
they do not by themselves prove those geometric comparisons.

In particular, this module does not use the proposition
`UniversalPerfectSectionsStatement` as proof evidence, nor establish total
cohomology vanishing, finite-support acyclicity, or a Leray comparison. The
whole-base case `U = ⊤` and restriction to an open complement of a finite
closed set are specializations of this same statement, with no change to
its hypotheses or its actual geometric objects.
