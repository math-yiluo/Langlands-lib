# Total cohomology vanishing from vanishing of every direct image

This module packages the published pushforward comparison and injective
acyclicity theorem for actual structure-sheaf modules. Worker 1013 implemented
it from the proof design supplied by Worker 727, who is a coauthor.
Its provenance is internal and derived entirely from those Library results;
it introduces no new source transcription or geometric theorem.

For arbitrary universe `u`, schemes `X,Y : Scheme.{u}`, a morphism
`f : X ⟶ Y`, a commutative ring `R : CommRingCat.{u}`, a morphism
`g : Y ⟶ Spec R`, and an actual module `M : X.Modules`, the definition
`Langlands.AlgebraicGeometry.Modules.DerivedSections.pushforwardCohomologyIso`
has the complete type

```lean
(f : X ⟶ Y) → (g : Y ⟶ Spec R) → (M : X.Modules) →
  (∀ q : ℕ, IsZero ((higherDirectImage f (q + 1)).obj M)) →
  (n : ℕ) →
  ((relativeCohomology (f ≫ g) n).obj M ≅
    (relativeCohomology g n).obj ((Scheme.Modules.pushforward f).obj M))
```

Here the arrows display the explicit arguments of the definition; `X,Y,R`
are implicit. `higherDirectImage f n` and `relativeCohomology g n` are
the actual right-derived functors defined in `DerivedSections`, not
abstract cohomology groups supplied as data.

The isomorphism is `asIso` of the existing `pushforwardComparison`.
The existing `isIso_pushforwardComparison` requires positive-degree
vanishing of the direct images of `M`, and acyclicity of pushforwards
of injective modules. The former is the displayed hypothesis. The latter
is discharged for every injective `J` and every `q : ℕ` by the proved
`Langlands.AlgebraicGeometry.Modules.pushforwardInjectiveAcyclic`
in module `PushforwardInjectiveAcyclicProof`, using its relative-cohomology
component at `R,g`. Thus the isomorphism has no separate injective
acyclicity hypothesis.

The accompanying theorem
`Langlands.AlgebraicGeometry.Modules.DerivedSections.isZero_relativeCohomology_of_higherDirectImage`
has the complete type

```lean
(f : X ⟶ Y) → (g : Y ⟶ Spec R) → (M : X.Modules) →
  (∀ q : ℕ, IsZero ((higherDirectImage f q).obj M)) →
  (n : ℕ) →
  IsZero ((relativeCohomology (f ≫ g) n).obj M)
```

The quantifier on `q` includes degree zero. The proof transports the
degree-zero vanishing along `(higherDirectImageZeroIso f).app M` to
obtain `IsZero ((Scheme.Modules.pushforward f).obj M)`. The published lemma
`Langlands.Cohomology.AcyclicComparison.isZero_rightDerived_obj_of_isZero`
shows that the right-derived functor of `relativeGlobalSections g` sends
this zero pushforward to a zero object. This lemma uses preservation of
zero morphisms for right-derived functors, so no additivity instance for
`relativeCohomology g n` is needed. Transport along `pushforwardCohomologyIso`
then gives the displayed conclusion.

The module needs no properness, smoothness, affine source or target,
line bundle, finite-generation, or field hypotheses. Only the final
structure morphism `g` has an affine codomain, which specifies the
scalar ring of the cohomology. No spectral sequence is constructed.

This is a helper unit for the first-projection exact proof task
`651d1a6b-549e-4d79-ae47-19627b02f30d`. The theorem takes vanishing
of all actual higher direct images as a hypothesis; it does not prove
that vanishing from rational fibres and does not prove the host task's
unconditional abelian-square proposition. That geometric input and
the final exact-target proof remain separate obligations.
