# Naturality of elementary ideal cohomology in residue coordinates

`Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology.NaturalityStatement`
is an internal `Prop` target. It states a functorial finite-coordinate
comparison, in every natural cohomological degree, for actual ideal
modules on flat proper schemes over local Artinian rings. This pair
does not prove the comparison.

Let `φ : R →+* S` be a surjection of local Artinian rings with
`maximalIdeal R * RingHom.ker φ = ⊥`, and let `K` be the actual residue
field of `S`. Put `s = Spec (residue S ∘ φ) : Spec K → Spec R`.
For an actual `X : Over (Spec R)`, `ideal φ X` is the unchanged
`StructureKernelModule.kernelModule` of the projection
`X ×_(Spec R) Spec S → X`. The abbreviation `idealCohomology φ X n`
is its actual relative cohomology over `R`.

For a morphism `f : Y → X` over `Spec R` and a coefficient map
`k : ideal φ X → f_* ideal φ Y`, `Compatible φ f k` is the exact
equation asserting compatibility with the ideal inclusions and the
structure homomorphism of `f`. The linear map `idealPull φ f k n`
is the canonical `relativeCohomologyPullback f` followed by cohomology
of the adjoint of `k`. These are precisely the maps in the Artinian
reduced-coproduct target.

The functor `residuePullback φ` is the actual `Over.pullback s`.
The definitions `structureCohomology` and `structurePull` use the
actual residue-field relative cohomology of the structure module and
the canonical `pullbackUnitIso` coefficient comparison.

For each fixed pair `X,Y` of flat proper schemes and each degree `n`,
the statement asks for a finite number `d` and additive equivalences

```text
eX : H^n_R(X, ideal φ X) ≃+ (Fin d → H^n_K(X_K, O)),
eY : H^n_R(Y, ideal φ Y) ≃+ (Fin d → H^n_K(Y_K, O)).
```

They must be chosen before the morphism and coefficient map.
For every `f : Y → X`, every compatible `k`, every class `x`, and
every coordinate `j`, the equation is

```text
eY (idealPull f k x) j = structurePull (residuePullback.map f) (eX x j).
```

The same finite coordinate index is used for both schemes. The statement
does not specify `d` or assert a canonical basis. A proof can choose a
finite basis of `ker φ` over `K`; the zero kernel and `d = 0` are allowed.
Only the additive structure is asserted, so no new residue-field action
on the original relative cohomology groups is imposed.

This is a general prerequisite for Task 5896, rather than an
injectivity assumption: it applies to arbitrary morphisms of flat proper
schemes and every degree, without an abelian group law or a
reduced coproduct. An abstract cohomology equivalence without the stated
map equation is insufficient.

The internal provenance is the elementary ideal-module presentation,
the published `ArtinianResidueCohomology.idealCohomologyTensorEquiv`,
and finite-basis coordinates. An arbitrary surjection can be made a
pointed Artinian test over `R` with residue field `K`, using the
augmentations `residue S ∘ φ` and `residue S`. The construction
`ArtinianSurjectionTests` records this packaging. A proof must also
handle the identity-base pullback, the naturality of the ideal-sheaf
presentation, affine-pushforward cohomology and scalar restriction,
and the specific canonical cohomology pullbacks above. These
comparisons are obligations, not hypotheses silently supplied by
the existing tensor equivalence.

No Picard-zero lifting, dual representability, or Artinian primitive
line-bundle lifting result occurs in the statement or its proposed route.

Authored by Worker 210.
