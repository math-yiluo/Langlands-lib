# The actual nondegenerate-part coreflection

Author: Worker 6 (construction and intrinsic laws). Worker 345 verified the
source correspondence and published interfaces and prepared the submission.
This paired module contains the construction and its intrinsic laws.

The inclusion `nondegenerateInclusion A` of the existing full subcategory is
left adjoint to the existing `nondegeneratePartFunctor hA`. These functors,
their objects, original additive intertwiners, and the natural inclusion
`nondegeneratePartInclusion hA` are imported unchanged from the published
`Langlands.Algebra.NonUnitalModule`.

For any original map `f : M → N` whose source is nondegenerate,
`NonUnitalModuleHom.factorNondegeneratePart hA hM f` sends a vector `m` to
the same vector `f m`, now regarded as an element of the actual part of `N`.
If an idempotent fixes `m`, equivariance shows that it fixes `f m`.
Additivity and equivariance follow from the same properties of `f`.
No choice of fixing idempotents is an input to the factorization: the source
nondegeneracy proof supplies membership for each vector. Composition with the actual part inclusion recovers `f`, and the factor is
unique because that inclusion is the underlying subtype map. The ring,
source-carrier and target-carrier universes are independent in this
unbundled construction.

For `X` in the existing nondegenerate category and `Y` in the existing
ambient category, `nondegeneratePartHomEquiv hA X Y` is the equivalence

```lean
((nondegenerateInclusion A).obj X ⟶ Y) ≃
  (X ⟶ (nondegeneratePartFunctor hA).obj Y)
```

Its forward map restricts the codomain as above. Its inverse composes the
underlying original map with the actual part inclusion. Both inverse
identities follow by evaluation and subtype extensionality.
The two evaluation laws retain these exact original maps.

`nondegeneratePartAdjunction hA` applies Mathlib's `Adjunction.mkOfHomEquiv`
to this equivalence. For a source morphism `k : X′ ⟶ X`, the inverse map
sends `k ≫ g` to `(nondegenerateInclusion A).map k` followed by the inverse
image of `g`. For a target morphism `l : Y ⟶ Y′`, the forward map sends
`f ≫ l` to the forward image of `f` followed by
`(nondegeneratePartFunctor hA).map l`. Both equations are proved by
evaluation on vectors and extensionality, using subtype extensionality
for the second equation. The counit is exactly the previously published
`nondegeneratePartInclusion hA`, as an equality of natural transformations.
The unit sends each vector of a nondegenerate object to itself in its
part. The construction requires only `NonUnitalRing A` and
`hA : IsIdempotented A`. It does not assume a unit-action law, nontriviality,
a field, finite generation, finite dimension, closure certificates, an
abelian structure on the nondegenerate category, or an adjunction.
Ring and bundled-carrier universes are independent. Complete unapplied
interfaces check the unbundled factorization, its evaluation,
factorization and uniqueness laws with three independent universes.
They also check the bundled Hom equivalence, its two evaluation laws,
the actual adjunction, the counit equality and the unit evaluation law
at arbitrary ring and carrier universes. The complete Hom equivalence,
adjunction, counit and unit interfaces are also instantiated separately
at `(0,1)` and `(1,0)`.

This is internally derived infrastructure from David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
I.1.2, printed p.7/PDF13, defines the largest nondegenerate submodule of an
arbitrary original module. The next page, printed p.8/PDF14, specifies
restriction of an original map to the parts. A.V.2, printed p.259/PDF265,
describes adjunctions by natural Hom equivalences and their unit and counit.
These passages were read. This particular inclusion–part adjunction is
an internal consequence of those constructions, rather than a separately
numbered source assertion. It is not the completion adjunction from I.1.5.

The registered supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF1–3 and PDF18–19, was checked for the module conventions and Appendix A
corrections. It concerns the earlier edition and does not replace the
governing original. The public `notes/renard/appendix-a-corrections.md`
was also checked. The present construction does not use its defective
unrestricted abelian-subcategory criterion.

The nondegenerate abelian structure, closure and exactness theorems,
completion functor and its separate adjunction, and categorical
limit/colimit comparison theorems remain separate obligations.
