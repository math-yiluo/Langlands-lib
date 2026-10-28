# Canonical strong symmetric monoidal scheme-module pullback

For every morphism `f : X ⟶ Y` of schemes in universe `u`, this module
constructs a strong monoidal and braided structure on the existing functor
`F = Scheme.Modules.pullback f : Y.Modules ⥤ X.Modules`. Both module
categories carry the symmetric monoidal structures of `TensorMonoidal`.
Consequently `pullbackBraided f` supplies symmetric monoidal pullback.
There is no assumed preservation, invertibility, or coherence instance.

The two tensor conventions are retained. Write `T(M,N) = tensorObj M N`
for the explicit sheafification of the presheaf tensor, and
`c_X(M,N) = localizedTensorIso X M N` for the isomorphism from `M ⊗ N`
to `T(M,N)`. The instance `pullbackTensorComparison_isIso f` applies the
published unconditional theorem `pullbackTensorComparisonIsIso` to the
fixed canonical comparison natural transformation. Its components are
isomorphisms, giving

`pullbackTensorIso f M N : F(T(M,N)) ≅ T(FM,FN)`.

The forward map is exactly `pullbackTensorComparisonApp f M N`. The
localized comparison is also an isomorphism: by its published formula it is

`d_f(M,N) = F.map c_Y(M,N).hom ≫ pullbackTensorComparisonApp f M N ≫ c_X(FM,FN).inv`.

The resulting `localizedPullbackTensorIso f M N` goes from `F(M ⊗ N)`
to `FM ⊗ FN`, with forward map exactly `d_f(M,N)`.

The construction `pullbackOplaxMonoidal f` has unit map
`(pullbackUnitIso f).hom` and tensor map `d_f`. Naturality comes from the
published localized comparison natural transformation, specialized to
pairs consisting of a morphism and an identity. Associativity is precisely
the published theorem `localizedPullbackTensorAssociativity`.

The lemmas `localizedPullbackTensorLeftUnitor` and
`localizedPullbackTensorRightUnitor` transfer the published explicit unit
laws to the localized tensor. They expand the displayed formula for `d_f`,
replace the localized unitor by its comparison with the explicit unitor,
use naturality of `c_X`, and cancel its inverse and forward map. The
remaining equation is the respective published explicit pullback unit law.
Composing with the target unitor converts these forward equations into
Mathlib's inverse-unitor fields for an oplax monoidal functor.

The instance `pullbackMonoidal f` uses
`CategoryTheory.Functor.Monoidal.ofOplaxMonoidal` to invert these maps.
The four exported formulas `pullbackMonoidal_η`, `pullbackMonoidal_δ`,
`pullbackMonoidal_ε`, and `pullbackMonoidal_μ` identify its maps exactly:

- The oplax unit is `(pullbackUnitIso f).hom`.
- The oplax tensor map is `d_f(M,N)`.
- The lax unit is `(pullbackUnitIso f).inv`.
- The lax tensor map is `(localizedPullbackTensorIso f M N).inv`.

Finally, `localizedPullbackTensorSymmetry` proves
`d_f(M,N) ≫ β(FM,FN).hom = F.map β(M,N).hom ≫ d_f(N,M)`.
The proof cancels `c_X(FN,FM).hom`, uses the published comparison between
localized braiding and explicit factor swap, and applies the published
explicit symmetry equation. Cancelling the invertible `d_f(M,N)` converts
this equation into the lax braided-functor field of `pullbackBraided f`.
Its monoidal structure is exactly `pullbackMonoidal f`.

This is internal categorical infrastructure assembled from the genuine
sheaf-tensor constructions and their already proved canonical coherence
laws. The categorical conventions are those of the pinned Mathlib sources
`CategoryTheory/Monoidal/Functor.lean`, especially `OplaxMonoidal` and
`Monoidal.ofOplaxMonoidal`, and `CategoryTheory/Monoidal/Braided/Basic.lean`,
`Functor.Braided`. It asserts no separate external literature theorem.
Monoidality of the existing `pullbackId` and `pullbackComp` comparisons
remains a separate unit.
