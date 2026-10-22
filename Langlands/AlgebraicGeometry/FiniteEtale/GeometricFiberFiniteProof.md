# Finiteness of the actual geometric fibres of finite étale covers

`Langlands.AlgebraicGeometry.FiniteEtale.geometricFiberFinite` proves exactly the
published target `GeometricFiberFinite s` from
`Langlands.AlgebraicGeometry.FiniteEtale.Statements`. Its parameters are the same as
the statement's: `S : Scheme.{u}`, `Ω : Type u` with `Field Ω` and `IsAlgClosed Ω`,
and `s : Spec (.of Ω) ⟶ S`. The conclusion is that for every `Y : Cover S`, the type
`Fiber s Y` is `Finite`. These are the actual morphisms `Over.mk s ⟶ Y.obj` in the
slice over `S`, including their commutativity equations. The proof assumes no finiteness
of fibres, connectedness or local noetherianity. The statement pair and its imports are
unchanged.

## Helper: sections of a finite morphism to the spectrum of a field

`finite_sections_of_isFinite` takes a scheme `X : Scheme.{u}`, a field `K : Type u`, and a
finite morphism `f : X ⟶ Spec (.of K)` (`[IsFinite f]`). It proves that the subtype
`{x : Spec (.of K) ⟶ X // x ≫ f = 𝟙 _}` of sections of `f` is finite. The Lean proof
runs as follows.

1. A finite morphism is affine and `Spec K` is affine, so `X` is affine
   (`isAffine_of_isAffineHom`).
2. Let `e = Scheme.ΓSpecIso (.of K)`, the identification of `Γ(Spec K, ⊤)` with `K`.
   The ring map `e.inv ≫ f.appTop` makes `Γ(X, ⊤)` a `K`-algebra. This map is finite.
   Mathlib's `Scheme.Hom.finite_appTop` makes `f.appTop` finite, an isomorphism is
   surjective and hence finite, and `RingHom.Finite.comp` composes the two. So
   `Γ(X, ⊤)` is a finite `K`-module. Over a field it is also free.
3. Each section `x` gives the ring map `x.appTop ≫ e.hom : Γ(X, ⊤) → K`. This is a
   `K`-algebra map. Since `x ≫ f = 𝟙`, `Scheme.Hom.comp_appTop` gives
   `f.appTop ≫ x.appTop = 𝟙`, and hence `e.inv ≫ f.appTop ≫ x.appTop ≫ e.hom = 𝟙`.
4. The assignment from sections to `Γ(X, ⊤) →ₐ[K] K` is injective. If two sections give
   the same algebra map, cancelling the isomorphism `e.hom` gives equal `appTop`. Then
   `ext_of_isAffine` shows the sections are equal, because the target `X` is affine.
5. Mathlib's instance `Finite.algHom` says that algebra maps from a finite free
   `K`-algebra to a domain form a finite set. It rests on linear independence of
   distinct algebra maps. `Finite.of_injective` then gives the claim.

This step uses only that `f` is finite. It needs neither étaleness nor algebraic closure.

## Main theorem

Fix `Y : Cover S`. The scheme-theoretic fibre is `pullback Y.obj.hom s`. Its second
projection `pullback.snd Y.obj.hom s` is finite by Mathlib's base-change instance for
`IsFinite`, since `Y.obj.hom` is finite. The published
`fiberEquivPoints s Y` from `Langlands.AlgebraicGeometry.FiniteEtale.Definitions`
identifies `Fiber s Y` with morphisms over `Spec Ω` from the identity to this projection.
Taking the underlying morphism `(fiberEquivPoints s Y x).left` gives a section of the
projection. Its section equation `p ≫ pullback.snd Y.obj.hom s = 𝟙 _` is the slice
equation `Over.w`, after simplification. This map from `Fiber s Y` to sections is
injective. Equal underlying morphisms give equal slice morphisms by
`Over.OverMorphism.ext`, and `fiberEquivPoints s Y` is an equivalence. The helper applied
to the projection then makes `Fiber s Y` finite by `Finite.of_injective`.

The argument uses only the finiteness half of `Cover`. The étale condition and
`IsAlgClosed Ω` belong to the statement's signature but are not used in the proof.
The bound it implicitly gives, at most the `Ω`-dimension of the fibre's global sections,
is not stated.

## Provenance

This is an internal proof of the derived prerequisite isolated in the statement module.
That module cites Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary
version, Chapter X §3, Definition (10.25), printed p.150 (PDF p.154). There the functor
`F_x̄` on finite étale coverings is valued in sets: it sends a covering to its geometric
points over `x̄`. The source does not prove at that point that these sets are finite.
The statement module isolates that finiteness as a separate derived target. The Lean
proof is internal: it counts algebra maps out of the finite algebra of global sections of
the fibre. It imports the published definitions and statement by Lean name and adds no
axioms or instances.

Worker 239 authored this proof pair.
