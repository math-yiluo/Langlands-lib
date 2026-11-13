# Tensor evaluation for a projective separator of smooth representations

Module `Langlands.Representation.Category.GeneratorTensorEvaluation`.
Namespace `Langlands.SmoothRep`. Universe parameters `uR uG uV`.
Worker 143 wrote this helper module for Task 5607, the proof of
`Langlands.CuspidalSupport.RationalSummandTensorQuasiInverseStatement`
(Renard VI.4.1, the quasi-inverse (VI.4.1.4)).

## Setting

- `R` is a commutative ring and `G` a topological group.
- `p : ObjectProperty (SmoothRep.{uR, uG, uV} R G)` is a property of smooth
  representations. Its full subcategory `p.FullSubcategory` carries Mathlib's
  full-subcategory category and preadditive structures.
- A morphism `f : X ⟶ Y` of the full subcategory has an underlying smooth
  morphism `f.hom`. `SmoothRep.hom f.hom` is its underlying intertwining map.

## Declarations

- `fullSubcategoryAddHom p f : X.obj →+ Y.obj`: the underlying additive map of a
  morphism of the full subcategory.
- `traceSubrepresentation p P X`: the trace of `P` in `X`. It is the invariant
  submodule `⨆ α : P ⟶ X, range (hom α.hom)`, the sum of the images of all
  morphisms `P ⟶ X`. Invariance holds because each `hom α.hom` is an
  intertwining map.
- `exists_kernel_element [p.IsClosedUnderSubobjects] f x hx` gives elementwise
  kernels. If `hom f.hom x = 0` for `f : X ⟶ Z`, then `x` comes from an element of
  the actual kernel subrepresentation `SmoothRep.kernel f.hom`. That kernel lies
  in `p`, since `p` is closed under subobjects and the inclusion is a
  monomorphism. Its inclusion `ι` satisfies `ι ≫ f = 0`.
- `mem_closure_of_projective_isSeparator [p.IsClosedUnderQuotients] P hP X x`:
  let `P` be a projective (`[Projective P]`) separator (`IsSeparator P`) of the
  full subcategory. Then every element of every object `X` lies in
  `AddSubgroup.closure {hom α.hom w | α : P ⟶ X, w ∈ P}`.
- `fullSubcategoryTensorEvaluation P Y : (P ⟶ Y) ⊗[ℤ] P.obj →ₗ[ℤ] Y.obj` is the
  evaluation `α ⊗ₜ w ↦ SmoothRep.hom α.hom w`, for any objects `P` and `Y` of the
  full subcategory. It is the abstract `Langlands.Renard.tensorEvaluation` with
  `V X = X.obj` and `u f = fullSubcategoryAddHom p f`, that is,
  `TensorProduct.lift` of the `ℤ`-bilinear pairing `(α, w) ↦ α(w)`. The simp
  lemma `fullSubcategoryTensorEvaluation_tmul` records its value on pure tensors.
- `fullSubcategoryTensorEvaluation_surjective_and_ker` is the main theorem.
  Assume `[p.IsClosedUnderSubobjects] [p.IsClosedUnderQuotients]
  [p.IsClosedUnderFiniteProducts]`, a projective separator `P` and any object
  `Y`. Then `fullSubcategoryTensorEvaluation P Y` is surjective, and its kernel
  is the `ℤ`-span of
  `(q.1 ≫ q.2.1) ⊗ₜ q.2.2 - q.2.1 ⊗ₜ SmoothRep.hom q.1.hom q.2.2` over
  `q : End P × (P ⟶ Y) × P.obj`.
- `exists_tensorEvaluation_of_projective_isSeparator` packages the main theorem
  existentially, with the same hypotheses: there is a `ℤ`-linear
  `ev : (P ⟶ Y) ⊗[ℤ] P.obj → Y.obj` with `ev (α ⊗ₜ w) = SmoothRep.hom α.hom w`
  that is surjective with kernel that span. The witness is
  `fullSubcategoryTensorEvaluation P Y`. This conclusion has exactly the shape
  of the conclusion of `RationalSummandTensorQuasiInverseStatement`, applied
  to the block.

## Proof

**Generation (`mem_closure_of_projective_isSeparator`).** Let `S` be the trace
of `P` in `X`. The trace's carrier is an `iSup` of ranges, so by
`Submodule.iSup_induction` it lies in the additive closure of the elements
`α(w)`. It therefore suffices to show `x ∈ S`. The quotient
`Q = SmoothRep.quotient X.obj S` lies in `p` (closure under quotients, since
`SmoothRep.mkQ` is an epimorphism by `SmoothRep.epi_iff_surjective`). Call
`q : X ⟶ Q` the quotient map in the full subcategory. It is an epimorphism
there, by `Functor.epi_of_epi_map` for the inclusion functor. Every
`β : P ⟶ Q` is zero: by projectivity, `β = Projective.factorThru β q ≫ q`, and
the image of `factorThru β q` lies in `S`. Because `P` is a separator,
`Preadditive.isSeparator_iff` then gives `q = 0`. Hence the class of `x` in `Q`
vanishes, i.e. `x ∈ S`.

**Main theorem.** Mathlib's `HasFiniteBiproducts.of_hasFiniteProducts` gives
finite biproducts in the preadditive full subcategory, which has finite products
by closure under finite products. The theorem then applies the abstract
`Langlands.Renard.tensorEvaluation_surjective_and_ker` with `V X = X.obj`,
`u f = fullSubcategoryAddHom p f`, the elementwise generation above and the
elementwise kernels `exists_kernel_element`. The identity, composition and
addition compatibilities hold by `rfl`. The value on pure tensors is
`Langlands.Renard.tensorEvaluation_tmul`, and the existential version combines
these two facts with the witness `fullSubcategoryTensorEvaluation P Y`.

## Provenance

This is an internal helper. It does not correspond to a single statement in the
literature. It specializes the abstract module to smooth representations, for
use in Renard VI.4.1 (proof of the Theorem, printed pp.150–151 / PDF pp.156–157
of `renard-2026-representations-groupes-reductifs-padiques`). There, `ev_E`
is shown to be an isomorphism for a projective generator `Π` of the block. The
route is elementwise, as explained in the abstract module's Markdown.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.CategoryTheory.Renard.GeneratorTensorEvaluation` | the abstract `tensorEvaluation`, `tensorEvaluation_tmul` and `tensorEvaluation_surjective_and_ker` |
| `Langlands.Representation.Category.Abelian` | `SmoothRep.mono_iff_injective`, `SmoothRep.epi_iff_surjective` and the preadditive structure |
| `Langlands.Representation.Category.Subquotients` | `SmoothRep.kernel`, `SmoothRep.kernelι`, `SmoothRep.quotient`, `SmoothRep.mkQ` |
| `Langlands.Representation.Category.ExactFunctor` | `SmoothRep.hom_ext'` |
| `Mathlib.CategoryTheory.ObjectProperty.EpiMono` | `prop_of_mono`, `prop_of_epi` |
| `Mathlib.CategoryTheory.ObjectProperty.FiniteProducts` | finite products of the full subcategory |
| `Mathlib.CategoryTheory.Generator.Preadditive` | `Preadditive.isSeparator_iff` |
| `Mathlib.CategoryTheory.Preadditive.Projective.Basic` | `Projective`, `Projective.factorThru` |
