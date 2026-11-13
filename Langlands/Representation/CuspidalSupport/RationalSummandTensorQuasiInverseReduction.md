# Renard VI.4.1: the evaluation `ev_E`, and the quasi-inverse (VI.4.1.4) from the Theorem

Module `Langlands.Representation.CuspidalSupport.RationalSummandTensorQuasiInverseReduction`.
Namespace `Langlands.CuspidalSupport`. Universe parameters `uF uV`.
Worker 143 wrote this module for Task 5607, the proof of
`RationalSummandTensorQuasiInverseStatement`.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Locator: VI.4.1, the functors (VI.4.1.3) and (VI.4.1.4), the Theorem and its
proof, printed pp.150–151 / PDF pp.156–157. Worker 143 read these pages for
this unit. The evaluation is defined on printed p.150 (PDF p.156):
"ev_E : Hom_G(Π, τ) ⊗_R V_Π → E, α ⊗ w ↦ α(w)", with `R = End_G(Π)`.

## The definition

`rationalInertiaBlockTensorEvaluation G π P τ : (P ⟶ τ) ⊗[ℤ] P.obj →ₗ[ℤ] τ.obj`
is defined for any objects `P` and `τ` of the actual inertia block
`RationalInertiaBlock G π`. It is the `ℤ`-linear map with
`α ⊗ₜ w ↦ SmoothRep.hom α.hom w` (simp lemma
`rationalInertiaBlockTensorEvaluation_tmul`). It is
`SmoothRep.fullSubcategoryTensorEvaluation P τ` from the helper module
`Langlands.Representation.Category.GeneratorTensorEvaluation`, i.e.
`TensorProduct.lift` of the bilinear pairing `(α, w) ↦ α(w)`.

Correspondence with Renard. Renard's `Π` is `P`, his `(τ, E)` is `τ` with
underlying space `τ.obj`, and `Hom_G(Π, τ)` is the group of block morphisms
`P ⟶ τ`. These are the smooth `G`-morphisms, because the block is a full
subcategory. Renard tensors over `R = End_G(Π)`. The Lean map is on the tensor
product over `ℤ`, which surjects onto the tensor product over `R`; the kernel of
that surjection is the span of the balancing elements
`(r ≫ α) ⊗ w - α ⊗ r(w)`, `r : End P`. The Lean map kills these elements, so it
is Renard's `ev_E` composed with that surjection. Bijectivity of `ev_E` is
therefore the statement that the Lean map is onto with kernel exactly the
balancing span. This is the formulation of `RationalSummandTensorQuasiInverseStatement`.

## What the module proves

Beyond the definition, this module **reduces** the quasi-inverse statement to
the published VI.4.1 Theorem. It does **not** prove either one
unconditionally. Both the Theorem and the Proposition remain explicit
hypotheses.

- `projective_of_isEquivalence_preadditiveCoyonedaObj`: let `P` be an object of
  the actual inertia block `RationalInertiaBlock G π`. If
  `preadditiveCoyonedaObj P` (the functor `Hom(P, •)` to right `End P`-modules)
  is an equivalence, then `P` is projective in the block.
- `isSeparator_of_isEquivalence_preadditiveCoyonedaObj`: under the same
  hypothesis, `P` is a separator of the block.
- `rationalInertiaBlockTensorEvaluation_surjective_and_ker`: under the same
  hypothesis, for every object `τ` of the block,
  `rationalInertiaBlockTensorEvaluation G π P τ` is surjective, and its kernel is
  the `ℤ`-span of the balancing elements
  `(r ≫ α) ⊗ₜ w - α ⊗ₜ SmoothRep.hom r.hom w`, with `r : End P`. Here `G` is any
  affine group scheme locally of finite type over a nonarchimedean local field,
  `π` is any smooth representation and `P` is any block object.
- `exists_tensorEvaluation_of_isEquivalence_preadditiveCoyonedaObj`: the same
  result in existential form, with witness the definition above. There is a
  `ℤ`-linear `ev : (P ⟶ τ) ⊗[ℤ] P.obj → τ.obj` with
  `ev (α ⊗ₜ w) = SmoothRep.hom α.hom w`, surjective with kernel that span.
- `rationalSummandTensorQuasiInverse_of_homEquivalence`:
  `RationalSummandHomEquivalenceStatement.{uF, uV}` implies
  `RationalSummandTensorQuasiInverseStatement.{uF, uV}`. The two statements
  have the same quantifiers, premises and universes, and the same block
  membership `∃ hmem`. No premise is added.
- `rationalSummandTensorQuasiInverse_of_smallProgenerator`:
  `RationalSummandSmallProgeneratorStatement.{uF, uV}` (the VI.4.1 Proposition)
  implies the quasi-inverse statement. It composes the published
  `rationalSummandHomEquivalence_of_smallProgenerator` with the previous theorem.

## Proof

**Projectivity.** An equivalence is a left adjoint, so it preserves
epimorphisms. The adjunction is `(preadditiveCoyonedaObj P).asEquivalence.toAdjunction`,
and `Functor.preservesEpimorphisms_of_adjunction` applies to it. Mathlib's
`Projective.projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj` turns
this into `Projective P`. The adjunction is passed explicitly because instance
search for the left-adjoint route timed out.

**Separator.** An equivalence is faithful (`IsEquivalence.faithful`). Mathlib's
`isSeparator_iff_faithful_preadditiveCoyonedaObj` turns this into
`IsSeparator P`.

**Evaluation.** The block property is closed under subobjects and quotients
(Serre class) and under finite products. These are the local instances
`rationalSummandTensorQuasiInverseSerreClass` and
`rationalSummandTensorQuasiInverseFiniteProducts`, described below. So the
helper theorem
`Langlands.SmoothRep.fullSubcategoryTensorEvaluation_surjective_and_ker` (module
`Langlands.Representation.Category.GeneratorTensorEvaluation`) applies to the
block and to the projective separator `P`. It gives
`rationalInertiaBlockTensorEvaluation_surjective_and_ker`. Together with
`rationalInertiaBlockTensorEvaluation_tmul`, this is literally the existential
conclusion required for `τ`.

That helper rests on the abstract
`Langlands.Renard.tensorEvaluation_surjective_and_ker` (module
`Langlands.CategoryTheory.Renard.GeneratorTensorEvaluation`). Surjectivity holds
because the images of all `α : P ⟶ τ` generate `τ`: the quotient by their sum
receives only zero maps from the projective `P`, so it vanishes, `P` being a
separator. For the kernel, a tensor `∑_s α_s ⊗ w_s` killed by `ev` gives an
element of the kernel of `⨁_s P → τ`. That kernel lies in the block and is
generated by images of `P`, and these images are sent to sums of balancing
elements.

**Statement level.** `rationalSummandTensorQuasiInverse_of_homEquivalence`
introduces the binders of the target. As in the published
`rationalSummandHomEquivalence_of_smallProgenerator`, it restores the instances
that the statement provides through `haveI`: `hG.isAffineHom`, affineness of
`G.X.left`, and `hG.smooth`. It applies the Theorem to the same data, obtaining
`hmem` and the equivalence. It then supplies the same `hmem` and applies the
objectwise result to `P = ⟨_, hmem⟩` and every `τ`.

## Block instances and the import constraint

The Serre-class and finite-product instances of `rationalInertiaBlockProperty G π`
are restated as local instances under module-specific names. They come from
`SmoothRep.irreducibleSubquotientsProperty_isSerreClass` and
`SmoothRep.irreducibleSubquotientsProperty_isClosedUnderFiniteProducts`, as in
the published `RationalSummandHomEquivalenceReduction`. The published global
instances live in `RationalInertiaPresentations`, which cannot be imported
together with the VI.4.1 statement modules: both declare the same automatically
named local topology instance. The additive structure on the block is Mathlib's
full-subcategory one throughout. This is the structure used by
`preadditiveCoyonedaObj` in the Theorem and by `P ⟶ τ` and `End P` in the
target.

## Provenance

This is an internal derived unit. Renard proves the quasi-inverse assertion
(printed pp.150–151) as follows. `F = G_Π ∘ F_Π` is right exact and commutes
with direct sums; `ev_{V_Π}` is the isomorphism `R ⊗_R V_Π ≅ V_Π`; every `E`
in the block has a presentation `⊕_I V_Π → ⊕_J V_Π → E → 0` (Lemma A.VIII.2);
the five lemma on (VI.4.1.5) then shows that `ev_E` is an isomorphism. The
implemented route uses only that `Π` is a projective separator of the abelian
block. It argues elementwise with finite biproducts, as described above, so it
needs neither smallness of `Π` nor right exactness of the tensor product. It
proves exactly the target's formulation: `ev` on `Hom(Π, τ) ⊗_ℤ V_Π` is onto
with kernel the balancing span, which is bijectivity of
`Hom_G(Π, τ) ⊗_R V_Π → E`. The second half of Renard's proof, that
`θ_M : M → Hom_G(V_Π, M ⊗_R V_Π)` is an isomorphism, is not stated by the
target and is not proved here.

## Status

The result is conditional on `RationalSummandHomEquivalenceStatement` (or on
`RationalSummandSmallProgeneratorStatement`). The Library proves these only
from further hypotheses, such as the joint special compact basis. Once an
unconditional proof of either is published, composing it with this module
proves `RationalSummandTensorQuasiInverseStatement`.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.CuspidalSupport.RationalSummandTensorQuasiInverseStatement` | the target statement |
| `Langlands.Representation.CuspidalSupport.RationalSummandHomEquivalenceReduction` | `rationalSummandHomEquivalence_of_smallProgenerator`; transitively `RationalSummandHomEquivalenceStatement`, `RationalSummandSmallProgeneratorStatement` and `ConstituentSerre` |
| `Langlands.Representation.Category.GeneratorTensorEvaluation` | `SmoothRep.fullSubcategoryTensorEvaluation`, its `_tmul` lemma and `SmoothRep.fullSubcategoryTensorEvaluation_surjective_and_ker` |
| `Mathlib.CategoryTheory.Preadditive.Yoneda.Projective` | `projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj` |
| `Mathlib.CategoryTheory.Generator.Preadditive` | `isSeparator_iff_faithful_preadditiveCoyonedaObj` |
