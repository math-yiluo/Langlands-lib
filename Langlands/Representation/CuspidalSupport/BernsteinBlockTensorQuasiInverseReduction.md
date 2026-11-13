# Renard VI.10.2: the evaluation `ev_τ` on a Bernstein block, and the tensor quasi-inverse from VI.10.1

Module `Langlands.Representation.CuspidalSupport.BernsteinBlockTensorQuasiInverseReduction`.
Namespace `Langlands.CuspidalSupport`. Universe parameters `uF uV`.
Worker 130 wrote this module for Task 5686, the proof of
`BernsteinBlockTensorQuasiInverseStatement`.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Worker 130 read
these pages for this unit:

- VI.10.1, Theorem and proof, printed p.208 / PDF p.214: `Π_Ω` is a finitely generated
  progenerator of `M(G)_Ω`.
- VI.10.2, printed p.208 / PDF p.214: `R_Ω = End_G(Π_Ω)`,
  `F_{Π_Ω}(π, V) = Hom_G(Π_Ω, π)` and `G_{Π_Ω}(M) = M ⊗_{R_Ω} Π_Ω`. Renard writes that
  the proof of the VI.4.1 Theorem "peut être recopiée mot pour mot". The Theorem says the two
  functors are quasi-inverse.
- VI.4.1, the Theorem and the first half of its proof, printed pp.150–151 / PDF
  pp.156–157. Printed p.150 defines "ev_E : Hom_G(Π, τ) ⊗_R V_Π → E, α ⊗ w ↦ α(w)". The
  proof shows that `ev_E` is an isomorphism, using presentations by direct sums of `V_Π`
  (Lemma A.VIII.2) and the diagram (VI.4.1.5).

## The definition

Fix `F`, `G`, `T`, `i`, `ν` and `family` with the instances of the published
`BernsteinBlockCoproducts`, and an inertial class
`s : BernsteinInertialClass.{uF, max uF uV} i ν family`. For objects `P` and `τ` of the
published block `BernsteinSaturatedBlock i ν family s`,

`bernsteinSaturatedBlockTensorEvaluation i ν family s P τ : (P ⟶ τ) ⊗[ℤ] P.obj →ₗ[ℤ] τ.obj`

is the `ℤ`-linear map with `α ⊗ₜ w ↦ SmoothRep.hom α.hom w` (simp lemma
`bernsteinSaturatedBlockTensorEvaluation_tmul`). It is
`SmoothRep.fullSubcategoryTensorEvaluation P τ` from
`Langlands.Representation.Category.GeneratorTensorEvaluation`, that is,
`TensorProduct.lift` of the bilinear pairing `(α, w) ↦ α(w)`.

Correspondence with Renard. Renard's `Π_Ω` is `P` and his `(π, V)` is `τ`, with
underlying space `τ.obj`. `Hom_G(Π_Ω, π)` is the group of block morphisms `P ⟶ τ`; these
are the smooth `G`-morphisms, because the block is a full subcategory. Renard tensors over
`R_Ω = End_G(Π_Ω)`, while the Lean map is on the tensor product over `ℤ`. The latter
surjects onto the tensor product over `R_Ω`, with kernel the span of the balancing elements
`(r ≫ α) ⊗ w - α ⊗ r(w)`, `r : End P`. The Lean map kills these elements, so it is Renard's
evaluation composed with that surjection. Bijectivity of Renard's evaluation is therefore
the statement that the Lean map is onto with kernel exactly the balancing span. That is the
formulation of `BernsteinBlockTensorQuasiInverseStatement`.

## What the module proves

Beyond the definition, the module **reduces** the target to the published VI.10.1 and
VI.10.2 statements. It proves the target **only conditionally**: those statements remain
explicit hypotheses.

- `bernsteinSaturatedBlockTensorEvaluation_surjective_and_ker`: let `P` be an object of the
  block. Suppose `P` lifts every morphism `P ⟶ Z` along every epimorphism `Y ⟶ Z` of the
  block, and that for all `f ≠ g : X ⟶ Y` in the block some `h : P ⟶ X` has
  `h ≫ f ≠ h ≫ g`. These are the projectivity and generator conjuncts of
  `BernsteinInducedProgeneratorStatement`, in its own words. Then for every object `τ`,
  `bernsteinSaturatedBlockTensorEvaluation i ν family s P τ` is surjective, and its kernel
  is the `ℤ`-span of the elements `(r ≫ α) ⊗ₜ w - α ⊗ₜ SmoothRep.hom r.hom w`, for
  `r : End P`, `α : P ⟶ τ` and `w : P.obj`.
- `exists_bernsteinSaturatedBlockTensorEvaluation`: the same result in existential form, in
  the exact shape of the target's conclusion for `τ`, with witness the definition above.
- `projective_and_generator_of_isEquivalence_preadditiveCoyonedaObj`: if
  `preadditiveCoyonedaObj P` (the functor `Hom(P, •)` to right `End P`-modules) is an
  equivalence, then `P` has both properties above.
- `bernsteinBlockTensorQuasiInverse_of_inducedProgenerator`:
  `BernsteinInducedProgeneratorStatement.{uF, uV}` implies
  `BernsteinBlockTensorQuasiInverseStatement.{uF, uV}`. The two statements have the same
  quantifiers, premises, universes and object `Π_Ω`. The block-membership witness `hmem`
  is passed on unchanged. The finite-generation conjunct is not used.
- `bernsteinBlockTensorQuasiInverse_of_homEquivalence`:
  `BernsteinBlockHomEquivalenceStatement.{uF, uV}` implies
  `BernsteinBlockTensorQuasiInverseStatement.{uF, uV}`, again with the same quantifiers,
  premises, universes and `hmem`.

No premise is added in either implication.

## Proof

**Projective separator.** From the lifting hypothesis, `P` is `Projective` in the block:
the Mathlib structure asks for exactly that lift. From the generator hypothesis, `P` is an
`IsSeparator`. With `isSeparator_def`, suppose `h ≫ f = h ≫ g` for all `h : P ⟶ X`. If
`f ≠ g`, the hypothesis gives an `h` with `h ≫ f ≠ h ≫ g`, a contradiction.

**Evaluation.** The block property `bernsteinSaturatedBlockProperty i ν family s` is a Serre
class, hence closed under subobjects and quotients. It is also closed under finite products.
These are the published global instances `bernsteinSaturatedBlockProperty_isSerreClass`
and `bernsteinSaturatedBlockProperty_isClosedUnderFiniteProducts` of
`BernsteinBlockCoproducts`. So `SmoothRep.fullSubcategoryTensorEvaluation_surjective_and_ker`
applies to the block and to the projective separator `P`. It proves the surjectivity and
kernel assertion. That helper argues elementwise as follows.

- Surjectivity: the images of all `α : P ⟶ τ` generate `τ`. The quotient of `τ` by their sum
  receives only zero maps from the projective `P`, so the quotient map is zero, because `P`
  is a separator.
- Kernel: a tensor `∑_s α_s ⊗ w_s` killed by `ev` gives an element of the kernel of the map
  `⨁_s P → τ`. That kernel lies in the block and is generated by images of `P`, which are
  sent to sums of balancing elements.

**From an equivalence.** An equivalence is a left adjoint, so it preserves epimorphisms.
The adjunction is `(preadditiveCoyonedaObj P).asEquivalence.toAdjunction`, passed to
`Functor.preservesEpimorphisms_of_adjunction`. Mathlib's
`Projective.projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj` turns this into
`Projective P`, and `Projective.factorThru` gives the lifts. An equivalence is also
faithful, and Mathlib's `isSeparator_iff_faithful_preadditiveCoyonedaObj` makes `P` a
separator. If `f ≠ g` but every `h : P ⟶ X` had `h ≫ f = h ≫ g`, then `isSeparator_def`
would give `f = g`.

**Statement level.** Both implications introduce the binders of the target. They apply the
hypothesis to the same data and obtain `hmem` together with the projectivity and generator
conjuncts, or with the equivalence. They return the same `hmem` and apply
`exists_bernsteinSaturatedBlockTensorEvaluation` to `P = ⟨Π_Ω, hmem⟩` and every `τ`. The
binders, the `haveI`/`letI` instances and the `let` of `Π_Ω` are the same in all three
statements, so the hypothesis applies verbatim.

## Provenance

This is an internal derived unit. Renard argues as follows (printed pp.150–151, applied to
`Π_Ω` by VI.10.2). The composite `G_Π ∘ F_Π` is right exact and commutes with direct sums,
and `ev` is the isomorphism `R ⊗_R V_Π ≅ V_Π` for `τ = Π`. Every `τ` in the block has a
presentation `⊕_I V_Π → ⊕_J V_Π → E → 0` (Lemma A.VIII.2), and the five lemma on (VI.4.1.5)
concludes. The implemented route uses only that `Π_Ω` is a projective separator of the
block. It argues elementwise with finite biproducts, through the helper module of
`Langlands.Representation.Category.GeneratorTensorEvaluation`, so it needs neither
smallness nor right exactness of the tensor product. The same route is used for the VI.4.1
analogue in `RationalSummandTensorQuasiInverseReduction`. The second half of Renard's
proof, that `θ_M : M → Hom_G(Π_Ω, M ⊗_{R_Ω} Π_Ω)` is an isomorphism, is not stated by the
target and is not proved here.

## Status

The result is conditional on `BernsteinInducedProgeneratorStatement` (VI.10.1) or on
`BernsteinBlockHomEquivalenceStatement` (VI.10.2). Neither has an unconditional proof in the
Library; their proof task is 2174cd68-b110-4f86-b992-28712c29d35f. Once an unconditional
proof of either is published, composing it with this module proves
`BernsteinBlockTensorQuasiInverseStatement`.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.CuspidalSupport.BernsteinBlockTensorQuasiInverseStatement` | the target statement |
| `Langlands.Representation.CuspidalSupport.BernsteinBlockHomEquivalenceReduction` | transitively `BernsteinInducedProgeneratorStatement`, `BernsteinBlockHomEquivalenceStatement` and `BernsteinBlockCoproducts` (the Serre-class and finite-product instances of the block) |
| `Langlands.Representation.Category.GeneratorTensorEvaluation` | `SmoothRep.fullSubcategoryTensorEvaluation`, its `_tmul` lemma and `SmoothRep.fullSubcategoryTensorEvaluation_surjective_and_ker` |
| `Mathlib.CategoryTheory.Preadditive.Yoneda.Projective` | `projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj` |
| `Mathlib.CategoryTheory.Generator.Preadditive` | `isSeparator_iff_faithful_preadditiveCoyonedaObj` |
