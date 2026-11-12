# Renard I.2.3: the unital right adjoint and the closing Remark

Author: Worker 1222. Module `Langlands.Algebra.RenardForgetfulFunctorStatements`, namespace
`Langlands.Algebra.RenardForgetfulFunctor`. Entry proposition
`RenardForgetfulFunctorStatements : Prop`, the conjunction of
`UnitalCoextensionAdjunctionStatement` and `ForgetfulFunctorRemarkStatement`. Nothing is
proved here.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, I.2.3, printed pp.16–18 / PDF pp.22–24. The registered source ID is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Two assertions of I.2.3 had no published statement:

1. Printed p.16 / PDF p.22. For unital `ℂ`-algebras `A`, `B` and a unital morphism
   `φ : A → B`, the forgetful functor `φ_* : M(B) → M(A)`, `a · n := φ(a) · n`, has a left
   adjoint `M ↦ B ⊗_A M` and a right adjoint `φ^* : M ↦ Hom_A(B, M)`. Here `B` is a left
   `A`-module through `φ`, and `Hom_A(B, M)` is a `B`-module through right multiplication on
   `B`. The left adjoint is published as `ScalarExtensionAdjunctionStatements` (module
   `Langlands.Algebra.UnitalScalarExtensionAdjunctionStatements`, from A.V.2). This module
   states the right adjoint.
2. Printed p.18 / PDF p.24, the Remark closing I.2.3. In translation: suppose the
   `A`-bimodule structure of `B` comes from a morphism `φ : A → B` and is nondegenerate, so
   that for every finite family `(b_i)` of `B` there is an idempotent `e` of `A` with
   `φ(e) b_i = b_i φ(e) = b_i` for all `i`. Then the forgetful functor equals `φ_*` by
   (I.2.3.3). In other words `{φ(e), e ∈ Idem(A)}` is a filtering system of idempotents for
   `B` (Remark I.1.2). In particular the nondegenerate part of a `B`-module coincides with
   its nondegenerate part for the `A`-module structure given by the forgetful functor. For a
   nondegenerate `B`-module `N`, `Hom_B(B, N)_A = Hom_B(B, N)_B ≃ N`, so the pseudo-forgetful
   functor is in this case naturally isomorphic to the forgetful functor.

## `UnitalCoextensionAdjunctionStatement`

For rings `A : Type uA`, `B : Type uB` and a ring homomorphism `φ : A →+* B`, there is an
adjunction

`adj : ModuleCat.restrictScalars φ ⊣ ModuleCat.coextendScalars φ`

between `ModuleCat.{max uB uM} B` and `ModuleCat.{max uB uM} A`, such that for every
`g : φ_* N ⟶ M`, every `n ∈ N` and `b ∈ B`,

`(adj.homEquiv N M g).hom n b = g.hom (b • n)`.

- `ModuleCat.restrictScalars φ` is Mathlib's restriction of scalars, which is `φ_*`:
  `a • n = φ(a) • n`.
- `ModuleCat.coextendScalars φ` is Mathlib's coextension of scalars. Its value at `M` has
  carrier `B →ₗ[A] M`, with `B` an `A`-module through `φ`, and `B` acts by
  `(b • f)(b') = f(b' b)` (`ModuleCat.CoextendScalars.smul_apply`). This is Renard's
  `Hom_A(B, M)` with its `B`-module structure from right multiplication on `B`.
- The formula fixes the Hom bijection: a morphism `g : φ_* N → M` corresponds to
  `n ↦ (b ↦ g(b · n))`. Mathlib's `Adjunction` packages naturality in both variables.

The carrier universe is `max uB uM` because Mathlib's coextension of scalars is a functor
`ModuleCat.{max v uB} A ⥤ ModuleCat.{max v uB} B`. The source's unital `ℂ`-algebras are generalized to arbitrary
unital rings, as in the published left-adjoint statement. For `ℂ`-algebras nothing changes:
`A`-linear maps between unital modules over a unital `ℂ`-algebra are automatically
`ℂ`-linear.

## `ForgetfulFunctorRemarkStatement`

The statement quantifies over nonunital rings `A : Type uA`, `B : Type uB`, a proof
`hA : IsIdempotented A`, a nonunital ring homomorphism `φ : A →ₙ+* B`, and
`hφ : NonUnitalModuleRestrictScalars.HasTwoSidedLocalUnits φ`, the published form of the
source's hypothesis: every `s : Finset B` has an idempotent `e` of `A` with
`φ(e) b = b` and `b φ(e) = b` for `b ∈ s`. It asserts the conjunction of:

1. `IsIdempotented B`: `B` is a ring with idempotents, as the source's appeal to Remark I.1.2
   presupposes.
2. The filtering claim: every `s : Finset (Idempotent B)` has an idempotent `e` of `A` with
   `φ(e) f = f` and `f φ(e) = f` for `f ∈ s`. In the published order on idempotents
   (`Idempotent.le_iff_mul`) this says `f ≤ φ(e)`: every finite family of idempotents of `B`
   has an upper bound among the `φ(e)`, which is Renard's definition of a filtering system
   (Remark I.1.2, 2).
3. Coincidence of nondegenerate parts: for every additive group `M : Type uM` with a
   `NonUnitalModule B M` and every `m : M`, `m` is fixed by some idempotent of `B` if and
   only if it is fixed by `φ(e)` for some idempotent `e` of `A`. The right side is the
   action of `e` on `m` for the restricted structure `a • m = φ(a) • m`
   (`NonUnitalModuleRestrictScalars.module`). The membership condition of the published
   `nondegeneratePart` is exactly "fixed by some idempotent", so this is the coincidence of
   the two nondegenerate parts, stated elementwise and for every `B`-module.
4. `TensorForgetfulRemark A B hA φ hφ`. It installs on `B` the left `A`-action
   `a • b = φ(a) b` (`NonUnitalModuleRestrictScalars.module φ (NonUnitalModule.regular B)`)
   and the right regular action of `B` (`NonUnitalModule.rightRegular B`, `op b' • b = b b'`).
   It asserts that these actions commute (`ActionsCommute A B B`) and are two-sided
   nondegenerate (`IsNondegenerateBimodule A B B`), and that for all such proofs `hAB`,
   `hnd` there is a natural isomorphism

   `NondegenerateTensorFunctor.F hA hAB hnd ≅ NonUnitalModuleRestrictScalars.nondegenerateFunctor φ _`

   of functors from nondegenerate `B`-modules to nondegenerate `A`-modules, on carriers in
   `max uB uM`. Here `F` is the published `F_{AB} : N ↦ B ⊗_B N` of (I.2.3.1), and
   `nondegenerateFunctor φ _` is the published restriction `φ_*` on nondegenerate modules;
   its last argument is the left-local-unit consequence
   `HasTwoSidedLocalUnits.hasLeftLocalUnits φ hφ`.
5. `PseudoForgetfulRemark A B hA φ hφ`. It installs on `B` the right `A`-action
   `op a • b = b φ(a)` (`NonUnitalModuleRestrictScalars.module (NonUnitalRingHom.op φ)
   (NonUnitalModule.rightRegular B)`) and the left regular action of `B`. It asserts that
   these actions commute (`ActionsCommute B A B`) and are two-sided nondegenerate
   (`IsNondegenerateBimodule B A B`), and that for every such proof `hBA` there is a natural
   isomorphism

   `RenardHomFunctors.pseudoF hBA hA ≅ NonUnitalModuleRestrictScalars.nondegenerateFunctor φ _`

   on carriers in `max uB uM`. `pseudoF` is the published pseudo-forgetful functor
   `ˇF_{AB} : N ↦ Hom_B(B, N)_A` of (I.2.3.2), with `A` acting by `(a · ψ)(b') = ψ(b' φ(a))`.

The universe `max uB uM` is used in 4 and 5 because `F` and `ˇF` send carriers in `Type w`
to carriers in `Type (max uB w)`, while restriction preserves the carrier universe. In 3 the
carrier universe `uM` is arbitrary.

## Faithfulness notes

- The source's "the forgetful functor equals `φ_*`" is read as a natural isomorphism: `F`
  is defined as `B ⊗_B N`, which the source identifies with `N` through (I.2.3.3).
- The source states the Remark for the bimodule structures that `φ` induces on `B`. Items 4
  and 5 install exactly these structures. They also assert that the structures satisfy the
  hypotheses of the published `F` and `ˇF`, so the universal quantification over `hAB`,
  `hnd` and `hBA` is not vacuous. These are proof arguments of propositions, so the
  quantification only lets the statement name `F` and `ˇF` at these structures.
- `hA : IsIdempotented A` is an explicit hypothesis, as in the source's context ("anneaux à
  idempotents") and in the published `F` and `ˇF`. No hypothesis on `B` is assumed;
  item 1 derives that `B` is idempotented.
- No coefficient field is involved: the Remark concerns rings with idempotents and their
  additive modules, as in the published I.2.3 functors.

## Remaining obligations

The proof is a separate obligation. For the unital case Mathlib's
`ModuleCat.restrictCoextendScalarsAdj` has the required Hom formula
(`RestrictionCoextensionAdj.HomEquiv.fromRestriction_hom_apply_apply`). For the Remark the
source uses Lemma (I.2.3.3) (whose contraction `B ⊗_B N → N` is stated in
`Langlands.Algebra.RegularTensorContractionStatements`), the isomorphism (I.2.3.4) of a
nondegenerate `N` with the `B`-nondegenerate part of `Hom_B(B, N)`, and the coincidence of
nondegenerate parts.

## Provenance

Source assertions of Renard 2026 I.2.3: the right adjoint `φ^*` of `φ_*` in the unital case
(printed p.16 / PDF p.22) and the closing Remark (printed p.18 / PDF p.24). Formal choices:
Mathlib's restriction and coextension of scalars for the unital case, over arbitrary rings;
the published nonunital framework (`NonUnitalModuleRestrictScalars`,
`NondegenerateTensorFunctor.F`, `RenardHomFunctors.pseudoF`) for the Remark, with the
bimodule structures on `B` induced by `φ` written out explicitly.
