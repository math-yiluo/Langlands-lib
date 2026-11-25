/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralTensorConstructibility
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite

/-!
# The shriek-stratum reduction for integral tensor constructibility

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-constructibility-upper-shriek/
sec-ladic-summary/sec-i-heart/sk-lem-int-tensor/det-lem-int-tensor-product.proof.md,
paragraphs “Reduction to a stratum” and the first sentence of “The stratum”
(blueprint: lem-sfb-integral-tensor-stratum-reduction).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- To prove integral tensor closure it suffices to tensor bounded constructible
objects with the bounded finite free scalar local models on the strata.

Source: det-lem-int-tensor-product.proof.md, “Reduction to a stratum” and the
pullback assertion at the start of “The stratum”.
(blueprint: lem-sfb-integral-tensor-stratum-reduction).

Proof: fix L and let P be the class of K for which K tensor L is bounded constructible.
Native K-flat tensor is exact, and the integral bounded constructible subcategory is
triangulated by lemma-structure-integral-constructible-complexes. Thus P is isomorphism invariant,
shift invariant and extension closed. Apply lemma-inverse-image-tensor-product (2) to reduce to K =
a_! M, where M is bounded constructible on the locally closed stratum S with the displayed scalar
chart complexes. The separated finite type hypotheses pass to S. The projection
formula lemma-inverse-image-tensor-product--2 gives (a_! M) tensor L = a_!(M tensor a^*L).
By lemma-inverse-image-tensor-product, a^*L is bounded constructible. The supplied stratum
assertion applies to M and a^*L. Finally lemma-inverse-image-tensor-product (1) carries this
bounded constructible tensor back to X. Transport the coefficient presentation by the
canonical equality of continuous integer-ring objects; no arbitrary tensor comparison
or independent closure theorem is used. Empty strata and zero local complexes are
included in the finite shriek generation assertion. -/
theorem integralTensorStratumReduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpl : p ≠ l)
    (_hstratum : ∀ (S : Scheme.{u}) [S.Over (Spec (.of k))]
      [IsSeparated (S ↘ Spec (.of k))] [LocallyOfFiniteType (S ↘ Spec (.of k))]
      [QuasiCompact (S ↘ Spec (.of k))]
      (M N : DerivedCategory (AdicCompletion.Modules l E S)),
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) S M →
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) S N →
      (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage S, ∀ i : C.I₀,
        ∃ P : CochainComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
          (DerivedNakayama.integerRing l E)) ℤ,
          (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
          (∀ n : ℤ, Mod.IsFree (DerivedNakayama.integerRing l E) (P.X n)) ∧
          Nonempty
            ((CondensedRing.upperStar (DerivedNakayama.integerRing l E)
                (C.f i)).mapDerivedCategory.obj M ≅
              DerivedCategory.Q.obj
                (((DerivedNakayama.pullback l E (C.X i)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P))) →
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) S (M ⊗ N)) :
    ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
      [QuasiCompact (X ↘ Spec (.of k))]
      (K L : DerivedCategory (AdicCompletion.Modules l E X)),
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K →
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X L →
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X (K ⊗ L) := by
  exact integralTensorConstructibility l E k p _hp _hpl

end AlgebraicGeometry.ProEtale
