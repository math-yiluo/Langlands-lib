import Langlands.Algebra.NonUnitalModuleCornerEvaluation
import Langlands.Algebra.NonUnitalModuleIdempotentGenerated
import Langlands.Algebra.IdempotentAnnihilatorQuotient.NamedCarrier
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.ObjectProperty.EpiMono
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Renard I.3.2: simple modules and the equivalence criterion for `j_e`

Renard (9 July 2026), I.3.2, printed pp.21–22 / PDF pp.27–28. Proposition definitions for the
Proposition (`M ↦ e·M` is a bijection `Irr(A,e) → Irr(eAe)` with inverse
`W ↦ (A ⊗_{eAe} W)_e`) and for the Theorem (`j_e : M(A,e) → M(eAe)` is an equivalence iff
`M(A,e)` is stable under subquotients in `M(A)`, the category is then abelian, and the inverse is
corner induction). All objects are the published constructions.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalModuleCornerSimpleStatements

open CategoryTheory
open NonUnitalModuleCorner NonUnitalModuleCornerInduction NonUnitalModuleCornerEvaluation
open NonUnitalModuleIdempotentGenerated

attribute [local instance] rightCornerModule cornerModule tensorModule

universe uA uM uW

/-- Proposition of I.3.2, the map `M ↦ e·M`: for a simple object `M` of `M(A)` with `e·M ≠ 0`,
the fixed part `e·M` is a simple unital `eAe`-module. -/
def SimpleFixedPartStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (_hA : IsIdempotented A) (e : Idempotent A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M] (hM : IsNondegenerate A M),
    Simple (⟨NonUnitalModuleCat.of A M, hM⟩ : NondegenerateModuleCat.{uA, uM} A) →
    Nontrivial (FixedPart e M) →
    IsSimpleModule (Idempotent.Corner e) (FixedPart e M)

/-- Proposition of I.3.2, the map `W ↦ (A ⊗_{eAe} W)_e`: for a simple unital `eAe`-module `W`,
the published object `(A ⊗_{eAe} W)_e` of `M(A)` is simple and has nonzero fixed part. -/
def SimpleInducedQuotientStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A)
    (W : Type uW) [AddCommGroup W] [Module (Idempotent.Corner e) W],
    IsSimpleModule (Idempotent.Corner e) W →
    Simple ((NonUnitalModuleCat.nondegenerateAnnihilatorQuotientFunctor e).obj
        (nondegenerateObject hA e W)) ∧
      Nontrivial (FixedPart e ((NonUnitalModuleCat.nondegenerateAnnihilatorQuotientFunctor e).obj
        (nondegenerateObject hA e W)).obj)

/-- Proof of the Proposition of I.3.2, `W ≃ e·(A ⊗_{eAe} W)_e`: composing (I.3.2.1) with the
isomorphism (I.3.2.2), `w ↦ [e ⊗ w]` is an isomorphism of unital `eAe`-modules from `W` onto the
fixed part of `(A ⊗_{eAe} W)_e`. -/
def FixedPartInducedQuotientStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (e : Idempotent A)
    (W : Type uW) [AddCommGroup W] [Module (Idempotent.Corner e) W],
    letI := tensorAddCommGroup e W
    ∃ E : W ≃ₗ[Idempotent.Corner e]
        FixedPart e (annihilatorQuotientCarrier e (Tensor e W)),
      ∀ w : W, (E w).val = annihilatorQuotientProjection e (Tensor e W) (tmul e (e : A) w)

/-- Proof of the Proposition of I.3.2, `M ≃ (A ⊗_{eAe} e·M)_e`: for a simple object `M` of `M(A)`
with `e·M ≠ 0`, the evaluation `φ : a ⊗ e·m ↦ a·e·m` factors through
`(A ⊗_{eAe} e·M)_e` as a bijective intertwiner `φ̄`. -/
def InducedQuotientFixedPartStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (_hA : IsIdempotented A) (e : Idempotent A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M] (hM : IsNondegenerate A M),
    Simple (⟨NonUnitalModuleCat.of A M, hM⟩ : NondegenerateModuleCat.{uA, uM} A) →
    Nontrivial (FixedPart e M) →
    letI := tensorAddCommGroup e (FixedPart e M)
    ∃ φbar : NonUnitalModuleHom A (annihilatorQuotientCarrier e (Tensor e (FixedPart e M))) M,
      φbar.comp (annihilatorQuotientProjection e (Tensor e (FixedPart e M))) = evaluation e M ∧
        Function.Bijective φbar

/-- The Proposition of I.3.2 in four parts: the two maps between `Irr(A,e)` and `Irr(eAe)` are
well defined, and the two composites are isomorphic to the identity. -/
def SimpleCorrespondenceStatement : Prop :=
  SimpleFixedPartStatement.{uA, uM} ∧ SimpleInducedQuotientStatement.{uA, uW} ∧
    FixedPartInducedQuotientStatement.{uA, uW} ∧ InducedQuotientFixedPartStatement.{uA, uM}

/-- Theorem of I.3.2: `j_e : M(A,e) → M(eAe)` is an equivalence of categories iff the full
subcategory `M(A,e)` of `M(A)` is closed under subobjects and quotients. Carriers live in a
universe containing that of `A`. -/
def CornerEquivalenceCriterionStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (_hA : IsIdempotented A) (e : Idempotent A),
    (cornerFunctor.{uA, max uA uM} e).IsEquivalence ↔
      ((generatedProperty.{uA, max uA uM} e).IsClosedUnderSubobjects ∧
        (generatedProperty.{uA, max uA uM} e).IsClosedUnderQuotients)

/-- Theorem of I.3.2, "en particulier, c'est alors une catégorie abélienne": under the subquotient
condition, `M(A,e)` carries an abelian structure extending its inherited preadditive structure. -/
def GeneratedCategoryAbelianStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (_hA : IsIdempotented A) (e : Idempotent A),
    (generatedProperty.{uA, max uA uM} e).IsClosedUnderSubobjects →
    (generatedProperty.{uA, max uA uM} e).IsClosedUnderQuotients →
    ∃ h : Abelian (GeneratedModuleCat.{uA, max uA uM} e),
      h.toPreadditive = (inferInstance : Preadditive (GeneratedModuleCat.{uA, max uA uM} e))

/-- Theorem of I.3.2, "le foncteur inverse est donné par le foncteur `i`": under the subquotient
condition, for every object `V` of `M(A,e)` the evaluation `ψ_V : A ⊗_{eAe} e·V → V`,
`a ⊗ e·v ↦ a·e·v`, is bijective. -/
def CornerInductionInverseStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (_hA : IsIdempotented A) (e : Idempotent A),
    (generatedProperty.{uA, max uA uM} e).IsClosedUnderSubobjects →
    (generatedProperty.{uA, max uA uM} e).IsClosedUnderQuotients →
    ∀ V : GeneratedModuleCat.{uA, max uA uM} e, Function.Bijective (evaluation e V.obj.obj)

/-- The Theorem of I.3.2 in three parts. -/
def CornerEquivalenceStatement : Prop :=
  CornerEquivalenceCriterionStatement.{uA, uM} ∧ GeneratedCategoryAbelianStatement.{uA, uM} ∧
    CornerInductionInverseStatement.{uA, uM}

/-- The Proposition and the Theorem of I.3.2 together. -/
def Statements : Prop :=
  SimpleCorrespondenceStatement.{uA, uM, uW} ∧ CornerEquivalenceStatement.{uA, uM}

end Langlands.Algebra.NonUnitalModuleCornerSimpleStatements
