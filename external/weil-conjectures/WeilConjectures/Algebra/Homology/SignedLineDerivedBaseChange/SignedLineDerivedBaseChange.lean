/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLineDerivedBaseChangeData
import WeilConjectures.Algebra.Homology.Signed.SignedLinePullbackUnique
import WeilConjectures.Algebra.Homology.Signed.SignedLinePullbackExistence
import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLinePullbackFiniteLimits
import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLinePullbackNaturality
import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLineDerivedAction
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Signed line comparisons on unbounded derived categories -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v w z
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace SheafOfModules.SignedLineDerivedBaseChange

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]
  {R : Sheaf J CommRingCat.{max u v w}}
  {S : Sheaf K CommRingCat.{max u v w}}

variable
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
  (P : KFlatFixedTensor.Modules R) (Q : KFlatFixedTensor.Modules S)
  (t : (pull a).obj P ≅ Q)

/-- The unique normalized signed comparisons, their naturality, and their canonical
unbounded derived tensor action.
Source: Stacks 03EL, 0GMX, 0FNY, 06YQ, 07A4 and 015F; blueprint Powers and duals
(blueprint: lem-pur-signed-line-derived-base-change).
Proof: exactness and the adjunction give the exact module pullback. The identity
scalar-extension square gives a normalized signed family. Tensor recursion and
evaluation prove it unique. Apply ordinary naturality and the derived-action
construction to this same family, then use normalized uniqueness once more for
the final existential uniqueness. -/
theorem signed_line_derived_base_change
    [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
    (_hcover : CoverPreserving J K U)
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [∀ V : D, (K.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (rInv : Sheaf J RingCat.{max u v w} ⥤ Sheaf K RingCat.{max u v w})
    (rAdj : rInv ⊣ U.sheafPushforwardContinuous RingCat J K)
    (_ha : IsIso ((rAdj.homEquiv _ _).symm a))
    (_hP : ∃ (I : Type u) (V : I → C), J.CoversTop V ∧
      ∀ i : I, Nonempty (P.over (V i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (V i))))
    (_hQ : ∃ (I : Type u) (V : I → D), K.CoversTop V ∧
      ∀ i : I, Nonempty (Q.over (V i) ≅
        unit (((sheafCompose K (forget₂ CommRingCat RingCat)).obj S).over (V i))))
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)] :
    ∃ (hAdd : (pull a).Additive)
      (hLim : PreservesFiniteLimits (pull a)) (hCol : PreservesFiniteColimits (pull a)),
    ∃! T : ∀ d : ℤ, (pull a).obj (signedLinePower.{u, v, w} P d) ≅
        signedLinePower.{u, v, w} Q d,
      SignedLinePullbackNormalized a P Q t T ∧
      (∀ T', SignedLinePullbackNormalized a P Q t T' → T' = T) ∧
      IsoNaturality a P Q t T ∧ ScalarNaturality a P Q t rInv rAdj T ∧
      (fun [_add : (pull a).Additive] [_lim : PreservesFiniteLimits (pull a)]
        [_col : PreservesFiniteColimits (pull a)] ↦
        ∃ γ : ∀ d : ℤ, siteSheafTensorRight (signedLinePower.{u, v, w} P d) ⋙ pull a ≅
            pull a ⋙ siteSheafTensorRight (signedLinePower.{u, v, w} Q d),
          (∀ (d : ℤ) (M : KFlatFixedTensor.Modules R) (V : C) (x : M.val.obj (op V))
            (y : (signedLinePower.{u, v, w} P d).val.obj (op V)),
            ((γ d).hom.app M).val.app (op (U.obj V))
                (ringedSitePullbackSection a
                  (module_pushforward_isRightAdjoint_of_universes a)
                  ((siteSheafTensorRight (signedLinePower.{u, v, w} P d)).obj M) V
                  (siteSheafTensorTmul M (signedLinePower.{u, v, w} P d) (op V) x y)) =
              siteSheafTensorTmul ((pull a).obj M) (signedLinePower.{u, v, w} Q d)
                (op (U.obj V))
                (ringedSitePullbackSection a
                  (module_pushforward_isRightAdjoint_of_universes a) M V x)
                ((T d).hom.val.app (op (U.obj V))
                  (ringedSitePullbackSection a
                    (module_pushforward_isRightAdjoint_of_universes a)
                    (signedLinePower.{u, v, w} P d) V y))) ∧
          ∃ b : ∀ d : ℤ, DerivedActionData (pull a) (signedLinePower.{u, v, w} P d)
            (signedLinePower.{u, v, w} Q d),
            (∀ d : ℤ, DerivedAction (pull a) (signedLinePower.{u, v, w} P d)
              (signedLinePower.{u, v, w} Q d) (γ d) (b d)) ∧
            DerivedFamilyCoherence (pull a) P Q b)
        (_add := hAdd) (_lim := hLim) (_col := hCol) := by
  let hAdj := module_pushforward_isRightAdjoint_of_universes a
  let := hAdj
  let : (pushforward a).Additive := ⟨by intros; rfl⟩
  have hAdd : (pull a).Additive :=
    (pullbackPushforwardAdjunction a).left_adjoint_additive
  have hLim := identified_ring_pullback_finiteLimits a _hcover rInv rAdj _ha
  have : PreservesColimitsOfSize.{0, 0} (pull a) :=
    (pullbackPushforwardAdjunction a).leftAdjoint_preservesColimits
  have hCol : PreservesFiniteColimits (pull a) := inferInstance
  obtain ⟨T, hT⟩ := exists_signedLinePullbackNormalized _hcover a P Q _hP t
  obtain ⟨hIso, hSc⟩ :=
    signed_line_pullback_naturality a P Q t _hcover rInv rAdj _ha _hP _hQ T hT
  let := hAdd
  let := hLim
  let := hCol
  refine ⟨hAdd, hLim, hCol, T, ?_, ?_⟩
  · refine ⟨hT, ?_, hIso, hSc, ?_⟩
    · intro T' hT'
      exact signedLinePullback_normalized_unique _hcover a P Q t T' T hT' hT
    · exact signed_line_derived_action a P Q t _hcover rInv rAdj _ha T hT _hP _hQ
  · intro T' hT'
    exact signedLinePullback_normalized_unique _hcover a P Q t T' T hT'.1 hT

end SheafOfModules.SignedLineDerivedBaseChange
