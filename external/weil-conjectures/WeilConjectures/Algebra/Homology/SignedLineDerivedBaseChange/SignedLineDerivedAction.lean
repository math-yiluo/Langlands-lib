/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLineDerivedBaseChangeData
import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLinePullbackTensor
import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLinePowerFlat
import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.FlatTensorDerivedAction
import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLineLocalizedCoherence

/-! # Derived action of normalized signed comparisons -/

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

/-- The normalized signed line family acts canonically on unbounded derived tensor.
Source: Stacks Project, Tags 03EL, 0FNY, 06YQ, 06YU, 07A4 and 015F;
Powers and duals, steps 8--11 of the signed-line base-change argument.
(blueprint: lem-pur-signed-line-derived-action)
Proof: restriction to a line chart shows that all positive powers and their
duals are lines. Their evaluation maps are locally multiplication with the
basis-dual inverse, and glue independently of the basis. Tensoring with each
signed line is thus an exact equivalence. A flat sheaf concentrated in degree
zero is K-flat with flat terms. Apply flat_single_derived_normalization to both
line factors. Compose its localization comparison with collapse to obtain cR
and cS; the representative equation proves ResolvingNormalization by cancellation.
The ordinary tensor-pullback comparison followed by T gives gamma with its pure
tensor formula. Localize its termwise isomorphism using cR and cS and the exact
pullback factorization to obtain eta. Full faithfulness of whiskering by the
localization proves the displayed square on every complex and uniqueness of eta.
The ordinary unit, positive associator and dual evaluation have precisely the
three pure tensor formulas in DerivedLineConstraints. Localize them to obtain
the required derived constraints. Their compatibility with gamma follows from
normalization of T and evaluation. Whiskering by the localization detects the
three required equalities, proving DerivedFamilyCoherence. Only the degree-zero
line factors are bounded; the varying complex is arbitrary. Zero rings and empty
covers satisfy the same local argument. -/
theorem signed_line_derived_action
    [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
    (_hcover : CoverPreserving J K U)
    (rInv : Sheaf J RingCat.{max u v w} ⥤ Sheaf K RingCat.{max u v w})
    (rAdj : rInv ⊣ U.sheafPushforwardContinuous RingCat J K)
    (ha : IsIso ((rAdj.homEquiv _ _).symm a))
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [∀ V : D, (K.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)]
    (T : ∀ d : ℤ, (pull a).obj (signedLinePower.{u, v, w} P d) ≅
        signedLinePower.{u, v, w} Q d)
    (_hT : SignedLinePullbackNormalized a P Q t T)
    (_hP : ∃ (I : Type u) (V : I → C), J.CoversTop V ∧
      ∀ i : I, Nonempty (P.over (V i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (V i))))
    (_hQ : ∃ (I : Type u) (V : I → D), K.CoversTop V ∧
      ∀ i : I, Nonempty (Q.over (V i) ≅
        unit (((sheafCompose K (forget₂ CommRingCat RingCat)).obj S).over (V i))))
    [_add : (pull a).Additive] [_lim : PreservesFiniteLimits (pull a)]
    [_col : PreservesFiniteColimits (pull a)] :
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
            DerivedFamilyCoherence (pull a) P Q b := by
  choose γ hγ using fun d : ℤ ↦ identified_ring_pullback_tensor a _hcover rInv rAdj ha
    (signedLinePower.{u, v, w} P d) (signedLinePower.{u, v, w} Q d) (T d)
  have hp (d : ℤ) := signed_line_power_flat R P _hP d
  have hq (d : ℤ) := signed_line_power_flat S Q _hQ d
  choose b hb using fun d : ℤ ↦ flat_tensor_derived_action (pull a)
    (signedLinePower.{u, v, w} P d) (signedLinePower.{u, v, w} Q d) (hp d) (hq d) (γ d)
  exact ⟨γ, hγ, b, hb,
    signed_line_localized_coherence a P Q t T _hT γ hγ b hb⟩

end SheafOfModules.SignedLineDerivedBaseChange
