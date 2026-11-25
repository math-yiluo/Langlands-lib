/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarPullbackSquare
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackPairingTransfer
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement

/-! # Uniqueness of the normalized signed pullback comparison

Source: Stacks Project, Tags 03EL, 0GMX, 0FNY and 07A4; the current blueprint,
Powers and duals in lemma-inverse-image-coefficient-sheaves--2.
(blueprint: lem-pur-signed-line-pullback-unique)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace SheafOfModules

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

variable [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
  (hcover : CoverPreserving J K U)
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [∀ V : D, (K.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
  (P : ringedSiteModules.{max u v w}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (Q : ringedSiteModules.{max u v w}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
  (t : (ringedSitePullbackFunctor a
    (module_pushforward_isRightAdjoint_of_universes a)).obj P ≅ Q)

private theorem pullback_hom_ext
    (L : ringedSiteModules.{max u v w}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (M : ringedSiteModules.{max u v w}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
    (f g : (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj L ⟶ M)
    (h : ∀ (V : C) (x : L.val.obj (op V)),
      f.val.app (op (U.obj V))
        (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
          L V x) =
      g.val.app (op (U.obj V))
        (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
          L V x)) : f = g := by
  let := module_pushforward_isRightAdjoint_of_universes a
  apply (pullbackPushforwardAdjunction a).homEquiv _ _ |>.injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact h V.unop

include hcover in
/-- Evaluation and tensor recursion determine all signed pullback comparisons.
Source: Stacks 03EL and 0GMX; Powers and duals, uniqueness of the normalized extension.
(blueprint: lem-pur-signed-line-pullback-unique)
Proof: the adjunction unit detects morphisms out of a pullback. Degree zero and one
are fixed. Induction and tensor generation determine every positive degree. For a
negative degree, postcompose with the dual of the positive comparison. Both resulting
maps are the unique transfer of the same evaluation pairing. Cancel that dual
isomorphism to obtain equality. The argument also applies over the zero ring. -/
theorem signedLinePullback_normalized_unique
    (T T' : ∀ d : ℤ, (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj
        (signedLinePower.{u, v, w} P d) ≅ signedLinePower.{u, v, w} Q d)
    (hT : SignedLinePullbackNormalized a P Q t T)
    (hT' : SignedLinePullbackNormalized a P Q t T') : T = T' := by
  have hpos : ∀ n : ℕ, T (.ofNat n) = T' (.ofNat n) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero =>
      apply Iso.ext
      apply pullback_hom_ext a
      intro V r
      exact (hT.1 V r).trans (hT'.1 V r).symm
    | one =>
      apply Iso.ext
      exact hT.2.1.trans hT'.2.1.symm
    | more n _ ih =>
      apply Iso.ext
      let := module_pushforward_isRightAdjoint_of_universes a
      apply (pullbackPushforwardAdjunction a).homEquiv _ _ |>.injective
      apply scalarTensor_hom_ext
      intro V x y
      change (T (.ofNat (n + 2))).hom.val.app (op (U.obj V.unop))
        (ringedSitePullbackSection a _ _ V.unop (siteSheafTensorTmul _ _ V x y)) = _
      have ht := hT.2.2.1 n V.unop x y
      rw [ih] at ht
      exact ht.trans (hT'.2.2.1 n V.unop x y).symm
  funext d
  cases d with
  | ofNat n => exact hpos n
  | negSucc n =>
    apply Iso.ext
    let hAdj := module_pushforward_isRightAdjoint_of_universes a
    let L := scalarTensorPower R P (n + 1)
    let DQ := signedLinePower.{u, v, w} Q (.negSucc n)
    let dp := homObjMap (T (.ofNat (n + 1))).hom (𝟙 (unit _))
    let di := homObjMap (T (.ofNat (n + 1))).inv (𝟙 (unit _))
    have hd : dp ≫ di = 𝟙 DQ := by
      dsimp [dp, di, DQ]
      rw [homObjMap_comp_homObjMap, Iso.inv_hom_id, Category.id_comp, homObjMap_id]
      rfl
    have hf : (T (.negSucc n)).hom ≫ dp = (T' (.negSucc n)).hom ≫ dp := by
      obtain ⟨δ, _, hδ⟩ := exists_pullback_pairing_transfer a hcover hAdj
        L (homObj L (unit _)) (𝟙 _)
      apply (hδ _ ?_).trans (hδ _ ?_).symm
      · intro V φ x
        change (((T (.negSucc n)).hom.val.app (op (U.obj V))
          (ringedSitePullbackSection a hAdj _ V φ)).app
            (op (Over.mk (𝟙 (U.obj V)))))
          ((T (.ofNat (n + 1))).hom.val.app (op (U.obj V))
            (ringedSitePullbackSection a hAdj _ V x)) = _
        exact hT.2.2.2 n V φ x
      · intro V φ x
        change (((T' (.negSucc n)).hom.val.app (op (U.obj V))
          (ringedSitePullbackSection a hAdj _ V φ)).app
            (op (Over.mk (𝟙 (U.obj V)))))
          ((T (.ofNat (n + 1))).hom.val.app (op (U.obj V))
            (ringedSitePullbackSection a hAdj _ V x)) = _
        rw [hpos (n + 1)]
        exact hT'.2.2.2 n V φ x
    have hh := hf =≫ di
    simp only [Category.assoc, hd] at hh
    exact (Category.comp_id _).symm.trans (hh.trans (Category.comp_id _))

end SheafOfModules
