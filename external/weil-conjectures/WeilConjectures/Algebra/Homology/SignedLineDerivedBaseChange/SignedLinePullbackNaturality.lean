/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLineDerivedBaseChangeData
import WeilConjectures.Algebra.Homology.Signed.SignedLinePullbackUnique
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualLocalIso
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackPairingTransfer

/-! # Naturality of signed pullback comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v w z
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace SheafOfModules.SignedLineDerivedBaseChange

attribute [local irreducible] monoidalCategory
  siteSheafTensorRight siteSheafTensorTmul siteSheafTensorSecondMap

private theorem inverse_square {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) {X X' : A} {Y Y' : B} (b : X ≅ X') (c : Y ≅ Y')
    (t : F.obj X ⟶ Y) (t' : F.obj X' ⟶ Y')
    (h : F.map b.hom ≫ t' = t ≫ c.hom) : F.map b.inv ≫ t = t' ≫ c.inv := by
  apply (cancel_mono c.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h, ← Category.assoc, ← CategoryTheory.Functor.map_comp, b.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

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

private theorem pullbackSection_natural
    {L M : KFlatFixedTensor.Modules R} (f : L ⟶ M) (V : C) (x : L.val.obj (op V)) :
    ((pull a).map f).val.app (op (U.obj V))
      (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a) L V x) =
      ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a) M V
        (f.val.app (op V) x) := by
  let := module_pushforward_isRightAdjoint_of_universes a
  exact (congrArg (fun g ↦ g.val.app (op V) x)
    ((pullbackPushforwardAdjunction a).unit.naturality f)).symm

private theorem powerMap_pure {A : Sheaf J CommRingCat.{max u v w}}
    {L M : KFlatFixedTensor.Modules A} (f : L ⟶ M) (n : ℕ) (V : Cᵒᵖ)
    (x : (scalarTensorPower A L (n + 1)).val.obj V) (y : L.val.obj V) :
    (scalarTensorPowerMap A f (n + 2)).val.app V
      (siteSheafTensorTmul (scalarTensorPower A L (n + 1)) L V x y) =
      siteSheafTensorTmul (scalarTensorPower A M (n + 1)) M V
        ((scalarTensorPowerMap A f (n + 1)).val.app V x) (f.val.app V y) := by
  change (siteSheafTensorSecondMap _ f).val.app V
    (((siteSheafTensorRight L).map (scalarTensorPowerMap A f (n + 1))).val.app V
      (siteSheafTensorTmul _ _ V x y)) = _
  rw [scalarTensor_first_tmul, scalarTensor_second_tmul]

private theorem positive_naturality
    (T : ∀ d : ℤ, (pull a).obj (signedLinePower.{u, v, w} P d) ≅
      signedLinePower.{u, v, w} Q d)
    (hT : SignedLinePullbackNormalized a P Q t T)
    (P' : KFlatFixedTensor.Modules R) (Q' : KFlatFixedTensor.Modules S)
    (b : P ≅ P') (c : Q ≅ Q') (t' : (pull a).obj P' ≅ Q')
    (T' : ∀ d : ℤ, (pull a).obj (signedLinePower.{u, v, w} P' d) ≅
      signedLinePower.{u, v, w} Q' d)
    (ht : (pull a).map b.hom ≫ t'.hom = t.hom ≫ c.hom)
    (hT' : SignedLinePullbackNormalized a P' Q' t' T') :
    ∀ n : ℕ, (pull a).map (scalarTensorPowerMap R b.hom n) ≫ (T' (.ofNat n)).hom =
      (T (.ofNat n)).hom ≫ scalarTensorPowerMap S c.hom n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    simp only [scalarTensorPowerMap, CategoryTheory.Functor.map_id, Category.id_comp]
    let := module_pushforward_isRightAdjoint_of_universes a
    apply (pullbackPushforwardAdjunction a).homEquiv _ _ |>.injective
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change (T' 0).hom.val.app (op (U.obj V.unop))
      (ringedSitePullbackSection a _ _ V.unop r) = _
    exact (hT'.1 V.unop r).trans (hT.1 V.unop r).symm
  | one =>
    change (pull a).map b.hom ≫ (T' 1).hom = (T 1).hom ≫ c.hom
    rw [hT.2.1, hT'.2.1]
    exact ht
  | more n _ ih =>
    let := module_pushforward_isRightAdjoint_of_universes a
    apply (pullbackPushforwardAdjunction a).homEquiv _ _ |>.injective
    apply scalarTensor_hom_ext
    intro V x y
    change (T' (.ofNat (n + 2))).hom.val.app (op (U.obj V.unop))
      (((pull a).map (scalarTensorPowerMap R b.hom (n + 2))).val.app _
        (ringedSitePullbackSection a _ _ V.unop (siteSheafTensorTmul _ _ V x y))) = _
    rw [pullbackSection_natural]
    erw [powerMap_pure]
    rw [hT'.2.2.1]
    change _ = (scalarTensorPowerMap S c.hom (n + 2)).val.app _
      ((T (.ofNat (n + 2))).hom.val.app _
        (ringedSitePullbackSection a _ _ V.unop (siteSheafTensorTmul _ _ V x y)))
    have hrec := hT.2.2.1 n V.unop x y
    apply Eq.trans ?_ (congrArg
      ((scalarTensorPowerMap S c.hom (n + 2)).val.app (op (U.obj V.unop))) hrec).symm
    erw [powerMap_pure]
    have hi := congrArg (fun f ↦ f.val.app (op (U.obj V.unop))
      (ringedSitePullbackSection a _ _ V.unop x)) ih
    have h1 := congrArg (fun f ↦ f.val.app (op (U.obj V.unop))
      (ringedSitePullbackSection a _ _ V.unop y)) ht
    change (T' (.ofNat (n + 1))).hom.val.app (op (U.obj V.unop))
      (((pull a).map (scalarTensorPowerMap R b.hom (n + 1))).val.app _
        (ringedSitePullbackSection a _ _ V.unop x)) =
      (scalarTensorPowerMap S c.hom (n + 1)).val.app _
        ((T (.ofNat (n + 1))).hom.val.app _
          (ringedSitePullbackSection a _ _ V.unop x)) at hi
    change t'.hom.val.app (op (U.obj V.unop))
      (((pull a).map b.hom).val.app _ (ringedSitePullbackSection a _ _ V.unop y)) =
      c.hom.val.app _ (t.hom.val.app _ (ringedSitePullbackSection a _ _ V.unop y)) at h1
    rw [pullbackSection_natural] at hi h1
    exact congrArg₂ (siteSheafTensorTmul _ _ (op (U.obj V.unop))) hi h1

/-- Naturality of any normalized signed line pullback family.
Source: Stacks Project, Tags 03EL, 0GMX and 0FNY; Powers and duals,
steps 5--7 of the signed-line base-change argument.
(blueprint: lem-pur-signed-line-pullback-naturality)
Proof: the unit comparison is natural and degree one is the given compatible
square. For positive degrees, induct on the tensor recursion; unit naturality
and the bilinear pullback comparison identify both maps on pulled pure tensors,
and adjunction plus tensor generation give equality. For a negative degree,
postcompose by the dual of the positive comparison. Both composites transfer
the same evaluation pairing, so evaluation uniqueness identifies them; cancel
the dual isomorphism. For scalar extension, trivialize the source lines and use
the induced bases after scalar extension, which is locally free even for a
nonflat ring map. Apply the normalized signed scalar/pullback square theorem
and uniqueness to identify its two families with T and T-prime. Balancing
multiplies the scalar factors, hence proves the positive squares; the evaluation
formula proves the negative ones. All identities are local and therefore also
hold over the zero ring or an empty cover. -/
theorem signed_line_pullback_scalar_naturality
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
    (T : ∀ d : ℤ, (pull a).obj (signedLinePower.{u, v, w} P d) ≅
      signedLinePower.{u, v, w} Q d)
    (_hT : SignedLinePullbackNormalized a P Q t T) :
    ScalarNaturality a P Q t rInv rAdj T  := by
  intro R' S' α β a' ha' hsq t' T' B E hT' hB hE hdegree
  obtain ⟨IP, VP, hVP, heP⟩ := _hP
  obtain ⟨IQ, VQ, hVQ, heQ⟩ := _hQ
  let : P.IsInvertible := isInvertible_of_forall_over_unit.{max u v w, v, u} VP hVP heP
  let : Q.IsInvertible := isInvertible_of_forall_over_unit.{max u v w, v, u} VQ hVQ heQ
  let : (changeOfRingsOfUniverses α P).IsInvertible :=
    (scalarExtensionDual_localIsomorphism R R' α P).1
  let : (changeOfRingsOfUniverses β Q).IsInvertible :=
    (scalarExtensionDual_localIsomorphism S S' β Q).1
  have hlocal {A : Sheaf J CommRingCat.{max u v w}}
      (M : KFlatFixedTensor.Modules A) [M.IsInvertible] :
      ∃ (I : Type u) (V : I → C), J.CoversTop V ∧
        ∀ i : I, Nonempty (M.over (V i) ≅
          unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).over (V i))) := by
    obtain ⟨q, hq⟩ := IsInvertible.exists_isInvertibleData (M := M)
    let := hq
    refine ⟨q.I, q.X, q.coversTop, ?_⟩
    intro i
    let := (hq.nonempty_unique i).some
    exact ⟨(asIso (q.generators i).π).symm ≪≫ freeUniqueIso _⟩
  have hlocalS {A : Sheaf K CommRingCat.{max u v w}}
      (M : KFlatFixedTensor.Modules A) [M.IsInvertible] :
      ∃ (I : Type u) (V : I → D), K.CoversTop V ∧
        ∀ i : I, Nonempty (M.over (V i) ≅
          unit (((sheafCompose K (forget₂ CommRingCat RingCat)).obj A).over (V i))) := by
    obtain ⟨q, hq⟩ := IsInvertible.exists_isInvertibleData (M := M)
    let := hq
    refine ⟨q.I, q.X, q.coversTop, ?_⟩
    intro i
    let := (hq.nonempty_unique i).some
    exact ⟨(asIso (q.generators i).π).symm ≪≫ freeUniqueIso _⟩
  obtain ⟨PQ, hPQ, _⟩ := existsUnique_signedLineScalarPullbackSquare _hcover
    α β a a' hsq P (changeOfRingsOfUniverses α P) Q (changeOfRingsOfUniverses β Q)
    ⟨IP, VP, hVP, heP⟩ (hlocal _) ⟨IQ, VQ, hVQ, heQ⟩ (hlocalS _)
    (Iso.refl _) (Iso.refl _) t t' hdegree B E hB hE
  have hfirst := signedLinePullback_normalized_unique _hcover a P Q t PQ.1 T hPQ.1 _hT
  have hsecond := signedLinePullback_normalized_unique _hcover a'
    _ _ t' PQ.2 T' hPQ.2.1 hT'
  simpa only [hfirst, hsecond] using hPQ.2.2

/-- One normalized family commutes with both line isomorphisms and coefficient extension.
Source: Stacks 03EL and 0FNY.
(blueprint: lem-pur-signed-line-pullback-naturality)
Proof: combine the isomorphism square with the scalar-extension square proved above. -/
theorem signed_line_pullback_naturality
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
    (T : ∀ d : ℤ, (pull a).obj (signedLinePower.{u, v, w} P d) ≅
      signedLinePower.{u, v, w} Q d)
    (_hT : SignedLinePullbackNormalized a P Q t T) :
    IsoNaturality a P Q t T ∧ ScalarNaturality a P Q t rInv rAdj T := by
  refine ⟨?_, signed_line_pullback_scalar_naturality a P Q t _hcover rInv rAdj
    _ha _hP _hQ T _hT⟩
  intro P' Q' b c t' T' ht hT' d
  cases d with
  | ofNat n => exact positive_naturality a P Q t T _hT P' Q' b c t' T' ht hT' n
  | negSucc n =>
    let hAdj := module_pushforward_isRightAdjoint_of_universes a
    let := hAdj
    have hti := inverse_square (pull a) b c t.hom t'.hom ht
    have hi := positive_naturality a P' Q' t' T' hT' P Q b.symm c.symm t T hti _hT
      (n + 1)
    let dp := homObjMap (T' (.ofNat (n + 1))).hom (𝟙 (unit _))
    let di := homObjMap (T' (.ofNat (n + 1))).inv (𝟙 (unit _))
    have hd : dp ≫ di = 𝟙 (signedLinePower.{u, v, w} Q' (.negSucc n)) := by
      dsimp [dp, di]
      rw [homObjMap_comp_homObjMap, Iso.inv_hom_id, Category.id_comp, homObjMap_id]
      rfl
    let L := scalarTensorPower R P' (n + 1)
    let B := homObjMap (scalarTensorPowerMap R b.inv (n + 1)) (𝟙 (unit _))
    obtain ⟨δ, _, hδ⟩ := exists_pullback_pairing_transfer a _hcover hAdj L
      (homObj (scalarTensorPower R P (n + 1)) (unit _)) B
    have heq : ((pull a).map (signedIsoHom b (.negSucc n)) ≫
        (T' (.negSucc n)).hom) ≫ dp =
        ((T (.negSucc n)).hom ≫ signedIsoHom c (.negSucc n)) ≫ dp := by
      apply (hδ _ ?_).trans (hδ _ ?_).symm
      · intro V φ x
        change (((T' (.negSucc n)).hom.val.app (op (U.obj V))
          (((pull a).map B).val.app _ (ringedSitePullbackSection a hAdj _ V φ))).app
            (op (Over.mk (𝟙 (U.obj V)))))
          ((T' (.ofNat (n + 1))).hom.val.app (op (U.obj V))
            (ringedSitePullbackSection a hAdj _ V x)) = _
        rw [pullbackSection_natural]
        exact hT'.2.2.2 n V (B.val.app _ φ) x
      · intro V φ x
        have hiv := congrArg (fun f ↦ f.val.app (op (U.obj V))
          (ringedSitePullbackSection a hAdj L V x)) hi
        change (T (.ofNat (n + 1))).hom.val.app (op (U.obj V))
          (((pull a).map (scalarTensorPowerMap R b.inv (n + 1))).val.app _
            (ringedSitePullbackSection a hAdj L V x)) =
            (scalarTensorPowerMap S c.inv (n + 1)).val.app _
              ((T' (.ofNat (n + 1))).hom.val.app _
                (ringedSitePullbackSection a hAdj L V x)) at hiv
        rw [pullbackSection_natural] at hiv
        change (((T (.negSucc n)).hom.val.app (op (U.obj V))
          (ringedSitePullbackSection a hAdj _ V φ)).app
            (op (Over.mk (𝟙 (U.obj V)))))
          ((scalarTensorPowerMap S c.inv (n + 1)).val.app _
            ((T' (.ofNat (n + 1))).hom.val.app _
              (ringedSitePullbackSection a hAdj L V x))) = _
        have heval := congrArg (fun y ↦
          (((T (.negSucc n)).hom.val.app (op (U.obj V))
            (ringedSitePullbackSection a hAdj _ V φ)).app
              (op (Over.mk (𝟙 (U.obj V)))) y)) hiv.symm
        exact heval.trans (_hT.2.2.2 n V φ
          ((scalarTensorPowerMap R b.inv (n + 1)).val.app _ x))
    have hh := heq =≫ di
    rw [Category.assoc, Category.assoc, hd, Category.comp_id,
      Category.assoc, Category.assoc, hd, Category.comp_id] at hh
    exact hh

end SheafOfModules.SignedLineDerivedBaseChange
