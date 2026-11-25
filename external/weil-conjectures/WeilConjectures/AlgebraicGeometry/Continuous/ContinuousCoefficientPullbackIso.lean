/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientPullbackSupplement
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientLocalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteTowerLimit
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Invertibility of continuous coefficient pullback along immersions -/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits Opposite
open AlgebraicGeometry Scheme
namespace AlgebraicGeometry.Scheme

private theorem constantComparison_pullback (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    {Z X : Scheme.{u}} (h : Z ⟶ X) :
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        (continuousCoefficientConstantComparison X T) ≫ continuousCoefficientPullback T h =
      proEtaleConstantInverseImageMap h CommRingCat.{u + 1} (CommRingCat.of T) ≫
        continuousCoefficientConstantComparison Z T := by
  let adj := proEtaleSheafAdjunction h CommRingCat.{u + 1}
  change _ ≫ (adj.homEquiv _ _).symm _ = (adj.homEquiv _ _).symm _ ≫ _
  rw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm]
  congr 1
  apply ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of T)) _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  unfold continuousCoefficientConstantComparison proEtaleConstantDirectImageMap
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  have hz := Equiv.apply_symm_apply
    ((sheafificationAdjunction (ProEt.topology Z) CommRingCat.{u + 1}).homEquiv
      ((Functor.const Z.ProEtᵒᵖ).obj (CommRingCat.of T)) (continuousCoefficientSheaf Z T))
    (continuousCoefficientConstants Z T)
  exact (congrArg (fun f ↦ f.app ((proEtaleBaseChange h).op.obj U)) hz).symm

private theorem constantRing_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : CommRingCat.{u + 1}) :
    IsIso (proEtaleConstantInverseImageMap f CommRingCat.{u + 1} A) := by
  change IsIso ((proEtaleConstantComparison f).app A)
  let T := ⊤_ Y.ProEt
  let hT := terminalIsTerminal (C := Y.ProEt)
  let hGT := hT.isTerminalObj (proEtaleBaseChange f)
  let adjY := constantSheafAdj (ProEt.topology Y) CommRingCat.{u + 1} hT
  let adjX := constantSheafAdj (ProEt.topology X) CommRingCat.{u + 1} hGT
  let adj := (adjY.comp (proEtaleSheafAdjunction f CommRingCat.{u + 1})).ofNatIsoRight
    ((proEtaleBaseChange f).sheafPushforwardContinuousCompSheafSectionsObjIso
      CommRingCat.{u + 1} (ProEt.topology Y) (ProEt.topology X) (op T))
  have he : (proEtaleConstantComparison f).app A =
      (adj.leftAdjointUniq adjX).hom.app A := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply]
    change (adjY.comp (proEtaleSheafAdjunction f CommRingCat.{u + 1})).homEquiv _ _
      ((proEtaleConstantComparison f).app A) ≫ 𝟙 _ = _
    rw [Category.comp_id, Adjunction.comp_homEquiv]
    change adjY.homEquiv _ _
      ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
        (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).symm
          (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A))) = _
    rw [Equiv.apply_symm_apply]
    change ((constantPresheafAdj CommRingCat.{u + 1} hT).comp
      (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1})).homEquiv _ _
        (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A) = _
    rw [Adjunction.comp_homEquiv]
    change (constantPresheafAdj CommRingCat.{u + 1} hT).homEquiv _ _
      ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv _ _
        (((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
          _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    change 𝟙 A ≫ _ = _
    rw [Category.id_comp]
    rfl
  rw [he]
  infer_instance

private theorem discretePullback_isIso (T : CommRingCat.{u + 1})
    {Z X : Scheme.{u}} (h : Z ⟶ X) :
    let : TopologicalSpace T := ⊥
    let : DiscreteTopology T := ⟨rfl⟩
    IsIso (continuousCoefficientPullback T h) := by
  dsimp only
  let : TopologicalSpace T := ⊥
  let : DiscreteTopology T := ⟨rfl⟩
  have hc := constantRing_isIso h (CommRingCat.of T)
  change IsIso (proEtaleConstantInverseImageMap h CommRingCat.{u + 1}
    (CommRingCat.of T)) at hc
  let := hc
  let := continuousCoefficientConstantComparison_isIso X T
  let := continuousCoefficientConstantComparison_isIso Z T
  have hh : IsIso ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
      (continuousCoefficientConstantComparison X T) ≫ continuousCoefficientPullback T h) := by
    rw [constantComparison_pullback]
    infer_instance
  let := hh
  exact IsIso.of_isIso_comp_left
    ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
      (continuousCoefficientConstantComparison X T)) (continuousCoefficientPullback T h)

private theorem integralPullback_isIso (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Z X : Scheme.{u}} (h : Z ⟶ X) :
    let := coefficientExtensionNormedField l E
    IsIso (continuousCoefficientPullback
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) h) := by
  classical
  dsimp only
  let := coefficientExtensionNormedField l E
  let Q := finiteCoefficientRingTower l E
  let L := proEtaleSheafInverseImage h CommRingCat.{u + 1}
  let : ∀ n : ℕᵒᵖ, Finite (Q.obj n) := fun n ↦ by
    let := Padic.finite_coefficientExtensionRing l E (n.unop + 1) (Nat.succ_le_succ (Nat.zero_le _))
    exact inferInstanceAs (Finite (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E (n.unop + 1))))
  let : CategoryTheory.Limits.PreservesLimit
      (Q ⋙ constantSheaf (ProEt.topology X) CommRingCat.{u + 1}) L :=
    proEtaleSheafInverseImage_preserves_finite_tower h Q
  let e := Functor.isoWhiskerLeft Q (discreteContinuousCoefficientIso X)
  let : CategoryTheory.Limits.PreservesLimit
      (Q ⋙ discreteContinuousCoefficientFunctor X) L :=
    CategoryTheory.Limits.preservesLimit_of_iso_diagram L e
  let d : (Q ⋙ discreteContinuousCoefficientFunctor X) ⋙ L ≅
      Q ⋙ discreteContinuousCoefficientFunctor Z :=
    NatIso.ofComponents (fun n ↦ by
      let : TopologicalSpace (Q.obj n) := ⊥
      let : DiscreteTopology (Q.obj n) := ⟨rfl⟩
      let := discretePullback_isIso (Q.obj n) h
      exact asIso (continuousCoefficientPullback (Q.obj n) h)) (by
        intro n m f
        let : TopologicalSpace (Q.obj n) := ⊥
        let : DiscreteTopology (Q.obj n) := ⟨rfl⟩
        let : TopologicalSpace (Q.obj m) := ⊥
        let : DiscreteTopology (Q.obj m) := ⟨rfl⟩
        exact continuousCoefficientPullback_naturality (Q.map f).hom
          continuous_of_discreteTopology h)
  let hcX := CategoryTheory.Limits.isLimitOfPreserves L
    (Classical.choice (continuousCoefficientResidueCone_isLimit l E X))
  let hcZ := Classical.choice (continuousCoefficientResidueCone_isLimit l E Z)
  let c := hcX.conePointsIsoOfNatIso hcZ d
  have he : continuousCoefficientPullback
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) h = c.hom := by
    apply hcZ.hom_ext
    intro n
    rw [hcX.conePointsIsoOfNatIso_hom_comp hcZ d n]
    let : TopologicalSpace (Q.obj n) := ⊥
    let : DiscreteTopology (Q.obj n) := ⟨rfl⟩
    change continuousCoefficientPullback _ h ≫ continuousCoefficientReduction l E Z n.unop =
      L.map (continuousCoefficientReduction l E X n.unop) ≫
        continuousCoefficientPullback (Q.obj n) h
    symm
    let adj := proEtaleSheafAdjunction h CommRingCat.{u + 1}
    change _ ≫ (adj.homEquiv _ _).symm _ = (adj.homEquiv _ _).symm _ ≫ _
    rw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm]
    congr 1
  rw [he]
  infer_instance

private theorem constantComparison_map {T S : Type (u + 1)}
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [TopologicalSpace S] [CommRing S] [IsTopologicalRing S]
    (φ : T →+* S) (hφ : Continuous φ) (X : Scheme.{u}) :
    (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom φ) ≫ continuousCoefficientConstantComparison X S =
      continuousCoefficientConstantComparison X T ≫ continuousCoefficientMap φ hφ X := by
  let adj := sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}
  unfold continuousCoefficientConstantComparison
  change (presheafToSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom φ)) ≫
      (adj.homEquiv _ _).symm _ = (adj.homEquiv _ _).symm _ ≫ _
  rw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm]
  congr 1

private theorem rationalMap_ext (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    {G : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (f g : rationalCoefficientSheaf l X E ⟶ G)
    (hfg : integralRationalCoefficientMap l E X ≫ f =
      integralRationalCoefficientMap l E X ≫ g) : f = g := by
  let := coefficientExtensionNormedField l E
  let T := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)
  let t : T := ULift.up (Padic.coefficientExtensionUniformizer l E)
  obtain ⟨b, hb⟩ := continuousCoefficientLocalization l E X
  apply (cancel_epi b.hom).mp
  apply ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
    (localizedContinuousMapPresheaf X T t) G).injective
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  change @Eq (Localization.Away (ContinuousMap.const U.unop.left t) →+* G.obj.obj U) _ _
  apply IsLocalization.ringHom_ext
    (S := Localization.Away (ContinuousMap.const U.unop.left t))
    (Submonoid.powers (ContinuousMap.const U.unop.left t))
  apply RingHom.ext
  intro a
  change C(U.unop.left, T) at a
  have hbapp : b.hom.hom.app U
      ((toSheafify (ProEt.topology X) (localizedContinuousMapPresheaf X T t)).app U
        (algebraMap C(U.unop.left, T)
          (Localization.Away (ContinuousMap.const U.unop.left t)) a)) =
        (integralRationalCoefficientMap l E X).hom.app U a := by
    apply ContinuousMap.ext
    intro x
    apply ULift.ext
    exact hb U a x
  change f.hom.app U (b.hom.hom.app U _) = g.hom.app U (b.hom.hom.app U _)
  exact (congrArg (f.hom.app U) hbapp).trans
    ((congrArg (fun q ↦ q.hom.app U a) hfg).trans (congrArg (g.hom.app U) hbapp).symm)

private theorem rationalLift (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (G : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (g : integralCoefficientSheaf l X E ⟶ G)
    (hg : let := coefficientExtensionNormedField l E
      ∀ U : X.ProEtᵒᵖ, IsUnit (g.hom.app U (ContinuousMap.const U.unop.left
      (ULift.up (Padic.coefficientExtensionUniformizer l E))))) :
    ∃ v : rationalCoefficientSheaf l X E ⟶ G,
      integralRationalCoefficientMap l E X ≫ v = g := by
  let := coefficientExtensionNormedField l E
  let T := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)
  let t : T := ULift.up (Padic.coefficientExtensionUniformizer l E)
  let φ (U : X.ProEtᵒᵖ) : Localization.Away (ContinuousMap.const U.unop.left t) →+*
      G.obj.obj U := IsLocalization.Away.lift (ContinuousMap.const U.unop.left t) (hg U)
  have hφ (U : X.ProEtᵒᵖ) (a : C(U.unop.left, T)) :
      φ U (algebraMap C(U.unop.left, T)
        (Localization.Away (ContinuousMap.const U.unop.left t)) a) = g.hom.app U a :=
    IsLocalization.Away.lift_eq _ _ _
  let f : localizedContinuousMapPresheaf X T t ⟶ G.obj :=
    { app := fun U ↦ CommRingCat.ofHom (φ U)
      naturality := by
        intro U V a
        apply CommRingCat.hom_ext
        apply IsLocalization.ringHom_ext
          (S := Localization.Away (ContinuousMap.const U.unop.left t))
          (Submonoid.powers (ContinuousMap.const U.unop.left t))
        apply RingHom.ext
        intro b
        change φ V (localizedContinuousMapRestriction X T t a (algebraMap _ _ b)) =
          G.obj.map a (φ U (algebraMap _ _ b))
        simp only [localizedContinuousMapRestriction, IsLocalization.Away.map,
          IsLocalization.map_eq, hφ]
        exact ConcreteCategory.congr_hom (g.hom.naturality a) b }
  let vloc : integralCoefficientLocalization l X E ⟶ G :=
    ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
      (localizedContinuousMapPresheaf X T t) G).symm f
  have hvloc : toSheafify (ProEt.topology X) (localizedContinuousMapPresheaf X T t) ≫
      vloc.hom = f := by
    change ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
      (localizedContinuousMapPresheaf X T t) G) vloc = f
    exact Equiv.apply_symm_apply _ f
  obtain ⟨b, hb⟩ := continuousCoefficientLocalization l E X
  let v := b.inv ≫ vloc
  have hcomp : b.hom ≫ v = vloc := by simp [v]
  refine ⟨v, ?_⟩
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change C(U.unop.left, T) at a
  have hbapp : b.hom.hom.app U
      ((toSheafify (ProEt.topology X) (localizedContinuousMapPresheaf X T t)).app U
        (algebraMap C(U.unop.left, T)
          (Localization.Away (ContinuousMap.const U.unop.left t)) a)) =
        (integralRationalCoefficientMap l E X).hom.app U a := by
    apply ContinuousMap.ext
    intro x
    apply ULift.ext
    exact hb U a x
  change v.hom.app U ((integralRationalCoefficientMap l E X).hom.app U a) = g.hom.app U a
  have hc := congrArg (fun q ↦ q.hom.app U
    ((toSheafify (ProEt.topology X) (localizedContinuousMapPresheaf X T t)).app U
      (algebraMap C(U.unop.left, T)
        (Localization.Away (ContinuousMap.const U.unop.left t)) a))) hcomp
  change v.hom.app U (b.hom.hom.app U _) = vloc.hom.app U _ at hc
  have hvval := congrArg (fun q ↦ q.app U
    (algebraMap C(U.unop.left, T)
      (Localization.Away (ContinuousMap.const U.unop.left t)) a)) hvloc
  exact (congrArg (v.hom.app U) hbapp).symm.trans
    (hc.trans (hvval.trans (hφ U a)))

/-- The canonical integral and rational pullback maps are isomorphisms for immersions.

Source: Bhatt--Scholze, Lemma 6.5.8(1) and paragraph before Definition 6.8.6
(blueprint: lem-weil-pbc-continuous-coefficient-pullback-isIso).

Proof: Compare the continuous residue cones with the finite constant towers.
Inverse image preserves these towers by the existing finite-tower theorem. The
canonical integral pullback is the resulting isomorphism because its compositions
with all residue projections agree, by the inverse-image adjunction and pointwise
reduction. No additional limit-preservation theorem for immersions is needed.
For rational coefficients, the normalized localization comparison proves both
uniqueness of maps on integral numerators and extension of maps that invert the
uniformizer. Compose inverse integral pullback with pulled-back integral inclusion.
The canonical constant-ring comparisons show this map inverts the uniformizer:
it agrees on constants with a map from the constant field sheaf. Extend it to
rational coefficients. Coefficient naturality and uniqueness on integral numerators
prove one inverse equation. The other follows by cancelling pulled-back integral
inclusion, an epimorphism by the same uniqueness and the inverse-image adjunction. -/
theorem continuousCoefficientPullback_isIso (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    [AlgebraicGeometry.IsLocallyNoetherian X] [CompactSpace X]
    {Z : Scheme.{u}} (h : Z ⟶ X) [AlgebraicGeometry.IsImmersion h] :
    letI := coefficientExtensionNormedField l E
    IsIso (continuousCoefficientPullback
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) h) ∧
    IsIso (continuousCoefficientPullback (ULift.{u + 1, u} E) h) := by
  let := coefficientExtensionNormedField l E
  have hA := integralPullback_isIso l E h
  let := hA
  refine ⟨hA, ?_⟩
  let A := Padic.coefficientExtensionIntegers l E
  let T := ULift.{u + 1, u} A
  let K := ULift.{u + 1, u} E
  let L := proEtaleSheafInverseImage h CommRingCat.{u + 1}
  let aX := integralRationalCoefficientMap l E X
  let aZ := integralRationalCoefficientMap l E Z
  let cA := asIso (continuousCoefficientPullback T h)
  let cE := continuousCoefficientPullback K h
  let g : integralCoefficientSheaf l Z E ⟶ L.obj (rationalCoefficientSheaf l X E) :=
    cA.inv ≫ L.map aX
  let inc : T →+* K := RingHom.ulift (Padic.coefficientExtensionIntegers l E).subtype
  have hinc : Continuous inc :=
    continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)
  let c0A := proEtaleConstantInverseImageMap h CommRingCat.{u + 1} (CommRingCat.of T)
  let c0K := proEtaleConstantInverseImageMap h CommRingCat.{u + 1} (CommRingCat.of K)
  let := constantRing_isIso h (CommRingCat.of T)
  let := constantRing_isIso h (CommRingCat.of K)
  let mK := (asIso c0K).inv ≫ L.map (continuousCoefficientConstantComparison X K)
  have hn : L.map ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom inc)) = c0A ≫
        (constantSheaf (ProEt.topology Z) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom inc) ≫ (asIso c0K).inv := by
    apply (cancel_mono c0K).mp
    have hinv : (asIso c0K).inv ≫ c0K = 𝟙 _ := (asIso c0K).inv_hom_id
    rw [Category.assoc, Category.assoc, hinv, Category.comp_id]
    exact proEtaleConstantInverseImageMap_naturality h (CommRingCat.ofHom inc)
  have hgconst : continuousCoefficientConstantComparison Z T ≫ g =
      (constantSheaf (ProEt.topology Z) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom inc) ≫ mK := by
    apply (cancel_epi c0A).mp
    calc
      _ = (L.map (continuousCoefficientConstantComparison X T) ≫ cA.hom) ≫ g := by
        exact (Category.assoc c0A (continuousCoefficientConstantComparison Z T) g).symm.trans
          (congrArg (fun q ↦ q ≫ g) (constantComparison_pullback T h).symm)
      _ = L.map (continuousCoefficientConstantComparison X T ≫ aX) := by
        simp only [g, Category.assoc, Iso.hom_inv_id_assoc, ← L.map_comp]
      _ = L.map ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom inc) ≫ continuousCoefficientConstantComparison X K) := by
        exact congrArg L.map (constantComparison_map inc hinc X).symm
      _ = _ := by rw [L.map_comp, hn]; simp [mK, Category.assoc]
  have hs := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hm0 : Padic.coefficientExtensionMaximalIdeal l E ≠ ⊥ :=
    hs.2.2.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set A) =
      Padic.coefficientExtensionMaximalIdeal l E := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  let t : T := ULift.up (Padic.coefficientExtensionUniformizer l E)
  have ht : inc t ≠ 0 := by
    intro hz
    apply hm0
    have hp : Padic.coefficientExtensionUniformizer l E = 0 := by
      apply Subtype.ext
      exact congrArg ULift.down hz
    rw [← hgen, hp, Ideal.span_singleton_zero]
  have hgunit : ∀ U : Z.ProEtᵒᵖ,
      IsUnit (g.hom.app U (ContinuousMap.const U.unop.left t)) := by
    intro U
    let ηA := toSheafify (ProEt.topology Z) ((Functor.const Z.ProEtᵒᵖ).obj
      (CommRingCat.of T))
    let ηK := toSheafify (ProEt.topology Z) ((Functor.const Z.ProEtᵒᵖ).obj
      (CommRingCat.of K))
    have hc : (continuousCoefficientConstantComparison Z T).hom.app U (ηA.app U t) =
        ContinuousMap.const U.unop.left t := by
      have hh := Equiv.apply_symm_apply
        ((sheafificationAdjunction (ProEt.topology Z) CommRingCat.{u + 1}).homEquiv
          ((Functor.const Z.ProEtᵒᵖ).obj (CommRingCat.of T))
          (continuousCoefficientSheaf Z T)) (continuousCoefficientConstants Z T)
      exact congrArg (fun q ↦ q.app U t) hh
    have hi : ((constantSheaf (ProEt.topology Z) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom inc)).hom.app U (ηA.app U t) = ηK.app U (inc t) := by
      have hh := (toSheafification (ProEt.topology Z) CommRingCat.{u + 1}).naturality
        ((Functor.const Z.ProEtᵒᵖ).map (CommRingCat.ofHom inc))
      exact (congrArg (fun q ↦ q.app U t) hh).symm
    have hu := congrArg (fun q ↦ q.hom.app U (ηA.app U t)) hgconst
    change g.hom.app U ((continuousCoefficientConstantComparison Z T).hom.app U
      (ηA.app U t)) = mK.hom.app U _ at hu
    have hu' : g.hom.app U (ContinuousMap.const U.unop.left t) =
        mK.hom.app U (ηK.app U (inc t)) :=
      (congrArg (g.hom.app U) hc).symm.trans (hu.trans (congrArg (mK.hom.app U) hi))
    exact hu'.symm ▸
      (((isUnit_iff_ne_zero.mpr ht).map (ηK.app U).hom).map (mK.hom.app U).hom)
  obtain ⟨v, hv⟩ := rationalLift l E Z (L.obj (rationalCoefficientSheaf l X E)) g hgunit
  have hnat : L.map aX ≫ cE = cA.hom ≫ aZ :=
    continuousCoefficientPullback_naturality inc hinc h
  have hright : v ≫ cE = 𝟙 (rationalCoefficientSheaf l Z E) := by
    apply rationalMap_ext l E Z
    change aZ ≫ (v ≫ cE) = aZ ≫ 𝟙 _
    rw [← Category.assoc, hv]
    simp only [g, Category.assoc, hnat, Iso.inv_hom_id_assoc, Category.comp_id]
  have haX : Epi aX := ⟨by
    intro G f g hh
    exact rationalMap_ext l E X f g hh⟩
  let := haX
  let := Functor.preservesEpimorphisms_of_adjunction
    (proEtaleSheafAdjunction h CommRingCat.{u + 1})
  have hleft : cE ≫ v = 𝟙 (L.obj (rationalCoefficientSheaf l X E)) := by
    apply (cancel_epi (L.map aX)).mp
    rw [← Category.assoc, hnat, Category.assoc, hv]
    simp [g]
  exact ⟨v, hleft, hright⟩

end AlgebraicGeometry.Scheme
