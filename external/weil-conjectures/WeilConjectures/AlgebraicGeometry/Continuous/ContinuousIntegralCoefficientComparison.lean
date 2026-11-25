/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement

/-!
# Normalized continuous integral coefficient comparison

Source: Bhatt--Scholze, Lemmas 4.2.12 and 6.8.2(1), and Section 6.5.
(blueprint: lem-weil-pbc-continuous-integral-coefficient-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
open Scheme

private noncomputable def integerEquiv (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    latticeCoefficientIntegers l E ≃+* Padic.coefficientExtensionIntegers l E :=
  RingEquiv.restrict (WithAbs.equiv (Padic.coefficientExtensionAbsoluteValue l E))
    (latticeCoefficientIntegers l E) (Padic.coefficientExtensionIntegers l E)
    (fun _ ↦ Iff.rfl)
private noncomputable def integerSheafIso (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    latticeCoefficientSheaf X (latticeCoefficientIntegers l E) ≅
      integralCoefficientSheaf l X E := by
  let := coefficientExtensionNormedField l E
  let e := integerEquiv l E
  have he : Isometry e := by
    apply AddMonoidHomClass.isometry_of_norm e
    intro x
    rfl
  have hei : Isometry e.symm := by
    intro x y
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm
  refine
    { hom := ⟨{
        app := fun V ↦ CommRingCat.ofHom
          { toFun := fun f ↦ ⟨fun x ↦ ULift.up (e (f.down x)),
                continuous_uliftUp.comp (he.continuous.comp f.down.continuous)⟩
            map_one' := rfl
            map_mul' := fun _ _ ↦ rfl
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun V ↦ CommRingCat.ofHom
          { toFun := fun f ↦ ULift.up ⟨fun x ↦ e.symm (f x).down,
                hei.continuous.comp (continuous_uliftDown.comp f.continuous)⟩
            map_one' := rfl
            map_mul' := fun _ _ ↦ rfl
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by ext V f; rfl
      inv_hom_id := by ext V f; rfl }
private noncomputable def completedIso (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    pbcAdicCompletion X (pbcIntegralDatum l E) ≅ finiteCoefficientLimit l X E := by
  let d := pbcIntegralDatum l E
  let F := constantSheaf (ProEt.topology X) CommRingCat.{u + 1}
  have hq (n : ℕ) (x : PbcIntegralRing l E) :
      integralCoefficientULift l E n (Ideal.Quotient.mk _ x) =
        ULift.up (Ideal.Quotient.mk _ x.down) :=
    (integralCoefficientULift_exists l E n).exists.choose_spec x
  have ht (n : ℕ) :
      CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1)) ≫
        (integralCoefficientULift l E n).toCommRingCatIso.hom =
      (integralCoefficientULift l E (n + 1)).toCommRingCatIso.hom ≫
        finiteCoefficientRingMap l E (Nat.le_succ n) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change integralCoefficientULift l E n
      (Ideal.Quotient.factorPowSucc d.ideal (n + 1) (Ideal.Quotient.mk _ x)) = _
    change integralCoefficientULift l E n (Ideal.Quotient.mk _ x) = _
    rw [hq]
    change ULift.up (Ideal.Quotient.mk _ x.down) =
      (finiteCoefficientRingMap l E (Nat.le_succ n))
        ((integralCoefficientULift l E (n + 1)) (Ideal.Quotient.mk _ x))
    rw [hq]
    rfl
  let c : adicLisseRingSystem X d.ideal ⟶ finiteCoefficientTower l X E :=
    NatTrans.ofOpSequence
      (fun n ↦ F.map (integralCoefficientULift l E n).toCommRingCatIso.hom)
      (by
        intro n
        simp only [adicLisseRingSystem, Functor.ofOpSequence_map_homOfLE_succ,
          finiteCoefficientTower]
        change F.map (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) ≫
          F.map (integralCoefficientULift l E n).toCommRingCatIso.hom =
          F.map (integralCoefficientULift l E (n + 1)).toCommRingCatIso.hom ≫
          F.map (finiteCoefficientRingMap l E (Nat.le_succ n))
        simp only [← F.map_comp, ht])
  have (n : ℕᵒᵖ) : IsIso (c.app n) := by
    change IsIso (F.map (integralCoefficientULift l E n.unop).toCommRingCatIso.hom)
    infer_instance
  have : IsIso c := NatIso.isIso_of_isIso_app c
  exact (pbcCompletedComparison X d).symm ≪≫ HasLimit.isoOfNatIso (asIso c)
private theorem completedIso_scalar (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    pbcCompletedScalar X (pbcIntegralDatum l E) ≫ (completedIso X l E).hom ≫
      limit.π (finiteCoefficientTower l X E) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (integralCoefficientULift l E n).toCommRingCatIso.hom := by
  dsimp only [completedIso, pbcCompletedScalar, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [HasLimit.isoOfNatIso_hom_π]
  rw [← Category.assoc]
  exact congrArg (fun f ↦ f ≫ (constantSheaf (ProEt.topology X)
      CommRingCat.{u + 1}).map (integralCoefficientULift l E n).toCommRingCatIso.hom)
    ((adicDatumScalar_exists X
      { toCompleteCoefficientDatum := (pbcIntegralDatum l E).toCompleteCoefficientDatum
        quotientFinite := (pbcIntegralDatum l E).quotientFinite }).exists.choose_spec n)
private noncomputable def liftedIntegerEquiv (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ULift.{u + 1} (latticeCoefficientIntegers l E) ≃+* PbcIntegralRing l E :=
  ULift.ringEquiv.trans ((integerEquiv l E).trans ULift.ringEquiv.symm)
private theorem normalizedCoefficientIso_exists (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ c : pbcAdicCompletion X (pbcIntegralDatum l E) ≅
        latticeCoefficientSheaf X (latticeCoefficientIntegers l E),
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (liftedIntegerEquiv l E).toCommRingCatIso.hom ≫
        pbcCompletedScalar X (pbcIntegralDatum l E) =
      continuousCoefficientConstantMap X (latticeCoefficientIntegers l E) ≫ c.inv := by
  obtain ⟨i, hi⟩ := continuousCoefficientCompletion l E X
  let b := completedIso X l E
  let k := integerSheafIso X l E
  let c := b ≪≫ i.symm ≪≫ k.symm
  refine ⟨c, ?_⟩
  apply (cancel_mono b.hom).mp
  change _ ≫ b.hom = _ ≫ (k.hom ≫ i.hom ≫ b.inv) ≫ b.hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply limit.hom_ext
  intro n
  dsimp only [b]
  simp only [Category.assoc]
  rw [completedIso_scalar X l E n.unop]
  obtain ⟨q, hq, hiq⟩ := hi n.unop
  apply (cancel_mono q.hom).mp
  apply ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of
      (ULift.{u + 1} (latticeCoefficientIntegers l E)))) _).injective
  simp only [← Functor.map_comp, constantSheaf, Functor.comp_map, Category.assoc]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [continuousCoefficientConstantMap, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext V
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  let : TopologicalSpace (finiteCoefficientRing l E n.unop) := ⊥
  let : DiscreteTopology (finiteCoefficientRing l E n.unop) := ⟨rfl⟩
  -- Both sides are finite coefficient functions, with equal values at every point.
  apply ContinuousMap.ext
  intro x
  change finiteContinuousCoefficientValue l E X n.unop V
    (q.hom.hom.app V ((toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (finiteCoefficientRing l E n.unop))).app V _)) x = _
  rw [hq]
  change integralCoefficientULift l E n.unop
    (Ideal.Quotient.mk _ ((liftedIntegerEquiv l E) a)) = _
  have hu : integralCoefficientULift l E n.unop
      (Ideal.Quotient.mk _ ((liftedIntegerEquiv l E) a)) =
      ULift.up (Ideal.Quotient.mk _ ((liftedIntegerEquiv l E) a).down) :=
    (integralCoefficientULift_exists l E n.unop).exists.choose_spec _
  rw [hu]
  apply ULift.ext
  exact (hiq V (k.hom.hom.app V
    ((continuousCoefficientConstants X (latticeCoefficientIntegers l E)).app V a)) x).symm

/-- The continuous integral coefficient ring agrees with the completed quotient
presentation, compatibly with its actual constant scalar map.
Source: Bhatt--Scholze, Lemmas 4.2.12 and 6.8.2(1), completed coefficients of Section 6.5.
(blueprint: lem-weil-pbc-continuous-integral-coefficient-comparison).

Proof: restrict WithAbs.equiv to the integer subrings. Its isometry gives an isomorphism
of continuous-function sheaves, exchanging the two ULift conventions. The uniquely
normalized quotient equivalences identify the constant residue diagrams; take their
limit and compose with the continuous coefficient completion isomorphism. For the
constant scalar square, compare its composites with each finite projection, followed by
the finite continuous-functions isomorphism. Constant-sheaf adjunction naturality reduces
the left side to a constant residue and the right side to the residue of a constant
function. The two residue-normalization formulas identify these. Limit and constant-sheaf
universal properties then give the stated equality. -/
theorem continuousIntegralCoefficientComparison
    (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ (s : ULift.{u + 1} (latticeCoefficientIntegers l E) ≃+* PbcIntegralRing l E)
      (c : pbcAdicCompletion X (pbcIntegralDatum l E) ≅
        latticeCoefficientSheaf X (latticeCoefficientIntegers l E)),
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          s.toCommRingCatIso.hom ≫ pbcCompletedScalar X (pbcIntegralDatum l E) =
        continuousCoefficientConstantMap X (latticeCoefficientIntegers l E) ≫ c.inv := by
  obtain ⟨c, hc⟩ := normalizedCoefficientIso_exists X l E
  exact ⟨liftedIntegerEquiv l E, c, hc⟩

end AlgebraicGeometry.ProEtale
