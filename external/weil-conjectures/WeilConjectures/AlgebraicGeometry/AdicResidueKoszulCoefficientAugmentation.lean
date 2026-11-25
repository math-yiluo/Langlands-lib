/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueQuotientTensorTower
import WeilConjectures.CategoryTheory.RingedNegativeKoszulDuality
import WeilConjectures.CategoryTheory.RingedNegativeKoszulLowDegrees

/-! # The coefficient Koszul augmentation, before tensoring

Source: Stacks Project, algebraization.tex, lemma-derived-completion-koszul (0A0E),
and proetale.tex, lemma-naive-completion (099M).
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
  (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)

private def quotientProjection (n : ℕ) :
    SheafOfModules.unit (siteModuleRings
      ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U)) ⟶
        adicResidueQuotientModule X J U n :=
  (adicResidueQuotientModule X J U n).unitHomEquiv.symm
    ⟨fun V ↦ (1 : (adicResidueQuotientRing X J U n).obj.obj V),
      fun {V W} f ↦ by
        change (adicResidueQuotientRing X J U n).obj.map f 1 = 1
        exact map_one _⟩

private theorem quotientProjection_step (n : ℕ) :
    quotientProjection X J U (n + 1) ≫ adicResidueQuotientModuleStep X J U n =
      quotientProjection X J U n := by
  apply (SheafOfModules.unitHomEquiv _).injective
  rw [SheafOfModules.unitHomEquiv_comp_apply]
  simp only [quotientProjection, Equiv.apply_symm_apply]
  ext V
  change (((coefficientProEtaleModelTopology.{u, v} X).overPullback CommRingCat U).map
    (transition (coefficientProEtaleModelTopology.{u, v} X) A J n)).hom.app V 1 = 1
  exact map_one _

private theorem completedScalar_quotient_zero (a : A) (ha : a ∈ J) (n : ℕ)
    (V : (Over U)ᵒᵖ) :
    (adicResidueLocalProjection X J U n).hom.app V
      ((ringedKoszulSliceSection
        (completed (coefficientProEtaleModelTopology.{u, v} X) A J)
        (algebraSection (coefficientMap (coefficientProEtaleModelTopology.{u, v} X) A J)
          a) U).val V ^ (n + 1)) = 0 := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let W := op V.unop.left
  let η := toSheafify T ((Functor.const _).obj (CommRingCat.of A))
  let η' := toSheafify T ((Functor.const _).obj (CommRingCat.of (A ⧸ J ^ (n + 1))))
  let q : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ J ^ (n + 1)) :=
    CommRingCat.ofHom (Ideal.Quotient.mk _)
  have hc := congrArg (fun f ↦ f.hom.app W ((η.app W a) ^ (n + 1)))
    (limit.lift_π (quotientCone T A J) (op n))
  change (projection T A J n).hom.app W
    ((coefficientMap T A J).hom.app W ((η.app W a) ^ (n + 1))) = _ at hc
  rw [map_pow] at hc
  change (projection T A J n).hom.app W
    (((coefficientMap T A J).hom.app W (η.app W a)) ^ (n + 1)) = 0
  rw [hc]
  have hn := congrArg (fun f ↦ f.app W (a ^ (n + 1)))
    (toSheafify_naturality T ((Functor.const _).map q))
  change η'.app W (q (a ^ (n + 1))) =
    (quotient T A J n).hom.app W (η.app W (a ^ (n + 1))) at hn
  have hq : q (a ^ (n + 1)) = 0 := by
    change Ideal.Quotient.mk _ (a ^ (n + 1)) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow ha _)
  erw [← map_pow (η.app W).hom, ← hn, hq, map_zero]

private theorem scalarPower_quotientProjection (a : A) (ha : a ∈ J) (n : ℕ) :
    ((ringedKoszulScalar
      ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U)
      (ringedKoszulSliceSection
        (completed (coefficientProEtaleModelTopology.{u, v} X) A J)
        (algebraSection (coefficientMap (coefficientProEtaleModelTopology.{u, v} X) A J)
          a) U)) ^ (n + 1)).asHom ≫ quotientProjection X J U n = 0 := by
  let O := (completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U
  let b : (O.obj ⋙ CategoryTheory.forget CommRingCat).sections := ringedKoszulSliceSection
    (completed (coefficientProEtaleModelTopology.{u, v} X) A J)
    (algebraSection (coefficientMap (coefficientProEtaleModelTopology.{u, v} X) A J) a) U
  have hp (k : ℕ) (V : (Over U)ᵒᵖ) (x : O.obj.obj V) :
      ((ringedKoszulScalar O b) ^ k).asHom.val.app V x =
        x * (show O.obj.obj V from b.val V) ^ k := by
    induction k with
    | zero => change x = x * _ ^ 0; simp
    | succ k ih =>
      rw [pow_succ']
      change (ringedKoszulScalar O b).asHom.val.app V
        (((ringedKoszulScalar O b) ^ k).asHom.val.app V x) = _
      change (show O.obj.obj V from ((ringedKoszulScalar O b) ^ k).asHom.val.app V x) *
        (show O.obj.obj V from b.val V) = _
      rw [ih, pow_succ, mul_assoc]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (adicResidueLocalProjection X J U n).hom.app V
    (((ringedKoszulScalar O b) ^ (n + 1)).asHom.val.app V x) * 1 = 0
  rw [hp, map_mul, completedScalar_quotient_zero X J U a ha n V, mul_zero, zero_mul]

/-- Normalized maps to single complexes are natural when the unit is invertible in degree zero. -/
private theorem single_naturality_of_normalized_unit
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    {K L : CochainComplex C ℤ} {M N₁ N₂ : C}
    (u : (HomologicalComplex.single C (.up ℤ) 0).obj M ⟶ K)
    (v : (HomologicalComplex.single C (.up ℤ) 0).obj M ⟶ L)
    (i : ((HomologicalComplex.single C (.up ℤ) 0).obj M).X 0 ≅ K.X 0)
    (hi : i.hom = u.f 0) (f : K ⟶ L)
    (p : L ⟶ (HomologicalComplex.single C (.up ℤ) 0).obj N₂)
    (q : K ⟶ (HomologicalComplex.single C (.up ℤ) 0).obj N₁)
    (g : N₁ ⟶ N₂) (a₁ : M ⟶ N₁) (a₂ : M ⟶ N₂)
    (hf : u ≫ f = v)
    (hp : v ≫ p = (HomologicalComplex.single C (.up ℤ) 0).map a₂)
    (hq : u ≫ q = (HomologicalComplex.single C (.up ℤ) 0).map a₁)
    (ha : a₁ ≫ g = a₂) :
    f ≫ p = q ≫ (HomologicalComplex.single C (.up ℤ) 0).map g := by
  apply HomologicalComplex.to_single_hom_ext
  apply (Iso.cancel_iso_hom_left i _ _).1
  rw [hi]
  simp only [← HomologicalComplex.comp_f]
  rw [← Category.assoc, hf, hp, ← Category.assoc, hq, ← Functor.map_comp, ha]

attribute [local irreducible] completed homComplexFunctor

/-- Quotient maps annihilating the Koszul powers give a normalized augmentation
of the dual tower. -/
private theorem ringedKoszulDualTower_quotient_augmentation
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    (O : Sheaf S CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (O.obj ⋙ CategoryTheory.forget CommRingCat).sections)
    (Q : ℕ → Mod O) (s : ∀ n, Q (n + 1) ⟶ Q n)
    (q : ∀ n, SheafOfModules.unit (siteModuleRings O) ⟶ Q n)
    (hq : ∀ n, q (n + 1) ≫ s n = q n)
    (hscalar : ∀ n i, ((ringedKoszulScalar O (b i)) ^ (n + 1)).asHom ≫ q n = 0) :
    ∃ ε : ringedKoszulDualTower O r b ⟶ Functor.ofOpSequence
        (X := fun n ↦ (HomologicalComplex.single (Mod O) (.up ℤ) 0).obj (Q n))
        (fun n ↦ (HomologicalComplex.single (Mod O) (.up ℤ) 0).map (s n)),
      ∀ n : ℕ, ringedKoszulDualUnit O r b n ≫ ε.app (op n) =
        (HomologicalComplex.single (Mod O) (.up ℤ) 0).map (q n) := by
  let F := Functor.ofOpSequence (X := fun n ↦
    (HomologicalComplex.single (Mod O) (.up ℤ) 0).obj (Q n)) (fun n ↦
    (HomologicalComplex.single (Mod O) (.up ℤ) 0).map (s n))
  let T := ringedKoszulDualTower O r b
  obtain ⟨d, _, hu⟩ :
      ∃ d : ∀ n : ℕ, ringedNegativeKoszul O r b n ≅ T.obj (op n),
        (∀ n, ringedNegativeKoszulTransition O r b n ≫ (d n).hom =
          (d (n + 1)).hom ≫ T.map (homOfLE (Nat.le_succ n)).op) ∧
        (∀ n, ringedNegativeKoszulBasis O r b n ∅ 0 ≫ (d n).hom.f 0 =
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
            (ringedKoszulDualUnit O r b n).f 0) := by
    cases r with
    | zero => exact ringedNegativeKoszulZeroDuality O b
    | succ r => exact ringedNegativeKoszulSuccDuality O r b
  choose z t hz ht using fun n ↦ ringedNegativeKoszulLowDegrees O r b n
  have hkill (n : ℕ) :
      (ringedNegativeKoszul O r b n).d (-1) 0 ≫
        (z n).hom ≫ q n = 0 := by
    apply (cancel_epi (t n).hom).1
    apply biproduct.hom_ext'
    intro i
    have h := congrArg (fun f ↦ f ≫ q n) (ht n i)
    rw [hscalar n i] at h
    simpa only [Category.assoc, comp_zero] using h
  let p (n : ℕ) : (T.obj (op n)).X 0 ⟶ Q n :=
    (d n).inv.f 0 ≫ (z n).hom ≫ q n
  have hp (n : ℕ) (i : ℤ) (hi : (ComplexShape.up ℤ).Rel i 0) :
      (T.obj (op n)).d i 0 ≫ p n = 0 := by
    have hi' : i = -1 := by change i + 1 = 0 at hi; omega
    subst i
    dsimp only [p]
    rw [← (d n).inv.comm_assoc, hkill, comp_zero]
  let e (n : ℕ) : T.obj (op n) ⟶
      (HomologicalComplex.single (Mod O) (.up ℤ) 0).obj
        (Q n) :=
    HomologicalComplex.mkHomToSingle (p n) (hp n)
  have hunit0 (n : ℕ) : (ringedKoszulDualUnit O r b n).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).hom ≫
        (z n).inv ≫ (d n).hom.f 0 := by
    rw [hz]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
      congrArg (fun f ↦ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).hom ≫ f)
        (hu n).symm
  have hnorm (n : ℕ) : ringedKoszulDualUnit O r b n ≫ e n =
      (HomologicalComplex.single (Mod O) (.up ℤ) 0).map (q n) := by
    apply HomologicalComplex.from_single_hom_ext
    dsimp only [HomologicalComplex.comp_f, e]
    rw [HomologicalComplex.mkHomToSingle_f, hunit0]
    have hdi : (d n).hom.f 0 ≫ (d n).inv.f 0 = 𝟙 _ := by
      exact congrArg (fun f ↦ f.f 0) (d n).hom_inv_id
    dsimp only [p]
    simp only [Category.assoc]
    rw [reassoc_of% hdi, Iso.inv_hom_id_assoc]
    exact (HomologicalComplex.single_map_f_self _ _ _).symm
  have hunit_naturality (n : ℕ) :
      ringedKoszulDualUnit O r b (n + 1) ≫
        T.map (homOfLE (Nat.le_succ n)).op = ringedKoszulDualUnit O r b n := by
    dsimp only [T, ringedKoszulDualUnit, ringedKoszulDualTower, Functor.comp_map,
      Functor.op_map, Functor.flip_obj_map]
    rw [Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp, ← op_comp,
      ringedKoszulProjection_naturality]
  have hstep (n : ℕ) :
      T.map (homOfLE (Nat.le_succ n)).op ≫ e n =
        e (n + 1) ≫ F.map
          (homOfLE (Nat.le_succ n)).op := by
    have hmap : F.map
        (homOfLE (Nat.le_succ n)).op =
        (HomologicalComplex.single (Mod O) (.up ℤ) 0).map
          (s n) := by
      exact Functor.ofOpSequence_map_homOfLE_succ _ n
    rw [hmap]
    let u := HomologicalComplex.singleObjXSelf (.up ℤ) 0 _ ≪≫
      (z (n + 1)).symm ≪≫ (HomologicalComplex.eval (Mod O) (.up ℤ) 0).mapIso
        (d (n + 1))
    exact single_naturality_of_normalized_unit (C := Mod O)
      (ringedKoszulDualUnit O r b (n + 1)) (ringedKoszulDualUnit O r b n)
      u (hunit0 (n + 1)).symm (T.map (homOfLE (Nat.le_succ n)).op) (e n) (e (n + 1))
      (s n)
      (q (n + 1)) (q n)
      (hunit_naturality n) (hnorm n) (hnorm (n + 1)) (hq n)
  exact ⟨NatTrans.ofOpSequence e hstep, hnorm⟩

/-- The coefficient augmentation exists before tensoring with any complex.
In particular neither K-flatness nor Noetherianity is needed for this construction.

Source: Stacks Project, algebraization.tex, lemma-derived-completion-koszul (0A0E),
and proetale.tex, lemma-naive-completion (099M).
(auxiliary; not a blueprint node).

Proof: identify the dual of the ordered positive finite free Koszul complex with
the negative exterior Koszul complex using the standard dual bases and Hom-complex
signs. Its degree-zero term is R and its differential into that term has image
in the ideal generated by the completed a_i^(n+1). These sections vanish in the
actual quotient B_n: each a_i lies in J and the quotient kills J^(n+1).
Consequently the quotient R to B_n in degree zero, with zero components in every
other degree, is a chain map. The diagonal power transitions are the identity
in degree zero, hence commute with these quotient maps. They give the required
natural transformation epsilon. The degree-zero dual Koszul unit sends 1 to 1,
which proves the normalization. The empty list gives the ordinary quotient of R
(the hypothesis then forces no extra generators); the same formulas handle
J equal to the unit ideal and the zero ring. No derived statement is used. -/
theorem adicResidue_koszul_coefficient_augmentation
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) ≤ J) :
    let R := (completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U
    let b := fun i ↦ ringedKoszulSliceSection
      (completed (coefficientProEtaleModelTopology.{u, v} X) A J)
      (algebraSection (coefficientMap (coefficientProEtaleModelTopology.{u, v} X) A J)
        (a i)) U
    ∃ ε : ringedKoszulDualTower R r b ⟶ adicResidueQuotientCoefficientTower X J U,
      ∀ n : ℕ, ringedKoszulDualUnit R r b n ≫ ε.app (op n) =
        adicResidueQuotientCoefficientUnit X J U n := by
  dsimp only
  have h := ringedKoszulDualTower_quotient_augmentation
    ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U) r
    (fun i ↦ ringedKoszulSliceSection
      (completed (coefficientProEtaleModelTopology.{u, v} X) A J)
      (algebraSection (coefficientMap (coefficientProEtaleModelTopology.{u, v} X) A J)
        (a i)) U)
    (adicResidueQuotientModule.{u, v} X J U)
    (fun n ↦ adicResidueQuotientModuleStep.{u, v} X J U n)
    (fun n ↦ quotientProjection.{u, v} X J U n)
    (fun n ↦ quotientProjection_step.{u, v} X J U n)
    (fun n i ↦ scalarPower_quotientProjection.{u, v} X J U (a i)
      (ha (Ideal.subset_span (Set.mem_range_self i))) n)
  simpa only [quotientProjection, adicResidueQuotientCoefficientTower,
    adicResidueQuotientCoefficientUnit] using h

set_option hygiene false in
set_option quotPrecheck false in
local notation "R" => ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U)

/-- Transposition preserves the adjacent differential of the strict Koszul tower. -/
theorem adicResidueKoszulTensorTranspose_comm
    (r : ℕ)
    (b : Fin r → (((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U).obj ⋙
      CategoryTheory.forget CommRingCat).sections)
    (P : Cx ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U))
    (i j : ℤ) (h : (ComplexShape.up ℤ).Rel i j) :
    (ringedKoszulTensorTowerComplex R r b P).d i j =
      ((HomologicalComplex.functorEquivalence (Mod R) (.up ℤ) ℕᵒᵖ).inverse.obj
        ((ringedKoszulTensorTower R r b).obj P)).d i j := by
  have hj : i + 1 = j := h
  subst j
  simp only [ringedKoszulTensorTowerComplex, HomologicalComplex.functorEquivalence,
    HomologicalComplex.functorEquivalence.inverse, CochainComplex.of_d]

/-- The comparison from the explicit adjacent-differential model to transposition. -/
def adicResidueKoszulTensorTranspose
    (r : ℕ)
    (b : Fin r → (((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U).obj ⋙
      CategoryTheory.forget CommRingCat).sections)
    (P : Cx ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U)) :
    ringedKoszulTensorTowerComplex R r b P ≅
      (HomologicalComplex.functorEquivalence (Mod R) (.up ℤ) ℕᵒᵖ).inverse.obj
        ((ringedKoszulTensorTower R r b).obj P) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (fun i j h ↦ by
    simpa only [Iso.refl_hom, Category.id_comp, Category.comp_id] using
      (adicResidueKoszulTensorTranspose_comm X J U r b P i j h).symm)

/-- Tensor a given coefficient augmentation and transpose its actual chain maps. -/
@[irreducible] def adicResidueKoszulTensorAugmentation
    (r : ℕ)
    (b : Fin r → (((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U).obj ⋙
      CategoryTheory.forget CommRingCat).sections)
    (P : Cx ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U))
    (ε : ringedKoszulDualTower R r b ⟶ adicResidueQuotientCoefficientTower X J U) :
    ringedKoszulTensorTowerComplex R r b P ⟶ adicResidueQuotientTensorComplex X J U P := by
  refine (adicResidueKoszulTensorTranspose X J U r b P).hom ≫ ?_
  change
    (HomologicalComplex.functorEquivalence (Mod R) (.up ℤ) ℕᵒᵖ).inverse.obj
        (ringedKoszulDualTower R r b ⋙ (ringedKoszulTensor R).obj P) ⟶
      (HomologicalComplex.functorEquivalence (Mod R) (.up ℤ) ℕᵒᵖ).inverse.obj
        (adicResidueQuotientCoefficientTower X J U ⋙ (ringedKoszulTensor R).obj P)
  exact (HomologicalComplex.functorEquivalence (Mod R) (.up ℤ) ℕᵒᵖ).inverse.map
    (Functor.whiskerRight ε ((ringedKoszulTensor R).obj P))

end AlgebraicGeometry.Scheme
