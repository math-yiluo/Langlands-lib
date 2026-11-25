/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseReductionConstruction
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseCoefficientQuotients
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible

/-!
# Compatible local bases for normalized towers

## References

* Bhatt--Scholze, Proposition 6.8.4(1), compatible-basis argument
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w z
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- Naturality of the canonical reduction projections on every module map. -/
private theorem integralLisseCokernelCone_natural
    {M N : ringedSiteModules.{u + 1} (integralLisseRing l E X)}
    (f : M ⟶ N) (n : ℕ) :
    f ≫ (integralLisseCokernelCone l E X N).app (op n) =
      (integralLisseCokernelCone l E X M).app (op n) ≫
        (integralLisseCokernelMap l E X f).app (op n) := by
  simp [integralLisseCokernelCone, integralLisseCokernelMap, cokernel.map]

/-- The concrete quotient-tower functor is additive. -/
private instance integralLisseCokernelFunctor_additive :
    (integralLisseCokernelFunctor l E X).Additive where
  map_add {M N} f g := by
    apply NatTrans.ext
    funext n
    apply (cancel_epi (cokernel.π _)).1
    change (integralLisseCokernelCone l E X M).app n ≫
        (integralLisseCokernelMap l E X (f + g)).app n = _
    rw [← integralLisseCokernelCone_natural l E X (f + g) n.unop]
    simp only [Preadditive.add_comp, Preadditive.comp_add, NatTrans.app_add]
    rw [integralLisseCokernelCone_natural l E X f n.unop,
      integralLisseCokernelCone_natural l E X g n.unop]
    rfl

/-- A section over an object defines compatible sections on its slice. -/
def integralLisseSectionOver
    (M : ringedSiteModules.{u + 1} (integralLisseRing l E X)) (U : X.ProEt)
    (x : M.val.obj (op U)) : (M.over U).sections :=
  PresheafOfModules.sectionsMk
    (fun V ↦ M.val.map V.unop.hom.op x) (by
      intro V W g
      change M.val.map g.unop.left.op (M.val.map V.unop.hom.op x) =
        M.val.map W.unop.hom.op x
      rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w])

private theorem lift_iso_square_zero {C : Type u} [Category.{v} C] [Abelian C]
    {P Q P₀ Q₀ : C} (aP : P ⟶ P) (aQ : Q ⟶ Q)
    (qP : P ⟶ P₀) (qQ : Q ⟶ Q₀)
    (hP : aP ≫ qP = 0) (hQ : aQ ≫ qQ = 0)
    (exP : (ShortComplex.mk aP qP hP).Exact)
    (exQ : (ShortComplex.mk aQ qQ hQ).Exact)
    (b : P ⟶ Q) (e : P₀ ≅ Q₀) (hb : b ≫ qQ = qP ≫ e.hom)
    (g : Q ⟶ P) (hg : g ≫ qP = qQ ≫ e.inv)
    (hbp : aP ≫ b = b ≫ aQ) (hgp : aQ ≫ g = g ≫ aP)
    (hPP : aP ≫ aP = 0) (hQQ : aQ ≫ aQ = 0) : IsIso b := by
  let dP := b ≫ g - 𝟙 P
  let dQ := g ≫ b - 𝟙 Q
  have hdP : dP ≫ qP = 0 := by
    simp [dP, Category.assoc, hg, reassoc_of% hb]
  have hdQ : dQ ≫ qQ = 0 := by
    simp [dQ, Category.assoc, hb, reassoc_of% hg]
  have hcP : aP ≫ dP = dP ≫ aP := by
    simp only [dP, Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
      Category.id_comp]
    rw [← Category.assoc, hbp, Category.assoc, hgp, Category.assoc]
  have hcQ : aQ ≫ dQ = dQ ≫ aQ := by
    simp only [dQ, Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
      Category.id_comp]
    rw [← Category.assoc, hgp, Category.assoc, hbp, Category.assoc]
  have hzP : dP ≫ dP = 0 :=
    exP.comp_eq_zero hdP (hcP.trans (exP.comp_eq_zero hdP hPP))
  have hzQ : dQ ≫ dQ = 0 :=
    exQ.comp_eq_zero hdQ (hcQ.trans (exQ.comp_eq_zero hdQ hQQ))
  have hbg : b ≫ g = 𝟙 P + dP := by dsimp [dP]; abel
  have hgb : g ≫ b = 𝟙 Q + dQ := by dsimp [dQ]; abel
  have hcor : g ≫ (𝟙 P - dP) = (𝟙 Q - dQ) ≫ g := by
    simp [dP, dQ, Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc]
  refine ⟨⟨g ≫ (𝟙 P - dP), ?_, ?_⟩⟩
  · rw [← Category.assoc, hbg]
    simp only [Preadditive.add_comp, Preadditive.comp_sub, Category.id_comp,
      Category.comp_id, hzP]
    abel
  · rw [hcor, Category.assoc, hgb]
    simp only [Preadditive.comp_add, Preadditive.sub_comp, Category.id_comp,
      Category.comp_id, hzQ]
    abel

private theorem lift_iso_of_projective_presentation
    {C : Type u} [Category.{v} C] [Abelian C]
    (a k : 𝟭 C ⟶ 𝟭 C) {P Q P₀ Q₀ T : C}
    (qP : P ⟶ P₀) (qQ : Q ⟶ Q₀) [Epi qP]
    (hP : a.app P ≫ qP = 0) (hQ : a.app Q ≫ qQ = 0)
    (exP : (ShortComplex.mk (a.app P) qP hP).Exact)
    (exQ : (ShortComplex.mk (a.app Q) qQ hQ).Exact)
    (b : P ⟶ Q) (e : P₀ ≅ Q₀) (hb : b ≫ qQ = qP ≫ e.hom)
    (hPP : a.app P ≫ a.app P = 0) (hQQ : a.app Q ≫ a.app Q = 0)
    [Projective T] (c : T ⟶ Q) (hc : k.app T ≫ c = 0)
    (hcol : IsColimit (CokernelCofork.ofπ c hc)) (hkP : k.app P = 0) :
    IsIso b := by
  let t := Projective.factorThru (c ≫ qQ ≫ e.inv) qP
  have ht : t ≫ qP = c ≫ qQ ≫ e.inv := Projective.factorThru_comp _ _
  have hkt : k.app T ≫ t = 0 := by
    calc
      k.app T ≫ t = t ≫ k.app P := (k.naturality t).symm
      _ = 0 := by rw [hkP, comp_zero]
  let g := hcol.desc (CokernelCofork.ofπ t hkt)
  have hcg : c ≫ g = t := hcol.fac _ WalkingParallelPair.one
  have hg : g ≫ qP = qQ ≫ e.inv := by
    have : Epi c := Cofork.IsColimit.epi hcol
    apply (cancel_epi c).1
    rw [← Category.assoc, hcg, ht]
  exact lift_iso_square_zero (a.app P) (a.app Q) qP qQ hP hQ exP exQ b e hb
    g hg (a.naturality b).symm (a.naturality g).symm hPP hQQ

private theorem sheaf_iso_of_basis {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {M N : Sheaf J AddCommGrpCat.{w}} (b : M ⟶ N)
    (h : ∀ V : C, ∃ (I : Type z) (W : I → C) (f : ∀ i, W i ⟶ V),
      (∀ i, Function.Bijective (b.hom.app (op (W i)))) ∧
        Sieve.ofArrows W f ∈ J V) : IsIso b := by
  have hi : ∀ V : Cᵒᵖ, Function.Injective (b.hom.app V) := by
    intro V x y hxy
    obtain ⟨I, W, f, hw, hcov⟩ := h V.unop
    apply Sheaf.isSeparated M V.unop _ hcov x y
    rintro Z g ⟨_, a, _, ⟨i⟩, rfl⟩
    have he : M.obj.map (f i).op x = M.obj.map (f i).op y := by
      apply (hw i).1
      simpa only [NatTrans.naturality_apply] using congrArg (N.obj.map (f i).op) hxy
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, he]
  have hinj : Sheaf.IsLocallyInjective b := (Sheaf.isLocallyInjective_iff_injective b).2 hi
  have hsurj : Sheaf.IsLocallySurjective b := by
    constructor
    intro V s
    obtain ⟨I, W, f, hw, hcov⟩ := h V
    apply J.superset_covering ((Sieve.generate_le_iff _ _).mpr ?_) hcov
    intro Z g hg
    obtain ⟨i⟩ := hg
    exact (hw i).2 (N.obj.map (f i).op s)
  exact (Sheaf.isLocallyBijective_iff_isIso b).1 ⟨hinj, hsurj⟩

private theorem evaluation_exact (W : X.ProEt)
    (hW : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W) :
    PreservesFiniteColimits
      (SheafOfModules.evaluation.{u + 1} (integralLisseRing l E X) (op W)) := by
  let ev := SheafOfModules.evaluation.{u + 1} (integralLisseRing l E X) (op W)
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{u + 1}
      (integralLisseRing l E X)) :=
    (moduleSheaves_colimits_forgetful (integralLisseRing l E X)).2.2.1
  have : ev.Additive := ⟨by intros; rfl⟩
  have : ev.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    let g := (SheafOfModules.toSheaf (integralLisseRing l E X)).map f
    have hg : Sheaf.IsLocallySurjective g :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1} g).2 inferInstance
    apply (ModuleCat.epi_iff_surjective _).2
    exact hW ((sheafCompose _ (forget AddCommGrpCat.{u + 1})).map g)
      ((Presheaf.isLocallySurjective_iff_whisker_forget _ _).1 hg)
  have : ev.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels ev
  exact Functor.preservesFiniteColimits_of_preservesHomology ev

private def freeFiniteIso (K : Type (u + 1)) [Finite K] (n : ℕ) :
    (integralLisseFiniteRestriction l E X n).obj (SheafOfModules.free K) ≅
      integralLisseCokernel l E X (SheafOfModules.free K) n := by
  classical
  let S := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (integralLisseFiniteRing l E X n)
  let res := integralLisseFiniteRestriction l E X n
  have : res.Additive := by dsimp [res, integralLisseFiniteRestriction]; infer_instance
  let Q := integralLisseCokernelFunctor l E X ⋙
    (CategoryTheory.evaluation ℕᵒᵖ _).obj (op n)
  let T := SheafOfModules.unit (integralLisseRing l E X)
  let p := integralLisseRingMap l E X
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (integralLisseReduction l E X n))
  let e : Q.obj T ≅ res.obj (SheafOfModules.unit S) :=
    have := isIso_integralLisseQuotient_desc l E X _ p
      (integralLisseCoefficient_quotients l E X n)
    asIso (cokernel.desc _ p (integralLisseCoefficient_quotients l E X n).choose)
  exact PreservesCoproduct.iso res (fun _ : K ↦ SheafOfModules.unit S) ≪≫
    Sigma.mapIso (fun _ : K ↦ e.symm) ≪≫
    (PreservesCoproduct.iso Q (fun _ : K ↦ T)).symm

private theorem finiteCharts (F : IntegralReductionTower l E X) (n : ℕ) :
    ∃ (I : Type (u + 1)) (U : I → X.ProEt) (K : I → Type (u + 1)),
      (Scheme.ProEt.topology X).CoversTop U ∧ (∀ i, Finite (K i)) ∧
      ∀ i, Nonempty ((F.obj.obj (op n)).over (U i) ≅
        (integralLisseCokernel l E X
          (SheafOfModules.free (R := integralLisseRing l E X) (K i)) n).over (U i)) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := F.property.1 n
  obtain ⟨q, hq, hf⟩ := hN.exists_localGeneratorsData
  let S := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (integralLisseFiniteRing l E X n)
  let ρ := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (integralLisseReduction l E X n)
  refine ⟨q.I, q.X, fun i ↦ (q.generators i).I, q.coversTop, ?_, ?_⟩
  · intro i
    have := hf.isFiniteType i
    infer_instance
  · intro i
    have := hf.isFiniteType i
    have := hq.isIso i
    let G := SheafOfModules.overFunctor.{u + 1} S (q.X i)
    let H := SheafOfModules.overFunctor.{u + 1} (integralLisseRing l E X) (q.X i)
    have := (ringedOverFunctor_exactGeneral S (q.X i)).1
    let ρU := ((Scheme.ProEt.topology X).overPullback RingCat.{u + 1} (q.X i)).map ρ
    let resU := SheafOfModules.restrictScalars.{u + 1} ρU
    let c : N.over (q.X i) ≅ (SheafOfModules.free
        (R := S) (q.generators i).I).over (q.X i) :=
      (asIso (q.generators i).π).symm ≪≫
        SheafOfModules.mapFreeIso G _ (Iso.refl _)
    exact ⟨H.mapIso e.symm ≪≫ resU.mapIso c ≪≫
      H.mapIso (freeFiniteIso l E X (q.generators i).I n)⟩

private theorem evaluated_free_projective (W : X.ProEt)
    (hW : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W)
    (K : Type (u + 1)) [Finite K] :
    Projective ((SheafOfModules.free (R := integralLisseRing l E X) K).val.obj (op W)) := by
  classical
  let ev := SheafOfModules.evaluation.{u + 1} (integralLisseRing l E X) (op W)
  have := evaluation_exact l E X W hW
  have : Projective (ev.obj (SheafOfModules.unit (integralLisseRing l E X))) := by
    change Projective (ModuleCat.of ((integralLisseRing l E X).obj.obj (op W))
      ((integralLisseRing l E X).obj.obj (op W)))
    infer_instance
  exact Projective.of_iso
    (PreservesCoproduct.iso ev (fun _ : K ↦
      SheafOfModules.unit (integralLisseRing l E X))).symm inferInstance

private def evaluatedScalar (W : X.ProEt) (a : Padic.coefficientExtensionIntegers l E) :
    𝟭 (ModuleCat.{u + 1} ((integralLisseRing l E X).obj.obj (op W))) ⟶ 𝟭 _ where
  app M := ModuleCat.ofHom
    { toFun := fun x ↦ lisseIntegerConstantSized l E X (op W) a • x
      map_add' := smul_add _
      map_smul' := fun r x ↦ by
        rw [smul_smul, smul_smul]
        exact congrArg (fun c : (lisseIntegerSheafSized l E X).obj.obj (op W) ↦ c • x)
          (mul_comm _ _) }
  naturality {_ _} f := by
    ext x
    exact (f.hom.map_smul _ x).symm

private theorem scalarCokernel_zero
    (M : ringedSiteModules.{u + 1} (integralLisseRing l E X)) (n : ℕ) :
    integralLisseScalar l E X (integralLisseCokernel l E X M n)
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) = 0 := by
  apply (cancel_epi (cokernel.π (integralLisseScalar l E X M
    (Padic.coefficientExtensionUniformizer l E ^ (n + 1))))).1
  exact (integralLisseScalar_natural l E X (cokernel.π _) _).symm.trans
    ((cokernel.condition _).trans comp_zero.symm)

private theorem towerScalar_zero (F : IntegralReductionTower l E X) (n : ℕ) :
    integralLisseScalar l E X (F.obj.obj (op n))
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) = 0 := by
  obtain ⟨N, _, ⟨e⟩⟩ := F.property.1 n
  apply (cancel_epi e.hom).1
  rw [← integralLisseScalar_natural]
  suffices integralLisseScalar l E X
      ((integralLisseFiniteRestriction l E X n).obj N)
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) = 0 by
    rw [this, zero_comp, comp_zero]
  let := spectralNorm.normedField ℚ_[l] E
  ext U x
  have hz : (integralLisseReduction l E X n).hom.app U
      (lisseIntegerConstantSized l E X U
        (Padic.coefficientExtensionUniformizer l E ^ (n + 1))) = 0 := by
    apply ULift.ext
    apply ContinuousMap.ext
    intro y
    change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change _ ∈ Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ (n + 1)
    rw [Ideal.span_singleton_pow]
    exact Ideal.subset_span (Set.mem_singleton _)
  change N.val.obj U at x
  change (integralLisseReduction l E X n).hom.app U _ • x = 0
  rw [hz, zero_smul]

private theorem scalar_square_zero
    (M : ringedSiteModules.{u + 1} (integralLisseRing l E X)) (n : ℕ)
    (h : integralLisseScalar l E X M
      (Padic.coefficientExtensionUniformizer l E ^ (n + 2)) = 0) :
    integralLisseScalar l E X M (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) ≫
      integralLisseScalar l E X M (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) =
        0 := by
  rw [← integralLisseScalar_mul]
  have hp : Padic.coefficientExtensionUniformizer l E ^ (n + 1) *
      Padic.coefficientExtensionUniformizer l E ^ (n + 1) =
      Padic.coefficientExtensionUniformizer l E ^ n *
        Padic.coefficientExtensionUniformizer l E ^ (n + 2) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [hp, integralLisseScalar_mul, h, zero_comp]

private theorem over_iso_of_wc_charts {M N : ringedSiteModules.{u + 1}
    (integralLisseRing l E X)} (W : X.ProEt) (b : M.over W ⟶ N.over W)
    {I : Type (u + 1)} (U : I → X.ProEt)
    (hU : (Scheme.ProEt.topology X).CoversTop U)
    (h : ∀ (V : X.ProEt) (f : V ⟶ W),
      (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} V →
        ∀ i, (V ⟶ U i) → IsIso (b.val.app (op (Over.mk f)))) : IsIso b := by
  suffices IsIso ((SheafOfModules.toSheaf
      ((integralLisseRing l E X).over W)).map b) from
    isIso_of_reflects_iso b (SheafOfModules.toSheaf ((integralLisseRing l E X).over W))
  apply sheaf_iso_of_basis
  intro Y
  let A := (V : X.ProEt) × { f : V ⟶ Y.left //
    (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} V ∧
      ∃ i, Nonempty (V ⟶ U i) }
  let Z (a : A) : Over W := Over.mk (a.2.val ≫ Y.hom)
  let g (a : A) : Z a ⟶ Y := Over.homMk a.2.val rfl
  refine ⟨A, Z, g, ?_, ?_⟩
  · intro a
    obtain ⟨i, ⟨f⟩⟩ := a.2.property.2
    have := h a.1 (a.2.val ≫ Y.hom) a.2.property.1 i f
    exact ConcreteCategory.bijective_of_isIso (b.val.app (op (Over.mk (a.2.val ≫ Y.hom))))
  · rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    apply (Scheme.ProEt.topology X).transitive (hU Y.left)
    rintro V f ⟨i, ⟨k⟩⟩
    obtain ⟨B, T, t, ht, hcov⟩ :=
      Scheme.ProEt.exists_isWeaklyContractible_cover.{u + 1} V
    apply (Scheme.ProEt.topology X).superset_covering ?_ hcov
    apply (Sieve.generate_le_iff _ _).2
    intro V' a ha
    obtain ⟨j⟩ := ha
    change (Sieve.ofArrows (fun a : A ↦ (Z a).left)
      (fun a ↦ (g a).left)) (t j ≫ f)
    exact Sieve.ofArrows_mk _ _
      (⟨T j, ⟨t j ≫ f, (ht j).2, ⟨i, ⟨t j ≫ k⟩⟩⟩⟩ : A)

private theorem lift_level_iso (F : IntegralReductionTower l E X)
    (K : Type (u + 1)) [Finite K] (W : X.ProEt) (n : ℕ)
    (b : (integralLisseCokernel l E X (SheafOfModules.free K) (n + 1)).over W ⟶
      (F.obj.obj (op (n + 1))).over W)
    (e : (integralLisseCokernel l E X (SheafOfModules.free K) n).over W ≅
      (F.obj.obj (op n)).over W)
    (hb : b ≫ (F.obj.map (homOfLE (Nat.le_succ n)).op).over W =
      (integralLisseCokernelTransition l E X (SheafOfModules.free K) n).over W ≫ e.hom) :
    IsIso b := by
  classical
  obtain ⟨I, U, J, hU, hJ, hchart⟩ := finiteCharts l E X F (n + 1)
  apply over_iso_of_wc_charts l E X W b U hU
  intro V f hV i g
  let : Finite (J i) := hJ i
  let ev := SheafOfModules.evaluation.{u + 1} (integralLisseRing l E X) (op V)
  have : ev.Additive := ⟨by intros; rfl⟩
  have := evaluation_exact l E X V hV
  let P := integralLisseCokernel l E X (SheafOfModules.free K) (n + 1)
  let Q := F.obj.obj (op (n + 1))
  let qP := integralLisseCokernelTransition l E X (SheafOfModules.free K) n
  let qQ := F.obj.map (homOfLE (Nat.le_succ n)).op
  let a := evaluatedScalar l E X V (Padic.coefficientExtensionUniformizer l E ^ (n + 1))
  let k := evaluatedScalar l E X V (Padic.coefficientExtensionUniformizer l E ^ (n + 2))
  obtain ⟨hP, ⟨hcP⟩⟩ :=
    integralLisseCokernelTransition_quotient l E X (SheafOfModules.free K) n
  obtain ⟨hQ, ⟨hcQ⟩⟩ := F.property.2 n
  have hP' : a.app (ev.obj P) ≫ ev.map qP = 0 := by
    exact ev.map_comp _ _ |>.symm.trans ((congrArg ev.map hP).trans (ev.map_zero _ _))
  have hQ' : a.app (ev.obj Q) ≫ ev.map qQ = 0 := by
    exact ev.map_comp _ _ |>.symm.trans ((congrArg ev.map hQ).trans (ev.map_zero _ _))
  have exP : (ShortComplex.mk (a.app (ev.obj P)) (ev.map qP) hP').Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (CokernelCofork.mapIsColimit _ hcP ev)
  have exQ : (ShortComplex.mk (a.app (ev.obj Q)) (ev.map qQ) hQ').Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (CokernelCofork.mapIsColimit _ hcQ ev)
  have : Epi qP := Cofork.IsColimit.epi hcP
  let evW := SheafOfModules.evaluation.{u + 1}
    ((integralLisseRing l E X).over W) (op (Over.mk f))
  let e₀ : ev.obj (integralLisseCokernel l E X (SheafOfModules.free K) n) ≅
      ev.obj (F.obj.obj (op n)) := evW.mapIso e
  have hb' : b.val.app (op (Over.mk f)) ≫ ev.map qQ = ev.map qP ≫ e₀.hom :=
    congrArg (fun t ↦ t.val.app (op (Over.mk f))) hb
  have hpzero : k.app (ev.obj P) = 0 := by
    exact congrArg (fun t ↦ t.val.app (op V))
      (scalarCokernel_zero l E X (SheafOfModules.free K) (n + 1))
  have hPP : a.app (ev.obj P) ≫ a.app (ev.obj P) = 0 := by
    exact ev.map_comp _ _ |>.symm.trans
      ((congrArg ev.map (scalar_square_zero l E X P n
        (scalarCokernel_zero l E X (SheafOfModules.free K) (n + 1)))).trans (ev.map_zero _ _))
  have hQQ : a.app (ev.obj Q) ≫ a.app (ev.obj Q) = 0 := by
    exact ev.map_comp _ _ |>.symm.trans
      ((congrArg ev.map (scalar_square_zero l E X Q n
        (towerScalar_zero l E X F (n + 1)))).trans (ev.map_zero _ _))
  let T := SheafOfModules.free (R := integralLisseRing l E X) (J i)
  let r := cokernel.π (integralLisseScalar l E X T
    (Padic.coefficientExtensionUniformizer l E ^ (n + 2)))
  let c₀ : ev.obj (integralLisseCokernel l E X T (n + 1)) ≅ ev.obj Q :=
    (SheafOfModules.evaluation.{u + 1}
    ((integralLisseRing l E X).over (U i)) (op (Over.mk g))).mapIso (hchart i).some.symm
  let c : ev.obj T ⟶ ev.obj Q := ev.map r ≫ c₀.hom
  have hrc : k.app (ev.obj T) ≫ c = 0 := by
    dsimp only [c]
    rw [← Category.assoc]
    change ev.map (integralLisseScalar l E X T
      (Padic.coefficientExtensionUniformizer l E ^ (n + 2))) ≫ ev.map r ≫ c₀.hom = 0
    rw [← Category.assoc, ← ev.map_comp, cokernel.condition, ev.map_zero, zero_comp]
  have hrc₀ : k.app (ev.obj T) ≫ ev.map r = 0 := by
    change ev.map (integralLisseScalar l E X T
      (Padic.coefficientExtensionUniformizer l E ^ (n + 2))) ≫ ev.map r = 0
    rw [← ev.map_comp, cokernel.condition, ev.map_zero]
  have hrcol : IsColimit (CokernelCofork.ofπ (ev.map r) hrc₀) :=
    CokernelCofork.mapIsColimit _ (cokernelIsCokernel _) ev
  have : Epi (ev.map r) := inferInstance
  have hc : IsColimit (CokernelCofork.ofπ c hrc) := by
    refine CokernelCofork.IsColimit.ofπ' c hrc ?_
    intro B t ht
    refine ⟨c₀.inv ≫ hrcol.desc (CokernelCofork.ofπ t ht), ?_⟩
    dsimp only [c]
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact hrcol.fac _ WalkingParallelPair.one
  have : Projective (ev.obj T) := evaluated_free_projective l E X V hV (J i)
  exact lift_iso_of_projective_presentation a k (ev.map qP) (ev.map qQ)
    hP' hQ' exP exQ (b.val.app (op (Over.mk f))) e₀ hb' hPP hQQ c hrc hc hpzero

private theorem compatibleFreeMaps (F : IntegralReductionTower l E X)
    (W : X.ProEt) (hW : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W)
    (K : Type (u + 1))
    (q : SheafOfModules.free (R := (integralLisseRing l E X).over W) K ⟶
      (F.obj.obj (op 0)).over W) :
    ∃ p : ∀ n : ℕ,
      SheafOfModules.free (R := (integralLisseRing l E X).over W) K ⟶
        (F.obj.obj (op n)).over W,
      p 0 = q ∧ ∀ n : ℕ, p (n + 1) ≫
        (F.obj.map (homOfLE (Nat.le_succ n)).op).over W = p n := by
  classical
  let ev := SheafOfModules.evaluation.{u + 1} (integralLisseRing l E X) (op W)
  have := evaluation_exact l E X W hW
  have ht (n : ℕ) : Function.Surjective
      ((F.obj.map (homOfLE (Nat.le_succ n)).op).val.app (op W)).hom := by
    obtain ⟨h, ⟨hc⟩⟩ := F.property.2 n
    have : Epi (F.obj.map (homOfLE (Nat.le_succ n)).op) := Cofork.IsColimit.epi hc
    exact (ModuleCat.epi_iff_surjective _).1
      (inferInstanceAs (Epi (ev.map (F.obj.map (homOfLE (Nat.le_succ n)).op))))
  let x (j : K) := (((F.obj.obj (op 0)).over W).freeHomEquiv q j).val
    (op (Over.mk (𝟙 W)))
  let s (j : K) : ∀ n : ℕ, (F.obj.obj (op n)).val.obj (op W) :=
    Nat.rec (x j) (fun n y ↦ Function.surjInv (ht n) y)
  have hs (j : K) (n : ℕ) :
      (F.obj.map (homOfLE (Nat.le_succ n)).op).val.app (op W) (s j (n + 1)) = s j n :=
    Function.surjInv_eq (ht n) (s j n)
  let p := fun n ↦ ((F.obj.obj (op n)).over W).freeHomEquiv.symm
    (fun j ↦ integralLisseSectionOver l E X (F.obj.obj (op n)) W (s j n))
  refine ⟨p, ?_, ?_⟩
  · apply (((F.obj.obj (op 0)).over W).freeHomEquiv).injective
    funext j
    simp only [p, Equiv.apply_symm_apply]
    apply PresheafOfModules.sections_ext
    intro V
    change (F.obj.obj (op 0)).val.map V.unop.hom.op (x j) = _
    exact PresheafOfModules.sections_property
      (((F.obj.obj (op 0)).over W).freeHomEquiv q j)
      (Over.homMk V.unop.hom (by simp) : V.unop ⟶ Over.mk (𝟙 W)).op
  · intro n
    apply (((F.obj.obj (op n)).over W).freeHomEquiv).injective
    funext j
    rw [SheafOfModules.freeHomEquiv_comp_apply]
    simp only [p, Equiv.apply_symm_apply]
    apply PresheafOfModules.sections_ext
    intro V
    change (F.obj.map (homOfLE (Nat.le_succ n)).op).val.app (op V.unop.left)
        ((F.obj.obj (op (n + 1))).val.map V.unop.hom.op (s j (n + 1))) =
      (F.obj.obj (op n)).val.map V.unop.hom.op (s j n)
    rw [PresheafOfModules.naturality_apply, hs]

private theorem localTowerIso (F : IntegralReductionTower l E X)
    (W : X.ProEt) (hW : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W)
    (K : Type (u + 1)) [Finite K]
    (e : (integralLisseCokernel l E X (SheafOfModules.free K) 0).over W ≅
      (F.obj.obj (op 0)).over W) :
    Nonempty (F.obj ⋙ SheafOfModules.overFunctor (integralLisseRing l E X) W ≅
      integralLisseCokernelTower l E X (SheafOfModules.free K) ⋙
        SheafOfModules.overFunctor (integralLisseRing l E X) W) := by
  classical
  let H := SheafOfModules.overFunctor.{u + 1} (integralLisseRing l E X) W
  have := (ringedOverFunctor_exactGeneral (integralLisseRing l E X) W).1
  have := (ringedOverFunctor_exactGeneral (integralLisseRing l E X) W).2.2
  let T := SheafOfModules.free (R := integralLisseRing l E X) K
  let c := SheafOfModules.mapFreeIso H K (Iso.refl _)
  let π := fun n ↦ cokernel.π (integralLisseScalar l E X T
    (Padic.coefficientExtensionUniformizer l E ^ (n + 1)))
  obtain ⟨p, hp, hstep⟩ := compatibleFreeMaps l E X F W hW K
    (c.hom ≫ H.map (π 0) ≫ e.hom)
  let t := fun n ↦ c.inv ≫ p n
  have ht (n : ℕ) : H.map (integralLisseScalar l E X T
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1))) ≫ t n = 0 := by
    have hn : H.map (integralLisseScalar l E X T
        (Padic.coefficientExtensionUniformizer l E ^ (n + 1))) ≫ t n =
      t n ≫ H.map (integralLisseScalar l E X (F.obj.obj (op n))
        (Padic.coefficientExtensionUniformizer l E ^ (n + 1))) := by
      ext V x
      exact ((t n).val.app V).hom.map_smul _ x
    rw [hn, towerScalar_zero, H.map_zero, comp_zero]
  have hπzero (n : ℕ) : H.map (integralLisseScalar l E X T
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1))) ≫ H.map (π n) = 0 := by
    rw [← H.map_comp, cokernel.condition, H.map_zero]
  let hc (n : ℕ) : IsColimit (CokernelCofork.ofπ (H.map (π n)) (hπzero n)) :=
    CokernelCofork.mapIsColimit _ (cokernelIsCokernel _) H
  let d (n : ℕ) : H.obj (integralLisseCokernel l E X T n) ⟶
      H.obj (F.obj.obj (op n)) := (hc n).desc (CokernelCofork.ofπ (t n) (ht n))
  have hd (n : ℕ) : H.map (π n) ≫ d n = t n :=
    (hc n).fac _ WalkingParallelPair.one
  have hdstep (n : ℕ) : d (n + 1) ≫
      H.map (F.obj.map (homOfLE (Nat.le_succ n)).op) =
      H.map (integralLisseCokernelTransition l E X T n) ≫ d n := by
    apply (cancel_epi (H.map (π (n + 1)))).1
    rw [← Category.assoc, hd, ← Category.assoc, ← H.map_comp]
    have hπ : π (n + 1) ≫ integralLisseCokernelTransition l E X T n = π n :=
      cokernel.π_desc _ _ _
    rw [hπ, hd]
    change (c.inv ≫ p (n + 1)) ≫ _ = c.inv ≫ p n
    rw [Category.assoc, hstep]
  have hd0 : d 0 = e.hom := by
    apply (cancel_epi (H.map (π 0))).1
    rw [hd]
    change c.inv ≫ p 0 = _
    rw [hp, Iso.inv_hom_id_assoc]
  have hi (n : ℕ) : IsIso (d n) := by
    induction n with
    | zero => rw [hd0]; infer_instance
    | succ n ih =>
      exact lift_level_iso l E X F K W n (d (n + 1)) (asIso (d n)) (hdstep n)
  let α : integralLisseCokernelTower l E X T ⋙ H ⟶ F.obj ⋙ H :=
    NatTrans.ofOpSequence d (fun n ↦ by
      simpa only [Functor.comp_map, integralLisseCokernelTower,
        Functor.ofOpSequence_map_homOfLE_succ] using (hdstep n).symm)
  have : IsIso α := (NatTrans.isIso_iff_isIso_app α).2 (fun n ↦ hi n.unop)
  exact ⟨(asIso α).symm⟩

end AlgebraicGeometry.ProEtale
