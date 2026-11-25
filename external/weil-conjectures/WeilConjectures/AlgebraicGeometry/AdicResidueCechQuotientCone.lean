/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueAdjointTower
public import WeilConjectures.AlgebraicGeometry.ExtendedCechCompletionModel
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic
import WeilConjectures.AlgebraicGeometry.AdicResidueCompletionModel
import WeilConjectures.AlgebraicGeometry.AdicResidueQuotientUnitUniversal
import all WeilConjectures.AlgebraicGeometry.CompletionFiniteReduction
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Milnor
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products

/-! # The quotient Roos cone of an augmented Cech completion

Source: Stacks Project, proetale.tex, Tag 099M, lemma-naive-completion;
algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul;
sites-cohomology.tex, Tags 0940 and 0941.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion

namespace AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

private theorem kernel_mono
    {C : Type*} [SmallCategory C] {T : GrothendieckTopology C}
    {R S : Sheaf T CommRingCat} (q : R ⟶ S) : Mono (kernelIdeal q).inclusion := by
  constructor
  intro N f g hfg
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun h ↦ h.val.app V x) hfg

/-- Finite scalar restrictions are complete: generators of J act nilpotently. -/
private theorem finiteRestriction_complete
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ)
    (N : D ((finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U)) :
    IsComplete (adicResidueLocalProjection.{u, v} X J U 0)
      ((dres (adicResidueLocalProjection.{u, v} X J U n)).obj N) := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let R := (completed T A J).over U
  let B := (finite T A J n).over U
  let q := adicResidueLocalProjection.{u, v} X J U n
  let P := DerivedCategory.Q.objPreimage N
  let L := (Q R).obj (((res q).mapHomologicalComplex (.up ℤ)).obj P)
  have hL : IsComplete (adicResidueLocalProjection.{u, v} X J U 0) L := by
    intro V f ⟨y, hy⟩
    apply (localCompleteness_models_iff (T.over U) R L V f).mpr
    obtain ⟨S, hS, _, _, _⟩ := ringedSite_complete_elements_ideal (T.over U) R L
    have hker : (kernelIdeal (adicResidueLocalProjection.{u, v} X J U 0)).sections V =
        Ideal.span (Set.range (fun a : ↥(J ^ (0 + 1)) ↦
          (algebraSection (coefficientMap T A J) (a : A)).val (op V.left))) := by
      have hk := (kernelIdeal_existsUnique
        (adicResidueLocalProjection.{u, v} X J U 0)).exists.choose_spec V
      change (kernelIdeal (adicResidueLocalProjection.{u, v} X J U 0)).sections V = _ at hk
      refine hk.trans ?_
      change RingHom.ker ((projection T A J 0).hom.app (op V.left)).hom = _
      exact ((flat_and_quotients T A J).2.1 0 V.left).2
    have hle : (kernelIdeal (adicResidueLocalProjection.{u, v} X J U 0)).sections V ≤
        S V := by
      rw [hker]
      apply Ideal.span_le.mpr
      rintro _ ⟨a, rfl⟩
      have ha : (a : A) ∈ J := by
        simpa only [Nat.zero_add, pow_one] using a.property
      apply (hS V _).mpr
      apply (restrictScalars_completeElement_iff (T.over U) R B q N V _).mpr
      apply CategoryTheory.AdicSites.completeElement_nilpotent (T.over U) B N V _ (n + 1)
      rw [← map_pow]
      apply RingHom.mem_ker.mp
      change (algebraSection (coefficientMap T A J) (a : A)).val (op V.left) ^ (n + 1) ∈
        RingHom.ker ((projection T A J n).hom.app (op V.left)).hom
      rw [((flat_and_quotients T A J).2.1 n V.left).2]
      apply Ideal.subset_span
      refine ⟨⟨(a : A) ^ (n + 1), Ideal.pow_mem_pow ha (n + 1)⟩, ?_⟩
      simp only [algebraSection, constantSection, map_pow]
    apply (hS V f).mp
    apply hle
    change y.val = f at hy
    exact hy ▸ y.property
  let e : L ≅ (dres q).obj N :=
    (resFactors q).app P ≪≫ (dres q).mapIso (DerivedCategory.Q.objObjPreimageIso N)
  intro V f hf
  let H := derivedInternalHom ((T.over U).over V) (R.over V)
  exact (hL V f hf).of_iso
    (H.mapIso ((Iso.refl _).prod ((ringedDerivedRestriction R V).mapIso e))).symm

/-- A reflector's complete locus is closed under every existing product. -/
private theorem complete_product
    {D : Type*} [Category D] (P : D → Prop) (F : D ⥤ D)
    (η : ∀ E, E ⟶ F.obj E) (hc : ∀ E, P (F.obj E))
    (hb : ∀ E L, P L → Function.Bijective (fun f : F.obj E ⟶ L ↦ η E ≫ f))
    (hi : ∀ {E L}, (E ≅ L) → P E → P L)
    (Y : ℕ → D) (hY : ∀ n, P (Y n)) (p : Fan Y) (hp : IsLimit p) : P p.pt := by
  classical
  choose f hf using fun n ↦ (hb p.pt (Y n) (hY n)).2 (p.proj n)
  let r := Fan.IsLimit.lift hp f
  have hr : η p.pt ≫ r = 𝟙 p.pt := by
    apply Fan.IsLimit.hom_ext hp
    intro n
    simpa only [r, Category.assoc, Fan.IsLimit.fac, Category.id_comp] using hf n
  have hs : r ≫ η p.pt = 𝟙 (F.obj p.pt) := by
    apply (hb p.pt (F.obj p.pt) (hc p.pt)).1
    simp only [← Category.assoc, hr, Category.id_comp, Category.comp_id]
  exact hi (Iso.mk r (η p.pt) hs hr) (hc p.pt)

/-- Completeness of a quotient Roos limit uses only nilpotence and reflection. -/
private theorem quotient_limit_complete
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (M : AdicResidueLocalDerived.{u, v} X J U)
    (K : ringedSiteComplex
      ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U))
    (ε : K ⟶ ringedSiteRingComplex
      ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U))
    (hK : HasLocalExtendedCechDescription
      ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U)
      (kernelIdeal (adicResidueLocalProjection.{u, v} X J U 0)).module
      (kernelIdeal (adicResidueLocalProjection.{u, v} X J U 0)).inclusion K ε)
    (c : Cone (adicResidueAdjointTower.{u, v} X J U M))
    (hc : Pretriangulated.IsHomotopyLimit c) :
    IsComplete (adicResidueLocalProjection.{u, v} X J U 0) c.pt := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let R := (completed T A J).over U
  let I := kernelIdeal (adicResidueLocalProjection.{u, v} X J U 0)
  have : Mono I.inclusion := kernel_mono _
  have : I.module.IsFiniteType := adicResidueKernel_finiteType.{u, v} X J U
  obtain ⟨hcomplete, _, hb, _⟩ :=
    ringedExtendedCech_reflector_properties (T.over U) R I.module I.inclusion K ε hK
  have hiso {E L : D R} (e : E ≅ L)
      (hE : IsComplete (adicResidueLocalProjection.{u, v} X J U 0) E) :
      IsComplete (adicResidueLocalProjection.{u, v} X J U 0) L := by
    intro V f hf
    let H := derivedInternalHom ((T.over U).over V) (R.over V)
    exact (hE V f hf).of_iso
      (H.mapIso ((Iso.refl _).prod ((ringedDerivedRestriction R V).mapIso e))).symm
  obtain ⟨p, hp, δ, htriangle⟩ := hc
  have hprod : IsComplete (adicResidueLocalProjection.{u, v} X J U 0) p.pt :=
    complete_product _ (ringedCechCompletionFunctor R K)
      (ringedCechCompletionUnit R K ε) hcomplete hb (fun e h ↦ hiso e h)
      (fun n ↦ (adicResidueAdjointTower.{u, v} X J U M).obj (op n))
      (fun n ↦ finiteRestriction_complete.{u, v} X J U n _) p hp
  intro V f hf
  obtain ⟨s, ht⟩ := (ringedInternalHom_exact ((T.over U).over V) (R.over V)).1
    ((DerivedCategory.singleFunctor _ 0).obj
      (ringedSectionLocalization (R.over V) (ringedSliceSection R V f)))
  let := s
  have := ht
  let H := (Functor.curry.obj (derivedInternalHom ((T.over U).over V) (R.over V))).obj
    (op ((DerivedCategory.singleFunctor _ 0).obj
      (ringedSectionLocalization (R.over V) (ringedSliceSection R V f))))
  let : (ringedDerivedRestriction R V).CommShift ℤ := by
    unfold ringedDerivedRestriction
    infer_instance
  have : (ringedDerivedRestriction R V).IsTriangulated := by
    unfold ringedDerivedRestriction
    infer_instance
  let G := ringedDerivedRestriction R V ⋙ H
  exact Pretriangulated.Triangle.isZero₁_of_isZero₂₃ _
    (G.map_distinguished _ htriangle) (hprod V f hf) (hprod V f hf)

private theorem milnor_surjective
    {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F : ℕᵒᵖ ⥤ D} (c : Cone F) (hc : Pretriangulated.IsHomotopyLimit c) (T : D) :
    Function.Surjective (Pretriangulated.milnorMap c T) := by
  obtain ⟨P, hP, δ, htriangle⟩ := hc
  intro x
  obtain ⟨g, hg⟩ := Pretriangulated.Triangle.coyoneda_exact₂ _ htriangle
    (Fan.IsLimit.lift hP x.val) (by
      refine Fan.IsLimit.hom_ext hP _ _ fun n ↦ ?_
      simp only [Pretriangulated.Triangle.mk_mor₂, Preadditive.comp_sub,
        Preadditive.sub_comp, Category.assoc, Pretriangulated.towerShift_proj,
        Fan.IsLimit.fac_assoc, zero_comp]
      erw [Category.id_comp, Fan.IsLimit.fac, x.property n, sub_self])
  refine ⟨g, Subtype.ext (funext fun n ↦ ?_)⟩
  have h := congrArg (fun k ↦ k ≫ P.proj n) hg
  simp only [Pretriangulated.Triangle.mk_mor₁, Fan.IsLimit.fac, Category.assoc] at h
  exact h.symm

/-- The Cech completion of any input has a quotient Roos cone with the actual scalar
units. Completeness of the input is not required. The augmented local description
allows any genuine Cech model for the residue kernel, rather than a chosen reflector.

Source: Stacks Project, proetale.tex, Tag 099M, proof of lemma-naive-completion;
algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul;
sites-cohomology.tex, Tags 0940 and 0941.
(auxiliary; not a blueprint node).

Proof: the residue kernel is finite type, so the given Cech model is a reflector
onto locally complete objects. Every finite quotient restriction is complete: its
coefficient generators act nilpotently, and the complete sections form an ideal.
The reflector mapping property shows that products of complete objects are complete.
Applying exact internal Hom after slice restriction to a Roos triangle therefore
shows that its fibre is complete as well. Countable products give a Roos cone for
the specified quotient tower; Milnor exactness lifts the compatible scalar units
to a map a from M into its point. The quotient-unit mapping-property theorem makes
this map universal into complete objects. Apply each of the two mapping bijections
to the other unit. Injectivity makes the resulting comparison maps inverse.
Transport the Roos cone along their isomorphism. Associativity and the factorization
equation identify every leg with the actual scalar unit. No boundedness or
finiteness of M is used; nilpotence also covers J=0 and J=A. -/
theorem adicResidue_cech_quotient_cone
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (M : AdicResidueLocalDerived.{u, v} X J U)
    (K : ringedSiteComplex
      ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U))
    (ε : K ⟶ ringedSiteRingComplex
      ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U))
    (hK : HasLocalExtendedCechDescription
      ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U)
      (kernelIdeal (adicResidueLocalProjection.{u, v} X J U 0)).module
      (kernelIdeal (adicResidueLocalProjection.{u, v} X J U 0)).inclusion K ε) :
    ∃ π : (Functor.const ℕᵒᵖ).obj
        ((ringedCechCompletionFunctor
          ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U) K).obj M) ⟶
        adicResidueAdjointTower.{u, v} X J U M,
      Pretriangulated.IsHomotopyLimit ⟨_, π⟩ ∧
      ∀ n : ℕ, ringedCechCompletionUnit
          ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U) K ε M ≫
          π.app (op n) = (adicResidueScalarAdjunction.{u, v} X J U n).unit.app M := by
  classical
  let T := coefficientProEtaleModelTopology.{u, v} X
  let R := (completed T A J).over U
  let I := kernelIdeal (adicResidueLocalProjection.{u, v} X J U 0)
  have : Mono I.inclusion := kernel_mono _
  have : I.module.IsFiniteType := adicResidueKernel_finiteType.{u, v} X J U
  obtain ⟨hcomplete, _, hb, _⟩ :=
    ringedExtendedCech_reflector_properties (T.over U) R I.module I.inclusion K ε hK
  let F := adicResidueAdjointTower.{u, v} X J U M
  have : IsGrothendieckAbelian.{max v (u + 1)} (Mod R) :=
    SheafOfModules.isGrothendieckAbelian _
  have : HasCountableProducts (D R) :=
    ⟨fun Y _ ↦ DerivedCategory.hasLimitsOfShape_discrete (Mod R) Y⟩
  obtain ⟨c, hc⟩ := Pretriangulated.exists_isHomotopyLimit F
  let x : Pretriangulated.towerHomLimit F M :=
    ⟨fun n ↦ (adicResidueScalarAdjunction.{u, v} X J U n).unit.app M, by
      intro n
      simpa only [F, adicResidueAdjointTower, Functor.ofOpSequence_map_homOfLE_succ] using
        adicResidueAdjointStep_unit.{u, v} X J U M n⟩
  obtain ⟨a, ha⟩ := milnor_surjective c hc M x
  have hleg (n : ℕ) : a ≫ c.π.app (op n) =
      (adicResidueScalarAdjunction.{u, v} X J U n).unit.app M :=
    congrArg (fun z : Pretriangulated.towerHomLimit F M ↦ z.val n) ha
  have hcp := quotient_limit_complete.{u, v} X J U M K ε hK c hc
  have hab := adicResidueQuotientUnit_universal.{u, v} X J U M c hc a hleg
  obtain ⟨f, hf⟩ := (hb M c.pt hcp).2 a
  obtain ⟨g, hg⟩ := (hab _ (hcomplete M)).2 (ringedCechCompletionUnit R K ε M)
  have hfg : f ≫ g = 𝟙 _ := by
    apply (hb M _ (hcomplete M)).1
    simp only [← Category.assoc, hf, hg, Category.comp_id]
  have hgf : g ≫ f = 𝟙 _ := by
    apply (hab _ hcp).1
    simp only [← Category.assoc, hg, hf, Category.comp_id]
  let e : (ringedCechCompletionFunctor R K).obj M ≅ c.pt := ⟨f, g, hfg, hgf⟩
  let c' : Cone F :=
    { pt := (ringedCechCompletionFunctor R K).obj M
      π := (Functor.const ℕᵒᵖ).map e.hom ≫ c.π }
  refine ⟨c'.π, hc.of_iso (Iso.refl F) c' e.symm (fun n ↦ ?_), ?_⟩
  · change c.π.app (op n) ≫ 𝟙 _ = e.inv ≫ (e.hom ≫ c.π.app (op n))
    simp only [Category.comp_id, Iso.inv_hom_id_assoc]
  · intro n
    change ringedCechCompletionUnit R K ε M ≫ (f ≫ c.π.app (op n)) = _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z ↦ z ≫ c.π.app (op n)) hf).trans (hleg n))

end AlgebraicGeometry.Scheme
