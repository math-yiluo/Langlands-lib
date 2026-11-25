/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueAdjointTower
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic
import WeilConjectures.AlgebraicGeometry.AdicResidueCompletionModel
import WeilConjectures.AlgebraicGeometry.AdicResidueKoszulNakayama
import WeilConjectures.AlgebraicGeometry.AdicResidueQuotientFiniteProjection
import WeilConjectures.AlgebraicGeometry.LocalCompletenessModels
import WeilConjectures.AlgebraicGeometry.RestrictionSectionCompleteness
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementsIdeal

/-! # Mapping property of the normalized quotient-limit unit

Source: Stacks Project, proetale.tex, Tag 099M, lemma-naive-completion;
algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.ConstantCompletion
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

/-- Nilpotence makes every leg of the multiplication colimit zero. -/
private theorem sequential_nilpotent_colimit
    {C : Type*} [Category C] [Preadditive C] [HasColimitsOfShape ℕ C]
    (M : C) (f : M ⟶ M) (k : ℕ) (hf : (End.of f) ^ k = 0) :
    IsZero (colimit (Functor.ofSequence (X := fun _ : ℕ ↦ M) (fun _ ↦ f))) := by
  let F := Functor.ofSequence (X := fun _ : ℕ ↦ M) (fun _ ↦ f)
  have hm (n j : ℕ) : F.map (homOfLE (Nat.le_add_right n j)) = ((End.of f) ^ j).asHom := by
    induction j with
    | zero =>
      simp only [Nat.add_zero, homOfLE_refl, CategoryTheory.Functor.map_id,
        pow_zero, End.one_asHom]
      rfl
    | succ j ih =>
      have he : homOfLE (Nat.le_add_right n (j + 1)) =
          homOfLE (Nat.le_add_right n j) ≫ homOfLE (Nat.le_succ (n + j)) := rfl
      rw [he, CategoryTheory.Functor.map_comp, ih]
      dsimp only [F]
      rw [Functor.ofSequence_map_homOfLE_succ]
      change ((End.of f) ^ j).asHom ≫ f = ((End.of f) ^ (j + 1)).asHom
      rw [pow_succ', End.mul_asHom]
  apply (IsZero.iff_id_eq_zero _).mpr
  apply colimit.hom_ext
  intro n
  have h := colimit.w F (homOfLE (Nat.le_add_right n k))
  rw [hm, hf] at h
  simpa only [End.zero_asHom, zero_comp, Category.comp_id, comp_zero] using h.symm

/-- Localization at a nilpotent section vanishes on its slice. -/
private theorem sectionLocalization_nilpotent
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C) (f : R.obj.obj (op U))
    (k : ℕ) (hf : f ^ k = 0) :
    IsZero (ringedSiteSectionLocalization R U f) := by
  let M := SheafOfModules.unit (R.over U)
  let μ : M ⟶ M := M.unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun V ↦ R.obj.map V.unop.hom.op f)
      (fun {V W} a ↦ ringedSiteSectionLocalization_compatible R U f V W a))
  have hp (j : ℕ) (V : (Over U)ᵒᵖ) (m : R.obj.obj (op V.unop.left)) :
      (((End.of μ) ^ j : End M).asHom.val.app V) m =
        m * (R.obj.map V.unop.hom.op f) ^ j := by
    induction j generalizing m with
    | zero => simp only [pow_zero, End.one_asHom]; exact (mul_one m).symm
    | succ j ih =>
      rw [pow_succ', End.mul_asHom]
      change ((μ.val.app V) ((((End.of μ) ^ j : End M).asHom.val.app V) m)) = _
      rw [ih]
      change (m * (R.obj.map V.unop.hom.op f) ^ j) * R.obj.map V.unop.hom.op f = _
      rw [mul_assoc, ← pow_succ]
  have hμ : (End.of μ) ^ k = 0 := by
    apply End.ext
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext
    erw [hp]
    have hz : (R.obj.map V.unop.hom.op f) ^ k = 0 := by
      rw [← map_pow, hf, map_zero]
    rw [hz, mul_zero]
    rfl
  exact sequential_nilpotent_colimit M μ k hμ

open CategoryTheory.Pretriangulated.Opposite in
private theorem completeElement_nilpotent
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{u + 1} (ConstantCompletion.Mod R)]
    [∀ U : C, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      ((siteModuleRings R).over U))]
    (K : DerivedCategory (ConstantCompletion.Mod R)) (U : C)
    (f : R.obj.obj (op U)) (k : ℕ) (hf : f ^ k = 0) :
    IsRingedSiteCompleteElement J R K U f := by
  let O := siteModuleRings R
  let L := (DerivedCategory.singleFunctor (SheafOfModules.{u} (O.over U)) 0).obj
    (ringedSiteSectionLocalization O U f)
  let N := ringedSiteDerivedRestriction O U K
  let : HasDerivedCategory.{u + 1} (ringedSiteModules.{u}
      (siteModuleRings (R.over U))) := inferInstanceAs
    (HasDerivedCategory.{u + 1} (SheafOfModules.{u} (O.over U)))
  obtain ⟨s, hs⟩ := (ringedInternalHom_exact (J.over U) (R.over U)).2 N
  let := s
  have := hs
  have hL : IsZero L := (DerivedCategory.singleFunctor _ 0).map_isZero
    (sectionLocalization_nilpotent O U f k hf)
  exact ((Functor.curry.obj (derivedInternalHom (J.over U) (R.over U))).flip.obj N).map_isZero
    hL.op

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
      apply completeElement_nilpotent (T.over U) B N V _ (n + 1)
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

/-- The universal scalar extension inherits exactness from the cochain model. -/
private theorem extension_exact
    {C : Type*} [SmallCategory C] {S : GrothendieckTopology C}
    {R B : Sheaf S CommRingCat} (q : R ⟶ B) :
    ∃ _s : (ConstantCompletion.extend q).CommShift ℤ,
      (ConstantCompletion.extend q).IsTriangulated := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let := HasDerivedCategory.standard (ConstantCompletion.Mod B)
  obtain ⟨E, hobj, hmap, hpres, F, hpw, ε, hu, htri, hc⟩ :=
    (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel q).some
  have hE : E = ConstantCompletion.change q := CategoryTheory.Functor.ext hobj (fun _ _ f ↦ hmap f)
  subst E
  let := hu
  let : (ConstantCompletion.extend q).IsLeftDerivedFunctor
      (ConstantCompletion.extendComparison q)
      (HomologicalComplex.quasiIso (ConstantCompletion.Mod R) (.up ℤ)) :=
    (ConstantCompletion.derivedExtension q).universal
  let e : F ≅ ConstantCompletion.extend q :=
    Functor.leftDerivedUnique (ConstantCompletion.extend q) F ε
      (ConstantCompletion.extendComparison q)
      (HomologicalComplex.quasiIso (ConstantCompletion.Mod R) (.up ℤ))
  obtain ⟨sF, hF⟩ := htri
  let := sF
  let := hF
  let s := Functor.CommShift.ofIso e ℤ
  have : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofIso_compatibility e ℤ
  exact ⟨s, Functor.isTriangulated_of_iso e⟩

/-- Completeness, defined by vanishing of exact internal Hom tests, is closed under cones. -/
private theorem complete_cone
    {C : Type*} [SmallCategory C] {S : GrothendieckTopology C}
    {R B : Sheaf S CommRingCat} (q : R ⟶ B)
    (T : Pretriangulated.Triangle (ConstantCompletion.D R))
    (hT : T ∈ distTriang (ConstantCompletion.D R))
    (h₁ : ConstantCompletion.IsComplete q T.obj₁)
    (h₂ : ConstantCompletion.IsComplete q T.obj₂) :
    ConstantCompletion.IsComplete q T.obj₃ := by
  intro U f hf
  let L := (DerivedCategory.singleFunctor _ 0).obj
    (ringedSectionLocalization (R.over U) (ringedSliceSection R U f))
  let H := (Functor.curry.obj (derivedInternalHom (S.over U) (R.over U))).obj (op L)
  obtain ⟨s, hH⟩ := (ringedInternalHom_exact (S.over U) (R.over U)).1 L
  let := s
  let := hH
  let : (ringedDerivedRestriction R U).CommShift ℤ := by
    unfold ringedDerivedRestriction
    infer_instance
  let : (ringedDerivedRestriction R U).IsTriangulated := by
    unfold ringedDerivedRestriction
    infer_instance
  let G := ringedDerivedRestriction R U ⋙ H
  exact Pretriangulated.Triangle.isZero₃_of_isZero₁₂ _ (G.map_distinguished T hT)
    (h₁ U f hf) (h₂ U f hf)

/-- The reflector unit is invertible after each finite scalar extension. -/
private theorem reflector_finite_unit_isIso
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (K : ringedSiteComplex
      ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U))
    (ε : K ⟶ ringedSiteRingComplex
      ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U))
    (hK : HasLocalExtendedCechDescription
      ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U)
      (kernelIdeal (adicResidueLocalProjection.{u, v} X J U 0)).module
      (kernelIdeal (adicResidueLocalProjection.{u, v} X J U 0)).inclusion K ε)
    (M : AdicResidueLocalDerived.{u, v} X J U) (n : ℕ) :
    IsIso ((adicResidueLocalReduction.{u, v} X J U n).map
      (ringedCechCompletionUnit
        ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U) K ε M)) := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let R := (completed T A J).over U
  let I := kernelIdeal (adicResidueLocalProjection.{u, v} X J U 0)
  have : Mono I.inclusion := kernel_mono _
  have : I.module.IsFiniteType := adicResidueKernel_finiteType.{u, v} X J U
  obtain ⟨_, _, hb, _⟩ :=
    ringedExtendedCech_reflector_properties (T.over U) R I.module I.inclusion K ε hK
  let adj := adicResidueScalarAdjunction.{u, v} X J U n
  apply isIso_of_coyoneda_map_bijective
  intro N
  have hbij := hb M _ (finiteRestriction_complete.{u, v} X J U n N)
  constructor
  · intro x y hxy
    apply (adj.homEquiv _ _).injective
    apply hbij.injective
    change ringedCechCompletionUnit R K ε M ≫ (adj.homEquiv _ _) x =
      ringedCechCompletionUnit R K ε M ≫ (adj.homEquiv _ _) y
    rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left]
    exact congrArg (adj.homEquiv _ _) hxy
  · intro y
    obtain ⟨x, hx⟩ := hbij.surjective ((adj.homEquiv _ _).toFun y)
    refine ⟨(adj.homEquiv _ _).symm x, ?_⟩
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply]
    exact hx

/-- The normalized map into a quotient Roos limit has the mapping property for complete
objects. This assertion does not assert completeness of the point of the limit.

Source: Stacks Project, proetale.tex, Tag 099M, lemma-naive-completion;
algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul.
(auxiliary; not a blueprint node).

Proof: choose finite generators of J and the negative Koszul towers with transitions
(a_i,1). Over the Noetherian constant ring the augmentation to the quotient tower
has pro-zero cone, by Artin--Rees for the finite Koszul homology modules. Sheafify
and tensor one flat-term K-flat representative of M. Total derived inverse limit
inverts the resulting pro-isomorphism. Flat restriction to constant coefficients
commutes with these limits and detects isomorphisms, so this computation applies
to completed coefficients and on every slice. The Koszul limit unit is initial
among maps to locally complete objects by the Koszul reflector theorem. The
augmentation preserves insertion of one and all quotient transitions, which are
the counit-transpose successors used here. Thus one normalized map to the given
Roos limit has this mapping property. For any other such a, its difference from
the normalized map is invisible at every quotient. Both factor through the Koszul
reflector, and their difference there has zero finite reductions; derived Nakayama
makes the resulting endomorphism with identity finite reductions invertible.
Precomposition by a therefore has the same mapping bijection. Empty generators
(J=0) give the identity unit; for J=A all complete targets vanish. No finiteness
or boundedness of either derived object is used. -/
theorem adicResidueQuotientUnit_universal
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (M : AdicResidueLocalDerived.{u, v} X J U)
    (c : Cone (adicResidueAdjointTower.{u, v} X J U M))
    (hc : Pretriangulated.IsHomotopyLimit c) (a : M ⟶ c.pt)
    (ha : ∀ n : ℕ, a ≫ c.π.app (op n) =
      (adicResidueScalarAdjunction.{u, v} X J U n).unit.app M) :
    ∀ L : AdicResidueLocalDerived.{u, v} X J U,
      IsComplete (adicResidueLocalProjection.{u, v} X J U 0) L →
        Function.Bijective (fun f : c.pt ⟶ L ↦ a ≫ f) := by
  classical
  let T := coefficientProEtaleModelTopology.{u, v} X
  let R := (completed T A J).over U
  let I := kernelIdeal (adicResidueLocalProjection.{u, v} X J U 0)
  have : Mono I.inclusion := kernel_mono _
  have : I.module.IsFiniteType := adicResidueKernel_finiteType.{u, v} X J U
  obtain ⟨K, ε, hK, _⟩ := adicResidueCompletionModel_exists.{u, v} X J U
  obtain ⟨hcomplete, _, hb, _⟩ :=
    ringedExtendedCech_reflector_properties (T.over U) R I.module I.inclusion K ε hK
  let η := ringedCechCompletionUnit R K ε M
  have hcp := quotient_limit_complete.{u, v} X J U M K ε hK c hc
  obtain ⟨f, hf⟩ := (hb M c.pt hcp).surjective a
  let F := adicResidueLocalReduction.{u, v} X J U 0
  let adj := adicResidueScalarAdjunction.{u, v} X J U 0
  let p := (adj.homEquiv c.pt (F.obj M)).symm (c.π.app (op 0))
  have hp : IsIso p := adicResidue_quotient_residue_projection_isIso X J U M c hc
  have hap : F.map a ≫ p = 𝟙 (F.obj M) := by
    apply (adj.homEquiv M (F.obj M)).injective
    rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply, Adjunction.homEquiv_id]
    exact ha 0
  have hFa : IsIso (F.map a) := by
    have he : F.map a = inv p := by
      apply (cancel_mono p).1
      rw [hap, IsIso.inv_hom_id]
    rw [he]
    infer_instance
  have hFη : IsIso (F.map η) :=
    reflector_finite_unit_isIso.{u, v} X J U K ε hK M 0
  have hFf : IsIso (F.map f) := by
    have he : F.map η ≫ F.map f = F.map a := by
      rw [← F.map_comp]
      exact congrArg F.map hf
    have : IsIso (F.map η ≫ F.map f) := he ▸ hFa
    exact IsIso.of_isIso_comp_left (F.map η) (F.map f)
  obtain ⟨sF, htriF⟩ := extension_exact (adicResidueLocalProjection.{u, v} X J U 0)
  let : F.CommShift ℤ := sF
  let : F.IsTriangulated := htriF
  obtain ⟨Q, g, h, htriangle⟩ := Pretriangulated.distinguished_cocone_triangle f
  let Δ := Pretriangulated.Triangle.mk f g h
  have hQ : IsComplete (adicResidueLocalProjection.{u, v} X J U 0) Q :=
    complete_cone _ Δ htriangle (hcomplete M) hcp
  have hQ0 : IsZero (F.obj Q) :=
    Pretriangulated.Triangle.isZero₃_of_isIso₁ _ (F.map_distinguished Δ htriangle) hFf
  have : IsIso f := (Δ.isZero₃_iff_isIso₁ htriangle).mp
    (adicResidue_isZero_of_complete_residue.{u, v} X J U Q hQ hQ0)
  intro L hL
  constructor
  · intro x y hxy
    apply (cancel_epi f).1
    apply (hb M L hL).injective
    simpa only [← Category.assoc, hf] using hxy
  · intro x
    obtain ⟨y, hy⟩ := (hb M L hL).surjective x
    refine ⟨inv f ≫ y, ?_⟩
    change a ≫ (inv f ≫ y) = x
    rw [← hf]
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using hy

end AlgebraicGeometry.Scheme
