/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Alternating Čech total complexes on finite open families

Source: Stacks, Cohomology, Section on Čech cohomology of unbounded complexes,
equation-global-sections-to-alternating-cech and lemma-alternating-cech-complex-complex
(blueprint: def-sc-alternating-cech-total-complex).

Čech degree is first. The total differential is d₁ + (-1)^p d₂.
All data are explicit; only identities needed by the constructions are postponed.

## Main definitions

- `alternatingCechComplexFunctor`: increasing-tuple cochains and signed face restrictions.
- `alternatingCechDoubleFunctor`: the double complex with Čech degree first.
- `alternatingCechTotalFunctor`: direct-sum totalization, including unbounded coefficients.
- `alternatingCechAugmentation`: restriction into Čech degree zero.
- `IsAlternatingCechDerivedComparison`: the canonical-map equation on K-injectives.
-/

@[expose] public section

universe u w v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

noncomputable section

variable {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)

/-- The intersection belonging to an increasing tuple.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechIntersection {p : ℕ} (t : Fin (p + 1) ↪o Fin r) : X.Opens :=
  ⨅ k, U (t k)

/-- Deleting one entry enlarges the intersection.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex).
Proof: Each factor of the face intersection is a factor of the full intersection; apply the
infimum universal property. -/
theorem alternatingCechIntersection_face_le (p : ℕ)
    (t : Fin (p + 2) ↪o Fin r) (j : Fin (p + 2)) :
    alternatingCechIntersection U t ≤
      alternatingCechIntersection U ((Fin.succAboveOrderEmb j).trans t) := by
  exact le_iInf fun k ↦ iInf_le (fun k ↦ U (t k)) ((Fin.succAboveOrderEmb j) k)

variable
  (G : X.Opensᵒᵖ ⥤ ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))

/-- Products of sections over strictly increasing tuples.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechTerms (p : ℕ) :
    ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  ModuleCat.of _ (∀ t : Fin (p + 1) ↪o Fin r,
    G.obj (op (alternatingCechIntersection U t)))

/-- The signed sum of face restrictions; linear maps specify its actual data.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechDifferential (p : ℕ) :
    alternatingCechTerms U G p ⟶ alternatingCechTerms U G (p + 1) :=
  ModuleCat.ofHom (LinearMap.pi fun t ↦
    ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
      (G.map (homOfLE (alternatingCechIntersection_face_le U p t j)).op).hom.comp
        (LinearMap.proj ((Fin.succAboveOrderEmb j).trans t)))

private theorem alternatingCechDifferential_apply (p : ℕ)
    (s : alternatingCechTerms U G p) (t : Fin (p + 2) ↪o Fin r) :
    (alternatingCechDifferential U G p).hom s t =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
        (G.map (homOfLE (alternatingCechIntersection_face_le U p t j)).op).hom
          (s ((Fin.succAboveOrderEmb j).trans t)) := by
  change (∀ q : Fin (p + 1) ↪o Fin r, G.obj (op (alternatingCechIntersection U q))) at s
  change ((∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
    (G.map (homOfLE (alternatingCechIntersection_face_le U p t j)).op).hom.comp
      (LinearMap.proj ((Fin.succAboveOrderEmb j).trans t))) s) = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  rfl

/-- The alternating face differential squares to zero.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex).
Proof: In the double sum, pair the two orders of deleting each pair of indices. The
restriction composites agree by presheaf functoriality; their face signs are opposite. -/
theorem alternatingCechDifferential_square (p : ℕ) :
    alternatingCechDifferential U G p ≫ alternatingCechDifferential U G (p + 1) = 0 := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change (∀ q : Fin (p + 1) ↪o Fin r, G.obj (op (alternatingCechIntersection U q))) at s
  funext t
  change (alternatingCechDifferential U G (p + 1)).hom
    ((alternatingCechDifferential U G p).hom s) t = 0
  rw [alternatingCechDifferential_apply]
  simp_rw [alternatingCechDifferential_apply]
  simp only [map_sum, map_zsmul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, ← Finset.sum_product', Finset.univ_product_univ]
  let P := Fin (p + 2) × Fin (p + 3)
  let S : Finset P := {ij : P | ij.2.val ≤ ij.1.val}
  rw [← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij ↦
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right (Fin.is_lt ij.1)),
      ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp only [S, φ, Finset.compl_filter, Finset.mem_filter_univ,
      Fin.val_succ, Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using congrArg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using
        congrArg Fin.castSucc (congrArg Prod.fst h)⟩
  · rintro ⟨i', j'⟩ hij'
    simp only [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred (by intro h; subst h; simp at hij'), i'.castSucc), ?_, ?_⟩
    · simpa [S] using Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    dsimp only [φ]
    rw [← neg_smul]
    congr 1
    · simp only [Fin.val_succ, Fin.val_castLT, pow_succ, mul_neg, neg_mul, neg_neg, mul_one]
      exact mul_comm _ _
    · have hj : j ≤ i.castSucc := (Finset.mem_filter.mp hij).2
      have hpred : i.predAbove j = j.castLT (lt_of_le_of_lt hj i.is_lt) := by
        rw [Fin.predAbove_of_le_castSucc _ _ hj]
        rfl
      have hsucc : j.succAbove i = i.succ := Fin.succAbove_of_le_castSucc j i hj
      have ht : (Fin.succAboveOrderEmb i).trans ((Fin.succAboveOrderEmb j).trans t) =
          (Fin.succAboveOrderEmb (j.castLT (lt_of_le_of_lt hj i.is_lt))).trans
            ((Fin.succAboveOrderEmb i.succ).trans t) := by
        apply DFunLike.ext
        intro k
        apply congrArg t
        exact (hsucc ▸ hpred ▸
          (Fin.succAbove_succAbove_succAbove_predAbove j i k)).symm
      change ((G.map (homOfLE (alternatingCechIntersection_face_le U p
          ((Fin.succAboveOrderEmb j).trans t) i)).op ≫
        G.map (homOfLE (alternatingCechIntersection_face_le U (p + 1) t j)).op).hom
          (s ((Fin.succAboveOrderEmb i).trans ((Fin.succAboveOrderEmb j).trans t)))) = _
      rw [← G.map_comp, ← op_comp]
      change _ = ((G.map (homOfLE (alternatingCechIntersection_face_le U p
          ((Fin.succAboveOrderEmb i.succ).trans t)
            (j.castLT (lt_of_le_of_lt hj i.is_lt)))).op ≫
        G.map (homOfLE (alternatingCechIntersection_face_le U (p + 1) t i.succ)).op).hom
          (s ((Fin.succAboveOrderEmb (j.castLT (lt_of_le_of_lt hj i.is_lt))).trans
            ((Fin.succAboveOrderEmb i.succ).trans t))))
      rw [← G.map_comp, ← op_comp]
      have hrestriction (a b : Fin (p + 1) ↪o Fin r)
          (ha : alternatingCechIntersection U t ≤ alternatingCechIntersection U a)
          (hb : alternatingCechIntersection U t ≤ alternatingCechIntersection U b)
          (hab : a = b) :
          (G.map (homOfLE ha).op).hom (s a) =
            (G.map (homOfLE hb).op).hom (s b) := by
        subst b
        rfl
      change (G.map (homOfLE (le_trans
        (alternatingCechIntersection_face_le U (p + 1) t j)
        (alternatingCechIntersection_face_le U p
          ((Fin.succAboveOrderEmb j).trans t) i))).op).hom
            (s ((Fin.succAboveOrderEmb i).trans ((Fin.succAboveOrderEmb j).trans t))) =
        (G.map (homOfLE (le_trans
          (alternatingCechIntersection_face_le U (p + 1) t i.succ)
          (alternatingCechIntersection_face_le U p
            ((Fin.succAboveOrderEmb i.succ).trans t)
              (j.castLT (lt_of_le_of_lt hj i.is_lt))))).op).hom
            (s ((Fin.succAboveOrderEmb (j.castLT (lt_of_le_of_lt hj i.is_lt))).trans
              ((Fin.succAboveOrderEmb i.succ).trans t)))
      exact hrestriction _ _ _ _ ht

/-- The nonnegative alternating Čech complex of a presheaf of global-ring modules.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechComplex :
    CochainComplex (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ℕ :=
  CochainComplex.of (alternatingCechTerms U G) (alternatingCechDifferential U G)
    (alternatingCechDifferential_square U G)

variable {G}
  {H K : X.Opensᵒᵖ ⥤ ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))}

/-- A morphism of presheaves acts componentwise on cochains.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechTermsMap (g : G ⟶ H) (p : ℕ) :
    alternatingCechTerms U G p ⟶ alternatingCechTerms U H p :=
  ModuleCat.ofHom (LinearMap.pi fun t ↦
    (g.app (op (alternatingCechIntersection U t))).hom.comp (LinearMap.proj t))

/-- Componentwise maps commute with the signed face differential.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex).
Proof: Naturality of g commutes with every face restriction. Apply it to each summand
of the finite signed sum and use linearity. -/
theorem alternatingCechTermsMap_comm (g : G ⟶ H) (p : ℕ) :
    alternatingCechTermsMap U g p ≫ (alternatingCechComplex U H).d p (p + 1) =
      (alternatingCechComplex U G).d p (p + 1) ≫ alternatingCechTermsMap U g (p + 1) := by
  classical
  set_option backward.isDefEq.respectTransparency false in
    simp only [alternatingCechComplex, CochainComplex.of_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change (∀ q : Fin (p + 1) ↪o Fin r, G.obj (op (alternatingCechIntersection U q))) at s
  funext t
  change (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
    (H.map (homOfLE (alternatingCechIntersection_face_le U p t j)).op).hom.comp
      (LinearMap.proj ((Fin.succAboveOrderEmb j).trans t)))
        (fun t ↦ (g.app (op (alternatingCechIntersection U t))).hom (s t)) =
    (g.app (op (alternatingCechIntersection U t))).hom
      ((∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
        (G.map (homOfLE (alternatingCechIntersection_face_le U p t j)).op).hom.comp
          (LinearMap.proj ((Fin.succAboveOrderEmb j).trans t))) s)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact congrArg (fun f ↦ f.hom (s ((Fin.succAboveOrderEmb j).trans t)))
    (g.naturality (homOfLE (alternatingCechIntersection_face_le U p t j)).op).symm

/-- The induced cochain map.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechComplexMap (g : G ⟶ H) :
    alternatingCechComplex U G ⟶ alternatingCechComplex U H :=
  CochainComplex.ofHom (fun p ↦ alternatingCechTermsMap U g p)
    (alternatingCechTermsMap_comm U g)

/-- Identity morphisms act as identity cochain maps.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex).
Proof: Evaluate in each degree and tuple; the component is the identity linear map. -/
theorem alternatingCechComplexMap_id :
    alternatingCechComplexMap U (𝟙 G) = 𝟙 (alternatingCechComplex U G) := by
  ext p s
  rfl

/-- Composition is componentwise composition.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex).
Proof: Evaluate in each degree and tuple; natural transformation composition is
componentwise composition, so both sides apply g and then h. -/
theorem alternatingCechComplexMap_comp (g : G ⟶ H) (h : H ⟶ K) :
    alternatingCechComplexMap U (g ≫ h) =
      alternatingCechComplexMap U g ≫ alternatingCechComplexMap U h := by
  ext p s
  rfl

/-- Alternating Čech cochains as a functor of the presheaf.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechComplexFunctor :
    (X.Opensᵒᵖ ⥤ ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ⥤
      CochainComplex (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ℕ where
  obj := alternatingCechComplex U
  map := alternatingCechComplexMap U
  map_id := fun G ↦ alternatingCechComplexMap_id U (G := G)
  map_comp := fun g h ↦ alternatingCechComplexMap_comp U g h

/-- The alternating Čech functor is additive.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex).
Proof: Addition of natural transformations and cochain maps is componentwise. The
explicit tuple maps preserve addition in every degree. -/
theorem alternatingCechComplexFunctor_additive :
    (alternatingCechComplexFunctor U).Additive := by
  constructor
  intro G H g h
  ext p s
  rfl

attribute [instance] alternatingCechComplexFunctor_additive

/-- The presheaf of Γ(X,O_X)-modules underlying an O_X-module.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechModulePresheaf :
    SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      (X.Opensᵒᵖ ⥤ ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) :=
  SheafOfModules.forget (moduleRings X.toRingedSpace) ⋙
    PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op

/-- The integer Čech complex, extended by zero in negative Čech degree.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechModuleFunctor :
    SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      CochainComplex (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ℤ :=
  alternatingCechModulePresheaf (X := X) ⋙ alternatingCechComplexFunctor U ⋙
    ComplexShape.embeddingUpNat.extendFunctor _

/-- The integer module Čech functor is additive.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex).
Proof: Forgetting to global-ring presheaves is additive, as are the tuple maps and
Mathlib extension by zero. The composite is therefore additive. -/
theorem alternatingCechModuleFunctor_additive :
    (alternatingCechModuleFunctor U).Additive := by
  have : (PresheafOfModules.forgetToPresheafModuleCat
      (R := (moduleRings X.toRingedSpace).obj) (op ⊤) isTerminalTop.op).Additive := by
    constructor
    intro M N g h
    ext V x
    rfl
  unfold alternatingCechModuleFunctor alternatingCechModulePresheaf
  infer_instance

attribute [instance] alternatingCechModuleFunctor_additive

/-- The double complex functor with Čech degree first and coefficient degree second.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechDoubleFunctor :
    CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ ⥤
      HomologicalComplex₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (alternatingCechModuleFunctor U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.flipFunctor _ (ComplexShape.up ℤ) (ComplexShape.up ℤ)

/-- The total complex functor, with differential d₁ + (-1)^p d₂.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechTotalFunctor :
    CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ ⥤
      CochainComplex (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ℤ :=
  alternatingCechDoubleFunctor U ⋙
    HomologicalComplex₂.totalFunctor _ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)

/-- Alternating Čech totalization is additive in the coefficient complex.
Source: Stacks, Cohomology, alternating Čech complexes of unbounded complexes
(blueprint: def-sc-alternating-cech-total-complex).
Proof: coefficient maps act linearly on every tuple. Mapping complexes and flipping
preserve addition componentwise. The coproduct universal property of totalization
then shows that total.map preserves addition in every degree. -/
theorem alternatingCechTotalFunctor_additive :
    (alternatingCechTotalFunctor U).Additive := by
  have : (HomologicalComplex₂.flipFunctor
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).Additive := by
    constructor
    intro K L f g
    ext i j
    rfl
  have : (HomologicalComplex₂.totalFunctor
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).Additive := by
    constructor
    intro K L f g
    apply HomologicalComplex.hom_ext
    intro n
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    change K.ιTotal (ComplexShape.up ℤ) i j n hij ≫
      (HomologicalComplex₂.total.map (f + g) (ComplexShape.up ℤ)).f n =
        K.ιTotal (ComplexShape.up ℤ) i j n hij ≫
          ((HomologicalComplex₂.total.map f (ComplexShape.up ℤ)).f n +
            (HomologicalComplex₂.total.map g (ComplexShape.up ℤ)).f n)
    simp only [ HomologicalComplex.add_f_apply,
      Preadditive.comp_add, HomologicalComplex₂.ιTotal_map]
    simp only [Preadditive.add_comp]
  unfold alternatingCechTotalFunctor alternatingCechDoubleFunctor
  infer_instance

attribute [instance] alternatingCechTotalFunctor_additive

variable (F : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)

/-- Restriction from the top open set to the zero Čech row of a presheaf.
Source: Stacks, Cohomology, equation-global-sections-to-alternating-cech
(blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechPresheafZero
    (P : X.Opensᵒᵖ ⥤ ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) :
    P.obj (op ⊤) ⟶ (alternatingCechComplex U P).X 0 :=
  ModuleCat.ofHom (LinearMap.pi fun t : Fin 1 ↪o Fin r ↦
    (P.map (homOfLE (le_top (a := alternatingCechIntersection U t))).op).hom)

private theorem alternatingCechPresheafZero_naturality
    {P Q : X.Opensᵒᵖ ⥤ ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))}
    (g : P ⟶ Q) :
    g.app (op ⊤) ≫ alternatingCechPresheafZero U Q =
      alternatingCechPresheafZero U P ≫ alternatingCechTermsMap U g 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext t
  exact congrArg (fun f ↦ f.hom s)
    (g.naturality (homOfLE (le_top (a := alternatingCechIntersection U t))).op).symm

/-- Restriction of global sections into the extended zero Čech row.
Source: Stacks, Cohomology, equation-global-sections-to-alternating-cech and
lemma-alternating-cech-complex-complex (blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechZero (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M ⟶
      ((alternatingCechModuleFunctor U).obj M).X 0 :=
  (ModuleCat.restrictScalarsId'App
      ((moduleRings X.toRingedSpace).obj.map (isTerminalTop.op.to (op ⊤))).hom
      (Scheme.Modules.moduleCech_top_restriction X) (M.val.obj (op ⊤))).inv ≫
    alternatingCechPresheafZero U ((alternatingCechModulePresheaf (X := X)).obj M) ≫
    ((alternatingCechComplex U ((alternatingCechModulePresheaf (X := X)).obj M)).extendXIso
      ComplexShape.embeddingUpNat (i := 0) rfl).inv

private theorem alternatingCechPresheafZero_d
    (P : X.Opensᵒᵖ ⥤ ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) :
    alternatingCechPresheafZero U P ≫ (alternatingCechComplex U P).d 0 1 = 0 := by
  classical
  simp only [alternatingCechComplex]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext t
  change (alternatingCechDifferential U P 0).hom
    ((alternatingCechPresheafZero U P).hom s) t = 0
  rw [alternatingCechDifferential_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  change (P.map (homOfLE (alternatingCechIntersection_face_le U 0 t 0)).op).hom
    ((P.map (homOfLE (le_top (a := alternatingCechIntersection U
      ((Fin.succAboveOrderEmb 0).trans t)))).op).hom s) +
    -(P.map (homOfLE (alternatingCechIntersection_face_le U 0 t 1)).op).hom
      ((P.map (homOfLE (le_top (a := alternatingCechIntersection U
        ((Fin.succAboveOrderEmb 1).trans t)))).op).hom s) = 0
  rw [add_neg_eq_zero]
  change ((P.map (homOfLE (le_top (a := alternatingCechIntersection U
      ((Fin.succAboveOrderEmb 0).trans t)))).op ≫
    P.map (homOfLE (alternatingCechIntersection_face_le U 0 t 0)).op).hom s) =
      ((P.map (homOfLE (le_top (a := alternatingCechIntersection U
        ((Fin.succAboveOrderEmb 1).trans t)))).op ≫
      P.map (homOfLE (alternatingCechIntersection_face_le U 0 t 1)).op).hom s)
  rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp]
  congr 3

private theorem alternatingCechZero_d
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    alternatingCechZero U M ≫ ((alternatingCechModuleFunctor U).obj M).d 0 1 = 0 := by
  unfold alternatingCechZero
  change _ ≫ ((alternatingCechComplex U
    ((alternatingCechModulePresheaf (X := X)).obj M)).extend
      ComplexShape.embeddingUpNat).d 0 1 = 0
  erw [HomologicalComplex.extend_d_eq _ _ (i := 0) (j := 1) rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  erw [← Category.assoc (alternatingCechPresheafZero U
    ((alternatingCechModulePresheaf (X := X)).obj M))
      ((alternatingCechComplex U ((alternatingCechModulePresheaf (X := X)).obj M)).d 0 1),
    alternatingCechPresheafZero_d]
  simp only [zero_comp, comp_zero]

private theorem alternatingCechZero_naturality
    {M N : SheafOfModules.{u} (moduleRings X.toRingedSpace)} (g : M ⟶ N) :
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).map g ≫ alternatingCechZero U N =
      alternatingCechZero U M ≫ ((alternatingCechModuleFunctor U).map g).f 0 := by
  unfold alternatingCechZero
  change _ = _ ≫ (HomologicalComplex.extendMap
    (alternatingCechComplexMap U ((alternatingCechModulePresheaf (X := X)).map g))
      ComplexShape.embeddingUpNat).f 0
  erw [HomologicalComplex.extendMap_f _ _ (i := 0) (i' := 0) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  dsimp only [alternatingCechComplexMap, CochainComplex.ofHom]
  erw [← Category.assoc (alternatingCechPresheafZero U
    ((alternatingCechModulePresheaf (X := X)).obj M))
      (alternatingCechTermsMap U ((alternatingCechModulePresheaf (X := X)).map g) 0)]
  erw [← alternatingCechPresheafZero_naturality]
  simp only [← Category.assoc]
  congr 1

/-- The augmentation component is restriction in Čech degree zero, included in total degree n.
Source: Stacks, Cohomology, equation-global-sections-to-alternating-cech and
lemma-alternating-cech-complex-complex (blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechAugmentationComponent (n : ℤ) :
    (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj F).X n ⟶ ((alternatingCechTotalFunctor U).obj F).X n :=
  alternatingCechZero U (F.X n) ≫
    ((alternatingCechDoubleFunctor U).obj F).ιTotal (ComplexShape.up ℤ) 0 n n
      (Int.zero_add n)

/-- The restriction components commute with the total differential.
Source: Stacks, Cohomology, equation-global-sections-to-alternating-cech and
lemma-alternating-cech-complex-complex (blueprint: def-sc-alternating-cech-total-complex).
Proof: Restrictions commute with d_F. The signed face differential of global-section
restrictions is zero by cancellation on each pair of opens. In Čech degree zero the
vertical sign is +1. Other components of the augmentation vanish. -/
theorem alternatingCechAugmentation_comm (n m : ℤ) :
    alternatingCechAugmentationComponent U F n ≫
        ((alternatingCechTotalFunctor U).obj F).d n m =
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj F).d n m ≫
          alternatingCechAugmentationComponent U F m := by
  by_cases h : n + 1 = m
  · subst m
    let B := (alternatingCechDoubleFunctor U).obj F
    change (alternatingCechZero U (F.X n) ≫
      B.ιTotal (ComplexShape.up ℤ) 0 n n (Int.zero_add n)) ≫
        (B.total (ComplexShape.up ℤ)).d n (n + 1) =
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).map (F.d n (n + 1)) ≫
        (alternatingCechZero U (F.X (n + 1)) ≫
          B.ιTotal (ComplexShape.up ℤ) 0 (n + 1) (n + 1) (Int.zero_add (n + 1)))
    rw [Category.assoc, HomologicalComplex₂.total_d, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
      HomologicalComplex₂.d₁_eq' _ _ (i₁' := 1) (by simp),
      HomologicalComplex₂.d₂_eq _ _ 0 (i₂' := n + 1) (by simp) _ (Int.zero_add _)]
    have he₁ : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (0, n) = 1 := rfl
    have he₂ : ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (0, n) = 1 := ComplexShape.ε_zero _
    simp only [he₁, he₂, one_smul, Preadditive.comp_add, ← Category.assoc]
    change (alternatingCechZero U (F.X n) ≫
        ((alternatingCechModuleFunctor U).obj (F.X n)).d 0 1) ≫ _ +
      (alternatingCechZero U (F.X n) ≫
        ((alternatingCechModuleFunctor U).map (F.d n (n + 1))).f 0) ≫ _ = _
    rw [alternatingCechZero_d, zero_comp, zero_add, ← alternatingCechZero_naturality]
  · rw [HomologicalComplex.shape _ n m h, HomologicalComplex.shape _ n m h]
    simp only [comp_zero, zero_comp]

/-- The explicit section-to-total augmentation cochain map.
Source: Stacks, Cohomology, equation-global-sections-to-alternating-cech and
lemma-alternating-cech-complex-complex (blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechAugmentationMap :
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj F ⟶ (alternatingCechTotalFunctor U).obj F where
  f := alternatingCechAugmentationComponent U F
  comm' := fun n m _ ↦ alternatingCechAugmentation_comm U F n m

/-- The augmentation is natural in the coefficient complex.
Source: Stacks, Cohomology, equation-global-sections-to-alternating-cech and
lemma-alternating-cech-complex-complex (blueprint: def-sc-alternating-cech-total-complex).
Proof: Evaluate in each total degree. Naturality of a module morphism commutes with
each restriction to a cover member, and total.map commutes with each summand inclusion.
There are no positive Čech-degree components in the augmentation. -/
theorem alternatingCechAugmentation_naturality
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (g : F ⟶ G) :
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g ≫ alternatingCechAugmentationMap U G =
        alternatingCechAugmentationMap U F ≫ (alternatingCechTotalFunctor U).map g := by
  apply HomologicalComplex.hom_ext
  intro n
  change (RingedSpace.globalSectionsFunctor X.toRingedSpace).map (g.f n) ≫
      (alternatingCechZero U (G.X n) ≫
        ((alternatingCechDoubleFunctor U).obj G).ιTotal (ComplexShape.up ℤ) 0 n n
          (Int.zero_add n)) =
    (alternatingCechZero U (F.X n) ≫
        ((alternatingCechDoubleFunctor U).obj F).ιTotal (ComplexShape.up ℤ) 0 n n
          (Int.zero_add n)) ≫
      (HomologicalComplex₂.total.map ((alternatingCechDoubleFunctor U).map g)
        (ComplexShape.up ℤ)).f n
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc]
  exact congrArg (fun f ↦ f ≫
    ((alternatingCechDoubleFunctor U).obj G).ιTotal (ComplexShape.up ℤ) 0 n n
      (Int.zero_add n)) (alternatingCechZero_naturality U (g.f n))

/-- The section-to-total augmentation as a natural transformation.
Source: Stacks, Cohomology, equation-global-sections-to-alternating-cech and
lemma-alternating-cech-complex-complex (blueprint: def-sc-alternating-cech-total-complex). -/
def alternatingCechAugmentation :
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ) ⟶ alternatingCechTotalFunctor U where
  app := alternatingCechAugmentationMap U
  naturality := fun F G g ↦ alternatingCechAugmentation_naturality U F G g

variable
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{v}
    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]

/-- The canonical comparison is characterized through every K-injective resolution.
This equation specifies the roof without choosing any unproved data.
The resolution need not have injective terms: compare it with one that does. The
comparison is a homotopy equivalence, preserved by sections and by the explicit
Čech totalization, so naturality transports the equation to this resolution.
Source: Stacks, Cohomology, equation-global-sections-to-alternating-cech and
lemma-alternating-cech-complex-complex (blueprint: def-sc-alternating-cech-total-complex). -/
def IsAlternatingCechDerivedComparison
    (β : DerivedCategory.Q.obj ((alternatingCechTotalFunctor U).obj F) ⟶
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj
        (DerivedCategory.Q.obj F)) : Prop :=
  ∀ (J : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [J.IsKInjective] (i : F ⟶ J) [QuasiIso i],
    β ≫ (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map
        (DerivedCategory.Q.map i) ≫
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorObjQIso J).hom ≫
      DerivedCategory.Q.map ((alternatingCechAugmentation U).app J) =
        DerivedCategory.Q.map ((alternatingCechTotalFunctor U).map i)

end
end AlgebraicGeometry
