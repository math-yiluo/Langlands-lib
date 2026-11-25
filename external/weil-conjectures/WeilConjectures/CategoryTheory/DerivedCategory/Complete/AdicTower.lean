/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.TensorQuotPow
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.ReductionCone
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower

/-!
# Reductions of the derived limit of a strict normalized adic tower

Let `(C, J)` be an essentially small site, `R` a commutative ring and `ϖ ∈ R` a nonzerodivisor
generating the ideal `I`. For a normalized `ϖ`-adic tower `T` of complexes of sheaves of
`R`-modules (`CochainComplex.IsNormalizedAdicTower`) and a homotopy limit
`K = R lim_n T_n` of its image in `D(J, R)`, the reductions `K ⊗ᴸ R/Iⁿ` are the `T_n`,
compatibly with the reduction maps and with the transitions:
`DerivedCategory.exists_derivedCompletionDiagram_iso_of_isNormalizedAdicTower`.

Proof sketch: `- ⊗ᴸ R/Iⁿ` is triangulated and commutes with countable products, hence with
`R lim`; on complexes it is the mapping cone of `ϖⁿ` (`DerivedCategory.reductionIso`), and the
tower of cones `cone(ϖⁿ on T_{m+n})` has derived limit `T_n`
(`CochainComplex.IsNormalizedAdicTower.isIso_π_comp`).

## Implementation notes

The monoidal structure of `D(J, R)` is taken from the fields of
`DerivedCategory.sheafTensorStructure J R`, as explained in the implementation notes of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory Opposite Pretriangulated

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]

attribute [-instance] commShift₂CurriedTensor commShiftTensorLeft commShiftTensorRight
  isTriangulated_tensorLeft isTriangulated_tensorRight monoidalPreadditive monoidalLinear

noncomputable local instance (priority := high) adicTowerMonoidalCategory :
    MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalCategory

noncomputable local instance (priority := high) adicTowerMonoidalPreadditive :
    MonoidalPreadditive (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalPreadditive

noncomputable local instance (priority := high) adicTowerMonoidalLinear :
    MonoidalLinear R (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalLinear

noncomputable local instance (priority := high) adicTowerCommShift₂ :
    (curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).CommShift₂Int :=
  (sheafTensorStructure J R).commShift₂

noncomputable local instance (priority := high) adicTowerIsTriangulatedLeft
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ((curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).obj K).IsTriangulated :=
  (sheafTensorStructure J R).isTriangulated_tensorLeft K

noncomputable local instance (priority := high) adicTowerIsTriangulatedRight
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ((curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).flip.obj K).IsTriangulated :=
  (sheafTensorStructure J R).isTriangulated_tensorRight K

local instance adicTowerIsIsoε : IsIso (sheafTensorStructure J R).ε :=
  (sheafTensorStructure J R).isIso_ε

variable {J}

section Products

variable {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

/-- Tensoring with `R/Iⁿ` commutes with countable products. -/
noncomputable def isLimit_fan_whiskerRight_quotPow (n : ℕ)
    {Y : ℕ → DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))} {P : Fan Y} (hP : IsLimit P) :
    IsLimit (Fan.mk (P.pt ⊗ (quotPowFunctor J I).obj (op n)) fun j ↦ P.proj j ▷ _) := by
  let T := fun j ↦ tensorQuotPowTriangle hϖ hI (Y j) n
  let ψ : tensorQuotPowTriangle hϖ hI P.pt n ⟶ productTriangle T :=
    productTriangle.lift T fun j ↦ tensorQuotPowTriangleMap hϖ hI (P.proj j) n
  have hU := isLimit_fan_whiskerRight_unit (J := J) hP
  have h₁ : IsIso ψ.hom₁ := by
    have : ψ.hom₁ = (hU.conePointUniqueUpToIso (productIsProduct _)).hom := by
      refine Pi.hom_ext _ _ fun j ↦ ?_
      erw [IsLimit.conePointUniqueUpToIso_hom_comp hU (productIsProduct _) ⟨j⟩]
      simp [ψ, tensorQuotPowTriangleMap]
      rfl
    rw [this]
    infer_instance
  have h₂ : IsIso ψ.hom₂ := by
    have : ψ.hom₂ = (hU.conePointUniqueUpToIso (productIsProduct _)).hom := by
      refine Pi.hom_ext _ _ fun j ↦ ?_
      erw [IsLimit.conePointUniqueUpToIso_hom_comp hU (productIsProduct _) ⟨j⟩]
      simp [ψ, tensorQuotPowTriangleMap]
      rfl
    rw [this]
    infer_instance
  have h₃ : IsIso ψ.hom₃ := isIso₃_of_isIso₁₂ ψ (tensorQuotPowTriangle_distinguished hϖ hI _ n)
    (productTriangle_distinguished T fun j ↦ tensorQuotPowTriangle_distinguished hϖ hI _ n) h₁ h₂
  refine IsLimit.ofIsoLimit (productIsProduct _) (Fan.ext (asIso ψ.hom₃).symm fun j ↦ ?_)
  rw [Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp]
  simp only [ψ, productTriangle.lift_hom₃, tensorQuotPowTriangleMap, Fan.mk_pt]
  exact Pi.lift_comp_π _ _

variable (J I) in
/-- The reduction functor `- ⊗ᴸ R/Iⁿ` on `D(J, R)`. -/
noncomputable abbrev reductionFunctor (n : ℕ) :
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  (curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).flip.obj
    ((quotPowFunctor J I).obj (op n))

include hϖ hI in
/-- The reduction functor `- ⊗ᴸ R/Iⁿ` preserves homotopy limits of towers. -/
lemma IsHomotopyLimit.map_reductionFunctor (n : ℕ)
    {F : ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))} {c : Cone F}
    (hc : IsHomotopyLimit c) : IsHomotopyLimit ((reductionFunctor J I n).mapCone c) := by
  have : PreservesLimit (Discrete.functor fun j : ℕ ↦ F.obj (op j)) (reductionFunctor J I n) :=
    preservesLimit_of_preserves_limit_cone (productIsProduct _)
      ((isLimitMapConeFanMkEquiv _ _ _).symm
        (isLimit_fan_whiskerRight_quotPow hϖ hI n (productIsProduct _)))
  exact hc.map (reductionFunctor J I n)

end Products

section Reduction

variable {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

lemma constantSheaf_map_smul_id (r : R) :
    (constantSheaf J (ModuleCat.{u + 1} R)).map (r • 𝟙 (𝟙_ (ModuleCat.{u + 1} R))) =
      r • 𝟙 (𝟙_ (Sheaf J (ModuleCat.{u + 1} R))) := by
  rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

include hI in
lemma smul_comp_sheafQuotPowCone_π (n : ℕ) :
    (ϖ ^ n • 𝟙 (𝟙_ (Sheaf J (ModuleCat.{u + 1} R)))) ≫ (Sheaf.quotPowCone J I).π.app (op n) =
      0 := by
  erw [← constantSheaf_map_smul_id]
  change (constantSheaf J (ModuleCat.{u + 1} R)).map _ ≫
    (constantSheaf J (ModuleCat.{u + 1} R)).map _ = 0
  rw [← Functor.map_comp]
  exact (congrArg _ (quotPowShortComplex I ϖ (mem_of_eq_span hI) n).zero).trans
    (Functor.map_zero _ _ _)

include hϖ in
/-- The short exact sequence `0 ⟶ R ⟶ R ⟶ R/Iⁿ ⟶ 0` of constant sheaves, the first map being
the multiplication by `ϖⁿ` on the monoidal unit. -/
lemma sheafQuotPowShortComplex_shortExact' (n : ℕ) :
    (ShortComplex.mk _ _ (smul_comp_sheafQuotPowCone_π (J := J) (R := R) hI n)).ShortExact := by
  have h := sheafQuotPowShortComplex_shortExact J hϖ hI n
  refine ShortComplex.shortExact_of_iso ?_ h
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp only [Iso.refl_hom, id_comp, comp_id, ShortComplex.map_f]
    exact (constantSheaf_map_smul_id (J := J) (ϖ ^ n)).symm
  · simp only [Iso.refl_hom, id_comp, comp_id, ShortComplex.map_g]
    rfl

/-- The reduction `Q X ⊗ᴸ R/Iⁿ` of a complex `X` of sheaves is the mapping cone of `ϖⁿ` on
`X`. -/
noncomputable def reductionConeIso (n : ℕ)
    (X : CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ) :
    Q.obj X ⊗ (quotPowFunctor J I).obj (op n) ≅
      Q.obj (CochainComplex.mappingCone (ϖ ^ n • 𝟙 X)) :=
  TensorStructure.reductionIso (sheafTensorStructure J R) rfl
    (smul_comp_sheafQuotPowCone_π hI n)
    (sheafQuotPowShortComplex_shortExact' hϖ hI n) X

end Reduction

section Reduction'

variable {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

lemma reductionConeIso_hom_naturality (n : ℕ)
    {X Y : CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ} (f : X ⟶ Y) :
    (Q.map f ▷ (quotPowFunctor J I).obj (op n)) ≫ (reductionConeIso hϖ hI n Y).hom =
      (reductionConeIso hϖ hI n X).hom ≫
        Q.map (CochainComplex.mappingCone.map (ϖ ^ n • 𝟙 X) (ϖ ^ n • 𝟙 Y) f f (by simp)) :=
  TensorStructure.reductionIso_hom_naturality (sheafTensorStructure J R) rfl _ _ f

/-- Under `reductionConeIso`, the reduction map `Q X ⟶ Q X ⊗ᴸ R/Iⁿ` is the inclusion of `X` into
the mapping cone. -/
lemma derivedCompletionCone_π_app_reductionConeIso_hom (n : ℕ)
    (X : CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ) :
    (derivedCompletionCone J I (Q.obj X)).π.app (op n) ≫ (reductionConeIso hϖ hI n X).hom =
      Q.map (CochainComplex.mappingCone.inr (ϖ ^ n • 𝟙 X)) :=
  by
  rw [show (derivedCompletionCone J I (Q.obj X)).π.app (op n) = (ρ_ (Q.obj X)).inv ≫
    Q.obj X ◁ ((sheafTensorStructure J R).ε ≫ (singleFunctor _ 0).map
      ((Sheaf.quotPowCone J I).π.app (op n))) from rfl, assoc]
  exact TensorStructure.reduction_reductionIso_hom (sheafTensorStructure J R) rfl
    (smul_comp_sheafQuotPowCone_π hI n) (sheafQuotPowShortComplex_shortExact' hϖ hI n) X

/-- `reductionConeIso` is compatible with the transition `R/Iⁿ ⟶ R/Iᵏ` for `k ≤ n`. -/
lemma derivedCompletionDiagram_map_reductionConeIso_hom {k n : ℕ} (h : k ≤ n)
    (X : CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ) :
    (derivedCompletionDiagram J I (Q.obj X)).map (homOfLE h).op ≫
        (reductionConeIso hϖ hI k X).hom =
      (reductionConeIso hϖ hI n X).hom ≫ Q.map (CochainComplex.mappingCone.map
        (ϖ ^ n • 𝟙 X) (ϖ ^ k • 𝟙 X) (ϖ ^ (n - k) • 𝟙 X) (𝟙 X)
        (smul_comp_smul_eq (by rw [← pow_add, Nat.add_sub_cancel' h]) X).symm) :=
  TensorStructure.whiskerLeft_reductionIso_hom (sheafTensorStructure J R) rfl
    (by rw [← pow_add, Nat.add_sub_cancel' h]) _ _ _ _ _ ((Sheaf.quotPowCone J I).w _) X

/-- The reduction maps `K ⟶ K ⊗ᴸ R/Iⁿ` are natural in `K`. -/
@[reassoc]
lemma derivedCompletionCone_π_app_naturality
    {K K' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (f : K ⟶ K') (n : ℕ) :
    (derivedCompletionCone J I K).π.app (op n) ≫ f ▷ (quotPowFunctor J I).obj (op n) =
      f ≫ (derivedCompletionCone J I K').π.app (op n) := by
  change ((ρ_ K).inv ≫ K ◁ _) ≫ _ = f ≫ (ρ_ K').inv ≫ K' ◁ _
  rw [assoc, whisker_exchange, ← assoc, ← rightUnitor_inv_naturality, assoc]

/-- Under `reductionConeIso`, the reduction map of `K` followed by the reduction of a morphism
`g : K ⟶ Q X` is `g` followed by the inclusion of `X` into the mapping cone. -/
@[reassoc]
lemma derivedCompletionCone_π_app_comp_reductionFunctor_map
    {K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    {X : CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ} (g : K ⟶ Q.obj X) (n : ℕ) :
    (derivedCompletionCone J I K).π.app (op n) ≫ (reductionFunctor J I n).map g ≫
        (reductionConeIso hϖ hI n X).hom =
      g ≫ Q.map (CochainComplex.mappingCone.inr (ϖ ^ n • 𝟙 X)) := by
  rw [← assoc]
  erw [derivedCompletionCone_π_app_naturality]
  rw [assoc, derivedCompletionCone_π_app_reductionConeIso_hom]

/-- Under `reductionConeIso`, the transitions of the tower of reductions of `K`, composed with
the reduction of a morphism `g : K ⟶ Q X`, become the maps of mapping cones induced by
`ϖⁿ⁻ᵏ`. -/
@[reassoc]
lemma derivedCompletionDiagram_map_comp_reductionFunctor_map
    {K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    {X : CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ} (g : K ⟶ Q.obj X) {k n : ℕ}
    (h : k ≤ n) :
    (derivedCompletionDiagram J I K).map (homOfLE h).op ≫ (reductionFunctor J I k).map g ≫
        (reductionConeIso hϖ hI k X).hom =
      (reductionFunctor J I n).map g ≫ (reductionConeIso hϖ hI n X).hom ≫
        Q.map (CochainComplex.mappingCone.map (ϖ ^ n • 𝟙 X) (ϖ ^ k • 𝟙 X) (ϖ ^ (n - k) • 𝟙 X)
          (𝟙 X) (smul_comp_smul_eq (by rw [← pow_add, Nat.add_sub_cancel' h]) X).symm) := by
  rw [← assoc]
  erw [whisker_exchange]
  rw [assoc]
  erw [derivedCompletionDiagram_map_reductionConeIso_hom]
  rfl

end Reduction'

end DerivedCategory

namespace CochainComplex.IsNormalizedAdicTower

open ConeCoimage

variable {R : Type*} [Ring R] {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [Linear R 𝒜]
  {ϖ : R} {T : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ}

lemma mappingCone_hom_ext {F G Z : CochainComplex 𝒜 ℤ} {φ : F ⟶ G}
    {a b : mappingCone φ ⟶ Z}
    (h₁ : ∀ p q (hpq : p + (-1) = q),
      (mappingCone.inl φ).v p q hpq ≫ a.f q = (mappingCone.inl φ).v p q hpq ≫ b.f q)
    (h₂ : mappingCone.inr φ ≫ a = mappingCone.inr φ ≫ b) : a = b := by
  ext j
  refine mappingCone.ext_from φ (j + 1) j rfl (h₁ _ _ _) ?_
  rw [← HomologicalComplex.comp_f, h₂, HomologicalComplex.comp_f]

lemma smul_comp_map_eq_zero (hT : IsNormalizedAdicTower ϖ T) {k n N : ℕ} (hk : k ≤ n)
    (hN : k ≤ N) : (ϖ ^ n • 𝟙 (T.obj (op N))) ≫ T.map (homOfLE hN).op = 0 := by
  rw [Linear.smul_comp, id_comp, ← comp_id (T.map _), ← Linear.comp_smul,
    show ϖ ^ n = ϖ ^ (n - k) * ϖ ^ k by rw [← pow_add, Nat.sub_add_cancel hk], ← smul_smul,
    hT.smul_eq_zero, smul_zero, comp_zero]

/-- The map `cone(ϖⁿ on T_N) ⟶ T_k`, for `k ≤ n` and `k ≤ N`, which vanishes on the shifted copy
of `T_N` and is the transition on the other one. -/
noncomputable def coneToLevel (hT : IsNormalizedAdicTower ϖ T) {k n N : ℕ} (hk : k ≤ n)
    (hN : k ≤ N) : mappingCone (ϖ ^ n • 𝟙 (T.obj (op N))) ⟶ T.obj (op k) :=
  mappingCone.desc _ 0 (T.map (homOfLE hN).op) (by
    simp [hT.smul_comp_map_eq_zero hk hN])

@[reassoc (attr := simp)]
lemma inr_coneToLevel (hT : IsNormalizedAdicTower ϖ T) {k n N : ℕ} (hk : k ≤ n) (hN : k ≤ N) :
    mappingCone.inr _ ≫ hT.coneToLevel hk hN = T.map (homOfLE hN).op := by
  simp [coneToLevel]

@[reassoc (attr := simp)]
lemma inl_v_coneToLevel_f (hT : IsNormalizedAdicTower ϖ T) {k n N : ℕ} (hk : k ≤ n)
    (hN : k ≤ N) (p q : ℤ) (hpq : p + (-1) = q) :
    (mappingCone.inl (ϖ ^ n • 𝟙 (T.obj (op N)))).v p q hpq ≫ (hT.coneToLevel hk hN).f q = 0 := by
  simp [coneToLevel]

lemma ρ_desc_cokerDesc (hT : IsNormalizedAdicTower ϖ T) (n : ℕ) :
    ρ.app _ ≫ desc.app _ ≫ hT.cokerDesc n (op 0) =
      hT.coneToLevel (k := n) (n := n) (N := 0 + n) le_rfl (by omega) := by
  refine mappingCone_hom_ext (fun p q hpq ↦ ?_) ?_
  · simp only [HomologicalComplex.comp_f]
    rw [← assoc, inl_v_ρ_app_f, assoc]
    simp only [desc_app, mappingCone.descShortComplex]
    erw [mappingCone.inl_v_desc_f_assoc]
    simp
  · erw [inr_coneToLevel, reassoc_of% (inr_ρ_desc ((arrowTower (ϖ := ϖ) (T := T) n).obj (op 0))),
      π_cokerDesc]
    rfl

lemma coneToLevel_comp_map (hT : IsNormalizedAdicTower ϖ T) {k k' n N : ℕ} (hk : k ≤ n)
    (hN : k ≤ N) (hk' : k' ≤ k) :
    hT.coneToLevel hk hN ≫ T.map (homOfLE hk').op =
      hT.coneToLevel (hk'.trans hk) (hk'.trans hN) := by
  refine mappingCone_hom_ext (fun p q hpq ↦ ?_) ?_
  · simp only [HomologicalComplex.comp_f, inl_v_coneToLevel_f_assoc, zero_comp,
      inl_v_coneToLevel_f]
  · simp only [inr_coneToLevel_assoc, inr_coneToLevel, ← Functor.map_comp]
    rfl

lemma map_map_coneToLevel (hT : IsNormalizedAdicTower ϖ T) {k n N N' : ℕ} (hk : k ≤ n)
    (hN' : k ≤ N') (h : N' ≤ N) :
    mappingCone.map (ϖ ^ n • 𝟙 (T.obj (op N))) (ϖ ^ n • 𝟙 (T.obj (op N')))
        (T.map (homOfLE h).op) (T.map (homOfLE h).op) (by simp) ≫
      hT.coneToLevel hk hN' = hT.coneToLevel hk (hN'.trans h) := by
  refine mappingCone_hom_ext (fun p q hpq ↦ ?_) ?_
  · simp [mappingCone.map]
  · simp only [mappingCone.map, mappingCone.inr_desc_assoc, assoc, inr_coneToLevel,
      ← Functor.map_comp]
    rfl

lemma map_smul_coneToLevel (hT : IsNormalizedAdicTower ϖ T) {k n n' N : ℕ} (hk : k ≤ n')
    (hn : n' ≤ n) (hN : k ≤ N) :
    mappingCone.map (ϖ ^ n • 𝟙 (T.obj (op N))) (ϖ ^ n' • 𝟙 (T.obj (op N)))
        (ϖ ^ (n - n') • 𝟙 _) (𝟙 _) (by
          rw [comp_id, Linear.smul_comp, id_comp, smul_smul, ← pow_add, Nat.sub_add_cancel hn]) ≫
      hT.coneToLevel hk hN = hT.coneToLevel (hk.trans hn) hN := by
  refine mappingCone_hom_ext (fun p q hpq ↦ ?_) ?_
  · simp [mappingCone.map]
  · simp [mappingCone.map]

end CochainComplex.IsNormalizedAdicTower

namespace DerivedCategory

open CochainComplex CochainComplex.IsNormalizedAdicTower ConeCoimage

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {R : Type (u + 1)} [CommRing R]
  {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})
  {T : ℕᵒᵖ ⥤ CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ}
  (hT : IsNormalizedAdicTower ϖ T)
  {c : Cone (T ⋙ Q)} (hc : IsHomotopyLimit c)

include hc in
lemma isIso_reduction_comp_coneToLevel (n : ℕ) :
    IsIso ((reductionFunctor J I n).map (c.π.app (op (0 + n))) ≫
      (reductionConeIso hϖ hI n (T.obj (op (0 + n)))).hom ≫
        Q.map (hT.coneToLevel (k := n) (n := n) (N := 0 + n) le_rfl (by omega))) := by
  let c₁ := (reductionFunctor J I n).mapCone c
  have hc₂ := (IsHomotopyLimit.map_reductionFunctor hϖ hI n hc).whiskerAdd n
  let E : addOpFunctor n ⋙ (T ⋙ Q) ⋙ reductionFunctor J I n ≅
      arrowTower (ϖ := ϖ) (T := T) n ⋙ cone ⋙ Q :=
    NatIso.ofComponents (fun m ↦ reductionConeIso hϖ hI n (T.obj ((addOpFunctor n).obj m)))
      (fun f ↦ reductionConeIso_hom_naturality hϖ hI n (T.map ((addOpFunctor n).map f)))
  let c₃ : Cone (arrowTower (ϖ := ϖ) (T := T) n ⋙ cone ⋙ Q) :=
    { pt := c₁.pt, π := (c₁.whisker (addOpFunctor n)).π ≫ E.hom }
  have hc₃ : IsHomotopyLimit c₃ := hc₂.of_iso E c₃ (Iso.refl _) fun m ↦ by
    simp only [Iso.refl_hom, id_comp]
    rfl
  have := hT.isIso_π_comp n hc₃
  rw [ρ_desc_cokerDesc] at this
  simpa [c₃, E, c₁] using this
/-- The composite `c.pt ⊗ᴸ R/Iⁿ ⟶ Q(cone(ϖⁿ on T_N)) ⟶ Q(T_k)` of the reduction of the leg
`c.π_N` with `coneToLevel` does not depend on `N`. -/
lemma reduction_comp_coneToLevel_eq {k n N N' : ℕ} (hk : k ≤ n) (hN' : k ≤ N') (h : N' ≤ N) :
    (reductionFunctor J I n).map (c.π.app (op N')) ≫
        (reductionConeIso hϖ hI n (T.obj (op N'))).hom ≫ Q.map (hT.coneToLevel hk hN') =
      (reductionFunctor J I n).map (c.π.app (op N)) ≫
        (reductionConeIso hϖ hI n (T.obj (op N))).hom ≫
          Q.map (hT.coneToLevel hk (hN'.trans h)) := by
  have := reductionConeIso_hom_naturality hϖ hI n (T.map (homOfLE h).op)
  rw [← c.w (homOfLE h).op, Functor.map_comp, assoc]
  erw [reassoc_of% this]
  rw [← Functor.map_comp, map_map_coneToLevel]

/-- For a normalized `ϖ`-adic tower `T` and a homotopy limit `c` of its image in `D(J, R)`, the
tower of reductions `c.pt ⊗ᴸ R/Iⁿ` is isomorphic to `n ↦ T_n`, compatibly with the legs of `c`
and the reduction maps `c.pt ⟶ c.pt ⊗ᴸ R/Iⁿ`. -/
theorem exists_derivedCompletionDiagram_iso_of_isNormalizedAdicTower
    (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})
    {T : ℕᵒᵖ ⥤ CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ}
    (hT : CochainComplex.IsNormalizedAdicTower ϖ T) {c : Cone (T ⋙ Q)} (hc : IsHomotopyLimit c) :
    ∃ e : derivedCompletionDiagram J I c.pt ≅ T ⋙ Q, ∀ n : ℕ,
      c.π.app (op n) = (derivedCompletionCone J I c.pt).π.app (op n) ≫ e.hom.app (op n) := by
  have hiso (n : ℕ) : IsIso ((reductionFunctor J I n).map (c.π.app (op n)) ≫
      (reductionConeIso hϖ hI n (T.obj (op n))).hom ≫
        Q.map (hT.coneToLevel (k := n) (n := n) (N := n) le_rfl le_rfl)) := by
    rw [reduction_comp_coneToLevel_eq hϖ hI hT le_rfl le_rfl (Nat.le_add_left n 0)]
    exact isIso_reduction_comp_coneToLevel hϖ hI hT hc n
  refine ⟨NatIso.ofComponents (fun n ↦ @asIso _ _ _ _ _ (hiso n.unop)) ?_, fun n ↦ ?_⟩
  · rintro ⟨n⟩ ⟨k⟩ f
    have h : k ≤ n := leOfHom f.unop
    obtain rfl : f = (homOfLE h).op := rfl
    simp only [asIso_hom, Opposite.unop_op, Functor.comp_map, assoc]
    rw [derivedCompletionDiagram_map_comp_reductionFunctor_map_assoc, ← Functor.map_comp,
      map_smul_coneToLevel hT le_rfl h, ← Functor.map_comp, coneToLevel_comp_map,
      reduction_comp_coneToLevel_eq hϖ hI hT h le_rfl h]
  · simp only [NatIso.ofComponents_hom_app, asIso_hom, Opposite.unop_op]
    rw [derivedCompletionCone_π_app_comp_reductionFunctor_map_assoc, ← Functor.map_comp,
      inr_coneToLevel]
    simp

end DerivedCategory
