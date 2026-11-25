/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.TensorQuotPow

/-!
# Derived completeness for a principal ideal

Let `(C, J)` be an essentially small site, `R` a commutative ring and `ϖ ∈ R` a nonzerodivisor.
This file shows that an object `K` of `D(J, R) = DerivedCategory (Sheaf J (ModuleCat R))` is
derived complete for the ideal `(ϖ)` (`DerivedCategory.derivedComplete`, defined by the Milnor
triangle `K ≅ R lim_n (K ⊗ᴸ R/ϖⁿ)`) if and only if every map to `K` from an object on which `ϖ`
acts invertibly vanishes. This is the characterisation `RHom(R[1/ϖ], K) = 0` of Stacks,
Tags 091Q and 0999, phrased with the class `DerivedCategory.smulInvertible J ϖ` of objects on
which `ϖ` acts invertibly (the objects `X ⊗ᴸ R[1/ϖ]`). As a consequence, the derived complete
objects form a triangulated subcategory.

## Main definitions

- `DerivedCategory.smulInvertible J ϖ`: the objects `X` of `D(J, R)` such that `ϖ • 𝟙 X` is an
  isomorphism.

## Main results

- `DerivedCategory.derivedComplete_iff_rightOrthogonal`: for `I = (ϖ)` with `ϖ` a
  nonzerodivisor, `K` is derived complete iff it is right orthogonal to
  `DerivedCategory.smulInvertible J ϖ`.
- `DerivedCategory.isTriangulated_derivedComplete`: the derived complete objects form a
  triangulated subcategory.

## Proof

If `K` is derived complete, the terms `K ⊗ᴸ R/ϖⁿ` of the tower are killed by `ϖⁿ`, so they
receive no nonzero maps from objects on which `ϖ` acts invertibly, and neither does their
homotopy limit `K`.

Conversely, let `K` be right orthogonal to `smulInvertible J ϖ`, let `F` be a homotopy limit of
the tower `K ⊗ᴸ R/ϖⁿ`, and let `φ : K ⟶ F` be a map extending the reductions, obtained by
comparing `F` with the Milnor triangle of the constant tower `K`. Its cone `X` is right
orthogonal to `smulInvertible J ϖ`. Tensoring with `M = R/ϖ` turns the reduction tower into a
tower which is pro-isomorphic to the constant tower `K ⊗ᴸ M`, because `ϖ` acts by zero on
`K ⊗ᴸ M`; since `- ⊗ᴸ M` is triangulated and commutes with products, `φ ⊗ᴸ M` is then an
isomorphism (`CategoryTheory.Pretriangulated.isIso_of_proIso`), so `X ⊗ᴸ M = 0`, that is `ϖ`
acts invertibly on `X`. Hence `X = 0` and `φ` is an isomorphism, which says that `K` is the
homotopy limit of its reductions.

## Implementation notes

The preliminary constructions are in
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.SmulInvertible`,
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.QuotPowTriangle` and
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.TensorQuotPow`, which this module
imports.

The monoidal structure of `D(J, R)` and the instances attached to it are taken from the fields
of `DerivedCategory.sheafTensorStructure J R`, declared below as local instances of high
priority, as explained in the implementation notes of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`. The statements of the main
results do not involve the monoidal structure.

-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory Opposite Pretriangulated

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]

attribute [-instance] commShift₂CurriedTensor commShiftTensorLeft commShiftTensorRight
  isTriangulated_tensorLeft isTriangulated_tensorRight monoidalPreadditive monoidalLinear

noncomputable local instance (priority := high) :
    MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalCategory

noncomputable local instance (priority := high) :
    MonoidalPreadditive (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalPreadditive

noncomputable local instance (priority := high) :
    MonoidalLinear R (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalLinear

noncomputable local instance (priority := high) :
    (curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).CommShift₂Int :=
  (sheafTensorStructure J R).commShift₂

noncomputable local instance (priority := high)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ((curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).obj K).IsTriangulated :=
  (sheafTensorStructure J R).isTriangulated_tensorLeft K

noncomputable local instance (priority := high)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ((curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).flip.obj K).IsTriangulated :=
  (sheafTensorStructure J R).isTriangulated_tensorRight K

local instance : IsIso (sheafTensorStructure J R).ε := (sheafTensorStructure J R).isIso_ε

variable {J}

section Main

variable {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

set_option hygiene false in
/-- The functor `- ⊗ᴸ R/ϖ` on `D(J, R)`, where `R/ϖ = R/I` is the first reduction. -/
local notation "⊗ᴸR/ϖ" => (curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).flip.obj
  ((quotPowFunctor J I).obj (op 1))

include hϖ hI in
/-- The reductions `K ⊗ᴸ R/ϖⁿ ⊗ᴸ R/ϖ` form a tower which is pro-isomorphic to the constant tower
`K ⊗ᴸ R/ϖ`: the transition map from level `n + 1` to level `n` factors through `K ⊗ᴸ R/ϖ`,
compatibly with the reduction maps. -/
lemma exists_lift_whiskerRight_derivedCompletionCone
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) (n : ℕ) :
    ∃ b : (derivedCompletionDiagram J I K ⋙ ⊗ᴸR/ϖ).obj (op (n + 1)) ⟶
        ((Functor.const ℕᵒᵖ).obj K ⋙ ⊗ᴸR/ϖ).obj (op n),
      b ≫ (Functor.whiskerRight (derivedCompletionCone J I K).π ⊗ᴸR/ϖ).app (op n) =
          (derivedCompletionDiagram J I K ⋙ ⊗ᴸR/ϖ).map (homOfLE n.le_succ).op ∧
        (Functor.whiskerRight (derivedCompletionCone J I K).π ⊗ᴸR/ϖ).app (op (n + 1)) ≫ b =
          ((Functor.const ℕᵒᵖ).obj K ⋙ ⊗ᴸR/ϖ).map (homOfLE n.le_succ).op := by
  let c := derivedCompletionCone J I K
  let TM := (curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).flip.obj
    ((quotPowFunctor J I).obj (op 1))
  have h₁ := tensor_whisker_smul_eq_zero hI K
    (quotPowTriangle J hϖ hI (n + 1)).obj₁ 0
  rw [zero_add, pow_one] at h₁
  obtain ⟨b, hb₁, hb₂⟩ := exists_lift_of_mor₁_eq_zero
    (TM.map_distinguished _ (tensorQuotPowTriangle_distinguished hϖ hI K (n + 1)))
    (TM.map_distinguished _ (tensorQuotPowTriangle_distinguished hϖ hI K n))
    (by
      change TM.map (K ◁ (quotPowTriangle J hϖ hI (n + 1)).mor₁) = 0
      rw [quotPowTriangle_mor₁]
      exact tensor_whisker_smul_eq_zero hI K _ n)
    (TM.mapTriangle.map (tensorQuotPowTriangleTransition hϖ hI K n))
    (by
      change TM.map (K ◁ (quotPowTriangleMap J hϖ hI n).hom₁) = 0
      rw [quotPowTriangleMap_hom₁]
      exact h₁)
  refine ⟨b ≫ TM.map (unitIso K).inv, ?_, ?_⟩
  · change _ ≫ TM.map (c.π.app (op n)) = _
    rw [derivedCompletionCone_π_app hϖ hI, TM.map_comp, assoc, ← TM.map_comp_assoc,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, id_comp]
    exact hb₂
  · change TM.map (c.π.app (op (n + 1))) ≫ _ = _
    rw [derivedCompletionCone_π_app hϖ hI, TM.map_comp, assoc]
    erw [reassoc_of% hb₁]
    change TM.map _ ≫ TM.map (K ◁ (quotPowTriangleMap J hϖ hI n).hom₂) ≫ _ = _
    rw [quotPowTriangleMap_hom₂, MonoidalCategory.whiskerLeft_id,
      CategoryTheory.Functor.map_id, id_comp, ← TM.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id]
    simp
    rfl

include hϖ hI in
/-- Let `F ⟶ ∏ₙ K ⊗ᴸ R/ϖⁿ ──1 - t──▶ ∏ₙ K ⊗ᴸ R/ϖⁿ ⟶ F⟦1⟧` be a Milnor triangle, so that
`F = R lim_n (K ⊗ᴸ R/ϖⁿ)` is a derived completion of `K`. Then `F` is right orthogonal to the
objects on which `ϖ` acts invertibly, and there is a map `φ : K ⟶ F` extending the reductions
whose cone is an object on which `ϖ` acts invertibly.

The cone `X` of `φ` satisfies `X ⊗ᴸ R/ϖ = 0`: tensoring with `M = R/ϖ` turns the reduction tower
into a tower pro-isomorphic to the constant tower `K ⊗ᴸ M`, so that `φ ⊗ᴸ M` is an isomorphism
(`CategoryTheory.Pretriangulated.isIso_of_proIso`). -/
theorem rightOrthogonal_and_exists_smulInvertible_cone
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))
    {P : Fan fun n : ℕ ↦ (derivedCompletionDiagram J I K).obj (op n)} (hP : IsLimit P)
    {F : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))} {ι : F ⟶ P.pt} {ε : P.pt ⟶ F⟦(1 : ℤ)⟧}
    (hT : Triangle.mk ι (𝟙 P.pt - towerShift hP) ε ∈ distTriang _) :
    (smulInvertible J ϖ).rightOrthogonal F ∧ ∃ φ : K ⟶ F,
      Fan.IsLimit.lift hP (fun n ↦ (derivedCompletionCone J I K).π.app (op n)) = φ ≫ ι ∧
      ∀ (X : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) (g : F ⟶ X) (h : X ⟶ K⟦(1 : ℤ)⟧),
        Triangle.mk φ g h ∈ distTriang _ → smulInvertible J ϖ X := by
  have hϖI := mem_of_eq_span hI
  let G := derivedCompletionDiagram J I K
  let c := derivedCompletionCone J I K
  -- the Milnor triangle of the constant tower `K`
  let c₀ : Cone ((Functor.const ℕᵒᵖ).obj K) := { pt := K, π := 𝟙 _ }
  have : ∀ n, IsIso (c₀.π.app n) := fun n ↦ by dsimp [c₀]; infer_instance
  obtain ⟨PK, hPK, δK, hTK⟩ := IsHomotopyLimit.of_isIso_π c₀
  let m := productTowerMap (PF := PK) hP c.π
  obtain ⟨φ, hφ₁, hφ₃⟩ := complete_distinguished_triangle_morphism₁ _ _ hTK hT m m
    (productTowerMap_comp_sub_towerShift hPK hP c.π).symm
  replace hφ₁ : Fan.IsLimit.lift hPK (fun n ↦ c₀.π.app (op n)) ≫ m = φ ≫ ι := hφ₁
  replace hφ₃ : δK ≫ φ⟦(1 : ℤ)⟧' = m ≫ ε := hφ₃
  have hlift : Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)) =
      Fan.IsLimit.lift hPK (fun n ↦ c₀.π.app (op n)) ≫ m :=
    Fan.IsLimit.hom_ext hP _ _ fun n ↦ by simp [m, c₀]
  -- `F` is right orthogonal to `smulInvertible J ϖ`
  have hF : (smulInvertible J ϖ).rightOrthogonal F := by
    intro L f hL
    have h₀ : f ≫ ι = 0 := Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
      rw [zero_comp]
      exact hL.hom_eq_zero (smul_id_derivedCompletionDiagram_obj J hϖI K n) _
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₁ _ hT (f⟦(1 : ℤ)⟧')
      (by rw [Triangle.mk_mor₁, ← Functor.map_comp, h₀, Functor.map_zero])
    have : g = 0 := Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
      rw [zero_comp]
      exact (ObjectProperty.le_shift _ 1 L hL).hom_eq_zero
        (smul_id_derivedCompletionDiagram_obj J hϖI K n) _
    rw [this, zero_comp] at hg
    exact (shiftFunctor _ (1 : ℤ)).map_eq_zero_iff.mp hg
  refine ⟨hF, φ, hlift.trans hφ₁, fun X g h hX ↦ ?_⟩
  -- `ϖ` acts invertibly on `X`, through `X ⊗ᴸ R/ϖ = 0`
  let M := (quotPowFunctor J I).obj (op 1)
  let TM := (curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).flip.obj M
  let F' : ℕᵒᵖ ⥤ _ := (Functor.const ℕᵒᵖ).obj K ⋙ TM
  let G' : ℕᵒᵖ ⥤ _ := G ⋙ TM
  let PM : Fan fun n : ℕ ↦ G'.obj (op n) := Fan.mk (P.pt ⊗ M) fun j ↦ P.proj j ▷ M
  have hPM : IsLimit PM := isLimit_fan_whiskerRight_quot hϖ hI hP
  let PKM : Fan fun n : ℕ ↦ F'.obj (op n) := Fan.mk (PK.pt ⊗ M) fun j ↦ PK.proj j ▷ M
  have hPKM : IsLimit PKM := isLimit_fan_whiskerRight_quot hϖ hI hPK
  have htK : TM.map (towerShift hPK) = towerShift hPKM :=
    Fan.IsLimit.hom_ext hPKM _ _ fun n ↦ by
      change TM.map _ ≫ TM.map _ = _
      rw [towerShift_proj, ← TM.map_comp, towerShift_proj, TM.map_comp]
      rfl
  have ht : TM.map (towerShift hP) = towerShift hPM :=
    Fan.IsLimit.hom_ext hPM _ _ fun n ↦ by
      change TM.map _ ≫ TM.map _ = _
      rw [towerShift_proj, ← TM.map_comp, towerShift_proj, TM.map_comp]
      rfl
  have hTKM : Triangle.mk (TM.map (Fan.IsLimit.lift hPK fun n ↦ c₀.π.app (op n)))
      (𝟙 _ - towerShift hPKM) (TM.map δK ≫ (TM.commShiftIso (1 : ℤ)).hom.app K) ∈
        distTriang _ :=
    isomorphic_distinguished _ (TM.map_distinguished _ hTK) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
        (by
          simp only [Triangle.mk_mor₂, Iso.refl_hom, comp_id, id_comp]
          change _ = TM.map (𝟙 PK.pt - towerShift hPK)
          rw [Functor.map_sub, CategoryTheory.Functor.map_id, htK]
          rfl)
        (by simp; rfl))
  have hTFM : Triangle.mk (TM.map ι) (𝟙 _ - towerShift hPM)
      (TM.map ε ≫ (TM.commShiftIso (1 : ℤ)).hom.app F) ∈ distTriang _ :=
    isomorphic_distinguished _ (TM.map_distinguished _ hT) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
        (by
          simp only [Triangle.mk_mor₂, Iso.refl_hom, comp_id, id_comp]
          change _ = TM.map (𝟙 P.pt - towerShift hP)
          rw [Functor.map_sub, CategoryTheory.Functor.map_id, ht]
          rfl)
        (by simp))
  let a : F' ⟶ G' := Functor.whiskerRight c.π TM
  have hb := exists_lift_whiskerRight_derivedCompletionCone hϖ hI K
  choose b hb₁ hb₂ using hb
  have hm : productTowerMap (PF := PKM) hPM a = TM.map m :=
    Fan.IsLimit.hom_ext hPM _ _ fun n ↦ by
      rw [productTowerMap_proj]
      change _ = TM.map _ ≫ TM.map _
      rw [← TM.map_comp, productTowerMap_proj, TM.map_comp]
      rfl
  have hφM : IsIso (TM.map φ) := isIso_of_proIso hPKM hPM hTKM hTFM a b hb₁ hb₂ (TM.map φ)
    (by rw [hm]; dsimp; rw [← TM.map_comp, ← TM.map_comp, hφ₁])
    (by
      rw [hm, assoc, ← TM.commShiftIso_hom_naturality, ← TM.map_comp_assoc, hφ₃,
        TM.map_comp_assoc])
  have hXM : IsZero (X ⊗ M) :=
    (Triangle.isZero₃_iff_isIso₁ _ (TM.map_distinguished _ hX)).2 hφM
  have h₁ := (Triangle.isZero₃_iff_isIso₁ _ (tensorQuotPowTriangle_distinguished hϖ hI X 1)).1 hXM
  change IsIso (X ◁ (quotPowTriangle J hϖ hI 1).mor₁) at h₁
  rw [quotPowTriangle_mor₁, pow_one, MonoidalLinear.whiskerLeft_smul,
    MonoidalCategory.whiskerLeft_id] at h₁
  change IsIso (ϖ • 𝟙 X)
  have : ϖ • 𝟙 X = (unitIso X).hom ≫ (ϖ • 𝟙 _) ≫ (unitIso X).inv := by
    rw [Linear.smul_comp, id_comp, Linear.comp_smul, Iso.hom_inv_id]
  have h₂ : IsIso (ϖ • 𝟙 (X ⊗ (singleFunctor (Sheaf J (ModuleCat.{u + 1} R)) 0).obj
      (𝟙_ (Sheaf J (ModuleCat.{u + 1} R))))) := h₁
  rw [this]
  infer_instance

include hϖ hI in
/-- The derived completion `R lim_n (K ⊗ᴸ R/ϖⁿ)` of an object `K`, given by a homotopy limit cone
`c` of its reductions, is right orthogonal to the objects on which `ϖ` acts invertibly, and there
is a map `φ : K ⟶ c.pt` compatible with the reduction maps whose cone is an object on which `ϖ`
acts invertibly. -/
theorem rightOrthogonal_and_exists_smulInvertible_cone_of_isHomotopyLimit
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))
    {c : Cone (derivedCompletionDiagram J I K)} (hc : IsHomotopyLimit c) :
    (smulInvertible J ϖ).rightOrthogonal c.pt ∧ ∃ φ : K ⟶ c.pt,
      ∀ (X : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) (g : c.pt ⟶ X)
        (h : X ⟶ K⟦(1 : ℤ)⟧), Triangle.mk φ g h ∈ distTriang _ → smulInvertible J ϖ X := by
  obtain ⟨P, hP, δ, hT⟩ := hc
  obtain ⟨hF, φ, -, hφ⟩ := rightOrthogonal_and_exists_smulInvertible_cone hϖ hI K hP hT
  exact ⟨hF, φ, hφ⟩

include hϖ hI in
/-- An object which is right orthogonal to the objects on which `ϖ` acts invertibly is derived
complete for `I = (ϖ)`. -/
theorem derivedComplete_of_rightOrthogonal {K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (hK : (smulInvertible J ϖ).rightOrthogonal K) : derivedComplete J I K := by
  let G := derivedCompletionDiagram J I K
  let P : Fan fun n : ℕ ↦ G.obj (op n) := Fan.mk _ (Pi.π _)
  have hP : IsLimit P := productIsProduct _
  obtain ⟨F, ι, ε, hT⟩ := distinguished_cocone_triangle₁ (𝟙 P.pt - towerShift hP)
  obtain ⟨hF, φ, hφ₁, hφX⟩ := rightOrthogonal_and_exists_smulInvertible_cone hϖ hI K hP hT
  -- the cone `X` of `φ` is right orthogonal to `smulInvertible J ϖ`, and `ϖ` acts invertibly on it
  obtain ⟨X, g, h, hX⟩ := distinguished_cocone_triangle φ
  have hXorth : (smulInvertible J ϖ).rightOrthogonal X := by
    intro L f hL
    have hK1 : (smulInvertible J ϖ).rightOrthogonal (K⟦(1 : ℤ)⟧) :=
      ObjectProperty.le_shift _ 1 K hK
    obtain ⟨f', hf'⟩ := Triangle.coyoneda_exact₃ _ hX f (hK1 _ hL)
    rw [hf', hF f' hL, zero_comp]
  have hXzero : IsZero X := by
    rw [IsZero.iff_id_eq_zero]
    exact hXorth (𝟙 X) (hφX X g h hX)
  have : IsIso φ := (Triangle.isZero₃_iff_isIso₁ _ hX).1 hXzero
  refine ⟨_, hP, ε ≫ (inv φ)⟦(1 : ℤ)⟧', isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (asIso φ) (Iso.refl _) (Iso.refl _) ?_ (by simp) ?_)⟩
  · change Fan.IsLimit.lift hP (fun n ↦ (derivedCompletionCone J I K).π.app (op n)) ≫ 𝟙 _ =
      φ ≫ ι
    rw [comp_id, hφ₁]
  · change (ε ≫ (inv φ)⟦(1 : ℤ)⟧') ≫ φ⟦(1 : ℤ)⟧' = 𝟙 _ ≫ ε
    rw [assoc, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, comp_id,
      id_comp]

include hϖ hI in
/-- For `I = (ϖ)` with `ϖ` a nonzerodivisor, an object of `D(J, R)` is derived complete if and
only if it receives no nonzero map from an object on which `ϖ` acts invertibly: this is the
characterisation `RHom(R[1/ϖ], K) = 0` of derived completeness (Stacks, Tags 091Q and 0999). -/
theorem derivedComplete_iff_rightOrthogonal
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    derivedComplete J I K ↔ (smulInvertible J ϖ).rightOrthogonal K :=
  ⟨rightOrthogonal_of_derivedComplete (mem_of_eq_span hI),
    derivedComplete_of_rightOrthogonal hϖ hI⟩

include hϖ hI in
lemma derivedComplete_eq_rightOrthogonal :
    derivedComplete J I = (smulInvertible J ϖ).rightOrthogonal :=
  funext fun K ↦ propext (derivedComplete_iff_rightOrthogonal hϖ hI K)

include hϖ hI in
/-- For `I = (ϖ)` with `ϖ` a nonzerodivisor, the derived complete objects of `D(J, R)` form a
triangulated subcategory. -/
lemma isTriangulated_derivedComplete : (derivedComplete J I).IsTriangulated := by
  rw [derivedComplete_eq_rightOrthogonal hϖ hI]
  infer_instance

/-- Every object is derived complete for the zero ideal: the tower `K ⊗ᴸ R/0ⁿ` is constant
from `n = 1` on, with the reduction maps isomorphisms there, so `K` is its homotopy limit
(`Pretriangulated.IsHomotopyLimit.of_isIso_π_succ`). -/
lemma derivedComplete_bot (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    derivedComplete J (⊥ : Ideal R) K := by
  have h (n : ℕ) : IsIso ((Ideal.quotPowCone (⊥ : Ideal R)).π.app (op (n + 1))) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun x y hxy ↦ ?_, Submodule.mkQ_surjective _⟩
    have : (⊥ : Ideal R) ^ (n + 1) = ⊥ := by simp
    change Submodule.mkQ _ x = Submodule.mkQ _ y at hxy
    rwa [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, this,
      Submodule.mem_bot, sub_eq_zero] at hxy
  have (n : ℕ) : IsIso ((derivedCompletionCone J ⊥ K).π.app (op (n + 1))) := by
    dsimp [derivedCompletionCone, quotPowCone, Sheaf.quotPowCone]
    infer_instance
  exact IsHomotopyLimit.of_isIso_π_succ _

end Main

end DerivedCategory
