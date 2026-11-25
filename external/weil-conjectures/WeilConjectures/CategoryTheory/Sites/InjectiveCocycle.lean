/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Ext

/-!
# One-cocycles of injective presheaves on a representable cover

Let `P` be an injective presheaf of abelian groups on a category `C` and `X` an object of `C`.
A family `c Z g₁ g₂ ∈ P(Z)`, indexed by pairs of morphisms `g₁ g₂ : Z ⟶ X`, which is natural in
`Z` and satisfies the cocycle identity `c g₁ g₂ + c g₂ g₃ = c g₁ g₃`, is a coboundary: there is
`w ∈ P(X)` with `c Z g₁ g₂ = P(g₁) w - P(g₂) w`.

The proof uses the free abelian presheaf `F(Z) = ℤ[Z ⟶ X]` and its sub-presheaf `N` of
coefficient sum zero: the cocycle defines a morphism `N ⟶ P`, which extends to `F` by
injectivity of `P`, and `w` is the image of `[𝟙 X]`.
-/

@[expose] public section

universe v w

open CategoryTheory Opposite

namespace CategoryTheory.Presheaf

variable {C : Type w} [Category.{v} C] (X : C)

namespace InjectiveCocycle

/-- The free abelian presheaf `Z ↦ ℤ[Z ⟶ X]` on the representable presheaf of `X`. -/
noncomputable def free : Cᵒᵖ ⥤ AddCommGrpCat.{max w v} where
  obj Z := AddCommGrpCat.of (ULift.{w} (Z.unop ⟶ X) →₀ ℤ)
  map {Z Z'} h := AddCommGrpCat.ofHom
    (Finsupp.mapDomain.addMonoidHom fun g ↦ ULift.up (h.unop ≫ g.down))
  map_id Z := by
    refine AddCommGrpCat.ext fun x ↦ ?_
    change Finsupp.mapDomain _ x = x
    convert Finsupp.mapDomain_id (v := x) using 2
    simp
  map_comp {Z Z' Z''} h h' := by
    refine AddCommGrpCat.ext fun x ↦ ?_
    change Finsupp.mapDomain _ x = Finsupp.mapDomain _ (Finsupp.mapDomain _ x)
    rw [← Finsupp.mapDomain_comp]
    congr 1
    funext g
    simp

/-- The augmentation `ℤ[Z ⟶ X] → ℤ`, sum of the coefficients. -/
noncomputable def aug (Z : C) : (ULift.{w} (Z ⟶ X) →₀ ℤ) →+ ℤ :=
  Finsupp.liftAddHom fun _ ↦ AddMonoidHom.id ℤ

lemma aug_mapDomain {Z Z' : C} (h : Z' ⟶ Z) (x : ULift.{w} (Z ⟶ X) →₀ ℤ) :
    aug X Z' (Finsupp.mapDomain (fun g ↦ ULift.up (h ≫ g.down)) x) = aug X Z x := by
  change ((aug X Z').comp (Finsupp.mapDomain.addMonoidHom _)) x = _
  congr 1
  refine Finsupp.addHom_ext fun g n ↦ ?_
  simp [aug, Finsupp.mapDomain.addMonoidHom]

/-- The sub-presheaf of `free X` of elements with coefficient sum zero. -/
noncomputable def augKer : Cᵒᵖ ⥤ AddCommGrpCat.{max w v} where
  obj Z := AddCommGrpCat.of (aug X Z.unop).ker
  map {Z Z'} h := AddCommGrpCat.ofHom
    (((Finsupp.mapDomain.addMonoidHom fun g ↦ ULift.up (h.unop ≫ g.down)).comp
      (aug X Z.unop).ker.subtype).codRestrict _ fun x ↦ by
        change aug X Z'.unop (Finsupp.mapDomain _ x.1) = 0
        rw [aug_mapDomain]
        exact x.2)
  map_id Z := by
    refine AddCommGrpCat.ext fun x ↦ Subtype.ext ?_
    change Finsupp.mapDomain _ x.1 = x.1
    convert Finsupp.mapDomain_id (v := x.1) using 2
    simp
  map_comp {Z Z' Z''} h h' := by
    refine AddCommGrpCat.ext fun x ↦ Subtype.ext ?_
    change Finsupp.mapDomain _ x.1 = Finsupp.mapDomain _ (Finsupp.mapDomain _ x.1)
    rw [← Finsupp.mapDomain_comp]
    congr 1
    funext g
    simp

/-- The inclusion of `augKer X` into `free X`. -/
noncomputable def augKerι : augKer X ⟶ free X where
  app Z := AddCommGrpCat.ofHom (aug X Z.unop).ker.subtype
  naturality _ _ _ := rfl

instance : Mono (augKerι X) := by
  have (Z : Cᵒᵖ) : Mono ((augKerι X).app Z) :=
    (AddCommGrpCat.mono_iff_injective _).2 Subtype.val_injective
  exact NatTrans.mono_of_mono_app _

variable {X} {P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}}
  (c : ∀ Z : C, (Z ⟶ X) → (Z ⟶ X) → P.obj (op Z))

/-- The morphism `ℤ[Z ⟶ X] → P(Z)`, `[g] ↦ c g g₀`. -/
noncomputable def σ {Z : C} (g₀ : Z ⟶ X) : (ULift.{w} (Z ⟶ X) →₀ ℤ) →+ P.obj (op Z) :=
  Finsupp.liftAddHom fun g ↦ zmultiplesHom _ (c Z g.down g₀)

@[simp]
lemma σ_single {Z : C} (g₀ : Z ⟶ X) (g : ULift.{w} (Z ⟶ X)) (n : ℤ) :
    σ c g₀ (Finsupp.single g n) = n • c Z g.down g₀ := by
  simp [σ]

lemma σ_sub (hcoc : ∀ (Z : C) (g₁ g₂ g₃ : Z ⟶ X), c Z g₁ g₂ + c Z g₂ g₃ = c Z g₁ g₃)
    {Z : C} (g₀ g₁ : Z ⟶ X) (x : ULift.{w} (Z ⟶ X) →₀ ℤ) :
    σ c g₁ x - σ c g₀ x = aug X Z x • c Z g₀ g₁ := by
  change (σ c g₁ - σ c g₀) x = ((zmultiplesHom _ (c Z g₀ g₁)).comp (aug X Z)) x
  congr 1
  refine Finsupp.addHom_ext fun g n ↦ ?_
  simp only [AddMonoidHom.sub_apply, σ_single, AddMonoidHom.comp_apply, aug,
    Finsupp.liftAddHom_apply_single, AddMonoidHom.id_apply, zmultiplesHom_apply, ← smul_sub]
  rw [← hcoc Z g.down g₀ g₁]
  simp

open Classical in
/-- The morphism `N(Z) → P(Z)` induced by the cocycle `c`. -/
noncomputable def ψApp (Z : C) : (aug X Z).ker →+ P.obj (op Z) :=
  if h : Nonempty (Z ⟶ X) then (σ c h.some).comp (aug X Z).ker.subtype else 0

lemma ψApp_apply (hcoc : ∀ (Z : C) (g₁ g₂ g₃ : Z ⟶ X), c Z g₁ g₂ + c Z g₂ g₃ = c Z g₁ g₃)
    {Z : C} (g₀ : Z ⟶ X) (x : (aug X Z).ker) : ψApp c Z x = σ c g₀ x.1 := by
  have h : Nonempty (Z ⟶ X) := ⟨g₀⟩
  rw [ψApp, dite_eq_left h, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, ← sub_eq_zero,
    σ_sub c hcoc, x.2, zero_smul]

/-- The morphism of presheaves `augKer X ⟶ P` induced by the cocycle `c`. -/
noncomputable def ψ (hnat : ∀ {Z Z' : C} (h : Z' ⟶ Z) (g₁ g₂ : Z ⟶ X),
      P.map h.op (c Z g₁ g₂) = c Z' (h ≫ g₁) (h ≫ g₂))
    (hcoc : ∀ (Z : C) (g₁ g₂ g₃ : Z ⟶ X), c Z g₁ g₂ + c Z g₂ g₃ = c Z g₁ g₃) :
    augKer X ⟶ P where
  app Z := AddCommGrpCat.ofHom (ψApp c Z.unop)
  naturality {Z Z'} h := by
    refine AddCommGrpCat.ext fun x ↦ ?_
    change ψApp c Z'.unop _ = P.map h (ψApp c Z.unop x)
    by_cases hZ : Nonempty (Z.unop ⟶ X)
    · obtain ⟨g₀⟩ := hZ
      rw [ψApp_apply c hcoc g₀, ψApp_apply c hcoc (h.unop ≫ g₀)]
      change σ c _ (Finsupp.mapDomain.addMonoidHom _ x.1) = _
      rw [← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply
        (AddCommGrpCat.Hom.hom (P.map h))]
      congr 1
      refine Finsupp.addHom_ext fun g n ↦ ?_
      simp only [AddMonoidHom.comp_apply, Finsupp.mapDomain.addMonoidHom_apply,
        Finsupp.mapDomain_single]
      rw [σ_single, σ_single, map_zsmul]
      congr 1
      exact (hnat h.unop g.down g₀).symm
    · have hx : x = 0 := Subtype.ext (Finsupp.ext fun a ↦ (hZ ⟨a.down⟩).elim)
      simp [hx]

end InjectiveCocycle

open InjectiveCocycle in
/-- The first Čech cohomology of an injective presheaf of abelian groups with respect to the
representable "cover" `X` vanishes: a family `c Z g₁ g₂ ∈ P(Z)` indexed by pairs of morphisms
`g₁ g₂ : Z ⟶ X`, natural in `Z` and satisfying the cocycle identity, is the coboundary of some
`w ∈ P(X)`. (blueprint: `lem-sc-cech-spectral`, injective case in degree one) -/
theorem exists_eq_sub_of_injective {C : Type w} [Category.{v} C] (X : C)
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}) [Injective P]
    (c : ∀ Z : C, (Z ⟶ X) → (Z ⟶ X) → P.obj (Opposite.op Z))
    (hnat : ∀ {Z Z' : C} (h : Z' ⟶ Z) (g₁ g₂ : Z ⟶ X),
      P.map h.op (c Z g₁ g₂) = c Z' (h ≫ g₁) (h ≫ g₂))
    (hcoc : ∀ (Z : C) (g₁ g₂ g₃ : Z ⟶ X), c Z g₁ g₂ + c Z g₂ g₃ = c Z g₁ g₃) :
    ∃ w : P.obj (Opposite.op X), ∀ (Z : C) (g₁ g₂ : Z ⟶ X),
      c Z g₁ g₂ = P.map g₁.op w - P.map g₂.op w := by
  set φ := Injective.factorThru (ψ c hnat hcoc) (augKerι X)
  have hφ := Injective.comp_factorThru (ψ c hnat hcoc) (augKerι X)
  refine ⟨φ.app (op X) (Finsupp.single (ULift.up (𝟙 X)) 1), fun Z g₁ g₂ ↦ ?_⟩
  have hsingle (g : Z ⟶ X) : φ.app (op Z) (Finsupp.single (ULift.up g) 1) =
      P.map g.op (φ.app (op X) (Finsupp.single (ULift.up (𝟙 X)) 1)) := by
    rw [← ConcreteCategory.comp_apply, ← φ.naturality, ConcreteCategory.comp_apply]
    congr 1
    change _ = Finsupp.mapDomain _ _
    rw [Finsupp.mapDomain_single]
    simp
  have hcc : c Z g₂ g₂ = 0 := by
    have := hcoc Z g₂ g₂ g₂
    rwa [add_eq_right] at this
  let x : (aug X Z).ker := ⟨Finsupp.single (ULift.up g₁) 1 - Finsupp.single (ULift.up g₂) 1,
    by rw [AddMonoidHom.mem_ker, map_sub]; simp [aug]⟩
  have h1 : ψApp c Z x = c Z g₁ g₂ := by
    rw [ψApp_apply c hcoc g₂]
    simp [x, hcc]
  have h2 := congr($(hφ).app (op Z) x)
  change φ.app (op Z) x.1 = ψApp c Z x at h2
  rw [← hsingle, ← hsingle, ← map_sub, ← h1]
  exact h2.symm

end CategoryTheory.Presheaf
