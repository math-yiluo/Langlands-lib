/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import WeilConjectures.CategoryTheory.Preadditive.TraceSplitting

/-!
# The trace of a Galois covering of a site

Let `C` be a site, `B : C ⥤ C` a functor with a natural transformation `ε : B ⟶ 𝟭 C`, and
`σ : Γ → (B ⟶ B)` an action of a finite group `Γ` by endomorphisms over `ε`. In the application
`C` is the pro-étale site of a scheme `X`, `B V = V ×_X Y` for a finite étale Galois covering
`g : Y ⟶ X` with group `Γ`, `ε` the projection and `σ` the action of `Γ` on `Y`; then for a sheaf
`H` the presheaf `B.op ⋙ H` is `g_* g^* H` and `ε` induces the unit `H ⟶ g_* g^* H`.

Assume each `ε_V` is a covering (the covering is surjective) and that it is *Galois*: two maps
`a b : T ⟶ B V` with `a ≫ ε = b ≫ ε` agree, locally on `T`, up to one of the `σ i`. Then
`H ⟶ B.op ⋙ H` is the inclusion of the `Γ`-invariants (`CategoryTheory.Presheaf.baseChangeDescend`,
descent for a Galois covering), and the norm `∑ i, σ i` factors through it. This factorization is
the *trace* `t : B.op ⋙ H ⟶ H` (`CategoryTheory.Presheaf.baseChangeTrace`); it satisfies

* `u ≫ t = |Γ| • 𝟙` (`CategoryTheory.Presheaf.baseChangeUnit_comp_baseChangeTrace`),
* `t ≫ u = ∑ i, σ i` (`CategoryTheory.Presheaf.baseChangeTrace_comp_baseChangeUnit`),

so `u` is split by the normalized trace when `|Γ|` is invertible on `H`, with idempotent the
average of the action (`CategoryTheory.nsmul_normalizedTrace_comp_eq_sum`). The trace is natural
in `H` (`CategoryTheory.Presheaf.baseChangeTrace_naturality`).
-/

@[expose] public section

universe w v u

open CategoryTheory Category Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] {B : C ⥤ C} (ε : B ⟶ 𝟭 C)

/-- The *unit* `H ⟶ B.op ⋙ H`, restriction along `ε_V : B V ⟶ V`. -/
@[simps]
def baseChangeUnit (H : Cᵒᵖ ⥤ AddCommGrpCat.{w}) : H ⟶ B.op ⋙ H where
  app V := H.map (ε.app V.unop).op
  naturality V W f := by
    simp only [Functor.comp_obj, Functor.op_obj, Functor.comp_map, Functor.op_map, ← H.map_comp]
    congr 1
    exact Quiver.Hom.unop_inj (ε.naturality f.unop).symm

/-- The *action* of an endomorphism `σ : B ⟶ B` on `B.op ⋙ H`, restriction along `σ_V`. -/
@[simps]
def baseChangeAction (σ : B ⟶ B) (H : Cᵒᵖ ⥤ AddCommGrpCat.{w}) : B.op ⋙ H ⟶ B.op ⋙ H where
  app V := H.map (σ.app V.unop).op
  naturality V W f := by
    simp only [Functor.comp_obj, Functor.op_obj, Functor.comp_map, Functor.op_map, ← H.map_comp]
    congr 1
    exact Quiver.Hom.unop_inj (σ.naturality f.unop).symm

variable {ε}

@[reassoc (attr := simp)]
lemma baseChangeUnit_comp_baseChangeAction {σ : B ⟶ B} (hσ : σ ≫ ε = ε)
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    baseChangeUnit ε H ≫ baseChangeAction σ H = baseChangeUnit ε H := by
  ext V : 2
  simp only [NatTrans.comp_app, baseChangeUnit_app, baseChangeAction_app, ← H.map_comp,
    ← op_comp]
  rw [← NatTrans.comp_app, hσ]

@[reassoc]
lemma baseChangeAction_comp (σ τ : B ⟶ B) (H : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    baseChangeAction σ H ≫ baseChangeAction τ H = baseChangeAction (τ ≫ σ) H := by
  ext V : 2
  simp [← H.map_comp, ← op_comp]

@[reassoc]
lemma baseChangeAction_naturality (σ : B ⟶ B) {H H' : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (φ : H ⟶ H') :
    baseChangeAction σ H ≫ Functor.whiskerLeft B.op φ =
      Functor.whiskerLeft B.op φ ≫ baseChangeAction σ H' := by
  ext V : 2
  simp [φ.naturality]

@[reassoc]
lemma baseChangeUnit_naturality {H H' : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (φ : H ⟶ H') :
    φ ≫ baseChangeUnit ε H' = baseChangeUnit ε H ≫ Functor.whiskerLeft B.op φ := by
  ext V : 2
  simp [φ.naturality]

section Descent

variable (J : GrothendieckTopology C) {Γ : Type*} (σ : Γ → (B ⟶ B))
  (hcov : ∀ V, Sieve.generate (Presieve.singleton (ε.app V)) ∈ J V)
  (hgal : ∀ (V T : C) (a b : T ⟶ B.obj V), a ≫ ε.app V = b ≫ ε.app V →
    ∃ S ∈ J T, ∀ ⦃Z : C⦄ (c : Z ⟶ T), S c → ∃ i, c ≫ b = c ≫ a ≫ (σ i).app V)
  {H : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (hH : Presieve.IsSheaf J (H ⋙ forget AddCommGrpCat))

include hcov hH in
/-- The restriction `H(V) ⟶ H(B V)` is injective. -/
lemma injective_map_app (V : C) : Function.Injective (H.map (ε.app V).op) :=
  (Presieve.isSeparatedFor_singleton (P := H ⋙ forget AddCommGrpCat)).1
    ((Presieve.isSheafFor_iff_generate _).2 (hH _ (hcov V))).isSeparatedFor

include hcov hH in
/-- The unit `H ⟶ B.op ⋙ H` is a monomorphism. -/
lemma mono_baseChangeUnit : Mono (baseChangeUnit ε H) := by
  have : ∀ V, Mono ((baseChangeUnit ε H).app V) := fun V ↦ by
    rw [AddCommGrpCat.mono_iff_injective]
    exact injective_map_app J hcov hH V.unop
  exact NatTrans.mono_of_mono_app _

include hcov hgal hH in
/-- **Descent for a Galois covering**: a section of `H` over `B V` fixed by all `σ i` comes from a
section over `V`. -/
lemma existsUnique_map_app_eq (V : C) (y : H.obj (op (B.obj V)))
    (hy : ∀ i, H.map ((σ i).app V).op y = y) : ∃! x, H.map (ε.app V).op x = y := by
  refine (Presieve.isSheafFor_singleton (P := H ⋙ forget AddCommGrpCat)).1
    ((Presieve.isSheafFor_iff_generate _).2 (hH _ (hcov V))) y fun {Z} p₁ p₂ h ↦ ?_
  obtain ⟨S, hS, hc⟩ := hgal V Z p₁ p₂ h
  refine (hH S hS).isSeparatedFor.ext fun W c hc' ↦ ?_
  obtain ⟨i, hi⟩ := hc c hc'
  change H.map c.op (H.map p₁.op y) = H.map c.op (H.map p₂.op y)
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← H.map_comp, ← H.map_comp,
    ← op_comp, ← op_comp, hi, ← assoc]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hy]

variable {K : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (f : K ⟶ B.op ⋙ H)
  (hf : ∀ i, f ≫ baseChangeAction (σ i) H = f)

include hf in
lemma map_app_apply_eq (V : Cᵒᵖ) (x : K.obj V) (i : Γ) :
    H.map ((σ i).app V.unop).op (f.app V x) = f.app V x := by
  conv_rhs => rw [← hf i]
  rfl

/-- **Descent for a Galois covering**: a morphism `f : K ⟶ B.op ⋙ H` invariant under the `σ i`
factors through the unit (`CategoryTheory.Presheaf.baseChangeDescend_comp`). -/
noncomputable def baseChangeDescend : K ⟶ H where
  app V := AddCommGrpCat.ofHom
    { toFun x := (existsUnique_map_app_eq J σ hcov hgal hH V.unop (f.app V x)
        (map_app_apply_eq σ f hf V x)).exists.choose
      map_zero' := by
        apply injective_map_app J hcov hH V.unop
        rw [(existsUnique_map_app_eq J σ hcov hgal hH V.unop (f.app V 0)
          (map_app_apply_eq σ f hf V 0)).exists.choose_spec, map_zero, map_zero]
      map_add' x y := by
        apply injective_map_app J hcov hH V.unop
        rw [(existsUnique_map_app_eq J σ hcov hgal hH V.unop (f.app V (x + y))
          (map_app_apply_eq σ f hf V (x + y))).exists.choose_spec, map_add, map_add,
          (existsUnique_map_app_eq J σ hcov hgal hH V.unop (f.app V x)
            (map_app_apply_eq σ f hf V x)).exists.choose_spec,
          (existsUnique_map_app_eq J σ hcov hgal hH V.unop (f.app V y)
            (map_app_apply_eq σ f hf V y)).exists.choose_spec] }
  naturality V W g := by
    ext x
    apply injective_map_app J hcov hH W.unop
    simp only [ConcreteCategory.comp_apply, AddCommGrpCat.hom_ofHom, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk]
    rw [(existsUnique_map_app_eq J σ hcov hgal hH W.unop (f.app W (K.map g x))
      (map_app_apply_eq σ f hf W _)).exists.choose_spec]
    have e₁ := ConcreteCategory.congr_hom (show H.map g ≫ H.map (ε.app W.unop).op =
        H.map (ε.app V.unop).op ≫ H.map (B.map g.unop).op by
      rw [← H.map_comp, ← H.map_comp]
      exact congrArg H.map (Quiver.Hom.unop_inj (ε.naturality g.unop).symm))
      (existsUnique_map_app_eq J σ hcov hgal hH V.unop (f.app V x)
        (map_app_apply_eq σ f hf V x)).exists.choose
    simp only [ConcreteCategory.comp_apply] at e₁
    erw [e₁,       (existsUnique_map_app_eq J σ hcov hgal hH V.unop (f.app V x)
        (map_app_apply_eq σ f hf V x)).exists.choose_spec]
    have e₂ := ConcreteCategory.congr_hom (f.naturality g) x
    simp only [ConcreteCategory.comp_apply] at e₂
    exact e₂

@[reassoc (attr := simp)]
lemma baseChangeDescend_comp :
    baseChangeDescend J σ hcov hgal hH f hf ≫ baseChangeUnit ε H = f := by
  ext V x
  exact (existsUnique_map_app_eq J σ hcov hgal hH V.unop (f.app V x)
    (map_app_apply_eq σ f hf V x)).exists.choose_spec

end Descent

section Trace

variable (J : GrothendieckTopology C) {Γ : Type*} [Group Γ] [Fintype Γ] (σ : Γ → (B ⟶ B))
  (hσ : ∀ a b, σ a ≫ σ b = σ (a * b))
  (hcov : ∀ V, Sieve.generate (Presieve.singleton (ε.app V)) ∈ J V)
  (hgal : ∀ (V T : C) (a b : T ⟶ B.obj V), a ≫ ε.app V = b ≫ ε.app V →
    ∃ S ∈ J T, ∀ ⦃Z : C⦄ (c : Z ⟶ T), S c → ∃ i, c ≫ b = c ≫ a ≫ (σ i).app V)
  {H : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (hH : Presieve.IsSheaf J (H ⋙ forget AddCommGrpCat))

include hσ in
lemma sum_baseChangeAction_comp (H : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (b : Γ) :
    (∑ a, baseChangeAction (σ a) H) ≫ baseChangeAction (σ b) H = ∑ a, baseChangeAction (σ a) H := by
  rw [Preadditive.sum_comp]
  simp_rw [baseChangeAction_comp, hσ]
  exact Fintype.sum_equiv (Equiv.mulLeft b) _ _ fun _ ↦ rfl

/-- The *trace* `B.op ⋙ H ⟶ H` of a Galois covering: the factorization of the norm
`∑ a, σ a` through the unit. -/
noncomputable def baseChangeTrace : B.op ⋙ H ⟶ H :=
  baseChangeDescend J σ hcov hgal hH (∑ a, baseChangeAction (σ a) H)
    (sum_baseChangeAction_comp σ hσ H)

/-- The trace followed by the unit is the norm `∑ a, σ a`. -/
@[reassoc (attr := simp)]
lemma baseChangeTrace_comp_baseChangeUnit :
    baseChangeTrace J σ hσ hcov hgal hH ≫ baseChangeUnit ε H = ∑ a, baseChangeAction (σ a) H :=
  baseChangeDescend_comp ..

/-- The unit followed by the trace is multiplication by the order of `Γ`. -/
lemma baseChangeUnit_comp_baseChangeTrace (hσε : ∀ a, σ a ≫ ε = ε) :
    baseChangeUnit ε H ≫ baseChangeTrace J σ hσ hcov hgal hH = Fintype.card Γ • 𝟙 H := by
  have := mono_baseChangeUnit J hcov hH
  exact comp_eq_nsmul_of_comp_eq_sum _ (fun a ↦ baseChangeUnit_comp_baseChangeAction (hσε a) H)
    (baseChangeTrace_comp_baseChangeUnit J σ hσ hcov hgal hH)

/-- The trace is natural in the sheaf `H`. -/
lemma baseChangeTrace_naturality {H' : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    (hH' : Presieve.IsSheaf J (H' ⋙ forget AddCommGrpCat)) (φ : H ⟶ H') :
    Functor.whiskerLeft B.op φ ≫ baseChangeTrace J σ hσ hcov hgal hH' =
      baseChangeTrace J σ hσ hcov hgal hH ≫ φ := by
  have := mono_baseChangeUnit J hcov hH'
  rw [← cancel_mono (baseChangeUnit ε H'), assoc, baseChangeTrace_comp_baseChangeUnit, assoc,
    baseChangeUnit_naturality, baseChangeTrace_comp_baseChangeUnit_assoc, Preadditive.comp_sum,
    Preadditive.sum_comp]
  simp_rw [baseChangeAction_naturality]

end Trace

end CategoryTheory.Presheaf
