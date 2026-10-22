import Langlands.Shimura.Coefficients.Associated
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Associated-sheaf trivialization from splitting of graph restrictions -/

noncomputable section

universe u v w

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type w} [Category.{v} C] [HasBinaryProducts C]
variable (J : GrothendieckTopology C)
variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] (Y : Action C G)

local instance : HasLimitsOfShape (SingleObj G) (ModuleCat.{u} R) :=
  ModuleCat.hasLimitsOfShape

/-- Evaluate cover sections at the chosen lift supplied by an object of the slice. -/
def productEvaluation (F : Sheaf J (ModuleCat.{u} R)) :
    (J.overPullback (ModuleCat.{u} R) Y.V).obj ((productSheaf J Y.V).obj F) ⟶
      (J.overPullback (ModuleCat.{u} R) Y.V).obj F where
  hom.app U := F.obj.map (prod.lift U.unop.hom (𝟙 U.unop.left)).op
  hom.naturality := by
    intro U V f
    change F.obj.map (prod.map (𝟙 Y.V) f.unop.left).op ≫
        F.obj.map (prod.lift V.unop.hom (𝟙 V.unop.left)).op =
      F.obj.map (prod.lift U.unop.hom (𝟙 U.unop.left)).op ≫ F.obj.map f.unop.left.op
    rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp]
    congr 2
    apply prod.hom_ext <;> simp [Over.w f.unop]

@[reassoc] theorem productEvaluation_natural
    {F F' : Sheaf J (ModuleCat.{u} R)} (f : F ⟶ F') :
    (J.overPullback (ModuleCat.{u} R) Y.V).map ((productSheaf J Y.V).map f) ≫
        productEvaluation J Y F' =
      productEvaluation J Y F ≫ (J.overPullback (ModuleCat.{u} R) Y.V).map f := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  exact (f.hom.naturality _).symm

/-- The canonical map from localized invariants to the localized underlying sheaf. -/
def associatedEvaluation (F : Action (Sheaf J (ModuleCat.{u} R)) G) :
    (J.overPullback (ModuleCat.{u} R) Y.V).obj (associated J Y F) ⟶
      (J.overPullback (ModuleCat.{u} R) Y.V).obj F.V :=
  (J.overPullback (ModuleCat.{u} R) Y.V).map (inclusion J Y F) ≫
    productEvaluation J Y F.V

/-- Evaluation is natural in all equivariant sheaf maps. -/
def associatedEvaluationNat :
    associatedFunctor J Y ⋙ J.overPullback (ModuleCat.{u} R) Y.V ⟶
      Action.forget (Sheaf J (ModuleCat.{u} R)) G ⋙
        J.overPullback (ModuleCat.{u} R) Y.V where
  app F := associatedEvaluation J Y F
  naturality {F F'} f := by
    dsimp [associatedEvaluation]
    rw [← Category.assoc, ← Functor.map_comp, inclusion_natural,
      Functor.map_comp, Category.assoc, productEvaluation_natural, Category.assoc]

/-- Sections of the invariant sheaf inject into sections over the cover. -/
theorem inclusion_section_injective
    (F : Action (Sheaf J (ModuleCat.{u} R)) G) (U : C) :
    Function.Injective ((inclusion J Y F).hom.app (op U)) := by
  let E := sheafToPresheaf J (ModuleCat.{u} R) ⋙
    (evaluation Cᵒᵖ (ModuleCat.{u} R)).obj (op U) ⋙ forget (ModuleCat.{u} R)
  let h := isLimitOfPreserves E (limit.isLimit ((invariantDiagram J Y).obj F))
  intro x y hxy
  apply (Types.isLimitEquivSections h).injective
  apply Subtype.ext
  funext j
  cases j
  exact hxy

/-- Every invariant section comes from a section of the invariant sheaf. -/
theorem inclusion_section_exists
    (F : Action (Sheaf J (ModuleCat.{u} R)) G) (U : C)
    (s : ((productSheaf J Y.V).obj F.V).obj.obj (op U))
    (hs : ∀ g : G, ((diagonal J Y F).ρ g).hom.app (op U) s = s) :
    ∃ t, (inclusion J Y F).hom.app (op U) t = s := by
  let E := sheafToPresheaf J (ModuleCat.{u} R) ⋙
    (evaluation Cᵒᵖ (ModuleCat.{u} R)).obj (op U) ⋙ forget (ModuleCat.{u} R)
  let h := isLimitOfPreserves E (limit.isLimit ((invariantDiagram J Y).obj F))
  let z : (((invariantDiagram J Y).obj F) ⋙ E).sections :=
    ⟨fun _ => s, by rintro ⟨⟩ ⟨⟩ g; exact hs g⟩
  exact ⟨(Types.isLimitEquivSections h).symm z,
    Types.isLimitEquivSections_symm_apply h z (SingleObj.star G)⟩

/-- Restrict cover sections to the graph translated by a group element. -/
def graphRestriction (F : Sheaf J (ModuleCat.{u} R)) (U : Over Y.V) (g : G) :
    F.obj.obj (op (Y.V ⨯ U.left)) ⟶ F.obj.obj (op U.left) :=
  F.obj.map (prod.lift (U.hom ≫ Y.ρ g) (𝟙 U.left)).op

@[simp] theorem graphRestriction_one (F : Sheaf J (ModuleCat.{u} R))
    (U : Over Y.V) :
    graphRestriction J Y F U 1 = (productEvaluation J Y F).hom.app (op U) := by
  simp [graphRestriction, productEvaluation]
  rfl

/-- Diagonal invariance permutes graph restrictions and acts on coefficients. -/
theorem graphRestriction_diagonal
    (F : Action (Sheaf J (ModuleCat.{u} R)) G) (U : Over Y.V) (g h : G) :
    ((diagonal J Y F).ρ g).hom.app (op U.left) ≫ graphRestriction J Y F.V U h =
      graphRestriction J Y F.V U (g⁻¹ * h) ≫ (F.ρ g).hom.app (op U.left) := by
  change F.V.obj.map (prod.map (Y.ρ g⁻¹) (𝟙 U.left)).op ≫
      (F.ρ g).hom.app (op (Y.V ⨯ U.left)) ≫
        F.V.obj.map (prod.lift (U.hom ≫ Y.ρ h) (𝟙 U.left)).op = _
  rw [← (F.ρ g).hom.naturality, ← Category.assoc, ← F.V.obj.map_comp, ← op_comp]
  dsimp [graphRestriction]
  congr 2
  rw [← op_comp]
  congr 1
  apply prod.hom_ext <;> simp [map_mul, End.mul_def, Category.assoc]

/-- An invariant section is determined on every translated graph by its evaluation. -/
theorem invariant_section_graph
    (F : Action (Sheaf J (ModuleCat.{u} R)) G) (U : Over Y.V)
    (s : F.V.obj.obj (op (Y.V ⨯ U.left)))
    (hs : ∀ g : G, ((diagonal J Y F).ρ g).hom.app (op U.left) s = s)
    (g : G) :
    graphRestriction J Y F.V U g s =
      (F.ρ g).hom.app (op U.left) ((productEvaluation J Y F.V).hom.app (op U) s) := by
  have h := ConcreteCategory.congr_hom (graphRestriction_diagonal J Y F U g g) s
  change graphRestriction J Y F.V U g (((diagonal J Y F).ρ g).hom.app (op U.left) s) =
    (F.ρ g).hom.app (op U.left) (graphRestriction J Y F.V U (g⁻¹ * g) s) at h
  simpa only [hs, inv_mul_cancel, graphRestriction_one] using! h

/-- The published inclusion sends each section to a diagonal-invariant section. -/
theorem inclusion_section_invariant
    (F : Action (Sheaf J (ModuleCat.{u} R)) G) (U : C)
    (t : (associated J Y F).obj.obj (op U)) (g : G) :
    ((diagonal J Y F).ρ g).hom.app (op U) ((inclusion J Y F).hom.app (op U) t) =
      (inclusion J Y F).hom.app (op U) t := by
  have h := congrArg (fun f => f.hom.app (op U)) (inclusion_invariant J Y F g)
  exact ConcreteCategory.congr_hom h t

/-- Bijective restriction to translated graphs makes invariant evaluation bijective. -/
theorem associatedEvaluation_bijective
    (F : Action (Sheaf J (ModuleCat.{u} R)) G) (U : Over Y.V)
    (hsplit : Function.Bijective (fun (s : F.V.obj.obj (op (Y.V ⨯ U.left)))
      (g : G) => graphRestriction J Y F.V U g s)) :
    Function.Bijective ((associatedEvaluation J Y F).hom.app (op U)) := by
  constructor
  · intro x y hxy
    apply inclusion_section_injective J Y F U.left
    apply hsplit.1
    funext g
    change (productEvaluation J Y F.V).hom.app (op U)
      ((inclusion J Y F).hom.app (op U.left) x) =
        (productEvaluation J Y F.V).hom.app (op U)
          ((inclusion J Y F).hom.app (op U.left) y) at hxy
    exact (invariant_section_graph J Y F U _
      (inclusion_section_invariant J Y F U.left x) g).trans
        ((congrArg (fun z => (F.ρ g).hom.app (op U.left) z) hxy).trans
          (invariant_section_graph J Y F U _
            (inclusion_section_invariant J Y F U.left y) g).symm)
  · intro x
    obtain ⟨s, hs⟩ := hsplit.2 (fun g => (F.ρ g).hom.app (op U.left) x)
    have hs' (g : G) : graphRestriction J Y F.V U g s =
        (F.ρ g).hom.app (op U.left) x := congrFun hs g
    have hinv (g : G) : ((diagonal J Y F).ρ g).hom.app (op U.left) s = s := by
      apply hsplit.1
      funext h
      have hd := ConcreteCategory.congr_hom (graphRestriction_diagonal J Y F U g h) s
      change graphRestriction J Y F.V U h (((diagonal J Y F).ρ g).hom.app (op U.left) s) =
        (F.ρ g).hom.app (op U.left) (graphRestriction J Y F.V U (g⁻¹ * h) s) at hd
      have hm := congrArg (fun f => f.hom.app (op U.left)) (F.ρ.map_mul g (g⁻¹ * h))
      have hm' := ConcreteCategory.congr_hom hm x
      change (F.ρ (g * (g⁻¹ * h))).hom.app (op U.left) x =
        (F.ρ g).hom.app (op U.left) ((F.ρ (g⁻¹ * h)).hom.app (op U.left) x) at hm'
      have hm'' : (F.ρ g).hom.app (op U.left) ((F.ρ (g⁻¹ * h)).hom.app (op U.left) x) =
          (F.ρ h).hom.app (op U.left) x := by simpa using hm'.symm
      exact hd.trans ((congrArg (fun z => (F.ρ g).hom.app (op U.left) z)
        (hs' (g⁻¹ * h))).trans (hm''.trans (hs' h).symm))
    obtain ⟨t, ht⟩ := inclusion_section_exists J Y F U.left s hinv
    refine ⟨t, ?_⟩
    change (productEvaluation J Y F.V).hom.app (op U)
      ((inclusion J Y F).hom.app (op U.left) t) = x
    erw [ht, ← graphRestriction_one, hs']
    simp
    rfl

/-- Canonical natural trivialization when all translated graph restrictions split sections. -/
def associatedTrivializationOfSplitting
    (hsplit : ∀ (F : Sheaf J (ModuleCat.{u} R)) (U : Over Y.V),
      Function.Bijective (fun (s : F.obj.obj (op (Y.V ⨯ U.left))) (g : G) =>
        graphRestriction J Y F U g s)) :
    (associatedFunctor J Y ⋙ J.overPullback (ModuleCat.{u} R) Y.V) ≅
      (Action.forget (Sheaf J (ModuleCat.{u} R)) G ⋙
        J.overPullback (ModuleCat.{u} R) Y.V) := by
  have hF (F : Action (Sheaf J (ModuleCat.{u} R)) G) : IsIso (associatedEvaluation J Y F) := by
    have (U : (Over Y.V)ᵒᵖ) : IsIso ((associatedEvaluation J Y F).hom.app U) :=
      (ConcreteCategory.isIso_iff_bijective _).2
        (associatedEvaluation_bijective J Y F U.unop (hsplit F.V U.unop))
    have := NatIso.isIso_of_isIso_app (associatedEvaluation J Y F).hom
    exact (ObjectProperty.isIso_hom_iff _).1 inferInstance
  haveI (F : Action (Sheaf J (ModuleCat.{u} R)) G) :
      IsIso ((associatedEvaluationNat (R := R) J Y).app F) := hF F
  haveI := NatIso.isIso_of_isIso_app (associatedEvaluationNat (R := R) J Y)
  exact asIso (associatedEvaluationNat (R := R) J Y)

/-- Constant coefficients specialize the sheaf-level trivialization functorially. -/
def constantAssociatedTrivializationOfSplitting [HasSheafify J (ModuleCat.{u} R)]
    (hsplit : ∀ (F : Sheaf J (ModuleCat.{u} R)) (U : Over Y.V),
      Function.Bijective (fun (s : F.obj.obj (op (Y.V ⨯ U.left))) (g : G) =>
        graphRestriction J Y F U g s)) :
    (constantAssociatedFunctor J Y ⋙ J.overPullback (ModuleCat.{u} R) Y.V) ≅
      (Action.forget (ModuleCat.{u} R) G ⋙ constantSheaf J (ModuleCat.{u} R) ⋙
        J.overPullback (ModuleCat.{u} R) Y.V) :=
  NatIso.ofComponents
    (fun F => (associatedTrivializationOfSplitting J Y hsplit).app
      (((constantSheaf J (ModuleCat.{u} R)).mapAction G).obj F))
    (fun f => (associatedTrivializationOfSplitting J Y hsplit).hom.naturality
      (((constantSheaf J (ModuleCat.{u} R)).mapAction G).map f))

end Langlands.Shimura.Coefficients
