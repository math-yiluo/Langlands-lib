import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.Algebra.Category.Grp.EpiMono

/-!
# Zero extension from a clopen open

Finite disjoint gluing gives actual additive maps, with independent space and
section-carrier universes. This is an all-open prerequisite for Renard II.2.4.
-/

noncomputable section

namespace Langlands.Sheaf.ClopenExtension

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v

variable {X : TopCat.{u}}

/-- The open complement of a closed open. -/
def complement (U : Opens X) (hU : IsClosed (U : Set X)) : Opens X :=
  ⟨(U : Set X)ᶜ, hU.isOpen_compl⟩

@[simp] theorem inf_complement (U : Opens X) (hU : IsClosed (U : Set X)) :
    U ⊓ complement U hU = ⊥ := by
  ext x
  simp [complement]

@[simp] theorem sup_complement (U : Opens X) (hU : IsClosed (U : Set X)) :
    U ⊔ complement U hU = ⊤ := by
  ext x
  simp [complement]

variable (F : TopCat.Sheaf AddCommGrpCat.{v} X)

/-- Restriction from global sections. -/
abbrev restrict (U : Opens X) : F.presheaf.obj (op ⊤) ⟶ F.presheaf.obj (op U) :=
  F.presheaf.map (homOfLE le_top : U ⟶ ⊤).op

/-- A disjoint two-open cover gives the product cone on its union. -/
def productOfDisjointCover (U V W : Opens X) (hd : U ⊓ V = ⊥)
    (hc : U ⊔ V = W) :
    IsLimit (BinaryFan.mk
      (F.presheaf.map (homOfLE (le_sup_left.trans_eq hc) : U ⟶ W).op)
      (F.presheaf.map (homOfLE (le_sup_right.trans_eq hc) : V ⟶ W).op)) := by
  subst W
  exact F.isProductOfDisjoint U V hd

/-- Disjoint sheaf gluing identifies global sections with the two restrictions. -/
def globalProduct (U : Opens X) (hU : IsClosed (U : Set X)) :
    IsLimit (BinaryFan.mk (restrict F U) (restrict F (complement U hU))) :=
  productOfDisjointCover F U (complement U hU) ⊤
    (inf_complement U hU) (sup_complement U hU)

/-- Extend a section by zero on the open complement. -/
def extend (U : Opens X) (hU : IsClosed (U : Set X)) :
    F.presheaf.obj (op U) ⟶ F.presheaf.obj (op ⊤) :=
  BinaryFan.IsLimit.lift (globalProduct F U hU) (𝟙 _) 0

@[simp, reassoc] theorem extend_restrict (U : Opens X) (hU : IsClosed (U : Set X)) :
    extend F U hU ≫ restrict F U = 𝟙 _ :=
  BinaryFan.IsLimit.lift_fst (globalProduct F U hU) _ _

@[simp, reassoc] theorem extend_restrict_complement
    (U : Opens X) (hU : IsClosed (U : Set X)) :
    extend F U hU ≫ restrict F (complement U hU) = 0 :=
  BinaryFan.IsLimit.lift_snd (globalProduct F U hU) _ _

/-- The restrictions to a clopen and its complement determine a morphism. -/
theorem hom_ext (U : Opens X) (hU : IsClosed (U : Set X))
    {A : AddCommGrpCat.{v}} {f g : A ⟶ F.presheaf.obj (op ⊤)}
    (h₁ : f ≫ restrict F U = g ≫ restrict F U)
    (h₂ : f ≫ restrict F (complement U hU) =
      g ≫ restrict F (complement U hU)) : f = g :=
  BinaryFan.IsLimit.hom_ext (globalProduct F U hU) h₁ h₂

/-- Restriction and vanishing on the complement characterize zero extension. -/
theorem extend_unique (U : Opens X) (hU : IsClosed (U : Set X))
    {A : AddCommGrpCat.{v}} (s : A ⟶ F.presheaf.obj (op U))
    (t : A ⟶ F.presheaf.obj (op ⊤))
    (h₁ : t ≫ restrict F U = s)
    (h₂ : t ≫ restrict F (complement U hU) = 0) :
    t = s ≫ extend F U hU := by
  apply hom_ext F U hU <;> simp [Category.assoc, h₁, h₂]

/-- The extension embeds the actual group of sections. -/
theorem extend_injective (U : Opens X) (hU : IsClosed (U : Set X)) :
    Function.Injective (extend F U hU) := by
  intro s t h
  have hs := congrArg (fun f => f s) (extend_restrict F U hU)
  have ht := congrArg (fun f => f t) (extend_restrict F U hU)
  exact hs.symm.trans ((congrArg (restrict F U) h).trans ht)

/-- The additive endomorphism that retains a section only on a clopen open. -/
def projector (U : Opens X) (hU : IsClosed (U : Set X)) :
    End (F.presheaf.obj (op ⊤)) :=
  restrict F U ≫ extend F U hU

@[simp] theorem projector_idempotent (U : Opens X) (hU : IsClosed (U : Set X)) :
    projector F U hU ≫ projector F U hU = projector F U hU := by
  dsimp only [projector]
  rw [Category.assoc, ← Category.assoc (extend F U hU), extend_restrict, Category.id_comp]

end Langlands.Sheaf.ClopenExtension
