/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsMapNaturality

/-!
# Naturality of the open tensor-section comparison

Source: Stacks Project, Descent, Tags 03DR (equation-quasi-coherent-presheaf) and
03DU, item 4. Normalized pullback composition and adjunction-unit naturality give
compatibility with every triangle over the open subscheme.
(blueprint: lem-weil-pbc-etale-open-qcoherent-identification-naturality)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Scheme.Modules

attribute [local irreducible] tensorPullback tensorPullbackObj

/-- Associativity of normalized left-adjoint composition, specialized to scheme
pushforwards. Source: Stacks 03DR, functoriality in equation-quasi-coherent-presheaf;
Mathlib `Adjunction.leftAdjointCompIso_assoc`. Pushforward coherence is sectionwise
identity, independently of the chosen left adjoints. -/
private theorem composition_associativity
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) :
    Functor.isoWhiskerLeft (L c)
        (Adjunction.leftAdjointCompIso (adj b) (adj a) (adj (a ≫ b))
          (pushforwardComp a b)) ≪≫
      Adjunction.leftAdjointCompIso (adj c) (adj (a ≫ b)) (adj ((a ≫ b) ≫ c))
        (pushforwardComp (a ≫ b) c) =
    (Functor.associator (L c) (L b) (L a)).symm ≪≫
      Functor.isoWhiskerRight
        (Adjunction.leftAdjointCompIso (adj c) (adj b) (adj (b ≫ c))
          (pushforwardComp b c)) (L a) ≪≫
      Adjunction.leftAdjointCompIso (adj (b ≫ c)) (adj a) (adj ((a ≫ b) ≫ c))
        (pushforwardComp a (b ≫ c)) := by
  apply Adjunction.leftAdjointCompIso_assoc
  ext M V x
  rfl

/-- The module component of normalized tensor-composition associativity.
Source: Stacks 03DR, equation-quasi-coherent-presheaf. -/
private theorem tensor_composition_associativity
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (F : D.Modules) :
    ((tensorSectionsComp a b).hom.app ((tensorPullback c).obj F)) ≫
      (tensorSectionsComp (a ≫ b) c).hom.app F =
    (tensorPullback a).map ((tensorSectionsComp b c).hom.app F) ≫
      (tensorSectionsComp a (b ≫ c)).hom.app F := by
  have h := congrArg (fun e ↦ e.hom.app F)
    (composition_associativity (@tensorPullback)
      (fun {A B} f ↦ Classical.choose (exists_tensorPullbackAdjunction f)) a b c)
  simp only [Adjunction.leftAdjointCompIso, Iso.trans_hom,
    Functor.comp_obj, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_inv_app, Category.id_comp] at h
  unfold tensorSectionsComp
  convert h using 1

/-- Move an inverse composition comparison across the other composition comparison.
Source: Stacks 03DR, equation-quasi-coherent-presheaf. This follows by cancelling
isomorphisms in the forward associativity equation. -/
private theorem tensor_composition_inverse
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (F : D.Modules) :
    (tensorSectionsComp a (b ≫ c)).hom.app F ≫
      (tensorSectionsComp (a ≫ b) c).inv.app F =
    (tensorPullback a).map ((tensorSectionsComp b c).inv.app F) ≫
      (tensorSectionsComp a b).hom.app ((tensorPullback c).obj F) := by
  have h := tensor_composition_associativity a b c F
  apply (cancel_epi ((tensorPullback a).map ((tensorSectionsComp b c).hom.app F))).mp
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id]
  erw [Category.id_comp]

/-- Naturality of the global-section unit in its module argument.
Source: Stacks 03DR, equation-quasi-coherent-presheaf; adjunction-unit naturality. -/
private theorem section_unit_naturality {A B : Scheme.{u}} (a : A ⟶ B)
    {M N : B.Modules} (φ : M ⟶ N) :
    tensorSectionsUnit a M ≫ ((tensorPullback a).map φ).app ⊤ =
      φ.app ⊤ ≫ tensorSectionsUnit a N := by
  have hn := congrArg (fun ψ ↦ ψ.app ⊤)
    ((Classical.choose (exists_tensorPullbackAdjunction a)).unit.naturality φ)
  have hi : (homOfLE a.preimage_top.ge).op =
      𝟙 (Opposite.op (⊤ : TopologicalSpace.Opens A)) := rfl
  unfold tensorSectionsUnit
  erw [hi, ((tensorPullback a).obj M).presheaf.map_id,
    ((tensorPullback a).obj N).presheaf.map_id, Category.comp_id, Category.comp_id]
  simp only [Functor.id_map, Functor.comp_map, Hom.comp_app, pushforward_map_app] at hn
  exact hn.symm

/-- The inverse comparison intertwines the section restrictions for a triangle.
Source: Stacks 03DR, equation-quasi-coherent-presheaf. Eliminate the triangle equality,
evaluate inverse associativity at the top open, and use unit naturality. -/
private theorem composition_restriction {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (j : C ⟶ D)
    (h : a ≫ b = c) (F : D.Modules) :
    (tensorSectionsUnit a ((tensorPullback (b ≫ j)).obj F) ≫
      ((tensorSectionsComp a (b ≫ j)).hom.app F).app ⊤ ≫
      (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj F)
        (show a ≫ (b ≫ j) = c ≫ j from by rw [← Category.assoc, h]))).app ⊤) ≫
        ((tensorSectionsComp c j).inv.app F).app ⊤ =
    ((tensorSectionsComp b j).inv.app F).app ⊤ ≫
      (tensorSectionsUnit a ((tensorPullback b).obj ((tensorPullback j).obj F)) ≫
        ((tensorSectionsComp a b).hom.app ((tensorPullback j).obj F)).app ⊤ ≫
        (eqToHom (congrArg (fun f ↦
          (tensorPullback f).obj ((tensorPullback j).obj F)) h)).app ⊤) := by
  subst c
  simp only [eqToHom_refl, Hom.id_app, Category.comp_id]
  have hc := congrArg (fun φ ↦ φ.app ⊤) (tensor_composition_inverse a b j F)
  simp only [Hom.comp_app] at hc
  rw [Category.assoc, hc, ← Category.assoc, section_unit_naturality, Category.assoc]
  rfl

/-- The prescribed comparison on global sections, constructed from two module
isomorphisms rather than chosen from an existence theorem.
Source: Stacks Descent 03DR, equation (35.8.1), and 03DU, item 4.
(blueprint: lem-weil-pbc-etale-open-qcoherent-identification-naturality) -/
noncomputable def etaleOpenTensorSectionsComponentIso {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (F : X.Modules) (v : U.Etale) :
    Γ((Scheme.Modules.tensorPullback (v.hom ≫ j)).obj F, ⊤) ≅
      Γ((Scheme.Modules.tensorPullback v.hom).obj
        ((Scheme.Modules.restrictFunctor j).obj F), ⊤) :=
  ((Scheme.Modules.toPresheaf v.left) ⋙
    (evaluation _ AddCommGrpCat.{u}).obj (Opposite.op ⊤)).mapIso
      (((Scheme.Modules.tensorSectionsComp v.hom j).app F).symm ≪≫
        (Scheme.Modules.tensorPullback v.hom).mapIso
          (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)).leftAdjointUniq
            (Scheme.Modules.restrictAdjunction j)).app F))

/-- The explicit section comparisons commute with an etale restriction.
Source: Stacks Descent 03DR, equation (35.8.1), and 03DU, item 4.
(blueprint: lem-weil-pbc-etale-open-qcoherent-identification-naturality)

Proof: expand each restriction as the canonical unit for g followed by the normalized
composition comparison and transport along the triangle equation. Naturality of the
unit moves the pullback of the tensor/restriction comparison past section pullback.
The associativity equation for normalized composition, applied to g.left, v.hom and j,
moves the inverse comparison for v.hom and j past the composition comparison for g.
Naturality of tensorSectionsComp moves the module comparison through the remaining
composition map. The two transports agree by g.w and associativity of scheme
composition. Evaluating these module morphism equations at the whole source scheme
proves the displayed equality. Identity arrows give the identity square; for the empty
scheme or the zero module both sides are the unique section homomorphism. -/
theorem etaleOpenTensorSectionsComponent_naturality {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (F : X.Modules) {v w : U.Etale} (g : w ⟶ v) :
    Scheme.Modules.etaleTensorSectionsRestriction F
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).map g) ≫
      (etaleOpenTensorSectionsComponentIso j F w).hom =
    (etaleOpenTensorSectionsComponentIso j F v).hom ≫
      Scheme.Modules.etaleTensorSectionsRestriction
        ((Scheme.Modules.restrictFunctor j).obj F) g := by
  let φ := ((Classical.choose (exists_tensorPullbackAdjunction j)).leftAdjointUniq
    (restrictAdjunction j)).hom.app F
  change etaleTensorSectionsRestriction F
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).map g) ≫
      (((tensorSectionsComp w.hom j).inv.app F).app ⊤ ≫
        ((tensorPullback w.hom).map φ).app ⊤) =
    (((tensorSectionsComp v.hom j).inv.app F).app ⊤ ≫
      ((tensorPullback v.hom).map φ).app ⊤) ≫
        etaleTensorSectionsRestriction ((restrictFunctor j).obj F) g
  rw [← Category.assoc]
  have hc := composition_restriction g.left v.hom w.hom j g.w F
  change etaleTensorSectionsRestriction F
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).map g) ≫
      ((tensorSectionsComp w.hom j).inv.app F).app ⊤ =
    ((tensorSectionsComp v.hom j).inv.app F).app ⊤ ≫
      etaleTensorSectionsRestriction ((tensorPullback j).obj F) g at hc
  rw [hc, Category.assoc, etaleTensorSectionsMap_naturality φ g, Category.assoc]

end AlgebraicGeometry
