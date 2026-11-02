import Langlands.CategoryTheory.Renard.HomAdjunctionComparisonStatements

/-!
# Renard A.V: proof of the comparison of the two definitions of adjunction

A native adjunction gives a natural isomorphism of the lifted Hom bifunctors
whose components are the lifted native Hom equivalence and its inverse.
Conversely, the components of a supplied isomorphism form a native Hom
equivalence, natural in each variable, from which Mathlib builds an
adjunction with exactly that Hom equivalence.
-/

open CategoryTheory Opposite
open Langlands.Renard.AdjunctionHom

namespace Langlands.Renard.HomAdjunctionComparison

universe vA uA vB uB

section

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {G : B ⥤ A} {F : A ⥤ B}

/-- The isomorphism of Hom bifunctors given by a native adjunction `G ⊣ F`. -/
def homIsoOfAdjunction (adj : G ⊣ F) : rightHomBifunctor F ≅ leftHomBifunctor G where
  hom :=
    { app := fun p => ↾fun ψ => ULift.up ((adj.homEquiv (unop p.2) p.1).symm ψ.down)
      naturality := fun p q f => by
        ext ψ
        apply ULift.ext
        change (adj.homEquiv (unop q.2) q.1).symm (f.2.unop ≫ ψ.down ≫ F.map f.1) =
          G.map f.2.unop ≫ (adj.homEquiv (unop p.2) p.1).symm ψ.down ≫ f.1
        rw [adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_right_symm] }
  inv :=
    { app := fun p => ↾fun ψ => ULift.up (adj.homEquiv (unop p.2) p.1 ψ.down)
      naturality := fun p q f => by
        ext ψ
        apply ULift.ext
        change adj.homEquiv (unop q.2) q.1 (G.map f.2.unop ≫ ψ.down ≫ f.1) =
          f.2.unop ≫ adj.homEquiv (unop p.2) p.1 ψ.down ≫ F.map f.1
        rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right] }
  hom_inv_id := by
    ext p ψ
    apply ULift.ext
    exact (adj.homEquiv (unop p.2) p.1).apply_symm_apply ψ.down
  inv_hom_id := by
    ext p ψ
    apply ULift.ext
    exact (adj.homEquiv (unop p.2) p.1).symm_apply_apply ψ.down

/-- The forward component is the inverse native Hom equivalence. -/
theorem homIsoOfAdjunction_hom_app_down (adj : G ⊣ F) (X : A) (Y : B)
    (k : Y ⟶ F.obj X) :
    ((homIsoOfAdjunction adj).hom.app (X, op Y) (ULift.up k)).down =
      (adj.homEquiv Y X).symm k := rfl

/-- The inverse component is the native Hom equivalence. -/
theorem homIsoOfAdjunction_inv_app_down (adj : G ⊣ F) (X : A) (Y : B)
    (h : G.obj Y ⟶ X) :
    ((homIsoOfAdjunction adj).inv.app (X, op Y) (ULift.up h)).down =
      adj.homEquiv Y X h := rfl

/-- The native Hom equivalence read off the components of a supplied isomorphism. -/
def coreHomEquivOfHomIso (theta : rightHomBifunctor F ≅ leftHomBifunctor G) :
    Adjunction.CoreHomEquiv G F where
  homEquiv Y X :=
    { toFun := fun h => (theta.inv.app (X, op Y) (ULift.up h)).down
      invFun := fun k => (theta.hom.app (X, op Y) (ULift.up k)).down
      left_inv := fun h =>
        congrArg ULift.down (types_congr_hom (theta.inv_hom_id_app (X, op Y)) (ULift.up h))
      right_inv := fun k =>
        congrArg ULift.down (types_congr_hom (theta.hom_inv_id_app (X, op Y)) (ULift.up k)) }
  homEquiv_naturality_left_symm := fun {Y' Y X} f g => by
    have h := congrArg ULift.down (types_congr_hom
      (theta.hom.naturality ((𝟙 X, f.op) : ((X, op Y) : A × Bᵒᵖ) ⟶ (X, op Y')))
      (ULift.up g))
    change (theta.hom.app (X, op Y') (ULift.up (f ≫ g ≫ F.map (𝟙 X)))).down =
      G.map f ≫ (theta.hom.app (X, op Y) (ULift.up g)).down ≫ 𝟙 X at h
    rw [F.map_id, Category.comp_id, Category.comp_id] at h
    exact h
  homEquiv_naturality_right := fun {Y X X'} f g => by
    have h := congrArg ULift.down (types_congr_hom
      (theta.inv.naturality ((g, 𝟙 (op Y)) : ((X, op Y) : A × Bᵒᵖ) ⟶ (X', op Y)))
      (ULift.up f))
    change (theta.inv.app (X', op Y) (ULift.up (G.map (𝟙 Y) ≫ f ≫ g))).down =
      𝟙 Y ≫ (theta.inv.app (X, op Y) (ULift.up f)).down ≫ F.map g at h
    rw [G.map_id, Category.id_comp, Category.id_comp] at h
    exact h

/-- The native adjunction whose Hom equivalence is given by a supplied isomorphism. -/
def adjunctionOfHomIso (theta : rightHomBifunctor F ≅ leftHomBifunctor G) : G ⊣ F :=
  Adjunction.mkOfHomEquiv (coreHomEquivOfHomIso theta)

/-- The inverse native Hom equivalence is the forward component of `theta`. -/
theorem adjunctionOfHomIso_homEquiv_symm_apply
    (theta : rightHomBifunctor F ≅ leftHomBifunctor G) (X : A) (Y : B) (k : Y ⟶ F.obj X) :
    ((adjunctionOfHomIso theta).homEquiv Y X).symm k =
      (theta.hom.app (X, op Y) (ULift.up k)).down := by
  rw [adjunctionOfHomIso, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The native Hom equivalence is the inverse component of `theta`. -/
theorem adjunctionOfHomIso_homEquiv_apply
    (theta : rightHomBifunctor F ≅ leftHomBifunctor G) (X : A) (Y : B) (h : G.obj Y ⟶ X) :
    (adjunctionOfHomIso theta).homEquiv Y X h =
      (theta.inv.app (X, op Y) (ULift.up h)).down := by
  rw [adjunctionOfHomIso, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

end

/-- A native adjunction gives the source Hom isomorphism with both exact maps. -/
theorem nativeToHomStatement : NativeToHomStatement.{vA, uA, vB, uB} := by
  intro A _ B _ G F adj
  exact ⟨homIsoOfAdjunction adj, homIsoOfAdjunction_hom_app_down adj,
    homIsoOfAdjunction_inv_app_down adj⟩

/-- Every supplied source Hom isomorphism gives a native adjunction preserving it. -/
theorem homToNativeStatement : HomToNativeStatement.{vA, uA, vB, uB} := by
  intro A _ B _ G F theta
  exact ⟨adjunctionOfHomIso theta,
    fun X Y k => (adjunctionOfHomIso_homEquiv_symm_apply theta X Y k).symm,
    fun X Y h => (adjunctionOfHomIso_homEquiv_apply theta X Y h).symm⟩

/-- Existence of the source Hom isomorphism is equivalent to native adjointness. -/
theorem homAdjunctionIffNativeStatement :
    HomAdjunctionIffNativeStatement.{vA, uA, vB, uB} := by
  intro A _ B _ G F
  unfold HomAdjunction
  exact ⟨fun ⟨theta⟩ => ⟨adjunctionOfHomIso theta⟩, fun ⟨adj⟩ => ⟨homIsoOfAdjunction adj⟩⟩

/-- Renard A.V: the two exact comparisons and their existential consequence. -/
theorem homAdjunctionComparisonStatements :
    HomAdjunctionComparisonStatements.{vA, uA, vB, uB} :=
  ⟨nativeToHomStatement, homToNativeStatement, homAdjunctionIffNativeStatement⟩

end Langlands.Renard.HomAdjunctionComparison
