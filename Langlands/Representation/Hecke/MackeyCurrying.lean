import Langlands.Representation.Hecke.MackeyModels
import Mathlib.CategoryTheory.Yoneda

/-! # Categorical currying and representability for the Mackey comparisons -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace Langlands.Hecke.Homomorphism

universe uC uD vC vD uG uH v

/-- A family of Hom equivalences natural in the representing and parameter
objects gives an isomorphism of the original functors. -/
def isoOfNaturalHomEquiv {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] (A B : D ⥤ C)
    (e : ∀ (X : C) (Y : D), (X ⟶ A.obj Y) ≃ (X ⟶ B.obj Y))
    (hl : ∀ {X X' : C} (Y : D) (f : X' ⟶ X) (g : X ⟶ A.obj Y),
      e X' Y (f ≫ g) = f ≫ e X Y g)
    (hr : ∀ (X : C) {Y Y' : D} (f : Y ⟶ Y') (g : X ⟶ A.obj Y),
      e X Y' (g ≫ A.map f) = e X Y g ≫ B.map f) : A ≅ B := by
  let i (Y : D) : A.obj Y ≅ B.obj Y :=
    { hom := e (A.obj Y) Y (𝟙 _)
      inv := (e (B.obj Y) Y).symm (𝟙 _)
      hom_inv_id := by
        apply (e (A.obj Y) Y).injective
        rw [hl, Equiv.apply_symm_apply, Category.comp_id]
      inv_hom_id := by
        have h := hl Y ((e (B.obj Y) Y).symm (𝟙 _)) (𝟙 (A.obj Y))
        simpa only [Category.comp_id, Equiv.apply_symm_apply] using h.symm }
  refine NatIso.ofComponents i ?_
  intro Y Y' f
  change A.map f ≫ e (A.obj Y') Y' (𝟙 _) = e (A.obj Y) Y (𝟙 _) ≫ B.map f
  rw [← hl, Category.comp_id, ← hr, Category.id_comp]

section Currying

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The full smooth subcategory has the original equivariant maps as morphisms. -/
def smoothMapEquiv (A B : SmoothRep.{0, uG, v} ℂ G) :
    (A ⟶ B) ≃ A.representation.IntertwiningMap B.representation where
  toFun := SmoothRep.hom
  invFun := SmoothRep.ofHom
  left_inv _ := rfl
  right_inv _ := rfl

/-- Renard III.1.15, on the actual categorical tensor and smooth Hom objects. -/
def smoothCurry (A V B : SmoothRep.{0, uG, v} ℂ G) :
    ((smoothTensorBifunctor G).obj (A, V) ⟶ B) ≃
      (A ⟶ (smoothHomBifunctor G).obj (Opposite.op V, B)) :=
  (smoothMapEquiv _ _).trans
    ((Renard.Smooth.TensorHom.smoothIntertwinerCurry
      A.representation V.representation B.representation A.isSmooth).toEquiv.trans
      (smoothMapEquiv A ((smoothHomBifunctor G).obj (Opposite.op V, B))).symm)

@[simp]
theorem smoothCurry_left {A A' V B : SmoothRep.{0, uG, v} ℂ G}
    (f : A' ⟶ A) (g : (smoothTensorBifunctor G).obj (A, V) ⟶ B) :
    smoothCurry A' V B ((smoothTensorBifunctor G).map (f, 𝟙 V) ≫ g) =
      f ≫ smoothCurry A V B g := by
  ext x
  apply Subtype.ext
  apply LinearMap.ext
  intro y
  rfl

@[simp]
theorem smoothCurry_right {A V B B' : SmoothRep.{0, uG, v} ℂ G}
    (f : (smoothTensorBifunctor G).obj (A, V) ⟶ B) (g : B ⟶ B') :
    smoothCurry A V B' (f ≫ g) = smoothCurry A V B f ≫
      (smoothHomBifunctor G).map (𝟙 (Opposite.op V), g) := by
  ext x
  apply Subtype.ext
  apply LinearMap.ext
  intro y
  rfl

@[simp]
theorem smoothCurry_middle {A V V' B : SmoothRep.{0, uG, v} ℂ G}
    (f : V' ⟶ V) (g : (smoothTensorBifunctor G).obj (A, V) ⟶ B) :
    smoothCurry A V' B ((smoothTensorBifunctor G).map (𝟙 A, f) ≫ g) =
      smoothCurry A V B g ≫ (smoothHomBifunctor G).map (f.op, 𝟙 B) := by
  ext x
  apply Subtype.ext
  apply LinearMap.ext
  intro y
  rfl

@[simp]
theorem smoothUncurry_left {A A' V B : SmoothRep.{0, uG, v} ℂ G}
    (f : A' ⟶ A) (g : A ⟶ (smoothHomBifunctor G).obj (Opposite.op V, B)) :
    (smoothCurry A' V B).symm (f ≫ g) =
      (smoothTensorBifunctor G).map (f, 𝟙 V) ≫ (smoothCurry A V B).symm g := by
  apply (smoothCurry A' V B).injective
  rw [Equiv.apply_symm_apply, smoothCurry_left, Equiv.apply_symm_apply]

@[simp]
theorem smoothUncurry_right {A V B B' : SmoothRep.{0, uG, v} ℂ G}
    (f : A ⟶ (smoothHomBifunctor G).obj (Opposite.op V, B)) (g : B ⟶ B') :
    (smoothCurry A V B').symm
      (f ≫ (smoothHomBifunctor G).map (𝟙 (Opposite.op V), g)) =
      (smoothCurry A V B).symm f ≫ g := by
  apply (smoothCurry A V B').injective
  rw [Equiv.apply_symm_apply, smoothCurry_right, Equiv.apply_symm_apply]

@[simp]
theorem smoothUncurry_middle {A V V' B : SmoothRep.{0, uG, v} ℂ G}
    (f : V' ⟶ V) (g : A ⟶ (smoothHomBifunctor G).obj (Opposite.op V, B)) :
    (smoothCurry A V' B).symm
      (g ≫ (smoothHomBifunctor G).map (f.op, 𝟙 B)) =
      (smoothTensorBifunctor G).map (𝟙 A, f) ≫ (smoothCurry A V B).symm g := by
  apply (smoothCurry A V' B).injective
  rw [Equiv.apply_symm_apply, smoothCurry_middle, Equiv.apply_symm_apply]

end Currying

section Pullback

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (φ : H →* G) (hφ : Continuous φ)

/-- Restriction commutes with the diagonal tensor, by the identity on tensors. -/
def restrictionTensorIso (A B : SmoothRep.{0, uG, v} ℂ G) :
    (restriction φ hφ).obj ((smoothTensorBifunctor G).obj (A, B)) ≅
      (smoothTensorBifunctor H).obj ((restriction φ hφ).obj A,
        (restriction φ hφ).obj B) := Iso.refl _

end Pullback

end Langlands.Hecke.Homomorphism
