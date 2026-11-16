import Langlands.GroupScheme.VectorGroupQuotient
import Langlands.GroupScheme.Rational.VectorGroupDimension

/-! # Coordinate blocks over arbitrary rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Classical
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.VectorGroup.CoordinateBlock

variable {R : CommRingCat.{u}}
    {V : GroupScheme (Spec R)} {d m : ℕ}
    (e : ∀ T : Over (Spec R),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (I : Set (Fin d)) (σ : Fin m ≃ I)

/-- Extend a point of the smaller vector group by zero outside the block. -/
def blockPoints (T : Over (Spec R)) :
    (T ⟶ (VectorGroup.groupScheme R m).X) →* (T ⟶ V.X) where
  toFun v := (e T).symm (Multiplicative.ofAdd fun a =>
    if h : a ∈ I then
      (VectorGroup.coordinates R m T v).toAdd (σ.symm ⟨a, h⟩)
    else 0)
  map_one' := by
    apply (e T).injective
    simp only [MulEquiv.apply_symm_apply, (e T).map_one,
      (VectorGroup.coordinates R m T).map_one]
    apply Multiplicative.toAdd.injective
    funext a
    change (if h : a ∈ I then (0 : Fin m → Γ(T.left, ⊤)) (σ.symm ⟨a, h⟩)
      else 0) = 0
    split_ifs <;> rfl
  map_mul' x y := by
    apply (e T).injective
    apply Multiplicative.toAdd.injective
    funext a
    simp only [MulEquiv.apply_symm_apply, map_mul, toAdd_mul, toAdd_ofAdd, Pi.add_apply]
    split_ifs <;> simp

@[simp]
theorem blockPoints_coord
    (T : Over (Spec R))
    (v : T ⟶ (VectorGroup.groupScheme R m).X) (a : Fin d) :
    (e T (blockPoints e I σ T v)).toAdd a =
      if h : a ∈ I then
        (VectorGroup.coordinates R m T v).toAdd (σ.symm ⟨a, h⟩)
      else 0 :=
  congrArg (fun z => z.toAdd a) ((e T).apply_symm_apply _)

variable {e I σ}

theorem block_natural
    (he : ∀ (T W : Over (Spec R)) (f : W ⟶ T) (v : T ⟶ V.X),
      (e W (f ≫ v)).toAdd = fun a => f.left.appTop ((e T v).toAdd a)) (I : Set (Fin d)) (σ : Fin m ≃ I)
    {T W : Over (Spec R)} (f : W ⟶ T)
    (v : T ⟶ (VectorGroup.groupScheme R m).X) :
    blockPoints e I σ W (f ≫ v) =
      f ≫ blockPoints e I σ T v := by
  apply (e W).injective
  apply Multiplicative.toAdd.injective
  funext a
  rw [blockPoints_coord, VectorGroup.coordinates_comp, he T W f]
  dsimp only
  rw [blockPoints_coord]
  split_ifs <;> simp

variable (e I σ)

/-- The inclusion of a coordinate block is an actual group-scheme morphism. -/
def blockInclusion (he : ∀ (T W : Over (Spec R)) (f : W ⟶ T) (v : T ⟶ V.X),
      (e W (f ≫ v)).toAdd = fun a => f.left.appTop ((e T v).toAdd a)) :
    VectorGroup.groupScheme R m ⟶ V :=
  homOfPoints (blockPoints e I σ)
    (block_natural he I σ)

@[simp]
theorem comp_blockInclusion (he : ∀ (T W : Over (Spec R)) (f : W ⟶ T) (v : T ⟶ V.X),
      (e W (f ≫ v)).toAdd = fun a => f.left.appTop ((e T v).toAdd a))
    (T : Over (Spec R))
    (v : T ⟶ (VectorGroup.groupScheme R m).X) :
    v ≫ (blockInclusion e I σ he).hom.hom =
      blockPoints e I σ T v :=
  comp_homOfPoints _ _ T v

/-- Read the coordinates indexed by the block. -/
def blockRestrictionPoints (T : Over (Spec R)) :
    (T ⟶ V.X) →* (T ⟶ (VectorGroup.groupScheme R m).X) where
  toFun v := (VectorGroup.coordinates R m T).symm
    (Multiplicative.ofAdd fun a => (e T v).toAdd (σ a))
  map_one' := by
    apply (VectorGroup.coordinates R m T).injective
    simp only [MulEquiv.apply_symm_apply, (e T).map_one,
      (VectorGroup.coordinates R m T).map_one]
    rfl
  map_mul' x y := by
    apply (VectorGroup.coordinates R m T).injective
    apply Multiplicative.toAdd.injective
    funext a
    simp only [MulEquiv.apply_symm_apply, map_mul, toAdd_mul, toAdd_ofAdd, Pi.add_apply]

@[simp]
theorem blockRestrictionPoints_coord
    (T : Over (Spec R)) (v : T ⟶ V.X) (a : Fin m) :
    (VectorGroup.coordinates R m T
      (blockRestrictionPoints e I σ T v)).toAdd a =
        (e T v).toAdd (σ a) :=
  congrArg (fun z => z.toAdd a)
    ((VectorGroup.coordinates R m T).apply_symm_apply _)

variable {e I σ}

theorem blockRestriction_natural
    (he : ∀ (T W : Over (Spec R)) (f : W ⟶ T) (v : T ⟶ V.X),
      (e W (f ≫ v)).toAdd = fun a => f.left.appTop ((e T v).toAdd a)) (I : Set (Fin d)) (σ : Fin m ≃ I)
    {T W : Over (Spec R)} (f : W ⟶ T) (v : T ⟶ V.X) :
    blockRestrictionPoints e I σ W (f ≫ v) =
      f ≫ blockRestrictionPoints e I σ T v := by
  apply (VectorGroup.coordinates R m W).injective
  apply Multiplicative.toAdd.injective
  funext a
  rw [blockRestrictionPoints_coord, he T W f,
    VectorGroup.coordinates_comp]
  dsimp only
  rw [blockRestrictionPoints_coord]

variable (e I σ)

/-- Coordinate restriction is an actual retraction of the block inclusion. -/
def blockRestriction (he : ∀ (T W : Over (Spec R)) (f : W ⟶ T) (v : T ⟶ V.X),
      (e W (f ≫ v)).toAdd = fun a => f.left.appTop ((e T v).toAdd a)) :
    V ⟶ VectorGroup.groupScheme R m :=
  homOfPoints (blockRestrictionPoints e I σ)
    (blockRestriction_natural he I σ)

@[simp]
theorem comp_blockRestriction (he : ∀ (T W : Over (Spec R)) (f : W ⟶ T) (v : T ⟶ V.X),
      (e W (f ≫ v)).toAdd = fun a => f.left.appTop ((e T v).toAdd a))
    (T : Over (Spec R)) (v : T ⟶ V.X) :
    v ≫ (blockRestriction e I σ he).hom.hom =
      blockRestrictionPoints e I σ T v :=
  comp_homOfPoints _ _ T v

theorem blockInclusion_restriction (he : ∀ (T W : Over (Spec R)) (f : W ⟶ T) (v : T ⟶ V.X),
      (e W (f ≫ v)).toAdd = fun a => f.left.appTop ((e T v).toAdd a)) :
    blockInclusion e I σ he ≫ blockRestriction e I σ he =
      𝟙 (VectorGroup.groupScheme R m) := by
  apply hom_ext_points
  intro T v
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_blockRestriction,
    comp_blockInclusion]
  apply (VectorGroup.coordinates R m T).injective
  apply Multiplicative.toAdd.injective
  funext a
  simp only [Grp.id_hom_hom, Category.comp_id,
    blockRestrictionPoints_coord, blockPoints_coord,
    dite_eq_left (σ a).property, Subtype.coe_eta, Equiv.symm_apply_apply]

theorem mono_blockInclusion (he : ∀ (T W : Over (Spec R)) (f : W ⟶ T) (v : T ⟶ V.X),
      (e W (f ≫ v)).toAdd = fun a => f.left.appTop ((e T v).toAdd a)) :
    Mono (blockInclusion e I σ he).hom.hom := by
  have h : (blockInclusion e I σ he).hom.hom ≫
      (blockRestriction e I σ he).hom.hom = 𝟙 _ :=
    congrArg (fun f => f.hom.hom) (blockInclusion_restriction e I σ he)
  exact ⟨fun _ _ hxy => by
    have hh := congrArg (fun f => f ≫
      (blockRestriction e I σ he).hom.hom) hxy
    simpa only [Category.assoc, h, Category.comp_id] using hh⟩

/-- The actual coordinate inclusion is closed when the ambient vector scheme is affine. -/
theorem isClosedSubgroup_blockInclusion
    [IsAffineHom V.X.hom] (he : ∀ (T W : Over (Spec R)) (f : W ⟶ T) (v : T ⟶ V.X),
      (e W (f ≫ v)).toAdd = fun a => f.left.appTop ((e T v).toAdd a)) :
    IsClosedSubgroup (blockInclusion e I σ he) := by
  let j := blockInclusion e I σ he
  let q := blockRestriction e I σ he
  have h : j.hom.hom.left ≫ q.hom.hom.left = 𝟙 _ :=
    congrArg (fun f => f.hom.hom.left)
      (blockInclusion_restriction e I σ he)
  have : IsSeparated (q.hom.hom.left ≫
      (VectorGroup.groupScheme R m).X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : IsSeparated q.hom.hom.left :=
    IsSeparated.of_comp _ (VectorGroup.groupScheme R m).X.hom
  have : IsClosedImmersion (j.hom.hom.left ≫ q.hom.hom.left) := by
    rw [h]
    infer_instance
  exact IsClosedImmersion.of_comp _ q.hom.hom.left


end Langlands.GroupScheme.VectorGroup.CoordinateBlock
