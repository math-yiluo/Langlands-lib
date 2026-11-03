import Langlands.GroupScheme.Rational.VectorCoordinateProduct
import Langlands.GroupScheme.VectorGroupQuotient
import Langlands.GroupScheme.CorepresentedSmooth

/-! # Actual smooth connected closed coordinate blocks -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Classical
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {V : GroupScheme (Spec (CommRingCat.of k))} {d m : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (I : Set (Fin d)) (σ : Fin m ≃ I)

/-- Extend a point of the smaller vector group by zero outside the block. -/
def vectorCoordinateBlockPoints (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) m).X) →* (T ⟶ V.X) where
  toFun v := (e T).symm (Multiplicative.ofAdd fun a =>
    if h : a ∈ I then
      (VectorGroup.coordinates (CommRingCat.of k) m T v).toAdd (σ.symm ⟨a, h⟩)
    else 0)
  map_one' := by
    apply (e T).injective
    simp only [MulEquiv.apply_symm_apply, (e T).map_one,
      (VectorGroup.coordinates (CommRingCat.of k) m T).map_one]
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
theorem vectorCoordinateBlockPoints_coord
    (T : Over (Spec (CommRingCat.of k)))
    (v : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) m).X) (a : Fin d) :
    (e T (vectorCoordinateBlockPoints e I σ T v)).toAdd a =
      if h : a ∈ I then
        (VectorGroup.coordinates (CommRingCat.of k) m T v).toAdd (σ.symm ⟨a, h⟩)
      else 0 :=
  congrArg (fun z => z.toAdd a) ((e T).apply_symm_apply _)

variable {e I σ}

theorem IsNaturalVectorCoordinates.vectorCoordinateBlock_natural
    (he : IsNaturalVectorCoordinates e) (I : Set (Fin d)) (σ : Fin m ≃ I)
    {T W : Over (Spec (CommRingCat.of k))} (f : W ⟶ T)
    (v : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) m).X) :
    vectorCoordinateBlockPoints e I σ W (f ≫ v) =
      f ≫ vectorCoordinateBlockPoints e I σ T v := by
  apply (e W).injective
  apply Multiplicative.toAdd.injective
  funext a
  rw [vectorCoordinateBlockPoints_coord, VectorGroup.coordinates_comp, he T W f]
  dsimp only
  rw [vectorCoordinateBlockPoints_coord]
  split_ifs <;> simp

variable (e I σ)

/-- The inclusion of a coordinate block is an actual group-scheme morphism. -/
def vectorCoordinateBlockInclusion (he : IsNaturalVectorCoordinates e) :
    VectorGroup.groupScheme (CommRingCat.of k) m ⟶ V :=
  homOfPoints (vectorCoordinateBlockPoints e I σ)
    (he.vectorCoordinateBlock_natural I σ)

@[simp]
theorem comp_vectorCoordinateBlockInclusion (he : IsNaturalVectorCoordinates e)
    (T : Over (Spec (CommRingCat.of k)))
    (v : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) m).X) :
    v ≫ (vectorCoordinateBlockInclusion e I σ he).hom.hom =
      vectorCoordinateBlockPoints e I σ T v :=
  comp_homOfPoints _ _ T v

/-- Read the coordinates indexed by the block. -/
def vectorCoordinateBlockRestrictionPoints (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ V.X) →* (T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) m).X) where
  toFun v := (VectorGroup.coordinates (CommRingCat.of k) m T).symm
    (Multiplicative.ofAdd fun a => (e T v).toAdd (σ a))
  map_one' := by
    apply (VectorGroup.coordinates (CommRingCat.of k) m T).injective
    simp only [MulEquiv.apply_symm_apply, (e T).map_one,
      (VectorGroup.coordinates (CommRingCat.of k) m T).map_one]
    rfl
  map_mul' x y := by
    apply (VectorGroup.coordinates (CommRingCat.of k) m T).injective
    apply Multiplicative.toAdd.injective
    funext a
    simp only [MulEquiv.apply_symm_apply, map_mul, toAdd_mul, toAdd_ofAdd, Pi.add_apply]

@[simp]
theorem vectorCoordinateBlockRestrictionPoints_coord
    (T : Over (Spec (CommRingCat.of k))) (v : T ⟶ V.X) (a : Fin m) :
    (VectorGroup.coordinates (CommRingCat.of k) m T
      (vectorCoordinateBlockRestrictionPoints e I σ T v)).toAdd a =
        (e T v).toAdd (σ a) :=
  congrArg (fun z => z.toAdd a)
    ((VectorGroup.coordinates (CommRingCat.of k) m T).apply_symm_apply _)

variable {e I σ}

theorem IsNaturalVectorCoordinates.vectorCoordinateBlockRestriction_natural
    (he : IsNaturalVectorCoordinates e) (I : Set (Fin d)) (σ : Fin m ≃ I)
    {T W : Over (Spec (CommRingCat.of k))} (f : W ⟶ T) (v : T ⟶ V.X) :
    vectorCoordinateBlockRestrictionPoints e I σ W (f ≫ v) =
      f ≫ vectorCoordinateBlockRestrictionPoints e I σ T v := by
  apply (VectorGroup.coordinates (CommRingCat.of k) m W).injective
  apply Multiplicative.toAdd.injective
  funext a
  rw [vectorCoordinateBlockRestrictionPoints_coord, he T W f,
    VectorGroup.coordinates_comp]
  dsimp only
  rw [vectorCoordinateBlockRestrictionPoints_coord]

variable (e I σ)

/-- Coordinate restriction is an actual retraction of the block inclusion. -/
def vectorCoordinateBlockRestriction (he : IsNaturalVectorCoordinates e) :
    V ⟶ VectorGroup.groupScheme (CommRingCat.of k) m :=
  homOfPoints (vectorCoordinateBlockRestrictionPoints e I σ)
    (he.vectorCoordinateBlockRestriction_natural I σ)

@[simp]
theorem comp_vectorCoordinateBlockRestriction (he : IsNaturalVectorCoordinates e)
    (T : Over (Spec (CommRingCat.of k))) (v : T ⟶ V.X) :
    v ≫ (vectorCoordinateBlockRestriction e I σ he).hom.hom =
      vectorCoordinateBlockRestrictionPoints e I σ T v :=
  comp_homOfPoints _ _ T v

theorem vectorCoordinateBlockInclusion_restriction (he : IsNaturalVectorCoordinates e) :
    vectorCoordinateBlockInclusion e I σ he ≫ vectorCoordinateBlockRestriction e I σ he =
      𝟙 (VectorGroup.groupScheme (CommRingCat.of k) m) := by
  apply hom_ext_points
  intro T v
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_vectorCoordinateBlockRestriction,
    comp_vectorCoordinateBlockInclusion]
  apply (VectorGroup.coordinates (CommRingCat.of k) m T).injective
  apply Multiplicative.toAdd.injective
  funext a
  simp only [Grp.id_hom_hom, Category.comp_id,
    vectorCoordinateBlockRestrictionPoints_coord, vectorCoordinateBlockPoints_coord,
    dite_eq_left (σ a).property, Subtype.coe_eta, Equiv.symm_apply_apply]

theorem mono_vectorCoordinateBlockInclusion (he : IsNaturalVectorCoordinates e) :
    Mono (vectorCoordinateBlockInclusion e I σ he).hom.hom := by
  have h : (vectorCoordinateBlockInclusion e I σ he).hom.hom ≫
      (vectorCoordinateBlockRestriction e I σ he).hom.hom = 𝟙 _ :=
    congrArg (fun f => f.hom.hom) (vectorCoordinateBlockInclusion_restriction e I σ he)
  exact ⟨fun _ _ hxy => by
    have hh := congrArg (fun f => f ≫
      (vectorCoordinateBlockRestriction e I σ he).hom.hom) hxy
    simpa only [Category.assoc, h, Category.comp_id] using hh⟩

/-- The block inclusion represents exactly the all-test coordinate subgroup. -/
theorem isRepresentedBy_vectorCoordinateBlockInclusion (he : IsNaturalVectorCoordinates e) :
    (vectorCoordinateSubgroup e he I).IsRepresentedBy
      (vectorCoordinateBlockInclusion e I σ he) := by
  refine ⟨mono_vectorCoordinateBlockInclusion e I σ he, ?_⟩
  ext T v
  rw [SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨x, rfl⟩ a ha
    simp only [comp_vectorCoordinateBlockInclusion, vectorCoordinateBlockPoints_coord,
      dite_eq_right ha]
  · intro hv
    refine ⟨vectorCoordinateBlockRestrictionPoints e I σ T v, ?_⟩
    rw [comp_vectorCoordinateBlockInclusion]
    apply (e T).injective
    apply Multiplicative.toAdd.injective
    funext a
    rw [vectorCoordinateBlockPoints_coord]
    split_ifs with ha
    · rw [vectorCoordinateBlockRestrictionPoints_coord]
      simp only [Equiv.apply_symm_apply]
    · exact (hv a ha).symm

/-- The actual coordinate inclusion is closed when the ambient vector scheme is affine. -/
theorem isClosedSubgroup_vectorCoordinateBlockInclusion
    [IsAffineHom V.X.hom] (he : IsNaturalVectorCoordinates e) :
    IsClosedSubgroup (vectorCoordinateBlockInclusion e I σ he) := by
  let j := vectorCoordinateBlockInclusion e I σ he
  let q := vectorCoordinateBlockRestriction e I σ he
  have h : j.hom.hom.left ≫ q.hom.hom.left = 𝟙 _ :=
    congrArg (fun f => f.hom.hom.left)
      (vectorCoordinateBlockInclusion_restriction e I σ he)
  have : IsSeparated (q.hom.hom.left ≫
      (VectorGroup.groupScheme (CommRingCat.of k) m).X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : IsSeparated q.hom.hom.left :=
    IsSeparated.of_comp _ (VectorGroup.groupScheme (CommRingCat.of k) m).X.hom
  have : IsClosedImmersion (j.hom.hom.left ≫ q.hom.hom.left) := by
    rw [h]
    infer_instance
  exact IsClosedImmersion.of_comp _ q.hom.hom.left

/-- Every coordinate block has an actual smooth connected closed realization. -/
theorem isSmoothConnectedClosed_vectorCoordinateSubgroup
    [IsAffineHom V.X.hom] (he : IsNaturalVectorCoordinates e) (I : Set (Fin d)) :
    IsSmoothConnectedClosed (vectorCoordinateSubgroup e he I) := by
  let : Fintype I := Fintype.ofFinite I
  let σ := (Fintype.equivFin I).symm
  refine ⟨VectorGroup.groupScheme (CommRingCat.of k) (Fintype.card I),
    vectorCoordinateBlockInclusion e I σ he,
    isRepresentedBy_vectorCoordinateBlockInclusion e I σ he,
    isClosedSubgroup_vectorCoordinateBlockInclusion e I σ he, ?_, ?_⟩
  · apply Corepresented.smooth_groupScheme_iff.mpr
    infer_instance
  · change ConnectedSpace (Spec (CommRingCat.of
      (MvPolynomial (Fin (Fintype.card I)) k)))
    infer_instance

end Langlands.GroupScheme.RelativeRoot
