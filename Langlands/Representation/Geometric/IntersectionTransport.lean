import Langlands.Representation.Geometric.WeylDefinitions
import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-! Actual Weyl transport between the two product-Levi intersections. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear CategoryTheory

universe uF uV uW

variable (F : Type uF) [CommRing F] {n : ℕ}
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))

/-- Conjugate a source intersection element and recover its actual target
product-Levi coordinates. -/
def intersectionLeviMap : sourceLevi F B C w →* C.Levi F :=
  (C.leviEquiv F).symm.toMonoidHom.comp
    (((conjugatedLeviMap F B w).comp (sourceLevi F B C w).subtype).codRestrict
      (C.leviSubgroup F) (fun m => m.property))

/-- The coordinate map is the prescribed matrix conjugation. -/
theorem intersectionLeviMap_embedding (m : sourceLevi F B C w) :
    C.leviEmbedding F (intersectionLeviMap F B C w m) =
      permutation n F w * B.leviEmbedding F m.val * (permutation n F w)⁻¹ := by
  let t : C.leviSubgroup F := ⟨conjugatedLeviMap F B w m.val, m.property⟩
  change ((C.leviEquiv F) ((C.leviEquiv F).symm t) : GeneralLinear n F) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- The conjugate belongs to the target intersection, with inverse permutation
used in its definition. -/
theorem intersectionLeviMap_mem (m : sourceLevi F B C w) :
    intersectionLeviMap F B C w m ∈ sourceLevi F C B w⁻¹ := by
  change conjugatedLeviMap F C w⁻¹ (intersectionLeviMap F B C w m) ∈ B.leviSubgroup F
  change permutation n F w⁻¹ * C.leviEmbedding F (intersectionLeviMap F B C w m) *
    (permutation n F w⁻¹)⁻¹ ∈ B.leviSubgroup F
  rw [intersectionLeviMap_embedding]
  simp only [map_inv, inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  exact ⟨m.val, rfl⟩

/-- Conjugation as a homomorphism between the actual intersection subgroups. -/
def intersectionLeviHom : sourceLevi F B C w →* sourceLevi F C B w⁻¹ :=
  (intersectionLeviMap F B C w).codRestrict _ (intersectionLeviMap_mem F B C w)

/-- Inverse conjugation recovers the source element. -/
theorem intersectionLeviHom_inverse (m : sourceLevi F B C w) :
    (intersectionLeviHom F C B w⁻¹ (intersectionLeviHom F B C w m)).val = m.val := by
  apply B.leviEmbedding_injective F
  change B.leviEmbedding F (intersectionLeviMap F C B w⁻¹
    (intersectionLeviHom F B C w m)) = _
  rw [intersectionLeviMap_embedding]
  change permutation n F w⁻¹ * C.leviEmbedding F (intersectionLeviMap F B C w m) *
    (permutation n F w⁻¹)⁻¹ = _
  rw [intersectionLeviMap_embedding]
  simp only [map_inv, inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

/-- The actual group equivalence `M ∩ w⁻¹ N ≃ w M ∩ N`, in the existing
product-Levi coordinates on both sides. -/
def intersectionLeviConjugation :
    sourceLevi F B C w ≃* sourceLevi F C B w⁻¹ where
  toFun := intersectionLeviHom F B C w
  invFun m := ⟨(intersectionLeviHom F C B w⁻¹ m).val, by
    simpa only [inv_inv] using (intersectionLeviHom F C B w⁻¹ m).property⟩
  left_inv m := Subtype.ext (intersectionLeviHom_inverse F B C w m)
  right_inv m := by
    apply Subtype.ext
    apply C.leviEmbedding_injective F
    change C.leviEmbedding F (intersectionLeviMap F B C w _) = _
    rw [intersectionLeviMap_embedding]
    change permutation n F w * B.leviEmbedding F (intersectionLeviMap F C B w⁻¹ m) *
      (permutation n F w)⁻¹ = _
    rw [intersectionLeviMap_embedding]
    simp only [map_inv, inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  map_mul' := (intersectionLeviHom F B C w).map_mul

@[simp]
theorem intersectionLeviConjugation_embedding (m : sourceLevi F B C w) :
    C.leviEmbedding F (intersectionLeviConjugation F B C w m).val =
      permutation n F w * B.leviEmbedding F m.val * (permutation n F w)⁻¹ :=
  intersectionLeviMap_embedding F B C w m

/-- Inverse transport is inverse matrix conjugation on the embedded groups. -/
theorem intersectionLeviConjugation_symm_embedding (m : sourceLevi F C B w⁻¹) :
    B.leviEmbedding F ((intersectionLeviConjugation F B C w).symm m).val =
      (permutation n F w)⁻¹ * C.leviEmbedding F m.val * permutation n F w := by
  change B.leviEmbedding F (intersectionLeviMap F C B w⁻¹ m) = _
  rw [intersectionLeviMap_embedding]
  simp only [map_inv, inv_inv]

section Topology

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- Continuity of the target coordinate map. -/
theorem continuous_intersectionLeviMap : Continuous (intersectionLeviMap F B C w) := by
  have h : Continuous (fun m : sourceLevi F B C w =>
      (⟨conjugatedLeviMap F B w m.val, m.property⟩ : C.leviSubgroup F)) := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul
      ((B.leviEmbeddingContinuous F).continuous.comp continuous_subtype_val)).mul continuous_const
  exact (C.leviEquivContinuous F).symm.continuous.comp h

/-- Both actual conjugation maps are continuous for the product and subgroup
topologies inherited from the matrix groups. -/
def intersectionLeviConjugationContinuous :
    sourceLevi F B C w ≃ₜ* sourceLevi F C B w⁻¹ where
  toMulEquiv := intersectionLeviConjugation F B C w
  continuous_toFun := (continuous_intersectionLeviMap F B C w).subtype_mk _
  continuous_invFun := (continuous_intersectionLeviMap F C B w⁻¹).subtype_mk _

end Topology

variable {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- BZ77 transport uses inverse conjugation in the action. -/
def intersectionTransport (ρ : Representation ℂ (sourceLevi F B C w) V) :
    Representation ℂ (sourceLevi F C B w⁻¹) V :=
  ρ.comp (intersectionLeviConjugation F B C w).symm.toMonoidHom

@[simp]
theorem intersectionTransport_apply
    (ρ : Representation ℂ (sourceLevi F B C w) V)
    (m : sourceLevi F C B w⁻¹) (v : V) :
    intersectionTransport F B C w ρ m v =
      ρ ((intersectionLeviConjugation F B C w).symm m) v := rfl

/-- Transport an intertwiner without changing its underlying linear map. -/
def intersectionTransportMap
    {ρ : Representation ℂ (sourceLevi F B C w) V}
    {σ : Representation ℂ (sourceLevi F B C w) W} (f : ρ.IntertwiningMap σ) :
    (intersectionTransport F B C w ρ).IntertwiningMap (intersectionTransport F B C w σ) where
  toLinearMap := f.toLinearMap
  isIntertwining' m := f.isIntertwining' ((intersectionLeviConjugation F B C w).symm m)

@[simp]
theorem intersectionTransportMap_apply
    {ρ : Representation ℂ (sourceLevi F B C w) V}
    {σ : Representation ℂ (sourceLevi F B C w) W}
    (f : ρ.IntertwiningMap σ) (v : V) :
    intersectionTransportMap F B C w f v = f v := rfl

section Smooth

variable [TopologicalSpace F] [IsTopologicalRing F]

theorem isSmooth_intersectionTransport
    {ρ : Representation ℂ (sourceLevi F B C w) V} (hρ : IsSmooth ρ) :
    IsSmooth (intersectionTransport F B C w ρ) :=
  isSmooth_comp (intersectionLeviConjugation F B C w).symm.toMonoidHom
    (intersectionLeviConjugationContinuous F B C w).symm.continuous hρ

/-- The actual Weyl transport functor for the geometric-lemma middle term. -/
def intersectionTransportFunctor :
    SmoothRep.{0, uF, uV} ℂ (sourceLevi F B C w) ⥤
      SmoothRep.{0, uF, uV} ℂ (sourceLevi F C B w⁻¹) where
  obj A := SmoothRep.of (intersectionTransport F B C w A.representation)
    (isSmooth_intersectionTransport F B C w A.isSmooth)
  map f := SmoothRep.ofHom (intersectionTransportMap F B C w (SmoothRep.hom f))
  map_id _ := rfl
  map_comp _ _ := rfl

end Smooth

end Langlands.Geometric
