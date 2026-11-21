import Langlands.Geometry.FormalGroup.FormalIdempotentImage
import Langlands.Geometry.FormalGroup.FormalIdempotentLinearization
import Langlands.Geometry.FormalGroup.ModuleHomOfPoints

/-! # Group laws on actual formal idempotent images -/

noncomputable section

universe u

namespace Langlands.FormalGroup.CoordinateMap.IdempotentCoordinates

open CoordinateMap

variable {R : Type u} [CommRing R]
variable {σ τ κ : Type} [Finite σ] [Finite τ]
variable {G : CommLaw R σ} {e : CommLaw.Hom G G}
variable (C : IdempotentCoordinates e.toCoordinateMap τ)

private abbrev includePoint (x : SeriesPoint R τ κ) : G.Point κ :=
  SeriesPoint.eval C.inclusion x

private abbrev projectPoint (x : G.Point κ) : SeriesPoint R τ κ :=
  SeriesPoint.eval C.projection x

private theorem project_include (x : SeriesPoint R τ κ) :
    C.projectPoint (C.includePoint x) = x := by
  change SeriesPoint.eval C.projection (SeriesPoint.eval C.inclusion x) = x
  rw [← SeriesPoint.eval_comp, C.projection_inclusion, SeriesPoint.eval_id]

private theorem include_project (x : G.Point κ) :
    C.includePoint (C.projectPoint x) = e.onPoints x := by
  change SeriesPoint R σ κ at x
  change SeriesPoint.eval C.inclusion (SeriesPoint.eval C.projection x) =
    SeriesPoint.eval e.toCoordinateMap x
  rw [← SeriesPoint.eval_comp, C.inclusion_projection]

private theorem include_injective : Function.Injective (C.includePoint (κ := κ)) :=
  Function.LeftInverse.injective (C.project_include (κ := κ))

private theorem include_fixed (x : SeriesPoint R τ κ) :
    e.onPoints (C.includePoint x) = C.includePoint x := by
  rw [← C.include_project, C.project_include]

private theorem include_zero : C.includePoint (SeriesPoint.zero (κ := κ)) = 0 :=
  SeriesPoint.eval_at_zero C.inclusion

omit [Finite σ] [Finite τ] in
private theorem exists_pair {α β : Type} [Finite α] [Finite β]
    (z : SeriesPoint R (α ⊕ β) κ) :
    ∃ x : SeriesPoint R α κ, ∃ y : SeriesPoint R β κ, z = x.pair y :=
  ⟨SeriesPoint.eval fst z, SeriesPoint.eval snd z, (SeriesPoint.pair_eval_fst_snd z).symm⟩

private def imageAddition : CoordinateMap R (τ ⊕ τ) τ :=
  C.projection.comp (G.addition.comp ((C.inclusion.comp fst).pair (C.inclusion.comp snd)))

private def imageInverse : CoordinateMap R τ τ :=
  C.projection.comp (G.inverse.comp C.inclusion)

private theorem include_eval_addition (x y : SeriesPoint R τ κ) :
    C.includePoint (SeriesPoint.eval C.imageAddition (x.pair y)) =
      C.includePoint x + C.includePoint y := by
  have h : SeriesPoint.eval C.imageAddition (x.pair y) =
      C.projectPoint (C.includePoint x + C.includePoint y) := by
    simp only [imageAddition, SeriesPoint.eval_comp, SeriesPoint.eval_pair, SeriesPoint.eval_fst,
      SeriesPoint.eval_snd]
    rfl
  rw [h, C.include_project, map_add, C.include_fixed, C.include_fixed]

private theorem include_eval_inverse (x : SeriesPoint R τ κ) :
    C.includePoint (SeriesPoint.eval C.imageInverse x) = -C.includePoint x := by
  have h : SeriesPoint.eval C.imageInverse x = C.projectPoint (-C.includePoint x) := by
    simp only [imageInverse, SeriesPoint.eval_comp]
    rfl
  rw [h, C.include_project, map_neg, C.include_fixed]

/-- Restrict the actual formal addition and inverse to the image coordinates. -/
def imageLaw : CommLaw R τ where
  addition := C.imageAddition
  inverse := C.imageInverse
  zero_add := by
    apply CoordinateMap.ext_eval
    intro x
    apply C.include_injective
    simp only [SeriesPoint.eval_comp, SeriesPoint.eval_pair, SeriesPoint.eval_zero,
      SeriesPoint.eval_id, C.include_eval_addition, C.include_zero, zero_add]
  add_zero := by
    apply CoordinateMap.ext_eval
    intro x
    apply C.include_injective
    simp only [SeriesPoint.eval_comp, SeriesPoint.eval_pair, SeriesPoint.eval_zero,
      SeriesPoint.eval_id, C.include_eval_addition, C.include_zero, add_zero]
  add_assoc := by
    apply CoordinateMap.ext_eval
    intro p
    obtain ⟨xy, z, rfl⟩ := exists_pair p
    obtain ⟨x, y, rfl⟩ := exists_pair xy
    apply C.include_injective
    simp only [SeriesPoint.eval_comp, SeriesPoint.eval_pair, SeriesPoint.eval_fst,
      SeriesPoint.eval_snd, C.include_eval_addition, _root_.add_assoc]
  add_comm := by
    apply CoordinateMap.ext_eval
    intro p
    obtain ⟨x, y, rfl⟩ := exists_pair p
    apply C.include_injective
    simp only [SeriesPoint.eval_comp, SeriesPoint.eval_pair, SeriesPoint.eval_fst,
      SeriesPoint.eval_snd, C.include_eval_addition, _root_.add_comm]
  neg_add := by
    apply CoordinateMap.ext_eval
    intro x
    apply C.include_injective
    simp only [SeriesPoint.eval_comp, SeriesPoint.eval_pair, SeriesPoint.eval_id,
      SeriesPoint.eval_zero, C.include_eval_addition, C.include_eval_inverse,
      C.include_zero, neg_add_cancel]

/-- The actual coordinate inclusion is a formal group homomorphism. -/
def imageInclusion : CommLaw.Hom C.imageLaw G where
  toCoordinateMap := C.inclusion
  map_add := by
    apply CoordinateMap.ext_eval
    intro p
    obtain ⟨x, y, rfl⟩ := exists_pair p
    simp only [SeriesPoint.eval_comp, SeriesPoint.eval_pair, SeriesPoint.eval_fst,
      SeriesPoint.eval_snd]
    exact C.include_eval_addition x y

/-- The actual coordinate projection is a formal group homomorphism. -/
def imageProjection : CommLaw.Hom G C.imageLaw where
  toCoordinateMap := C.projection
  map_add := by
    have hp : C.projection.comp e.toCoordinateMap = C.projection := by
      calc
        _ = C.projection.comp (C.inclusion.comp C.projection) :=
          congrArg (fun f : CoordinateMap R σ σ => C.projection.comp f) C.inclusion_projection.symm
        _ = _ := by rw [← comp_assoc, C.projection_inclusion, id_comp]
    change C.projection.comp G.addition =
      C.imageAddition.comp ((C.projection.comp fst).pair (C.projection.comp snd))
    simp only [imageAddition, comp_assoc, pair_comp, fst_pair, snd_pair]
    simp only [← comp_assoc C.inclusion C.projection, C.inclusion_projection]
    rw [← e.map_add, ← comp_assoc C.projection, hp]

@[simp]
theorem imageProjection_comp_inclusion :
    C.imageProjection.comp C.imageInclusion = CommLaw.Hom.id C.imageLaw :=
  CommLaw.Hom.ext C.projection_inclusion

@[simp]
theorem imageInclusion_comp_projection : C.imageInclusion.comp C.imageProjection = e :=
  CommLaw.Hom.ext C.inclusion_projection

section ModuleLaw

variable {O : Type*} [CommRing O] [Algebra O R]
variable {M : ModuleLaw O R σ} {b : ModuleLaw.Hom M M}
variable (A : IdempotentCoordinates b.toHom.toCoordinateMap τ)

private def imageScalar (a : O) : CommLaw.Hom A.imageLaw A.imageLaw :=
  A.imageProjection.comp ((M.action a).comp A.imageInclusion)

private theorem imageInclusion_scalar (a : O) :
    A.imageInclusion.comp (A.imageScalar a) = (M.action a).comp A.imageInclusion := by
  have hi : b.toHom.comp A.imageInclusion = A.imageInclusion := by
    calc
      _ = (A.imageInclusion.comp A.imageProjection).comp A.imageInclusion :=
        congrArg (fun f => f.comp A.imageInclusion) A.imageInclusion_comp_projection.symm
      _ = _ := by rw [CommLaw.Hom.comp_assoc, A.imageProjection_comp_inclusion, CommLaw.Hom.comp_id]
  rw [imageScalar, ← CommLaw.Hom.comp_assoc A.imageInclusion,
    A.imageInclusion_comp_projection, ← CommLaw.Hom.comp_assoc b.toHom, b.commutes,
    CommLaw.Hom.comp_assoc, hi]

private def imageAction : O →+* CommLaw.Hom A.imageLaw A.imageLaw where
  toFun := A.imageScalar
  map_one' := by
    rw [imageScalar, map_one]
    change A.imageProjection.comp ((CommLaw.Hom.id M.groupLaw).comp A.imageInclusion) =
      CommLaw.Hom.id A.imageLaw
    rw [CommLaw.Hom.id_comp, A.imageProjection_comp_inclusion]
  map_zero' := by simp [imageScalar]
  map_add' a c := by simp [imageScalar, CommLaw.Hom.comp_add, CommLaw.Hom.add_comp]
  map_mul' a c := by
    change A.imageProjection.comp ((M.action (a * c)).comp A.imageInclusion) =
      (A.imageProjection.comp ((M.action a).comp A.imageInclusion)).comp (A.imageScalar c)
    rw [map_mul]
    change A.imageProjection.comp (((M.action a).comp (M.action c)).comp A.imageInclusion) = _
    rw [CommLaw.Hom.comp_assoc (M.action a), CommLaw.Hom.comp_assoc A.imageProjection,
      CommLaw.Hom.comp_assoc (M.action a) A.imageInclusion, A.imageInclusion_scalar]

/-- The scalar action on the coordinate image has the required tangent action. -/
def imageModuleLaw : ModuleLaw O R τ where
  groupLaw := A.imageLaw
  action := A.imageAction
  linear_natural a i j := by
    classical
    let : Fintype τ := Fintype.ofFinite τ
    have hscalar (x : τ → R) :
        (A.imageScalar a).toCoordinateMap.linearPart x = (algebraMap O R a) • x := by
      have h := congrArg (fun f : CoordinateMap R τ τ => f.linearPart x) A.projection_inclusion
      simp only [linearPart_comp, linearPart_id, LinearMap.comp_apply, LinearMap.id_apply] at h
      change (A.projection.comp ((M.action a).toCoordinateMap.comp A.inclusion)).linearPart x = _
      simp only [linearPart_comp, LinearMap.comp_apply, M.action_on_tangent, map_smul, h]
    have h := congrFun (hscalar (Pi.single j 1)) i
    simp only [linearPart_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
    change (A.imageScalar a).toCoordinateMap.linearCoeff i j = scalarLinearCoeff _ _ _
    by_cases hij : j = i
    · simpa [scalarLinearCoeff, hij] using h
    · simpa [scalarLinearCoeff, hij, Ne.symm hij] using h

/-- The pointed retraction of the projector is an O-linear formal retraction. -/
def moduleImage : ModuleLaw.Hom.IdempotentImage b A.imageModuleLaw where
  inclusion := ⟨A.imageInclusion, A.imageInclusion_scalar⟩
  projection := ⟨A.imageProjection, by
    intro a
    have hp : A.imageProjection.comp b.toHom = A.imageProjection := by
      calc
        _ = A.imageProjection.comp (A.imageInclusion.comp A.imageProjection) :=
          congrArg (fun f => A.imageProjection.comp f) A.imageInclusion_comp_projection.symm
        _ = _ := by
          rw [← CommLaw.Hom.comp_assoc, A.imageProjection_comp_inclusion, CommLaw.Hom.id_comp]
    change A.imageProjection.comp (M.action a) = (A.imageScalar a).comp A.imageProjection
    rw [imageScalar, CommLaw.Hom.comp_assoc, CommLaw.Hom.comp_assoc (M.action a),
      A.imageInclusion_comp_projection, ← b.commutes, ← CommLaw.Hom.comp_assoc, hp]⟩
  projection_inclusion := ModuleLaw.Hom.ext A.imageProjection_comp_inclusion
  inclusion_projection := ModuleLaw.Hom.ext A.imageInclusion_comp_projection

end ModuleLaw

end Langlands.FormalGroup.CoordinateMap.IdempotentCoordinates

namespace Langlands.FormalGroup.ModuleLaw.Hom.IdempotentImage

variable {O R : Type*} [CommRing O] [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ] {M : ModuleLaw O R σ}

/-- A free presentation of the tangent image constructs an actual formal
O-module law and its projector presentation. -/
def ofTangentRetraction (e : Hom M M) (he : e.comp e = e)
    (j : (τ → R) →ₗ[R] (σ → R)) (r : (σ → R) →ₗ[R] (τ → R))
    (hj : r.comp j = LinearMap.id) (hr : j.comp r = e.tangent) :
    Σ N : ModuleLaw O R τ, IdempotentImage e N :=
  let A := CoordinateMap.IdempotentCoordinates.ofTangentRetraction e.toHom.toCoordinateMap
    (congrArg (fun f : Hom M M => f.toHom.toCoordinateMap) he) j r hj hr
  ⟨A.imageModuleLaw, A.moduleImage⟩

end Langlands.FormalGroup.ModuleLaw.Hom.IdempotentImage
