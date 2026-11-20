import Langlands.Geometry.FormalGroup.KernelPoints

/-! # Fixed points and coordinate images of formal idempotents -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.Hom

open CategoryTheory

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {S : Type z} [CommRing S] [Algebra O S]
variable {σ τ υ σ' τ' υ' : Type}
variable [Finite σ] [Finite τ] [Finite υ] [Finite σ'] [Finite τ'] [Finite υ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}
variable {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'} {P' : ModuleLaw O R υ'}
variable {T : CommAlgCat.{w} R}

/-- The actual fixed point submodule is the kernel of the endomorphism minus the identity. -/
abbrev fixedPoints (e : Hom M M) (T : CommAlgCat.{w} R) :=
  (e - id M).kernelPoints T

@[simp]
theorem mem_fixedPoints (e : Hom M M) (x : M.AlgebraPoint T) :
    x ∈ e.fixedPoints T ↔ e.onAlgebraPoints x = x := by
  have h : (e - id M).onAlgebraPoints (A := T) =
      e.onAlgebraPoints - (id M).onAlgebraPoints :=
    (onPointsLinear.comp (mapLinear (IsScalarTower.toAlgHom O R T))).map_sub e (id M)
  rw [mem_kernelPoints, h, LinearMap.sub_apply, onAlgebraPoints_id, sub_eq_zero]

/-- The fixed points with the induced maps on coefficient algebras. -/
abbrev fixedPointFunctor (e : Hom M M) : CommAlgCat.{w} R ⥤ ModuleCat.{w} O :=
  (e - id M).kernelPointFunctor

theorem mem_fixedPoints_iff_range (e : Hom M M) (he : e.comp e = e)
    (x : M.AlgebraPoint T) :
    x ∈ e.fixedPoints T ↔ x ∈ LinearMap.range e.onAlgebraPoints := by
  rw [mem_fixedPoints, LinearMap.mem_range]
  refine ⟨fun h => ⟨x, h⟩, ?_⟩
  rintro ⟨y, rfl⟩
  rw [← onAlgebraPoints_comp, he]

/-- A formal law with actual inclusion and projection presenting the image of `e`. -/
structure IdempotentImage (e : Hom M M) (M' : ModuleLaw O R σ') where
  inclusion : Hom M' M
  projection : Hom M M'
  projection_inclusion : projection.comp inclusion = id M'
  inclusion_projection : inclusion.comp projection = e

namespace IdempotentImage

variable {e : Hom M M} {d : Hom N N} {c : Hom P P}

@[simp]
theorem projector_inclusion (A : IdempotentImage e M') :
    e.comp A.inclusion = A.inclusion := by
  calc
    e.comp A.inclusion = (A.inclusion.comp A.projection).comp A.inclusion :=
      congrArg (fun z : Hom M M => z.comp A.inclusion) A.inclusion_projection.symm
    _ = A.inclusion := by rw [comp_assoc, A.projection_inclusion, comp_id]

@[simp]
theorem projection_projector (A : IdempotentImage e M') :
    A.projection.comp e = A.projection := by
  calc
    A.projection.comp e = A.projection.comp (A.inclusion.comp A.projection) :=
      congrArg (fun z : Hom M M => A.projection.comp z) A.inclusion_projection.symm
    _ = A.projection := by rw [← comp_assoc, A.projection_inclusion, id_comp]

/-- A coordinate presentation identifies its points with the actual fixed points. -/
def fixedPointEquiv (A : IdempotentImage e M') (T : CommAlgCat.{w} R) :
    M'.AlgebraPoint T ≃ₗ[O] e.fixedPoints T where
  toFun x := ⟨A.inclusion.onAlgebraPoints x, (mem_fixedPoints _ _).2 (by
    rw [← onAlgebraPoints_comp, A.projector_inclusion])⟩
  invFun y := A.projection.onAlgebraPoints y.val
  left_inv x := by
    change A.projection.onAlgebraPoints (A.inclusion.onAlgebraPoints x) = x
    rw [← onAlgebraPoints_comp, A.projection_inclusion, onAlgebraPoints_id]
  right_inv y := by
    apply Subtype.ext
    change A.inclusion.onAlgebraPoints (A.projection.onAlgebraPoints y.val) = y.val
    rw [← onAlgebraPoints_comp, A.inclusion_projection]
    exact (mem_fixedPoints _ _).1 y.property
  map_add' x y := Subtype.ext (map_add A.inclusion.onAlgebraPoints x y)
  map_smul' a x := Subtype.ext (map_smul A.inclusion.onAlgebraPoints a x)

/-- Coefficient extension preserves the same equations for the image. -/
def map (A : IdempotentImage e M') (φ : R →ₐ[O] S) :
    IdempotentImage (e.map φ) (M'.map φ) where
  inclusion := A.inclusion.map φ
  projection := A.projection.map φ
  projection_inclusion := by rw [← map_comp, A.projection_inclusion, map_id]
  inclusion_projection := by rw [← map_comp, A.inclusion_projection]

/-- The map of coordinate images is the original map between inclusion and projection. -/
def restrictHom (A : IdempotentImage e M') (B : IdempotentImage d N') (f : Hom M N) :
    Hom M' N' :=
  B.projection.comp (f.comp A.inclusion)

theorem inclusion_restrictHom (A : IdempotentImage e M') (B : IdempotentImage d N')
    (f : Hom M N) (hf : f.comp e = d.comp f) :
    B.inclusion.comp (A.restrictHom B f) = f.comp A.inclusion := by
  rw [restrictHom, ← comp_assoc B.inclusion, B.inclusion_projection, ← comp_assoc d,
    ← hf, comp_assoc, A.projector_inclusion]

@[simp]
theorem restrictHom_id (A : IdempotentImage e M') :
    A.restrictHom A (id M) = id M' := by
  rw [restrictHom, id_comp, A.projection_inclusion]

theorem restrictHom_comp (A : IdempotentImage e M') (B : IdempotentImage d N')
    (C : IdempotentImage c P') (g : Hom N P) (f : Hom M N) (hf : f.comp e = d.comp f) :
    A.restrictHom C (g.comp f) = (B.restrictHom C g).comp (A.restrictHom B f) := by
  change C.projection.comp ((g.comp f).comp A.inclusion) =
    (C.projection.comp (g.comp B.inclusion)).comp (A.restrictHom B f)
  rw [comp_assoc C.projection, comp_assoc g, comp_assoc g B.inclusion,
    A.inclusion_restrictHom B f hf]

/-- Two coordinate presentations of the same image have an integral comparison. -/
def iso (A : IdempotentImage e M') (B : IdempotentImage e N') : Iso M' N' where
  hom := A.restrictHom B (id M)
  inv := B.restrictHom A (id M)
  inv_hom := by
    rw [← A.restrictHom_comp B A _ _ (by simp), comp_id, A.restrictHom_id]
  hom_inv := by
    rw [← B.restrictHom_comp A B _ _ (by simp), comp_id, B.restrictHom_id]

end IdempotentImage

end Langlands.FormalGroup.ModuleLaw.Hom
