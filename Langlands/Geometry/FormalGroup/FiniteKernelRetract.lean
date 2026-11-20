import Langlands.Geometry.FormalGroup.FormalIdempotentImage
import Langlands.Geometry.FormalGroup.PiDivisible

/-! # Finite kernels under actual formal retractions -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.Hom

open CategoryTheory

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ σ' τ' : Type} [Finite σ] [Finite τ] [Finite σ'] [Finite τ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'}
variable {f : Hom M N} {g : Hom M' N'}

namespace FiniteKernelModel

/-- A retract of an actual represented kernel is represented by the image of
the corresponding idempotent on its finite projective algebra. -/
def ofKernelRetract (K : FiniteKernelModel f)
    (i : g.kernelSetFunctor ⟶ f.kernelSetFunctor)
    (r : f.kernelSetFunctor ⟶ g.kernelSetFunctor)
    (h : i ≫ r = 𝟙 g.kernelSetFunctor) : FiniteKernelModel g := by
  let A := K.coordinateAlgebra
  let E := K.represents
  have hri {T : CommAlgCat.{v} R} (y : g.kernelSetFunctor.obj T) :
      r.app T (i.app T y) = y :=
    congrArg (fun z => z.app T y) h
  let d : A ⟶ A := E.homEquiv.symm (i.app A (r.app A (E.homEquiv (𝟙 A))))
  have hd {T : CommAlgCat.{v} R} (c : A ⟶ T) :
      E.homEquiv (d ≫ c) = i.app T (r.app T (E.homEquiv c)) := by
    rw [E.homEquiv_comp]
    have hdA : E.homEquiv d = i.app A (r.app A (E.homEquiv (𝟙 A))) :=
      E.homEquiv.apply_symm_apply _
    rw [hdA, ← i.naturality_apply, ← r.naturality_apply, ← E.homEquiv_eq]
  have hdd : d ≫ d = d := by
    apply E.homEquiv.injective
    rw [hd]
    have hdA : E.homEquiv d = i.app A (r.app A (E.homEquiv (𝟙 A))) :=
      E.homEquiv.apply_symm_apply _
    rw [hdA, hri]
  let B : CommAlgCat.{v} R := CommAlgCat.of R d.hom.range
  let project : A ⟶ B := CommAlgCat.ofHom d.hom.rangeRestrict
  let inclusion : B ⟶ A := CommAlgCat.ofHom (Subalgebra.val d.hom.range)
  have hpi : project ≫ inclusion = d := by
    apply CommAlgCat.hom_ext
    exact d.hom.val_comp_rangeRestrict
  have hip : inclusion ≫ project = 𝟙 B := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    apply Subtype.ext
    obtain ⟨y, hy⟩ := x.property
    change d.hom x.val = x.val
    rw [← hy]
    exact congrArg (fun c : A ⟶ A => c.hom y) hdd
  refine {
    coordinateAlgebra := B
    finite := Module.Finite.of_surjective project.hom.toLinearMap d.hom.rangeRestrict_surjective
    projective := Module.Projective.of_split inclusion.hom.toLinearMap project.hom.toLinearMap
      (congrArg (fun c : B ⟶ B => c.hom.toLinearMap) hip)
    represents := {
      homEquiv := {
        toFun c := r.app _ (E.homEquiv (project ≫ c))
        invFun y := inclusion ≫ E.homEquiv.symm (i.app _ y)
        left_inv c := by
          change inclusion ≫ E.homEquiv.symm (i.app _ (r.app _ (E.homEquiv (project ≫ c)))) = c
          rw [← hd, Equiv.symm_apply_apply, ← hpi]
          simp only [← Category.assoc, hip, Category.id_comp]
        right_inv y := by
          change r.app _ (E.homEquiv (project ≫ (inclusion ≫ E.homEquiv.symm (i.app _ y)))) = y
          rw [← Category.assoc, hpi, hd, Equiv.apply_symm_apply, hri, hri]
      }
      homEquiv_comp := fun c b => by
        change r.app _ (E.homEquiv (project ≫ (b ≫ c))) =
          g.kernelSetFunctor.map c (r.app _ (E.homEquiv (project ≫ b)))
        rw [← Category.assoc, E.homEquiv_comp, r.naturality_apply]
    }
  }

end FiniteKernelModel

namespace IdempotentImage

variable {e : Hom M M} {d : Hom N N}
variable (A : IdempotentImage e M') (B : IdempotentImage d N')
variable (f : Hom M N) (hf : f.comp e = d.comp f)

include hf in
private theorem restrictHom_comp_projection :
    (A.restrictHom B f).comp A.projection = B.projection.comp f := by
  rw [restrictHom, comp_assoc B.projection, comp_assoc f, A.inclusion_projection,
    hf, ← comp_assoc B.projection, B.projection_projector]

private def kernelInclusion :
    (A.restrictHom B f).kernelPointFunctor ⟶ f.kernelPointFunctor :=
  f.kernelLift ((A.restrictHom B f).kernelι ≫ A.inclusion.algebraPointNatTrans) (by
    apply NatTrans.ext
    funext T
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (A.restrictHom B f).kernelPoints T at x
    change f.onAlgebraPoints (A.inclusion.onAlgebraPoints x.val) = 0
    rw [← onAlgebraPoints_comp, ← A.inclusion_restrictHom B f hf, onAlgebraPoints_comp,
      x.property, map_zero])

private def kernelProjection :
    f.kernelPointFunctor ⟶ (A.restrictHom B f).kernelPointFunctor :=
  (A.restrictHom B f).kernelLift (f.kernelι ≫ A.projection.algebraPointNatTrans) (by
    apply NatTrans.ext
    funext T
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change f.kernelPoints T at x
    change (A.restrictHom B f).onAlgebraPoints (A.projection.onAlgebraPoints x.val) = 0
    rw [← onAlgebraPoints_comp, A.restrictHom_comp_projection B f hf, onAlgebraPoints_comp,
      x.property, map_zero])

/-- The kernel of the restricted map is a represented direct summand of the ambient kernel. -/
def restrictHom_finiteKernelModel (K : FiniteKernelModel f) :
    FiniteKernelModel (A.restrictHom B f) :=
  K.ofKernelRetract
    (Functor.whiskerRight (A.kernelInclusion B f hf) (forget (ModuleCat.{v} O)))
    (Functor.whiskerRight (A.kernelProjection B f hf) (forget (ModuleCat.{v} O))) (by
      apply NatTrans.ext
      funext T
      apply (TypeCat.homEquiv).injective
      funext x
      change (A.restrictHom B f).kernelPoints T at x
      apply Subtype.ext
      change A.projection.onAlgebraPoints (A.inclusion.onAlgebraPoints x.val) = x.val
      rw [← onAlgebraPoints_comp, A.projection_inclusion, onAlgebraPoints_id])

include hf in
/-- Project an ambient fppf lift of the included point to obtain a lift in the image. -/
theorem restrictHom_isFppfLocallySurjective (h : f.IsFppfLocallySurjective) :
    (A.restrictHom B f).IsFppfLocallySurjective := by
  intro T y
  obtain ⟨S, φ, hFlat, hFinite, x, hx⟩ := h T (B.inclusion.onAlgebraPoints y)
  refine ⟨S, φ, hFlat, hFinite, A.projection.onAlgebraPoints x, ?_⟩
  rw [← onAlgebraPoints_comp, A.restrictHom_comp_projection B f hf, onAlgebraPoints_comp, hx,
    B.inclusion.onAlgebraPoints_natural, ← onAlgebraPoints_comp, B.projection_inclusion,
    onAlgebraPoints_id]

include hf in
/-- Restriction to the actual splitting preserves the integral isogeny condition. -/
theorem restrictHom_isIsogeny (h : f.IsIsogeny) : (A.restrictHom B f).IsIsogeny :=
  ⟨A.restrictHom_isFppfLocallySurjective B f hf h.1,
    h.2.elim fun K => ⟨A.restrictHom_finiteKernelModel B f hf K⟩⟩

private theorem restrictHom_scalarHom (a : O) :
    A.restrictHom A (M.scalarHom a) = M'.scalarHom a := by
  simp only [restrictHom, scalarHom, smul_comp, comp_smul, id_comp, A.projection_inclusion]

include A in
/-- An actual formal idempotent image of a scalar-divisible law is scalar-divisible. -/
theorem isPiDivisible {π : O} (hM : M.IsPiDivisible π) : M'.IsPiDivisible π := by
  refine ⟨hM.base_nilpotent, ?_, ?_, ?_⟩
  · intro T x
    obtain ⟨n, hn⟩ := hM.torsion T (A.inclusion.onAlgebraPoints x)
    refine ⟨n, ?_⟩
    have h := congrArg A.projection.onAlgebraPoints hn
    rw [map_smul, map_zero, ← onAlgebraPoints_comp, A.projection_inclusion, onAlgebraPoints_id] at h
    exact h
  · rw [← A.restrictHom_scalarHom π]
    exact A.restrictHom_isFppfLocallySurjective A _ (e.comp_scalarHom π).symm
      hM.scalar_locallySurjective
  · intro n
    rw [← A.restrictHom_scalarHom (π ^ n)]
    obtain ⟨K⟩ := hM.scalarPower_finiteKernel n
    exact ⟨A.restrictHom_finiteKernelModel A _ (e.comp_scalarHom (π ^ n)).symm K⟩

end IdempotentImage

end Langlands.FormalGroup.ModuleLaw.Hom
