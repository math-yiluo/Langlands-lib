import Langlands.Geometry.FormalGroup.FiniteKernel
import Langlands.Geometry.FormalGroup.OrderActionCentralScalars

/-! # Actual isogeny numerators with the central scalar law -/

noncomputable section

universe u v w c

namespace Langlands.FormalGroup.ModuleLaw.OrderAction

open CategoryTheory

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {C : Type c} [CommRing C] [Algebra C D] [Algebra C R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {E : OrderAction D M} {G : OrderAction D N}
variable {hs : ∀ (a : C) (x : σ → R),
  E.fiberTangent (RingHom.id R) (algebraMap C D a) x = algebraMap C R a • x}
variable {ht : ∀ (a : C) (x : τ → R),
  G.fiberTangent (RingHom.id R) (algebraMap C D a) x = algebraMap C R a • x}

/-- The coefficient extension of a formal order action to a test algebra. -/
abbrev overAlgebra (E : OrderAction D M) (B : CommAlgCat.{v} R) :=
  E.map (IsScalarTower.toAlgHom O R B)

include hs in
/-- A structural central tangent identity extends to the test algebra. -/
theorem centralTangent_overAlgebra (B : CommAlgCat.{v} R) (a : C) (x : σ → B) :
    (E.overAlgebra B).fiberTangent (RingHom.id B) (algebraMap C D a) x = algebraMap C B a • x := by
  rw [fiberTangent_map, RingHom.id_comp]
  have h := (E.centralOrder hs).fiberTangent_scalar (algebraMap R B) a x
  rw [centralOrder_fiberTangent] at h
  exact h

namespace Hom

variable (f : Hom E G)

/-- The same order-linear map has the same actual kernels after changing central scalars. -/
def centralScalarsKernelIso :
    f.val.kernelSetFunctor ≅ (f.centralScalars (h := hs) (h' := ht)).val.kernelSetFunctor :=
  NatIso.ofComponents (fun _ => (Equiv.refl _).toIso) (fun _ => rfl)

/-- Finite locally free kernels and actual local lifting transfer to the central formal law. -/
theorem centralScalars_isIsogeny (hf : f.val.IsIsogeny) :
    (f.centralScalars (h := hs) (h' := ht)).val.IsIsogeny := by
  refine ⟨hf.1, ?_⟩
  obtain ⟨K⟩ := hf.2
  exact ⟨{
    coordinateAlgebra := K.coordinateAlgebra
    finite := K.finite
    projective := K.projective
    represents := K.represents.ofIso (f.centralScalarsKernelIso (hs := hs) (ht := ht)) }⟩

variable (B : CommAlgCat.{v} R)

/-- Change the central scalars of an actual order-linear map over a test algebra. -/
def centralScalarsOverAlgebra (g : Hom (E.overAlgebra B) (G.overAlgebra B)) :
    Hom ((E.centralOrder hs).overAlgebra B) ((G.centralOrder ht).overAlgebra B) :=
  g.centralScalars (h := centralTangent_overAlgebra (hs := hs) B)
    (h' := centralTangent_overAlgebra (hs := ht) B)

@[simp]
theorem centralScalarsOverAlgebra_coordinates (g : Hom (E.overAlgebra B) (G.overAlgebra B)) :
    (g.centralScalarsOverAlgebra (hs := hs) (ht := ht) B).val.toHom.toCoordinateMap =
      g.val.toHom.toCoordinateMap := rfl

/-- Changing the scalar law on a test algebra preserves isogeny. -/
theorem centralScalarsOverAlgebra_isIsogeny (g : Hom (E.overAlgebra B) (G.overAlgebra B))
    (hg : g.val.IsIsogeny) : (g.centralScalarsOverAlgebra (hs := hs) (ht := ht) B).val.IsIsogeny :=
  g.centralScalars_isIsogeny hg

end Hom

end Langlands.FormalGroup.ModuleLaw.OrderAction
