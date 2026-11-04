import Langlands.GroupScheme.HopfSpecPoints

/-! # Natural convolution equivalence for affine Hopf-spectrum points -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry WithConv
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HopfSpecPoints

variable {R : CommRingCat.{u}} {C : CommHopfAlgCat.{u} R}
    {A B : CommAlgCat.{u} R}

/-- Convolution algebra points are precisely the actual affine test points of
the Hopf spectrum, with their group multiplication. -/
def specPointMulEquiv :
    WithConv (C →ₐ[R] A) ≃*
      ((algSpec R).obj (op A) ⟶ ((hopfSpec R).obj (op C)).X) where
  toEquiv := Equiv.ofBijective (fun f => specPoint f.ofConv)
    ⟨fun _ _ h => WithConv.ofConv_injective (specPoint_injective h),
      fun x => by
        obtain ⟨f, hf⟩ := exists_specPoint x
        exact ⟨toConv f, hf⟩⟩
  map_mul' f g := by
    change specPoint (f * g).ofConv = specPoint f.ofConv * specPoint g.ofConv
    rw [specPoint_mul]
    congr 1
    apply AlgHom.ext
    intro c
    exact AlgHom.convMul_apply f g c

@[simp]
theorem specPointMulEquiv_apply (f : WithConv (C →ₐ[R] A)) :
    specPointMulEquiv f = specPoint f.ofConv := rfl

/-- The affine-point identification is natural for all coefficient maps. -/
theorem specPoint_precomp (φ : A →ₐ[R] B) (f : C →ₐ[R] A) :
    (algSpec R).map (CommAlgCat.ofHom φ).op ≫ specPoint f =
      specPoint (φ.comp f) := by
  unfold specPoint cogroupPoint
  exact ((algSpec R).map_comp (CommAlgCat.ofHom φ).op
    (CommAlgCat.ofHom f).op).symm

theorem specPointMulEquiv_naturality (φ : A →ₐ[R] B)
    (f : WithConv (C →ₐ[R] A)) :
    (algSpec R).map (CommAlgCat.ofHom φ).op ≫ specPointMulEquiv f =
      specPointMulEquiv (toConv (φ.comp f.ofConv)) :=
  specPoint_precomp φ f.ofConv

end Langlands.GroupScheme.HopfSpecPoints
