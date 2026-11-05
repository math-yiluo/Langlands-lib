import Langlands.GroupScheme.Unipotent.PolynomialKernelProduct

/-! # Iterated vector factors of additive polynomial kernels -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace VectorGroup

variable (R : CommRingCat.{u})

/-- The zero-dimensional vector group has a unique point on every relative
scheme test. -/
theorem zero_points_ext {T : Over (Spec R)}
    (x y : T ⟶ (groupScheme R 0).X) : x = y :=
  points_ext fun i => Fin.elim0 i

/-- A product with the zero-dimensional vector group is the second factor. -/
def zeroProductIso (G : GroupScheme (Spec R)) : groupScheme R 0 ⊗ G ≅ G where
  hom := snd _ _
  inv := lift 0 (𝟙 G)
  hom_inv_id := by
    apply hom_ext
    · apply hom_ext_points
      intro T x
      exact zero_points_ext R _ _
    · simp
  inv_hom_id := by simp

end VectorGroup

namespace Unipotent

open OneDimensional RelativeRoot

variable {k : Type u} [Field k]

/-- A polynomial kernel in zero variables has only constant affine-line maps. -/
theorem hasConstantAffineLineMaps_polynomialKernel_zero
    (f : Fin 0 → k[X]) (hf : ∀ i, IsAdditive (f i)) :
    HasConstantAffineLineMaps (kernel (polynomialRow f hf)) := by
  intro a
  refine ⟨η[(kernel (polynomialRow f hf)).X], ?_⟩
  apply (cancel_mono (kernelι (polynomialRow f hf)).hom.hom).mp
  exact VectorGroup.zero_points_ext (CommRingCat.of k) _ _

/-- Iterating additive direct-factor extraction yields a vector factor and a
polynomial-kernel complement with only constant affine-line maps. The two
ambient coordinate counts sum to the original coordinate count. -/
theorem exists_polynomialKernelVectorFactor (n : ℕ)
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i)) :
    ∃ (r m : ℕ) (g : Fin m → k[X]) (hg : ∀ i, IsAdditive (g i)),
      r + m = n ∧ HasConstantAffineLineMaps (kernel (polynomialRow g hg)) ∧
        Nonempty (kernel (polynomialRow f hf) ≅
          VectorGroup.groupScheme (CommRingCat.of k) r ⊗
            kernel (polynomialRow g hg)) := by
  induction n with
  | zero =>
    exact ⟨0, 0, f, hf, rfl, hasConstantAffineLineMaps_polynomialKernel_zero f hf,
      ⟨(VectorGroup.zeroProductIso _ _).symm⟩⟩
  | succ n ih =>
    by_cases h : HasConstantAffineLineMaps (kernel (polynomialRow f hf))
    · exact ⟨0, n + 1, f, hf, Nat.zero_add _, h,
        ⟨(VectorGroup.zeroProductIso _ _).symm⟩⟩
    · obtain ⟨g, hg, ⟨e⟩⟩ :=
        exists_polynomialKernelAdditiveFactor_of_not_hasConstantAffineLineMaps f hf h
      obtain ⟨r, m, q, hq, hrm, hqconst, ⟨d⟩⟩ := ih g hg
      refine ⟨r + 1, m, q, hq, ?_, hqconst, ⟨?_⟩⟩
      · omega
      · exact e ≪≫ (Iso.refl _ ⊗ᵢ d) ≪≫ (α_ _ _ _).symm ≪≫
          ((VectorGroup.splitIso (CommRingCat.of k) (0 : Fin (r + 1))).symm ⊗ᵢ
            Iso.refl _)

end Unipotent

end Langlands.GroupScheme
