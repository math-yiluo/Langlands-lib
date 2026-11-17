import Langlands.GroupScheme.HomScheme.SplitTorusRangeKernel
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable

/-! # Homomorphisms from diagonalizable groups as Hopf points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.HomScheme.DiagonalizablePoint

open Langlands.FiniteBialgebraHom FiniteSource FiniteDiagonalizable

variable (R : Type u) [CommRing R] (Λ : Type u) [AddCommGroup Λ]

/-- The Hopf spectrum of the group algebra `R[Λ]` is the diagonalizable group `D(Λ)` over
`Spec R`. -/
def diagonalizableHopfIso :
    hopfGroup R (AddMonoidAlgebra R Λ) ≅
      RelativeMultiplicativeType.diagonalizable (Spec (CommRingCat.of R)) Λ :=
  Diagonalizable.hopfSpecIso (CommRingCat.of R) Λ ≪≫
    Diagonalizable.relativeModelIso (CommRingCat.of R) Λ

variable {R Λ} (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]

/-- Homomorphisms from the diagonalizable group `D(Λ)` to `G` after base change to `Spec C`
are Hopf points `O(G) → C ⊗[R] R[Λ]`. -/
def diagPointEquiv (C : Type u) [CommRing C] [Algebra R C] :
    RelativeHom (RelativeMultiplicativeType.diagonalizable (Spec (CommRingCat.of R)) Λ) G
        (specOver R C) ≃
      {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R Λ //
        IsHopfPoint R f} :=
  (transportEquiv (diagonalizableHopfIso R Λ).symm (coordinateIso G) (specOver R C)).symm.trans
    (pointEquiv _ _ C)

variable {G}

theorem diagPointEquiv_symm_apply {C : Type u} [CommRing C] [Algebra R C]
    (f : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R Λ //
      IsHopfPoint R f}) :
    (diagPointEquiv G C).symm f =
      transport (diagonalizableHopfIso R Λ).symm (coordinateIso G) ((pointEquiv _ _ C).symm f) :=
  rfl

/-- Naturality: evaluation along `Spec D ⟶ Spec C` pushes the Hopf point forward along
`C → D`. -/
theorem evaluate_diagPointEquiv_symm {C D : Type u} [CommRing C] [Algebra R C] [CommRing D]
    [Algebra R D] (g : C →ₐ[R] D)
    (f : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R Λ //
      IsHopfPoint R f}) :
    evaluate (specMap g) ((diagPointEquiv G C).symm f) =
      (diagPointEquiv G D).symm ⟨pushPoint R g f.1, f.2.pushPoint R g⟩ := by
  rw [diagPointEquiv_symm_apply, evaluate_transport, evaluate_specMap]
  rfl

/-- Naturality, read on Hopf points. -/
theorem diagPointEquiv_evaluate {C D : Type u} [CommRing C] [Algebra R C] [CommRing D]
    [Algebra R D] (g : C →ₐ[R] D)
    (j : RelativeHom (RelativeMultiplicativeType.diagonalizable (Spec (CommRingCat.of R)) Λ) G
      (specOver R C)) :
    (diagPointEquiv G D (evaluate (specMap g) j)).1 =
      pushPoint R g (diagPointEquiv G C j).1 := by
  obtain ⟨f, rfl⟩ := (diagPointEquiv G C).symm.surjective j
  rw [evaluate_diagPointEquiv_symm, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The homomorphism attached to a Hopf point is a closed immersion exactly when the
`C`-linear extension `C ⊗[R] O(G) → C ⊗[R] R[Λ]` of the point is surjective. -/
theorem isClosedSubgroup_diagPointEquiv_symm_iff {C : Type u} [CommRing C] [Algebra R C]
    (f : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R Λ //
      IsHopfPoint R f}) :
    IsClosedSubgroup ((diagPointEquiv G C).symm f) ↔
      Function.Surjective (AlgHom.liftEquiv R C _ _ f.1) := by
  rw [diagPointEquiv_symm_apply, isClosedSubgroup_transport_iff,
    isClosedSubgroup_pointEquiv_symm_iff]

/-- Range compatibility: evaluating along `Spec D ⟶ Spec C` gives the range of the
homomorphism of the pushed-forward Hopf point. -/
theorem evaluate_diagPointEquiv_symm_eq_range {C D : Type u} [CommRing C] [Algebra R C]
    [CommRing D] [Algebra R D] (g : C →ₐ[R] D)
    (f : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R Λ //
      IsHopfPoint R f}) :
    TorusSubgroupModuli.evaluate ((diagPointEquiv G C).symm f) (specMap g) =
      SubgroupFunctor.range ((diagPointEquiv G D).symm
        ⟨pushPoint R g f.1, f.2.pushPoint R g⟩) := by
  rw [evaluate_eq_range, evaluate_diagPointEquiv_symm]

variable {Λ' : Type u} [AddCommGroup Λ']

/-- Kernel criterion for inclusion of ranges of homomorphisms from two diagonalizable
groups. -/
theorem range_diagPointEquiv_symm_le_iff_ker₂ {C : Type u} [CommRing C] [Algebra R C]
    (f : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R Λ //
      IsHopfPoint R f})
    (f' : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R Λ' //
      IsHopfPoint R f})
    (hf : Function.Surjective (AlgHom.liftEquiv R C _ _ f.1)) :
    SubgroupFunctor.range ((diagPointEquiv G C).symm f') ≤
        SubgroupFunctor.range ((diagPointEquiv G C).symm f) ↔
      RingHom.ker (AlgHom.liftEquiv R C _ _ f.1) ≤
        RingHom.ker (AlgHom.liftEquiv R C _ _ f'.1) := by
  rw [diagPointEquiv_symm_apply, diagPointEquiv_symm_apply, range_transport_le_iff₂,
    range_pointEquiv_symm_le_iff_ker₂ f f' hf]

/-- Two closed homomorphisms from diagonalizable groups have the same range exactly when the
kernels of the linear extensions of their Hopf points agree. -/
theorem range_diagPointEquiv_symm_eq_iff_ker₂ {C : Type u} [CommRing C] [Algebra R C]
    (f : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R Λ //
      IsHopfPoint R f})
    (f' : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R Λ' //
      IsHopfPoint R f})
    (hf : Function.Surjective (AlgHom.liftEquiv R C _ _ f.1))
    (hf' : Function.Surjective (AlgHom.liftEquiv R C _ _ f'.1)) :
    SubgroupFunctor.range ((diagPointEquiv G C).symm f) =
        SubgroupFunctor.range ((diagPointEquiv G C).symm f') ↔
      RingHom.ker (AlgHom.liftEquiv R C _ _ f.1) =
        RingHom.ker (AlgHom.liftEquiv R C _ _ f'.1) := by
  rw [le_antisymm_iff, le_antisymm_iff, range_diagPointEquiv_symm_le_iff_ker₂ f' f hf',
    range_diagPointEquiv_symm_le_iff_ker₂ f f' hf]
  exact and_comm

/-- Same-lattice form of `range_diagPointEquiv_symm_eq_iff_ker₂`. -/
theorem range_diagPointEquiv_symm_eq_iff_ker {C : Type u} [CommRing C] [Algebra R C]
    (f f' : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R Λ //
      IsHopfPoint R f})
    (hf : Function.Surjective (AlgHom.liftEquiv R C _ _ f.1))
    (hf' : Function.Surjective (AlgHom.liftEquiv R C _ _ f'.1)) :
    SubgroupFunctor.range ((diagPointEquiv G C).symm f) =
        SubgroupFunctor.range ((diagPointEquiv G C).symm f') ↔
      RingHom.ker (AlgHom.liftEquiv R C _ _ f.1) =
        RingHom.ker (AlgHom.liftEquiv R C _ _ f'.1) :=
  range_diagPointEquiv_symm_eq_iff_ker₂ f f' hf hf'

end Langlands.GroupScheme.HomScheme.DiagonalizablePoint
