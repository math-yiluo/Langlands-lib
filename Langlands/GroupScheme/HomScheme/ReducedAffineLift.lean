import Langlands.GroupScheme.AffinePointBaseChangeSmooth
import Langlands.GroupScheme.Lie.NonaffineKernel
import Mathlib.RingTheory.Ideal.Over

/-! # Reductions of affine points through a homomorphism over the reduced base

Let `I` be an ideal of `R`, `r : Spec (R ⧸ I) ⟶ Spec R`, and `f₀ : H_{R/I} ⟶ G_{R/I}` a
homomorphism of the base-changed group schemes. For an `R`-algebra `A` with `J = I A`, a point
`h ∈ H(A)` reduces to `H(A ⧸ J) = H_{R/I}(A ⧸ J)`, is sent by `f₀` to `G_{R/I}(A ⧸ J)`, and is
read back in `G(A ⧸ J)`. This is a group homomorphism `H(A) → G(A ⧸ J)`; if `s : H ⟶ G` is any
morphism over `R` whose base change is `f₀`, it equals reduction of `h ≫ s`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomScheme

variable {R : CommRingCat.{u}} (I : Ideal R) {H G : GroupScheme (Spec R)}
  (f₀ : (GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).obj H ⟶
    (GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).obj G)
  (A : CommAlgCat.{u} R)

/-- Reduce a point of `H` modulo `I A`, apply `f₀` over `R ⧸ I`, and read the result in
`G(A ⧸ I A)`. -/
def reducedAffineHom : H.affinePoints A →* Lie.AffinePoints G (A ⧸ I.map (algebraMap R A)) :=
  (affinePointsBaseChangeMulEquiv R (R ⧸ I) (A ⧸ I.map (algebraMap R A)) G).symm.toMonoidHom.comp
    ((((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).obj H).affinePointsTarget f₀
        (CommAlgCat.of (R ⧸ I) (A ⧸ I.map (algebraMap R A)))).comp
      ((affinePointsBaseChangeMulEquiv R (R ⧸ I) (A ⧸ I.map (algebraMap R A)) H).toMonoidHom.comp
        (Lie.NonaffineKernel.reduction H (I.map (algebraMap R A)))))

/-- **Reductions of lifts**: if `s` base-changes to `f₀`, then reducing `h ≫ s` modulo `I A`
gives `reducedAffineHom I f₀ A h`. -/
theorem reducedAffineHom_of_lift (s : H.X ⟶ G.X)
    (hs : (Over.pullback (Spec.algebraMap R (R ⧸ I))).map s = f₀.hom.hom)
    (h : H.affinePoints A) :
    Lie.NonaffineKernel.reduction G (I.map (algebraMap R A)) (h ≫ s) =
      reducedAffineHom I f₀ A h := by
  have key : f₀.hom.hom.left ≫ pullback.fst G.X.hom (Spec.algebraMap R (R ⧸ I)) =
      pullback.fst H.X.hom (Spec.algebraMap R (R ⧸ I)) ≫ s.left := by
    have h1 : ((Over.pullback (Spec.algebraMap R (R ⧸ I))).map s).left ≫
        pullback.fst G.X.hom (Spec.algebraMap R (R ⧸ I)) =
          pullback.fst H.X.hom (Spec.algebraMap R (R ⧸ I)) ≫ s.left := by
      exact pullback.lift_fst _ _ _
    rw [← h1, hs]
    rfl
  apply Over.OverMorphism.ext
  change _ = ((affinePointsBaseChangeMulEquiv R (R ⧸ I) (A ⧸ I.map (algebraMap R A)) G).symm
    ((affinePointsBaseChangeMulEquiv R (R ⧸ I) (A ⧸ I.map (algebraMap R A)) H)
      (Lie.NonaffineKernel.reduction H (I.map (algebraMap R A)) h) ≫ f₀.hom.hom)).left
  rw [affinePointsBaseChangeMulEquiv_symm_left, Over.comp_left]
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (fun k => Over.Hom.left
    ((affinePointsBaseChangeMulEquiv R (R ⧸ I) (A ⧸ I.map (algebraMap R A)) H)
      (Lie.NonaffineKernel.reduction H (I.map (algebraMap R A)) h)) ≫ k) key).symm
  refine Eq.trans ?_ (Category.assoc _ _ _)
  have e := affinePointsBaseChangeMulEquiv_symm_left R (R ⧸ I) (A ⧸ I.map (algebraMap R A)) H
    ((affinePointsBaseChangeMulEquiv R (R ⧸ I) (A ⧸ I.map (algebraMap R A)) H)
      (Lie.NonaffineKernel.reduction H (I.map (algebraMap R A)) h))
  rw [MulEquiv.symm_apply_apply] at e
  exact congrArg (fun k => k ≫ s.left) e

/-- The underlying map of a reduced point, as a composite of scheme maps. -/
theorem reducedAffineHom_left (h : H.affinePoints A) :
    (reducedAffineHom I f₀ A h).left =
      ((affinePointsBaseChangeMulEquiv R (R ⧸ I) (A ⧸ I.map (algebraMap R A)) H)
        (Lie.NonaffineKernel.reduction H (I.map (algebraMap R A)) h)).left ≫
        f₀.hom.hom.left ≫ pullback.fst G.X.hom (Spec.algebraMap R (R ⧸ I)) := by
  change ((affinePointsBaseChangeMulEquiv R (R ⧸ I) (A ⧸ I.map (algebraMap R A)) G).symm
    ((affinePointsBaseChangeMulEquiv R (R ⧸ I) (A ⧸ I.map (algebraMap R A)) H)
      (Lie.NonaffineKernel.reduction H (I.map (algebraMap R A)) h) ≫ f₀.hom.hom)).left = _
  rw [affinePointsBaseChangeMulEquiv_symm_left, Over.comp_left]
  exact Category.assoc _ _ _

theorem baseChange_point_fst (h : H.affinePoints A) :
    ((affinePointsBaseChangeMulEquiv R (R ⧸ I) (A ⧸ I.map (algebraMap R A)) H)
        (Lie.NonaffineKernel.reduction H (I.map (algebraMap R A)) h)).left ≫
      pullback.fst H.X.hom (Spec.algebraMap R (R ⧸ I)) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap R A)))) ≫ h.left := by
  have e := affinePointsBaseChangeMulEquiv_symm_left R (R ⧸ I) (A ⧸ I.map (algebraMap R A)) H
    ((affinePointsBaseChangeMulEquiv R (R ⧸ I) (A ⧸ I.map (algebraMap R A)) H)
      (Lie.NonaffineKernel.reduction H (I.map (algebraMap R A)) h))
  rw [MulEquiv.symm_apply_apply] at e
  exact e.symm

theorem baseChange_point_snd (h : H.affinePoints A) :
    ((affinePointsBaseChangeMulEquiv R (R ⧸ I) (A ⧸ I.map (algebraMap R A)) H)
        (Lie.NonaffineKernel.reduction H (I.map (algebraMap R A)) h)).left ≫
      pullback.snd H.X.hom (Spec.algebraMap R (R ⧸ I)) =
        Spec.map (CommRingCat.ofHom (algebraMap (R ⧸ I) (A ⧸ I.map (algebraMap R A)))) :=
  Over.w ((affinePointsBaseChangeMulEquiv R (R ⧸ I) (A ⧸ I.map (algebraMap R A)) H)
    (Lie.NonaffineKernel.reduction H (I.map (algebraMap R A)) h))

section Naturality

variable {A} {B : CommAlgCat.{u} R} (φ : A ⟶ B)

theorem extended_le_comap :
    I.map (algebraMap R A) ≤ (I.map (algebraMap R B)).comap φ.hom := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
  exact Ideal.mem_map_of_mem _ hx

/-- The map of reductions induced by `φ`. -/
abbrev reducedMap : A ⧸ I.map (algebraMap R A) →ₐ[R] B ⧸ I.map (algebraMap R B) :=
  Ideal.quotientMapₐ (I.map (algebraMap R B)) φ.hom (extended_le_comap I φ)

/-- **Naturality** of `reducedAffineHom` in the coefficient algebra. -/
theorem reducedAffineHom_naturality (h : H.affinePoints A) :
    reducedAffineHom I f₀ B (H.affinePointMap φ h) =
      Lie.affineMap G (reducedMap I φ) (reducedAffineHom I f₀ A h) := by
  have hq : ((affinePointsBaseChangeMulEquiv R (R ⧸ I) (B ⧸ I.map (algebraMap R B)) H)
        (Lie.NonaffineKernel.reduction H (I.map (algebraMap R B)) (H.affinePointMap φ h))).left =
      Spec.map (CommRingCat.ofHom (reducedMap I φ).toRingHom) ≫
        ((affinePointsBaseChangeMulEquiv R (R ⧸ I) (A ⧸ I.map (algebraMap R A)) H)
          (Lie.NonaffineKernel.reduction H (I.map (algebraMap R A)) h)).left := by
    apply pullback.hom_ext
    · refine (baseChange_point_fst I B (H.affinePointMap φ h)).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans ?_ (congrArg (fun k => Spec.map
        (CommRingCat.ofHom (reducedMap I φ).toRingHom) ≫ k) (baseChange_point_fst I A h).symm)
      have e : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap R B)))) ≫
          Spec.map (CommRingCat.ofHom φ.hom.toRingHom) =
            Spec.map (CommRingCat.ofHom (reducedMap I φ).toRingHom) ≫
              Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap R A)))) := by
        rw [← Spec.map_comp, ← Spec.map_comp]
        rfl
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ h.left) e).trans (Category.assoc _ _ _))
    · refine (baseChange_point_snd I B (H.affinePointMap φ h)).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans ?_ (congrArg (fun k => Spec.map
        (CommRingCat.ofHom (reducedMap I φ).toRingHom) ≫ k) (baseChange_point_snd I A h).symm)
      rw [← Spec.map_comp]
      congr 1
      ext x
      change Ideal.Quotient.mk _ (algebraMap R B x) =
        Ideal.Quotient.mk _ (φ.hom (algebraMap R A x))
      rw [AlgHom.commutes]
  apply Over.OverMorphism.ext
  rw [reducedAffineHom_left]
  change _ = Spec.map (CommRingCat.ofHom (reducedMap I φ).toRingHom) ≫
    (reducedAffineHom I f₀ A h).left
  rw [reducedAffineHom_left, hq]
  exact Category.assoc _ _ _

end Naturality

end Langlands.GroupScheme.HomScheme
