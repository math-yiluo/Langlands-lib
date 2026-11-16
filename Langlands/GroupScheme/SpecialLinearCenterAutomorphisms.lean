import Langlands.GroupScheme.CenterAutomorphisms
import Langlands.GroupScheme.Reductive.SpecialLinearTorusAutomorphismProof
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-! # Matrix conjugation fixes the full centre of the special linear group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear

variable {n : Type} [Fintype n] [DecidableEq n]

/-- A central determinant-one matrix is fixed by conjugation by every invertible
matrix, over every commutative coefficient ring. -/
theorem matrix_conjugation_eq_of_mem_center {A : Type*} [CommRing A]
    (g : Matrix.SpecialLinearGroup n A)
    (hg : g ∈ Subgroup.center (Matrix.SpecialLinearGroup n A))
    (x : Matrix.GeneralLinearGroup n A) :
    (x : Matrix n n A) * (g : Matrix n n A) *
      ((x⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A) = g := by
  have hgc := (Matrix.SpecialLinearGroup.toGL_mem_center_iff g).mpr hg
  have hc := Subgroup.mem_center_iff.mp hgc x
  have he : x * Matrix.SpecialLinearGroup.toGL g * x⁻¹ =
      Matrix.SpecialLinearGroup.toGL g := by
    rw [hc, mul_inv_cancel_right]
  exact congrArg (fun y : Matrix.GeneralLinearGroup n A => (y : Matrix n n A)) he

variable {R : CommRingCat.{u}}

/-- A point of the full scheme-theoretic centre has a central matrix in its
actual coefficient ring. -/
theorem pointsEquiv_mem_center_of_mem_center
    {T : Over (Spec R)} {z : T ⟶ (groupScheme n R).X}
    (hz : z ∈ (center (groupScheme n R)).carrier T) :
    pointsEquiv n R T z ∈
      Subgroup.center (Matrix.SpecialLinearGroup n Γ(T.left, ⊤)) := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  have hc := (commute_of_mem_center hz ((pointsEquiv n R T).symm g)).map
    (pointsEquiv n R T).toMonoidHom
  simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hc.eq.symm

/-- On every test scheme there is an invertible matrix implementing the
automorphism on every point over that scheme. -/
def HasPointwiseMatrixConjugation (f : groupScheme n R ≅ groupScheme n R) : Prop :=
  ∀ T : Over (Spec R), ∃ x : Matrix.GeneralLinearGroup n Γ(T.left, ⊤),
    ∀ g : T ⟶ (groupScheme n R).X,
      (pointsEquiv n R T (g ≫ f.hom.hom.hom) : Matrix n n Γ(T.left, ⊤)) =
        (x : Matrix n n Γ(T.left, ⊤)) *
          (pointsEquiv n R T g : Matrix n n Γ(T.left, ⊤)) *
          ((x⁻¹ : Matrix.GeneralLinearGroup n Γ(T.left, ⊤)) : Matrix n n Γ(T.left, ⊤))

/-- All-test matrix conjugation fixes the full scheme-theoretic centre. -/
theorem HasPointwiseMatrixConjugation.fixesCenter
    {f : groupScheme n R ≅ groupScheme n R} (h : HasPointwiseMatrixConjugation f) :
    AutomorphismFixesCenter f := by
  intro T z hz
  obtain ⟨x, hx⟩ := h T
  apply (pointsEquiv n R T).injective
  apply Subtype.ext
  exact (hx z).trans
    (matrix_conjugation_eq_of_mem_center _ (pointsEquiv_mem_center_of_mem_center hz) x)

end Langlands.GroupScheme.SpecialLinear

namespace Langlands.GroupScheme

attribute [local instance] SpecialLinear.isAffineHom_groupScheme

/-- A torus-preserving split special-linear automorphism which moves the full
centre has nontrivial based-root action. -/
theorem specialLinearTorusAutomorphism_nontrivial_of_not_fixesCenter
    (k : Type u) [Field k] (n : ℕ)
    (p : SplitPinning (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of k)))
    (f : SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of k) ≅
      SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of k))
    (t : p.torus ≅ p.torus)
    (hsq : p.inclusion ≫ f.hom = CommGroupScheme.groupHom t.hom ≫ p.inclusion)
    (hf : ¬ AutomorphismFixesCenter f) :
    let δ := rootDatumEquivOfTorusCompatibleIso
      p.isConnectedReductive p.isConnectedReductive
      p.isSplitTorus p.isSplitTorus p.isMaximalTorus p.isMaximalTorus
      f t hsq p.isRootDatum p.isRootDatum
    let θ := p.basedRootDatumProjection δ
    ∃ v : p.base.support, θ.val.indexEquiv v.val ≠ v.val := by
  classical
  dsimp only
  by_contra h
  have htriv : ∀ v : p.base.support,
      (p.basedRootDatumProjection (rootDatumEquivOfTorusCompatibleIso
        p.isConnectedReductive p.isConnectedReductive
        p.isSplitTorus p.isSplitTorus p.isMaximalTorus p.isMaximalTorus
        f t hsq p.isRootDatum p.isRootDatum)).val.indexEquiv v.val = v.val := by
    simpa only [not_exists, not_not] using h
  obtain ⟨x, hx⟩ :=
    SpecialLinearTorusAutomorphism.specialLinearTorusAutomorphism k n p f t hsq
  apply hf
  apply SpecialLinear.HasPointwiseMatrixConjugation.fixesCenter
  intro T
  refine ⟨Matrix.GeneralLinearGroup.map (scalarMap T) x, fun g => ?_⟩
  have he := (hx T (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of k) T g)).1 htriv
  simpa only [MulEquiv.symm_apply_apply, map_inv] using he

end Langlands.GroupScheme
