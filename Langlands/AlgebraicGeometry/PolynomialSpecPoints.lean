import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.RingTheory.FiniteType

/-! # Points of relative affine spaces given by polynomial algebras -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.PolynomialSpecPoints

variable {R : CommRingCat.{u}}

/-- The adjoint algebra map of a point of a relative spectrum is pullback of
global functions along that point. -/
theorem adjunction_homEquiv_symm_apply (T : Over (Spec R)) (B : CommAlgCat.{u} R)
    (x : T ⟶ (algSpec R).obj (op B)) (b : B) :
    (((algΓAlgSpecAdjunction R).homEquiv T (op B)).symm x).unop.hom b =
      x.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) := by
  rw [Adjunction.homEquiv_counit]
  rfl

variable (R) (K : Type)

/-- The polynomial algebra with variables `K`, as a commutative `R`-algebra. -/
abbrev algebra : CommAlgCat.{u} R := CommAlgCat.of R (MvPolynomial K R)

/-- The relative affine space with coordinates indexed by `K`. -/
abbrev space : Over (Spec R) := (algSpec R).obj (op (algebra R K))

instance isAffineHom_space : IsAffineHom (space R K).hom := by
  change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial K R))))
  infer_instance

instance locallyOfFiniteType_space [Finite K] : LocallyOfFiniteType (space R K).hom := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial K R))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- The coordinate function `X κ` as a global function on the affine space. -/
def globalCoord (κ : K) : Γ((space R K).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial K R))).inv (MvPolynomial.X κ)

variable {R K}

/-- The coordinates of a point of the affine space on an arbitrary test scheme. -/
def coord {T : Over (Spec R)} (x : T ⟶ space R K) (κ : K) : Γ(T.left, ⊤) :=
  x.left.appTop (globalCoord R K κ)

/-- The point with prescribed global coordinates on an arbitrary test scheme. -/
def mk {T : Over (Spec R)} (v : K → Γ(T.left, ⊤)) : T ⟶ space R K :=
  (algΓAlgSpecAdjunction R).homEquiv T (op (algebra R K))
    (CommAlgCat.ofHom (MvPolynomial.aeval (R := R) (S₁ := ((algΓ R).obj T).unop) v)).op

@[simp]
theorem coord_mk {T : Over (Spec R)} (v : K → Γ(T.left, ⊤)) (κ : K) :
    coord (mk v) κ = v κ := by
  rw [coord, globalCoord, ← adjunction_homEquiv_symm_apply, mk, Equiv.symm_apply_apply]
  exact MvPolynomial.aeval_X (R := R) (S₁ := ((algΓ R).obj T).unop) v κ

/-- Points of the affine space are determined by their coordinates. -/
theorem ext {T : Over (Spec R)} {x y : T ⟶ space R K}
    (h : ∀ κ, coord x κ = coord y κ) : x = y := by
  apply ((algΓAlgSpecAdjunction R).homEquiv T (op (algebra R K))).symm.injective
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply MvPolynomial.algHom_ext
  intro κ
  rw [adjunction_homEquiv_symm_apply, adjunction_homEquiv_symm_apply]
  exact h κ

/-- Coordinates are natural under every test morphism. -/
theorem coord_comp {T T' : Over (Spec R)} (b : T' ⟶ T) (x : T ⟶ space R K) (κ : K) :
    coord (b ≫ x) κ = b.left.appTop (coord x κ) := by
  simp only [coord, Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

end Langlands.AlgebraicGeometry.PolynomialSpecPoints
