import Langlands.GroupScheme.Dynamic.RealLeviIwasawa
import Langlands.Global.InfiniteCompletionRCLike
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Field.ULift

/-! # Levi-compatible Iwasawa over arbitrary real or complex coefficients -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.Analytic

/-- Algebraic closure transfers through a ring equivalence even when the
fields have different universes. -/
theorem isAlgClosed_of_ringEquiv {A : Type v} [Field A] [IsAlgClosed A]
    (B : Type u) [Field B] (e : A ≃+* B) : IsAlgClosed B := by
  apply IsAlgClosed.of_exists_root
  intro p hmp hp
  have hpe : (p.map e.symm.toRingHom).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    exact ne_of_gt (Polynomial.degree_pos_of_irreducible hp)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (k := A) (p.map e.symm.toRingHom) hpe
  refine ⟨e x, ?_⟩
  rw [Polynomial.IsRoot] at hx
  apply e.symm.injective
  rw [map_zero, ← hx]
  clear hx hpe hp hmp
  induction p using Polynomial.induction_on <;> simp_all

/-- A complex coefficient field in any prescribed universe. -/
@[instance_reducible]
def complexLiftRCLike : RCLike (ULift.{u} ℂ) := by
  letI : NormedField (ULift.{u} ℂ) :=
    NormedField.induced _ _ ULift.ringEquiv ULift.down_injective
  exact rclikeOfNormPreservingRingEquiv ULift.ringEquiv (fun _ => rfl)

variable {k : Type u} [RCLike k]

/-- Embed a real `RCLike` field into the lifted complex numbers through its
real-part ring equivalence. -/
@[instance_reducible]
def realComplexLiftAlgebra (hI : (RCLike.I : k) = 0) :
    Algebra k (ULift.{u} ℂ) :=
  ((ULift.ringEquiv : ULift.{u} ℂ ≃+* ℂ).symm.toRingHom.comp
    (Complex.ofRealHom.comp (RCLike.realRingEquiv hI).toRingHom)).toAlgebra

/-- The lifted complex extension respects the original real scalar action. -/
theorem realComplexLiftAlgebra_scalarTower (hI : (RCLike.I : k) = 0) :
    let := complexLiftRCLike.{u}
    let := realComplexLiftAlgebra hI
    IsScalarTower ℝ k (ULift.{u} ℂ) := by
  let := complexLiftRCLike.{u}
  let := realComplexLiftAlgebra hI
  apply IsScalarTower.of_algebraMap_eq
  intro r
  apply ULift.down_injective
  change (r : ℂ) = (RCLike.re (algebraMap ℝ k r) : ℂ)
  rw [RCLike.ofReal_re]

end Langlands.Analytic

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [RCLike k]
  {G P M : GroupScheme (Spec (CommRingCat.of k))}

/-- Every real or complex coefficient field admits the conditional Hermitian
realization from ambient star realization and a common dynamic cocharacter. -/
theorem HasClosedStarRealization.hasRCLikeHermitianStarLeviRealization
    (h : HasClosedStarRealization G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {p : P ⟶ G} {m : M ⟶ G}
    (hp : (Dynamic.parabolic χ).IsRepresentedBy p)
    (hm : (Dynamic.centralizer χ).IsRepresentedBy m) :
    Dynamic.HasHermitianStarLeviRealization p m := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := k) with hI | hI
  · let := Langlands.Analytic.complexLiftRCLike.{u}
    let := Langlands.Analytic.realComplexLiftAlgebra hI
    let := Langlands.Analytic.realComplexLiftAlgebra_scalarTower hI
    let : IsAlgClosed (ULift.{u} ℂ) :=
      Langlands.Analytic.isAlgClosed_of_ringEquiv _ ULift.ringEquiv.symm
    have hreal (z : k) : star z = z :=
      RCLike.conj_eq_iff_im.mpr (RCLike.im_eq_zero hI z)
    exact h.hasRealHermitianStarLeviRealization (S := ULift.{u} ℂ) hreal χ hp hm
  · let : IsAlgClosed k :=
      Langlands.Analytic.isAlgClosed_of_ringEquiv k (RCLike.complexRingEquiv hI).symm
    exact h.hasHermitianStarLeviRealization χ hp hm

/-- Compatible diagonal realization over every `RCLike` coefficient field,
with no extension-field input. -/
theorem HasClosedStarRealization.hasRCLikeDiagonalStarLeviRealization
    (h : HasClosedStarRealization G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {p : P ⟶ G} {m : M ⟶ G}
    (hp : (Dynamic.parabolic χ).IsRepresentedBy p)
    (hm : (Dynamic.centralizer χ).IsRepresentedBy m) :
    Dynamic.HasDiagonalStarLeviRealization p m :=
  (h.hasRCLikeHermitianStarLeviRealization χ hp hm).hasDiagonalStarLeviRealization

local instance rclikeLeviIwasawaPointTopology
    (H : GroupScheme (Spec (CommRingCat.of k))) :
    TopologicalSpace (H.affinePoints (CommAlgCat.of k k)) :=
  H.affinePointsTopologicalSpace (CommAlgCat.of k k)

/-- All four actual-point Levi-compatible Iwasawa conclusions over every
`RCLike` coefficient field, from ambient star realization and a common
dynamic cocharacter. -/
theorem HasClosedStarRealization.hasRCLikeLeviCompatibleDecomposition
    [IsAffine G.X.left]
    (h : HasClosedStarRealization G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {p : P ⟶ G} {m : M ⟶ G}
    (hp : (Dynamic.parabolic χ).IsRepresentedBy p)
    (hm : (Dynamic.centralizer χ).IsRepresentedBy m) :
    CompactIwasawa.HasLeviCompatibleDecomposition
      (P.affinePointsTarget p (CommAlgCat.of k k))
      (M.affinePointsTarget m (CommAlgCat.of k k)) :=
  (h.hasRCLikeDiagonalStarLeviRealization χ hp hm).hasLeviCompatibleDecomposition

end Langlands.GroupScheme.MatrixRepresentation
