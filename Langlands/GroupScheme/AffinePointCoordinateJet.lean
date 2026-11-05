import Langlands.GroupScheme.AffinePointCoordinateSmooth
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Algebra.DualNumber

/-! # Actual regular-function first jets of affine point curves -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Topology TensorProduct

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
  {B : Type u} [NormedCommRing B] [NormedAlgebra ℝ B] [Algebra R B]

/-- A dual-number point records the value and derivative of every actual
regular-function evaluation of the specified real curve. -/
def CoordinateJet (p : ℝ → G.affinePoints (CommAlgCat.of R B))
    (q : G.affinePoints (CommAlgCat.of R (DualNumber B))) (t : ℝ) : Prop :=
  ∀ a : Γ(G.X.left, ⊤),
    (G.affinePointEvaluation (CommAlgCat.of R (DualNumber B)) q a).fst =
        G.affinePointEvaluation (CommAlgCat.of R B) (p t) a ∧
      HasDerivAt
        (fun s => G.affinePointEvaluation (CommAlgCat.of R B) (p s) a)
        (G.affinePointEvaluation (CommAlgCat.of R (DualNumber B)) q a).snd t

variable {G} in
theorem CoordinateJet.postcomp {G' : GroupScheme (Spec R)}
    {p : ℝ → G.affinePoints (CommAlgCat.of R B)}
    {q : G.affinePoints (CommAlgCat.of R (DualNumber B))} {t : ℝ}
    (h : G.CoordinateJet p q t) (f : G.X ⟶ G'.X) :
    G'.CoordinateJet (fun s => p s ≫ f) (q ≫ f) t := by
  intro a
  exact h (f.left.appTop a)

theorem coordinateJet_const (p : G.affinePoints (CommAlgCat.of R B)) (t : ℝ) :
    G.CoordinateJet (fun _ => p)
      (G.affinePointMap (CommAlgCat.ofHom (IsScalarTower.toAlgHom R B (DualNumber B))) p) t := by
  intro a
  rw [G.affinePointEvaluation_map
    (CommAlgCat.ofHom (IsScalarTower.toAlgHom R B (DualNumber B))) p a]
  exact ⟨rfl, hasDerivAt_const t _⟩

private theorem jet_tensorLift
    {D D' : Type u} [CommRing D] [CommRing D']
    [Algebra R D] [Algebra R D']
    (f : ℝ → D →ₐ[R] B) (g : ℝ → D' →ₐ[R] B)
    (fq : D →ₐ[R] DualNumber B) (gq : D' →ₐ[R] DualNumber B) (t : ℝ)
    (hf : ∀ d, (fq d).fst = f t d ∧ HasDerivAt (fun s => f s d) (fq d).snd t)
    (hg : ∀ d, (gq d).fst = g t d ∧ HasDerivAt (fun s => g s d) (gq d).snd t)
    (z : D ⊗[R] D') :
    (Algebra.TensorProduct.lift fq gq (fun _ _ => Commute.all _ _) z).fst =
        Algebra.TensorProduct.lift (f t) (g t) (fun _ _ => Commute.all _ _) z ∧
      HasDerivAt
        (fun s => Algebra.TensorProduct.lift (f s) (g s) (fun _ _ => Commute.all _ _) z)
        (Algebra.TensorProduct.lift fq gq (fun _ _ => Commute.all _ _) z).snd t := by
  induction z using TensorProduct.inductionOn with
  | tmul d d' =>
      simp only [Algebra.TensorProduct.lift_tmul, TrivSqZeroExt.fst_mul]
      refine ⟨by rw [(hf d).1, (hg d').1], ?_⟩
      convert! ((hf d).2.mul (hg d').2) using 1
      simp only [TrivSqZeroExt.snd_mul, smul_eq_mul, op_smul_eq_smul,
        (hf d).1, (hg d').1, mul_comm, add_comm]
  | add z z' hz hz' =>
      simp only [map_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add]
      exact ⟨congrArg₂ (· + ·) hz.1 hz'.1, hz.2.add hz'.2⟩

private theorem hopfJetEvaluation (A : CommAlgCat.{u} R) (D : CommHopfAlgCat.{u} R)
    (f : WithConv (D →ₐ[R] A)) (a : Γ(Spec (CommRingCat.of D), ⊤)) :
    affinePointEvaluation ((hopfSpec R).obj (op D)) A
        (Spec.mapMulEquiv (R := R) (S := D) (T := A) f) a =
      f ((Scheme.ΓSpecIso (CommRingCat.of D)).hom a) := by
  change ((Spec.map (CommRingCat.ofHom f.ofConv.toRingHom)).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom) a = _
  rw [Scheme.ΓSpecIso_naturality]
  rfl

private theorem hopfJetInverseEvaluation (A : CommAlgCat.{u} R)
    (D : CommHopfAlgCat.{u} R)
    (x : affinePoints ((hopfSpec R).obj (op D)) A) (d : D) :
    (Spec.mapMulEquiv (R := R) (S := D) (T := A)).symm x d =
      affinePointEvaluation ((hopfSpec R).obj (op D)) A x
        ((Scheme.ΓSpecIso (CommRingCat.of D)).inv d) := by
  obtain ⟨f, rfl⟩ := (Spec.mapMulEquiv (R := R) (S := D) (T := A)).surjective x
  rw [MulEquiv.symm_apply_apply, hopfJetEvaluation]
  simp

private theorem coordinateJet_hopf_mul (D : CommHopfAlgCat.{u} R)
    {p p' : ℝ → affinePoints ((hopfSpec R).obj (op D)) (CommAlgCat.of R B)}
    {q q' : affinePoints ((hopfSpec R).obj (op D)) (CommAlgCat.of R (DualNumber B))}
    {t : ℝ}
    (hp : CoordinateJet ((hopfSpec R).obj (op D)) p q t)
    (hp' : CoordinateJet ((hopfSpec R).obj (op D)) p' q' t) :
    CoordinateJet ((hopfSpec R).obj (op D)) (fun s => p s * p' s) (q * q') t := by
  intro a
  have hm (A : CommAlgCat.{u} R)
      (x y : affinePoints ((hopfSpec R).obj (op D)) A) :
      affinePointEvaluation ((hopfSpec R).obj (op D)) A (x * y) a =
        ((Spec.mapMulEquiv (R := R) (S := D) (T := A)).symm x *
          (Spec.mapMulEquiv (R := R) (S := D) (T := A)).symm y)
          ((Scheme.ΓSpecIso (CommRingCat.of D)).hom a) := by
    let e := Spec.mapMulEquiv (R := R) (S := D) (T := A)
    have hh := hopfJetEvaluation A D (e.symm (x * y)) a
    change affinePointEvaluation ((hopfSpec R).obj (op D)) A
      (e (e.symm (x * y))) a = _ at hh
    rw [e.apply_symm_apply] at hh
    rw [hh, e.symm.map_mul]
  simp_rw [hm, AlgHom.convMul_apply]
  apply jet_tensorLift
    (fun s => ((Spec.mapMulEquiv (R := R) (S := D)
      (T := CommAlgCat.of R B)).symm (p s)).ofConv)
    (fun s => ((Spec.mapMulEquiv (R := R) (S := D)
      (T := CommAlgCat.of R B)).symm (p' s)).ofConv)
  · intro d
    change ((Spec.mapMulEquiv (R := R) (S := D)
      (T := CommAlgCat.of R (DualNumber B))).symm q d).fst =
      (Spec.mapMulEquiv (R := R) (S := D) (T := CommAlgCat.of R B)).symm (p t) d ∧
      HasDerivAt (fun s => (Spec.mapMulEquiv (R := R) (S := D)
        (T := CommAlgCat.of R B)).symm (p s) d)
        ((Spec.mapMulEquiv (R := R) (S := D)
          (T := CommAlgCat.of R (DualNumber B))).symm q d).snd t
    rw [hopfJetInverseEvaluation (CommAlgCat.of R (DualNumber B)) D q d]
    simp_rw [hopfJetInverseEvaluation (CommAlgCat.of R B) D (p _) d]
    exact hp
      ((Scheme.ΓSpecIso (CommRingCat.of D)).inv d)
  · intro d
    change ((Spec.mapMulEquiv (R := R) (S := D)
      (T := CommAlgCat.of R (DualNumber B))).symm q' d).fst =
      (Spec.mapMulEquiv (R := R) (S := D) (T := CommAlgCat.of R B)).symm (p' t) d ∧
      HasDerivAt (fun s => (Spec.mapMulEquiv (R := R) (S := D)
        (T := CommAlgCat.of R B)).symm (p' s) d)
        ((Spec.mapMulEquiv (R := R) (S := D)
          (T := CommAlgCat.of R (DualNumber B))).symm q' d).snd t
    rw [hopfJetInverseEvaluation (CommAlgCat.of R (DualNumber B)) D q' d]
    simp_rw [hopfJetInverseEvaluation (CommAlgCat.of R B) D (p' _) d]
    exact hp'
      ((Scheme.ΓSpecIso (CommRingCat.of D)).inv d)

/-- The ordinary product rule agrees with the actual group law on dual-number
points of every affine group scheme. -/
theorem CoordinateJet.mul [IsAffine G.X.left]
    {p p' : ℝ → G.affinePoints (CommAlgCat.of R B)}
    {q q' : G.affinePoints (CommAlgCat.of R (DualNumber B))} {t : ℝ}
    (hp : G.CoordinateJet p q t) (hp' : G.CoordinateJet p' q' t) :
    G.CoordinateJet (fun s => p s * p' s) (q * q') t := by
  obtain ⟨D, ⟨e⟩⟩ := (essImage_hopfSpec (G := G)).mpr inferInstance
  have h := (coordinateJet_hopf_mul D.unop
    (hp.postcomp e.inv.hom.hom) (hp'.postcomp e.inv.hom.hom)).postcomp e.hom.hom.hom
  have he (A : CommAlgCat.{u} R) (x y : G.affinePoints A) :
      ((x ≫ e.inv.hom.hom) * (y ≫ e.inv.hom.hom)) ≫ e.hom.hom.hom = x * y := by
    change (G.affinePointsTarget e.inv A x * G.affinePointsTarget e.inv A y) ≫
      e.hom.hom.hom = x * y
    rw [← map_mul]
    change (x * y) ≫ e.inv.hom.hom ≫ e.hom.hom.hom = x * y
    have he' : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 G.X :=
      congrArg (fun f => f.hom.hom) e.inv_hom_id
    rw [he', Category.comp_id]
  simpa only [he] using h

end Langlands.GroupScheme
