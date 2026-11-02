import Langlands.GroupScheme.AffinePointTopology
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra

/-! # Smooth parameter families detected by actual regular functions -/

noncomputable section

universe u v w

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Topology TensorProduct Manifold ContDiff

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
  (A : CommAlgCat.{u} R)
  {B : Type u} [NormedCommRing B] [NormedAlgebra ℝ B]
  (c : A →+* B)
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- A parameter family of actual points is coordinate-smooth when every global
regular function has a smooth value after the specified coefficient map.
This definition does not assign a manifold to the point group. -/
def CoordinateSmooth (p : M → G.affinePoints A) : Prop :=
  ∀ a : Γ(G.X.left, ⊤), ContMDiff I 𝓘(ℝ, B) ∞
    (fun x => c (G.affinePointEvaluation A (p x) a))

theorem coordinateSmooth_const (p : G.affinePoints A) :
    G.CoordinateSmooth A c I (fun _ : M => p) :=
  fun _ => contMDiff_const

variable {G A c I} in
/-- A regular map of the underlying schemes preserves coordinate-smooth families. -/
theorem CoordinateSmooth.postcomp {G' : GroupScheme (Spec R)}
    {p : M → G.affinePoints A} (hp : G.CoordinateSmooth A c I p)
    (f : G.X ⟶ G'.X) :
    G'.CoordinateSmooth A c I (fun x => p x ≫ f) := by
  intro a
  simpa only [affinePointEvaluation_postcomp] using hp (f.left.appTop a)

theorem CoordinateSmooth.inv {p : M → G.affinePoints A}
    (hp : G.CoordinateSmooth A c I p) :
    G.CoordinateSmooth A c I (fun x => (p x)⁻¹) :=
  hp.postcomp (GrpObj.inv (X := G.X))

private theorem contMDiff_tensorLift
    {D D' : Type u} [CommRing D] [CommRing D']
    [Algebra R D] [Algebra R D']
    (f : M → D →ₐ[R] A) (g : M → D' →ₐ[R] A)
    (hf : ∀ d, ContMDiff I 𝓘(ℝ, B) ∞ (fun x => c (f x d)))
    (hg : ∀ d, ContMDiff I 𝓘(ℝ, B) ∞ (fun x => c (g x d)))
    (z : D ⊗[R] D') :
    ContMDiff I 𝓘(ℝ, B) ∞ (fun x =>
      c (Algebra.TensorProduct.lift (f x) (g x) (fun _ _ => Commute.all _ _) z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul d d' =>
      simpa only [Algebra.TensorProduct.lift_tmul, map_mul, Function.comp_def] using
        (contDiff_mul (𝕜 := ℝ) (𝔸 := B)).contMDiff.comp ((hf d).prodMk_space (hg d'))
  | add z z' hz hz' =>
      simpa only [map_add, Function.comp_def] using
        (contDiff_add (𝕜 := ℝ) (F := B)).contMDiff.comp (hz.prodMk_space hz')

private theorem hopfPointEvaluation (D : CommHopfAlgCat.{u} R)
    (f : WithConv (D →ₐ[R] A)) (a : Γ(Spec (CommRingCat.of D), ⊤)) :
    affinePointEvaluation ((hopfSpec R).obj (op D)) A
        (Spec.mapMulEquiv (R := R) (S := D) (T := A) f) a =
      f ((Scheme.ΓSpecIso (CommRingCat.of D)).hom a) := by
  change ((Spec.map (CommRingCat.ofHom f.ofConv.toRingHom)).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom) a = _
  rw [Scheme.ΓSpecIso_naturality]
  rfl

private theorem hopfPointInverseEvaluation (D : CommHopfAlgCat.{u} R)
    (x : affinePoints ((hopfSpec R).obj (op D)) A) (d : D) :
    (Spec.mapMulEquiv (R := R) (S := D) (T := A)).symm x d =
      affinePointEvaluation ((hopfSpec R).obj (op D)) A x
        ((Scheme.ΓSpecIso (CommRingCat.of D)).inv d) := by
  obtain ⟨f, rfl⟩ := (Spec.mapMulEquiv (R := R) (S := D) (T := A)).surjective x
  rw [MulEquiv.symm_apply_apply, hopfPointEvaluation]
  simp

private theorem coordinateSmooth_hopf_mul (D : CommHopfAlgCat.{u} R)
    {p q : M → affinePoints ((hopfSpec R).obj (op D)) A}
    (hp : CoordinateSmooth ((hopfSpec R).obj (op D)) A c I p)
    (hq : CoordinateSmooth ((hopfSpec R).obj (op D)) A c I q) :
    CoordinateSmooth ((hopfSpec R).obj (op D)) A c I (fun x => p x * q x) := by
  let e := Spec.mapMulEquiv (R := R) (S := D) (T := A)
  intro a
  have hm (x y : affinePoints ((hopfSpec R).obj (op D)) A) :
      affinePointEvaluation ((hopfSpec R).obj (op D)) A (x * y) a =
        (e.symm x * e.symm y) ((Scheme.ΓSpecIso (CommRingCat.of D)).hom a) := by
    have hh := hopfPointEvaluation A D (e.symm (x * y)) a
    change affinePointEvaluation ((hopfSpec R).obj (op D)) A
      (e (e.symm (x * y))) a = _ at hh
    rw [e.apply_symm_apply] at hh
    rw [hh, e.symm.map_mul]
  simp_rw [hm, AlgHom.convMul_apply]
  apply contMDiff_tensorLift A c I
    (fun x => (e.symm (p x)).ofConv) (fun x => (e.symm (q x)).ofConv)
  · intro d
    change ContMDiff I 𝓘(ℝ, B) ∞ (fun x =>
      c ((Spec.mapMulEquiv (R := R) (S := D) (T := A)).symm (p x) d))
    simp_rw [hopfPointInverseEvaluation]
    exact hp ((Scheme.ΓSpecIso (CommRingCat.of D)).inv d)
  · intro d
    change ContMDiff I 𝓘(ℝ, B) ∞ (fun x =>
      c ((Spec.mapMulEquiv (R := R) (S := D) (T := A)).symm (q x) d))
    simp_rw [hopfPointInverseEvaluation]
    exact hq ((Scheme.ΓSpecIso (CommRingCat.of D)).inv d)

/-- Actual group multiplication preserves coordinate-smooth families. Affineness
provides the Hopf algebra, and its finite tensor expressions give smoothness. -/
theorem CoordinateSmooth.mul [IsAffine G.X.left]
    {p q : M → G.affinePoints A} (hp : G.CoordinateSmooth A c I p)
    (hq : G.CoordinateSmooth A c I q) :
    G.CoordinateSmooth A c I (fun x => p x * q x) := by
  obtain ⟨D, ⟨e⟩⟩ := (essImage_hopfSpec (G := G)).mpr inferInstance
  have hp' := hp.postcomp e.inv.hom.hom
  have hq' := hq.postcomp e.inv.hom.hom
  have h := (coordinateSmooth_hopf_mul A c I D.unop hp' hq').postcomp e.hom.hom.hom
  have he (x y : G.affinePoints A) :
      ((x ≫ e.inv.hom.hom) * (y ≫ e.inv.hom.hom)) ≫ e.hom.hom.hom = x * y := by
    change (G.affinePointsTarget e.inv A x * G.affinePointsTarget e.inv A y) ≫
      e.hom.hom.hom = x * y
    rw [← map_mul]
    change (x * y) ≫ e.inv.hom.hom ≫ e.hom.hom.hom = x * y
    have he' : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 G.X := by
      exact congrArg (fun f => f.hom.hom) e.inv_hom_id
    rw [he', Category.comp_id]
  simpa only [he] using h

end Langlands.GroupScheme
