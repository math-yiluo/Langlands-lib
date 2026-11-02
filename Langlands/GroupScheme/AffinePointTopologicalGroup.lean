import Langlands.GroupScheme.AffinePointTopology
import Mathlib.Topology.Algebra.Ring.Basic

/-! # Topological group structure on actual affine group-scheme points -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Topology TensorProduct

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}}

/-- A group-scheme isomorphism induces a homeomorphism of the actual point spaces. -/
def affinePointsIsoHomeomorph {G H : GroupScheme (Spec R)} (e : G ≅ H)
    (A : CommAlgCat.{u} R) [TopologicalSpace A] : G.affinePoints A ≃ₜ H.affinePoints A where
  toEquiv := (((yonedaGrp.mapIso e).app (op ((algSpec R).obj (op A)))).groupIsoToMulEquiv).toEquiv
  continuous_toFun := G.continuous_affinePointsTarget A e.hom
  continuous_invFun := H.continuous_affinePointsTarget A e.inv

@[simp] theorem affinePointsIsoHomeomorph_apply {G H : GroupScheme (Spec R)} (e : G ≅ H)
    (A : CommAlgCat.{u} R) [TopologicalSpace A] (x : G.affinePoints A) :
    affinePointsIsoHomeomorph e A x = G.affinePointsTarget e.hom A x := rfl

@[simp] theorem affinePointsIsoHomeomorph_map_mul {G H : GroupScheme (Spec R)} (e : G ≅ H)
    (A : CommAlgCat.{u} R) [TopologicalSpace A] (x y : G.affinePoints A) :
    affinePointsIsoHomeomorph e A (x * y) =
      affinePointsIsoHomeomorph e A x * affinePointsIsoHomeomorph e A y :=
  (G.affinePointsTarget e.hom A).map_mul x y

private theorem continuous_tensorLift {B C : Type u} [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] {A : CommAlgCat.{u} R} [TopologicalSpace A]
    [IsTopologicalRing A] {T : Type v} [TopologicalSpace T]
    (f : T → B →ₐ[R] A) (g : T → C →ₐ[R] A)
    (hf : ∀ b, Continuous (fun t => f t b)) (hg : ∀ c, Continuous (fun t => g t c))
    (z : B ⊗[R] C) :
    Continuous (fun t =>
      Algebra.TensorProduct.lift (f t) (g t) (fun _ _ => Commute.all _ _) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul b c =>
      simpa only [Algebra.TensorProduct.lift_tmul] using (hf b).fun_mul (hg c)
  | add x y hx hy => simpa only [map_add] using hx.fun_add hy

private theorem hopfPointEvaluation (B : CommHopfAlgCat.{u} R) (A : CommAlgCat.{u} R)
    (f : WithConv (B →ₐ[R] A)) (a : Γ(Spec (CommRingCat.of B), ⊤)) :
    affinePointEvaluation ((hopfSpec R).obj (op B)) A
        (Spec.mapMulEquiv (R := R) (S := B) (T := A) f) a =
      f ((Scheme.ΓSpecIso (CommRingCat.of B)).hom a) := by
  change ((Spec.map (CommRingCat.ofHom f.ofConv.toRingHom)).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom) a = _
  rw [Scheme.ΓSpecIso_naturality]
  rfl

private theorem hopfPointInverseEvaluation (B : CommHopfAlgCat.{u} R)
    (A : CommAlgCat.{u} R) (x : affinePoints ((hopfSpec R).obj (op B)) A) (b : B) :
    (Spec.mapMulEquiv (R := R) (S := B) (T := A)).symm x b =
      affinePointEvaluation ((hopfSpec R).obj (op B)) A x
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) := by
  obtain ⟨f, rfl⟩ := (Spec.mapMulEquiv (R := R) (S := B) (T := A)).surjective x
  rw [MulEquiv.symm_apply_apply, hopfPointEvaluation]
  simp

private theorem continuous_hopfPointMul (B : CommHopfAlgCat.{u} R)
    (A : CommAlgCat.{u} R) [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (fun p : affinePoints ((hopfSpec R).obj (op B)) A ×
      affinePoints ((hopfSpec R).obj (op B)) A => p.1 * p.2) := by
  let G : GroupScheme (Spec R) := (hopfSpec R).obj (op B)
  let e : WithConv (B →ₐ[R] A) ≃* G.affinePoints A :=
    Spec.mapMulEquiv (R := R) (S := B) (T := A)
  have hc (b : B) : Continuous (fun x : G.affinePoints A => e.symm x b) := by
    have hh (x : G.affinePoints A) : e.symm x b =
        G.affinePointEvaluation A x ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) :=
      hopfPointInverseEvaluation B A x b
    simp_rw [hh]
    exact G.continuous_affinePointEvaluation A _
  apply (G.continuous_affinePoints_iff A _).mpr
  intro a
  have hp (x y : G.affinePoints A) :
      G.affinePointEvaluation A (x * y) a =
        (e.symm x * e.symm y) ((Scheme.ΓSpecIso (CommRingCat.of B)).hom a) := by
    have hh := hopfPointEvaluation B A (e.symm (x * y)) a
    change G.affinePointEvaluation A (e (e.symm (x * y))) a = _ at hh
    rw [e.apply_symm_apply] at hh
    rw [hh, e.symm.map_mul]
  simp_rw [hp, AlgHom.convMul_apply]
  exact continuous_tensorLift
    (fun p : G.affinePoints A × G.affinePoints A => (e.symm p.1).ofConv)
    (fun p : G.affinePoints A × G.affinePoints A => (e.symm p.2).ofConv)
    (fun b => (hc b).comp continuous_fst) (fun b => (hc b).comp continuous_snd) _

/-- The actual affine point groups are topological groups over any topological coefficient ring. -/
instance affinePointsIsTopologicalGroup (G : GroupScheme (Spec R)) [IsAffine G.X.left]
    (A : CommAlgCat.{u} R) [TopologicalSpace A] [IsTopologicalRing A] :
    IsTopologicalGroup (G.affinePoints A) where
  continuous_mul := by
    obtain ⟨B, ⟨e⟩⟩ := (essImage_hopfSpec (G := G)).mpr inferInstance
    let h := affinePointsIsoHomeomorph e A
    have hm := continuous_hopfPointMul B.unop A
    have hp := hm.comp ((h.symm.continuous.comp continuous_fst).prodMk
      (h.symm.continuous.comp continuous_snd))
    convert h.continuous.comp hp using 1
    funext p
    change p.1 * p.2 = h (h.symm p.1 * h.symm p.2)
    rw [affinePointsIsoHomeomorph_map_mul]
    change p.1 * p.2 = h (h.symm p.1) * h (h.symm p.2)
    rw [h.apply_symm_apply, h.apply_symm_apply]

end Langlands.GroupScheme
