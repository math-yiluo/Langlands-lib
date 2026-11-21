import Langlands.Geometry.FormalGroup.ScalarTorsionSchemes

/-! # The affine fppf short exact sequence of actual scalar torsion schemes -/

noncomputable section

set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.CommGroupScheme

variable {R : CommRingCat.{v}} {G H J : CommGroupScheme (Spec R)}

/-- The actual affine test scheme of a coefficient algebra over the base. -/
abbrev affineTest (A : CommAlgCat.{v} R) : Over (Spec R) := (algSpec R).obj (op A)

/-- Short exactness on affine fppf tests. The first map is injective on affine points,
its image is the kernel of the second, and the second has lifts after affine fppf extension. -/
def AffineFppfShortExact (i : G ⟶ H) (q : H ⟶ J) : Prop :=
  (∀ A : CommAlgCat.{v} R,
    Function.Injective (fun x : affineTest A ⟶ G.X => x ≫ i.toMul.hom.hom)) ∧
  (∀ (A : CommAlgCat.{v} R) (x : affineTest A ⟶ H.X),
    x ≫ q.toMul.hom.hom = 1 ↔ ∃ y : affineTest A ⟶ G.X, y ≫ i.toMul.hom.hom = x) ∧
  (∀ (A : CommAlgCat.{v} R) (y : affineTest A ⟶ J.X),
    ∃ (B : CommAlgCat.{v} R) (φ : A ⟶ B),
      φ.hom.toRingHom.FaithfullyFlat ∧ φ.hom.FinitePresentation ∧
        ∃ x : affineTest B ⟶ H.X, x ≫ q.toMul.hom.hom = (algSpec R).map φ.op ≫ y)

end Langlands.CommGroupScheme

namespace Langlands.FormalGroup.ModuleLaw.IsPiDivisible

open CommGroupScheme

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ] {M : ModuleLaw O R σ} {π : O}
variable (hM : M.IsPiDivisible π)

/-- The actual group scheme inclusion evaluates as the inclusion of scalar-kernel points. -/
theorem torsionSchemeInclusions_affinePoints {m n : ℕ} (i : m ⟶ n)
    (A : CommAlgCat.{v} R)
    (x : (algSpec (CommRingCat.of R)).obj (op A) ⟶ (hM.torsionKernelModel m).commGroupScheme.X) :
    let f : (hM.torsionKernelModel m).commGroupScheme ⟶ (hM.torsionKernelModel n).commGroupScheme :=
      hM.torsionSchemeInclusions.map i
    (hM.torsionKernelModel n).affinePointsEquiv A (Additive.ofMul (x ≫ f.toMul.hom.hom)) =
      (M.torsionIncl π (leOfHom i)).app A ((hM.torsionKernelModel m).affinePointsEquiv A (Additive.ofMul x)) :=
  (hM.torsionKernelModel m).commGroupSchemeMap_affinePoints (hM.torsionKernelModel n)
    (M.torsionIncl π (leOfHom i)) x

/-- The actual scalar transition evaluates as multiplication on the original kernel points. -/
theorem torsionSchemeTower_affinePoints {m n : ℕ} (i : m ⟶ n)
    (A : CommAlgCat.{v} R)
    (x : (algSpec (CommRingCat.of R)).obj (op A) ⟶ (hM.torsionKernelModel n).commGroupScheme.X) :
    let f : (hM.torsionKernelModel n).commGroupScheme ⟶ (hM.torsionKernelModel m).commGroupScheme :=
      hM.torsionSchemeTower.map i.op
    (hM.torsionKernelModel m).affinePointsEquiv A (Additive.ofMul (x ≫ f.toMul.hom.hom)) =
      (M.torsionTransition π (leOfHom i)).app A ((hM.torsionKernelModel n).affinePointsEquiv A (Additive.ofMul x)) :=
  (hM.torsionKernelModel n).commGroupSchemeMap_affinePoints (hM.torsionKernelModel m)
    (M.torsionTransition π (leOfHom i)) x

/-- At the actual scheme level, the scalar kernel inclusion and scalar multiplication
satisfy the affine fppf short exactness conditions. -/
theorem torsionSchemes_affineFppfShortExact (m n : ℕ) :
    AffineFppfShortExact (hM.torsionSchemeInclusions.map (homOfLE (Nat.le_add_left n m)))
      (hM.torsionSchemeTower.map (homOfLE (Nat.le_add_right m n)).op) := by
  let P := hM.torsionKernelModel n
  let Q := hM.torsionKernelModel (m + n)
  let U := hM.torsionKernelModel m
  let i : n ⟶ m + n := homOfLE (Nat.le_add_left n m)
  let j : m ⟶ m + n := homOfLE (Nat.le_add_right m n)
  let proj := (hM.torsionSchemeTower.map j.op).toMul.hom.hom
  refine ⟨?_, ?_, ?_⟩
  · intro A x y hxy
    apply (P.affinePointsEquiv A).injective
    apply torsionIncl_app_injective M π (Nat.le_add_left n m)
    exact (hM.torsionSchemeInclusions_affinePoints i A x).symm.trans
      ((congrArg (fun z => Q.affinePointsEquiv A z) hxy).trans
        (hM.torsionSchemeInclusions_affinePoints i A y))
  · intro A x
    have hproj : U.affinePointsEquiv A (x ≫ proj) =
        (M.torsionTransition π (Nat.le_add_right m n)).app A (Q.affinePointsEquiv A x) :=
      hM.torsionSchemeTower_affinePoints j A x
    have hz : U.affinePointsEquiv A (1 : affineTest A ⟶ U.commGroupScheme.X) = 0 :=
      (U.affinePointsEquiv A).map_zero
    constructor
    · intro hx
      have h : (M.torsionTransition π (Nat.le_add_right m n)).app A (Q.affinePointsEquiv A x) = 0 :=
        hproj.symm.trans ((congrArg (fun z => U.affinePointsEquiv A z) hx).trans hz)
      obtain ⟨y, hy⟩ := (M.torsionTransition_add_eq_zero_iff π m n (Q.affinePointsEquiv A x)).mp h
      let z := (P.affinePointsEquiv A).symm y
      refine ⟨z, (Q.affinePointsEquiv A).injective ?_⟩
      exact (hM.torsionSchemeInclusions_affinePoints i A z).trans
        ((congrArg ((M.torsionIncl π (Nat.le_add_left n m)).app A)
          ((P.affinePointsEquiv A).apply_symm_apply y)).trans hy)
    · rintro ⟨y, hy⟩
      apply (U.affinePointsEquiv A).injective
      have hm := (hM.torsionSchemeInclusions_affinePoints i A y).symm.trans
        (congrArg (fun z => Q.affinePointsEquiv A z) hy)
      exact hproj.trans (((M.torsionTransition_add_eq_zero_iff π m n _).mpr
        ⟨P.affinePointsEquiv A y, hm⟩).trans hz.symm)
  · intro A y
    obtain ⟨B, φ, hflat, hfp, x, hx⟩ := hM.torsionTransition_locallySurjective (Nat.le_add_right m n)
      (U.affinePointsEquiv A y)
    let z := (Q.affinePointsEquiv B).symm x
    refine ⟨B, φ, hflat, hfp, z, (U.affinePointsEquiv B).injective ?_⟩
    exact (hM.torsionSchemeTower_affinePoints j B z).trans
      ((congrArg ((M.torsionTransition π (Nat.le_add_right m n)).app B)
        ((Q.affinePointsEquiv B).apply_symm_apply x)).trans
          (hx.trans (U.affinePointsEquiv_naturality φ y).symm))

end Langlands.FormalGroup.ModuleLaw.IsPiDivisible
