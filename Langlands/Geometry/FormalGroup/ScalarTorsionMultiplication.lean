import Langlands.Geometry.FormalGroup.ScalarTorsionSchemeExactness

/-! # Scalar multiplication from inclusion and transfer on actual torsion schemes -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.FormalGroup.ModuleLaw.IsPiDivisible

open CommGroupScheme

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ] {M : ModuleLaw O R σ} {p : ℕ}
variable (hM : M.IsPiDivisible (p : O))

private theorem evaluate_nsmul_id {S : Scheme.{v}} (H : CommGroupScheme S) (k : ℕ)
    (T : Over S) (x : T ⟶ H.X) :
    let f : H ⟶ H := k • (𝟙 H)
    (Additive.ofMul (x ≫ f.toMul.hom.hom) : Additive (T ⟶ H.X)) = k • Additive.ofMul x := by
  let e : GroupScheme.HomAdd H.toGrp H.toGrp →+ Additive (T ⟶ H.X) :=
    GroupScheme.evalHom H.toGrp H.toGrp T x
  have he := e.map_nsmul k (𝟙 H)
  change (Additive.ofMul (x ≫ (k • (𝟙 H)).toMul.hom.hom) : Additive (T ⟶ H.X)) =
    k • Additive.ofMul (x ≫ 𝟙 H.X) at he
  rw [Category.comp_id] at he
  exact he

private theorem nsmul_id_affine {τ : Type} [Finite τ] {N : ModuleLaw O R τ} {g : Hom M N}
    (P : g.FiniteKernelModel) (k : ℕ) (A : CommAlgCat.{v} R)
    (x : affineTest A ⟶ P.commGroupScheme.X) :
    let f : P.commGroupScheme ⟶ P.commGroupScheme := k • (𝟙 P.commGroupScheme)
    P.affinePointsEquiv A (Additive.ofMul (x ≫ f.toMul.hom.hom)) =
      k • P.affinePointsEquiv A (Additive.ofMul x) :=
  (congrArg (P.affinePointsEquiv A) (evaluate_nsmul_id P.commGroupScheme k (affineTest A) x)).trans
    (map_nsmul (P.affinePointsEquiv A) k (Additive.ofMul x))

/-- Transfer followed by inclusion is actual multiplication on the higher level. -/
theorem torsionSchemeTower_comp_inclusion {m n : ℕ} (i : m ⟶ n) :
    hM.torsionSchemeTower.map i.op ≫ hM.torsionSchemeInclusions.map i =
      p ^ (n - m) • (𝟙 (hM.torsionSchemeInclusions.obj n)) := by
  let P := hM.torsionKernelModel n
  let Q := hM.torsionKernelModel m
  let inc : Q.commGroupScheme ⟶ P.commGroupScheme := hM.torsionSchemeInclusions.map i
  let tr : P.commGroupScheme ⟶ Q.commGroupScheme := hM.torsionSchemeTower.map i.op
  let k := p ^ (n - m)
  change tr ≫ inc = k • (𝟙 P.commGroupScheme)
  apply P.hom_ext_affinePoints P
  intro A x
  let y := x ≫ tr.toMul.hom.hom
  have ht : Q.affinePointsEquiv A (Additive.ofMul y) =
      (M.torsionTransition (p : O) (leOfHom i)).app A (P.affinePointsEquiv A (Additive.ofMul x)) :=
    hM.torsionSchemeTower_affinePoints i A x
  have hi : P.affinePointsEquiv A (Additive.ofMul (y ≫ inc.toMul.hom.hom)) =
      (M.torsionIncl (p : O) (leOfHom i)).app A (Q.affinePointsEquiv A (Additive.ofMul y)) :=
    hM.torsionSchemeInclusions_affinePoints i A y
  change P.affinePointsEquiv A (Additive.ofMul (x ≫ tr.toMul.hom.hom ≫ inc.toMul.hom.hom)) = _
  rw [← Category.assoc]
  exact hi.trans ((congrArg ((M.torsionIncl (p : O) (leOfHom i)).app A) ht).trans (by
    refine Eq.trans ?_ (nsmul_id_affine P k A x).symm
    apply Subtype.ext
    rw [torsionIncl_app_val, torsionTransition_app_val, ← Nat.cast_pow]
    exact Nat.cast_smul_eq_nsmul (R := O) k _))

/-- Inclusion followed by transfer is multiplication by the same scalar on the lower level. -/
theorem torsionSchemeInclusions_comp_transfer {m n : ℕ} (i : m ⟶ n) :
    hM.torsionSchemeInclusions.map i ≫ hM.torsionSchemeTower.map i.op =
      p ^ (n - m) • (𝟙 (hM.torsionSchemeInclusions.obj m)) := by
  let P := hM.torsionKernelModel m
  let Q := hM.torsionKernelModel n
  let inc : P.commGroupScheme ⟶ Q.commGroupScheme := hM.torsionSchemeInclusions.map i
  let tr : Q.commGroupScheme ⟶ P.commGroupScheme := hM.torsionSchemeTower.map i.op
  let k := p ^ (n - m)
  change inc ≫ tr = k • (𝟙 P.commGroupScheme)
  apply P.hom_ext_affinePoints P
  intro A x
  let y := x ≫ inc.toMul.hom.hom
  have hi : Q.affinePointsEquiv A (Additive.ofMul y) =
      (M.torsionIncl (p : O) (leOfHom i)).app A (P.affinePointsEquiv A (Additive.ofMul x)) :=
    hM.torsionSchemeInclusions_affinePoints i A x
  have ht : P.affinePointsEquiv A (Additive.ofMul (y ≫ tr.toMul.hom.hom)) =
      (M.torsionTransition (p : O) (leOfHom i)).app A (Q.affinePointsEquiv A (Additive.ofMul y)) :=
    hM.torsionSchemeTower_affinePoints i A y
  change P.affinePointsEquiv A (Additive.ofMul (x ≫ inc.toMul.hom.hom ≫ tr.toMul.hom.hom)) = _
  rw [← Category.assoc]
  exact ht.trans ((congrArg ((M.torsionTransition (p : O) (leOfHom i)).app A) hi).trans (by
    refine Eq.trans ?_ (nsmul_id_affine P k A x).symm
    apply Subtype.ext
    rw [torsionTransition_app_val, torsionIncl_app_val, ← Nat.cast_pow]
    exact Nat.cast_smul_eq_nsmul (R := O) k _))

end Langlands.FormalGroup.ModuleLaw.IsPiDivisible
