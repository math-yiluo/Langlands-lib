import Langlands.GroupScheme.Lie.HomogeneousBasis

/-! # Natural homogeneous coordinates on actual Lie kernels -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {d m : ℕ}

namespace Lie.FiniteCoordinates

variable (c : Lie.FiniteCoordinates G d)
    (v : Module.Basis (Fin m) k (Additive (lieKernel G k)))

/-- Coefficient change takes each extended basis vector to the corresponding
extended basis vector. -/
theorem baseChangeBasis_naturality
    {A B : CommAlgCat.{u} (CommRingCat.of k)} (f : A ⟶ B) (i : Fin m) :
    lieKernelMapLinear G f.hom (c.baseChangeBasis v A i) =
      c.baseChangeBasis v B i := by
  let fA : CommAlgCat.of (CommRingCat.of k) k ⟶ A :=
    CommAlgCat.ofHom (Algebra.ofId k A)
  let fB : CommAlgCat.of (CommRingCat.of k) k ⟶ B :=
    CommAlgCat.ofHom (Algebra.ofId k B)
  apply (c.equiv B).injective
  simp only [c.naturality, c.baseChangeBasis_apply]
  change (fun j => f.hom
      ((c.equiv A) (lieKernelMapLinear G fA.hom (v i)) j)) =
    (c.equiv B) (lieKernelMapLinear G fB.hom (v i))
  rw [c.naturality fA, c.naturality fB]
  funext j
  exact f.hom.commutes _

/-- Coordinates in any base-field basis are natural on every test algebra. -/
theorem baseChangeBasis_equivFun_naturality
    {A B : CommAlgCat.{u} (CommRingCat.of k)} (f : A ⟶ B)
    (x : Additive (lieKernel G A)) :
    (c.baseChangeBasis v B).equivFun (lieKernelMapLinear G f.hom x) =
      fun i => f.hom ((c.baseChangeBasis v A).equivFun x i) := by
  classical
  apply (c.baseChangeBasis v B).equivFun.symm.injective
  rw [LinearEquiv.symm_apply_apply, Module.Basis.equivFun_symm_apply]
  conv_lhs => rw [← (c.baseChangeBasis v A).sum_equivFun x]
  simp only [map_sum, LinearMap.map_smulₛₗ, c.baseChangeBasis_naturality v]
  rfl

/-- Replace finite Lie coordinates by the coordinates in an arbitrary base-field
basis, extended by the actual coefficient-change maps. -/
def inBasis : Lie.FiniteCoordinates G m where
  equiv A := (c.baseChangeBasis v A).equivFun
  naturality := c.baseChangeBasis_equivFun_naturality v

/-- The change from the original finite coordinates to the chosen basis. -/
def basisTransition (A : CommAlgCat.{u} (CommRingCat.of k)) :
    (Fin d → A) ≃ₗ[A] (Fin m → A) :=
  (c.equiv A).symm.trans ((c.inBasis v).equiv A)

/-- The change of basis commutes with every coefficient map. -/
theorem basisTransition_naturality
    {A B : CommAlgCat.{u} (CommRingCat.of k)} (f : A ⟶ B) (x : Fin d → A) :
    c.basisTransition v B (fun i => f.hom (x i)) =
      fun i => f.hom (c.basisTransition v A x i) := by
  have hx : (c.equiv B).symm (fun i => f.hom (x i)) =
      lieKernelMapLinear G f.hom ((c.equiv A).symm x) := by
    apply (c.equiv B).injective
    rw [LinearEquiv.apply_symm_apply, c.naturality, LinearEquiv.apply_symm_apply]
  change (c.inBasis v).equiv B ((c.equiv B).symm _) = _
  rw [hx, (c.inBasis v).naturality]
  rfl

end Lie.FiniteCoordinates

namespace HomogeneousLieBasis

variable {H : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {b : AutomorphicAction H G} {j : T.toGrp ⟶ H}
    (q : HomogeneousLieBasis b j) (c : Lie.FiniteCoordinates G d)

/-- In the extended homogeneous basis, the original differential acts by the
actual character value in each coordinate. -/
theorem differential_coordinates (A : CommAlgCat.{u} (CommRingCat.of k))
    (t : Lie.AffinePoints T.toGrp A) (x : Additive (lieKernel G A))
    (i : Fin q.dimension) :
    (c.inBasis q.basis).equiv A (b.differential (t ≫ j.hom.hom) x) i =
      (Lie.characterValue (q.weight i) t : A) *
        (c.inBasis q.basis).equiv A x i := by
  classical
  let v := c.baseChangeBasis q.basis A
  change v.equivFun (b.differential (t ≫ j.hom.hom) x) i =
    (Lie.characterValue (q.weight i) t : A) * v.equivFun x i
  have hdiff : b.differential (t ≫ j.hom.hom) x =
      ∑ l, v.equivFun x l • ((Lie.characterValue (q.weight l) t : A) • v l) := by
    conv_lhs => rw [← v.sum_equivFun x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [map_smul]
    exact congrArg (fun y => v.equivFun x l • y) (q.differential_basis c A t l)
  rw [hdiff, map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, Module.Basis.equivFun_self, smul_eq_mul]
  simp [mul_comm]

end HomogeneousLieBasis
end Langlands.GroupScheme
