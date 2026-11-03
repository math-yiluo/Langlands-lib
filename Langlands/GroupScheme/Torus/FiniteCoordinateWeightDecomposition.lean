import Langlands.GroupScheme.Lie.FiniteCoordinateCoefficients
import Langlands.GroupScheme.Torus.ActionWeightDecomposition

/-! # Split-torus Lie decomposition from natural finite coordinates -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace Lie.FiniteCoordinates

variable {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)}
    [IsAffineHom G.X.hom] {d : ℕ} (c : Lie.FiniteCoordinates G d)
    (b : AutomorphicAction H G)
    {A : Type u} [CommRing A] [Algebra R A] {M : Type u} [AddCommMonoid M]

include c in
/-- A constant differential commutes with each group-algebra coefficient. -/
theorem kernelCoefficient_differential (h : AffinePoints H A) (m : M)
    (x : Additive (lieKernel G (AddMonoidAlgebra A M))) :
    kernelCoefficient G A M m
        (b.differential
          (affineMap H (IsScalarTower.toAlgHom R A (AddMonoidAlgebra A M)) h) x) =
      b.differential h (kernelCoefficient G A M m x) := by
  classical
  have hsum (p : M →₀ Additive (lieKernel G A)) :
      kernelCoefficient G A M m
          (b.differential
            (affineMap H (IsScalarTower.toAlgHom R A (AddMonoidAlgebra A M)) h)
            (p.sum fun n y => AddMonoidAlgebra.single n (1 : A) •
              lieKernelMapLinear G (IsScalarTower.toAlgHom R A (AddMonoidAlgebra A M)) y)) =
        b.differential h (p m) := by
    induction p using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq =>
        rw [Finsupp.sum_add_index]
        · simp only [map_add, hp, hq, Finsupp.add_apply]
        · intro n; simp
        · intro n y z; simp [smul_add]
    | single n y =>
        rw [Finsupp.sum_single_index (by simp), map_smul, ← b.differential_naturality,
          kernelCoefficient_monomial]
        by_cases hnm : n = m
        · subst m; simp
        · simp [hnm, Ne.symm hnm]
  simpa only [FiniteCoordinates.kernelCoefficients_reconstruct, FiniteCoordinates.kernelCoefficients_apply] using
    hsum (c.kernelCoefficients A M x)

end Lie.FiniteCoordinates

namespace splitTorus.FiniteLieWeights

variable {R : CommRingCat.{u}} (I : Type u) [Fintype I] [DecidableEq I]
    (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]
    (b : AutomorphicAction (splitTorus (Spec R) I) G)

attribute [local instance] Lie.coordinateOriginAlgebra

private theorem kernelMapLinear_const {A B : Type u}
    [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (X : Additive (lieKernel G R)) :
    lieKernelMapLinear G f (lieKernelMapLinear G (Algebra.ofId R A) X) =
      lieKernelMapLinear G (Algebra.ofId R B) X := by
  apply (Lie.kernelDerivationLinearEquiv G).injective
  apply Derivation.ext
  intro c
  simp only [Lie.kernelDerivationLinearEquiv_map, Algebra.ofId_apply, AlgHom.commutes]

variable {d : ℕ} (c : Lie.FiniteCoordinates G d)

/-- The finite exponent coefficients of the actual universal differential. -/
def universalActionCoefficients :
    Additive (lieKernel G R) →ₗ[R] ((I → ℤ) →₀ Additive (lieKernel G R)) :=
  (c.kernelCoefficients R (I → ℤ)).comp (splitTorus.universalDifferential I G b)

@[simp] theorem universalActionCoefficients_apply
    (X : Additive (lieKernel G R)) (m : I → ℤ) :
    universalActionCoefficients I G b c X m =
      Lie.kernelCoefficient G R (I → ℤ) m (splitTorus.universalDifferential I G b X) := rfl

variable {A : Type u} [CommRing A] [Algebra R A]

/-- Each universal coefficient satisfies its exponent-weight equation over every test algebra. -/
theorem universalActionCoefficients_weight (t : I → Aˣ)
    (X : Additive (lieKernel G R)) (m : I → ℤ) :
    b.differential ((algebraPointsEquiv I A).symm t)
        (lieKernelMapLinear G (Algebra.ofId R A)
          (universalActionCoefficients I G b c X m)) =
      (exponentValue I t (Multiplicative.ofAdd m) : A) •
        lieKernelMapLinear G (Algebra.ofId R A)
          (universalActionCoefficients I G b c X m) := by
  have h := congrArg (Lie.kernelCoefficient G A (I → ℤ) m)
    (splitTorus.universalDifferential_translatedEvaluation I G b t X)
  rw [kernelCoefficient_translatedEvaluation, c.kernelCoefficient_differential,
    Lie.kernelCoefficient_map] at h
  exact h.symm

/-- A pure universal weight has only its prescribed coefficient. -/
theorem universalActionCoefficients_of_monomial
    (X : Additive (lieKernel G R)) (m : I → ℤ)
    (h : splitTorus.universalDifferential I G b X =
      AddMonoidAlgebra.single m (1 : R) •
        lieKernelMapLinear G (Algebra.ofId R _) X) :
    universalActionCoefficients I G b c X = Finsupp.single m X := by
  classical
  apply Finsupp.ext
  intro n
  rw [universalActionCoefficients_apply, h]
  have hf : IsScalarTower.toAlgHom R R (AddMonoidAlgebra R (I → ℤ)) =
      Algebra.ofId R (AddMonoidAlgebra R (I → ℤ)) := by ext
  have hk := Lie.kernelCoefficient_monomial G n m (1 : R) X
  rw [hf] at hk
  simpa only [Finsupp.single_apply, one_smul] using hk

private theorem universalDifferential_evaluateOne (X : Additive (lieKernel G R)) :
    lieKernelMapLinear G (evaluateUnits (R := R) I (fun _ => (1 : Rˣ)))
      (splitTorus.universalDifferential I G b X) = X := by
  have ht : (algebraPointsEquiv (R := R) I R).symm (fun _ => (1 : Rˣ)) = 1 := map_one _
  rw [splitTorus.universalDifferential_map, universalPoint_evaluateUnits, ht]
  change b.differentialRepresentation R 1 _ = _
  rw [map_one]
  change lieKernelMapLinear G (Algebra.ofId R R) X = X
  apply (Lie.kernelDerivationLinearEquiv G).injective
  apply Derivation.ext
  intro c
  simp only [Lie.kernelDerivationLinearEquiv_map, Algebra.ofId_self, AlgHom.id_apply]

/-- Universal action coefficients sum back to the original actual Lie vector. -/
theorem universalActionCoefficients_sum (X : Additive (lieKernel G R)) :
    (universalActionCoefficients I G b c X).sum (fun _ y => y) = X := by
  have h := congrArg (lieKernelMapLinear G (evaluateUnits (R := R) I (fun _ => (1 : Rˣ))))
    (c.kernelCoefficients_reconstruct R (I → ℤ) (splitTorus.universalDifferential I G b X))
  rw [universalDifferential_evaluateOne] at h
  rw [map_finsuppSum] at h
  have hc (y : Additive (lieKernel G R)) :
      lieKernelMapLinear G (Algebra.ofId R R) y = y := by
    apply (Lie.kernelDerivationLinearEquiv G).injective
    apply Derivation.ext
    intro c
    simp only [Lie.kernelDerivationLinearEquiv_map, Algebra.ofId_self, AlgHom.id_apply]
  have hf : IsScalarTower.toAlgHom R R (AddMonoidAlgebra R (I → ℤ)) =
      Algebra.ofId R (AddMonoidAlgebra R (I → ℤ)) := by ext
  rw [hf] at h
  have he (m : I → ℤ) :
      (evaluateUnits (R := R) I (fun _ => (1 : Rˣ))).toRingHom
        (AddMonoidAlgebra.single m 1) = 1 := by
    change evaluateUnits I (fun _ => (1 : Rˣ)) (AddMonoidAlgebra.single m 1) = 1
    simp [exponentValue]
  simpa only [universalActionCoefficients, LinearMap.comp_apply,
    LinearMap.map_smulₛₗ, kernelMapLinear_const, hc, he, one_smul] using h


end splitTorus.FiniteLieWeights

namespace splitTorus.FiniteLieWeights

variable (k : Type u) [Field k] (I : Type u) [Fintype I] [DecidableEq I]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (b : AutomorphicAction (splitTorus (Spec (CommRingCat.of k)) I) G)
    {d : ℕ} (c : Lie.FiniteCoordinates G d)

/-- Universal differential coefficients indexed by actual characters. -/
def characterActionCoefficients :
    Additive (lieKernel G k) →ₗ[k]
      (characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I) →₀
        Additive (lieKernel G k)) :=
  (Finsupp.lmapDomain _ k (characterLatticeEquiv k I).symm).comp
    (universalActionCoefficients I G b c)

@[simp] theorem characterActionCoefficients_apply
    (X : Additive (lieKernel G k))
    (χ : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I)) :
    characterActionCoefficients k I G b c X χ =
      universalActionCoefficients I G b c X (characterLatticeEquiv k I χ) := by
  change Finsupp.mapDomain (characterLatticeEquiv k I).symm
    (universalActionCoefficients I G b c X) χ = _
  simpa only [AddEquiv.symm_apply_apply] using
    Finsupp.mapDomain_apply_of_injective (characterLatticeEquiv k I).symm.injective
      (universalActionCoefficients I G b c X) (characterLatticeEquiv k I χ)

/-- Each character coefficient lies in its differential weight space on all test algebras. -/
theorem characterActionCoefficients_mem (X : Additive (lieKernel G k))
    (χ : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I)) :
    characterActionCoefficients k I G b c X χ ∈
      b.lieWeightSpace (𝟙 (splitTorus (Spec (CommRingCat.of k)) I)) χ := by
  rw [characterActionCoefficients_apply]
  intro A _ _ t
  have h := universalActionCoefficients_weight I G b c (algebraPointsEquiv I A t) X
    (characterLatticeEquiv k I χ)
  rw [MulEquiv.symm_apply_apply, ← characterValue_characterLatticeEquiv_symm k I,
    AddEquiv.symm_apply_apply] at h
  simpa only [Grp.id_hom_hom, Category.comp_id] using h

/-- A vector of one character weight has only that universal exponent coefficient. -/
theorem universalActionCoefficients_of_mem_lieWeightSpace (m : I → ℤ)
    (X : Additive (lieKernel G k))
    (hX : X ∈ b.lieWeightSpace
      (T := commGroupScheme (Spec (CommRingCat.of k)) I) (𝟙 _)
      ((characterLatticeEquiv k I).symm m)) :
    universalActionCoefficients I G b c X = Finsupp.single m X := by
  apply universalActionCoefficients_of_monomial
  have h := (AutomorphicAction.mem_lieWeightSpace.mp hX) _
    (universalPoint (R := CommRingCat.of k) I)
  simp only [Grp.id_hom_hom, Category.comp_id] at h
  rw [characterValue_characterLatticeEquiv_symm, exponentValue_universalPoint] at h
  exact h

/-- A vector in a character weight space has a singleton character coefficient family. -/
theorem characterActionCoefficients_of_mem_lieWeightSpace
    (χ : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I))
    (X : Additive (lieKernel G k)) (hX : X ∈ b.lieWeightSpace (𝟙 _) χ) :
    characterActionCoefficients k I G b c X = Finsupp.single χ X := by
  change Finsupp.mapDomain (characterLatticeEquiv k I).symm
    (universalActionCoefficients I G b c X) = _
  have hX' : X ∈ b.lieWeightSpace
      (T := commGroupScheme (Spec (CommRingCat.of k)) I) (𝟙 _)
      ((characterLatticeEquiv k I).symm (characterLatticeEquiv k I χ)) := by
    simpa only [AddEquiv.symm_apply_apply] using hX
  rw [universalActionCoefficients_of_mem_lieWeightSpace k I G b c _ X hX',
    Finsupp.mapDomain_single, AddEquiv.symm_apply_apply]

/-- Character coefficients sum to the original vector. -/
theorem characterActionCoefficients_sum (X : Additive (lieKernel G k)) :
    (characterActionCoefficients k I G b c X).sum (fun _ y => y) = X := by
  change (Finsupp.mapDomain (characterLatticeEquiv k I).symm
    (universalActionCoefficients I G b c X)).sum (fun _ y => y) = X
  rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
  exact universalActionCoefficients_sum I G b c X

open Classical in
/-- The differential of an actual action of the standard split torus decomposes
the Lie algebra as the internal direct sum of its character weight spaces. -/
theorem isInternal_lieWeightSpace (c : Lie.FiniteCoordinates G d) :
    DirectSum.IsInternal
      (b.lieWeightSpace (T := commGroupScheme (Spec (CommRingCat.of k)) I) (𝟙 _)) := by
  classical
  apply Langlands.LinearAlgebra.isInternal_of_finsupp _ (characterActionCoefficients k I G b c)
  · exact characterActionCoefficients_mem k I G b c
  · intro χ X
    exact characterActionCoefficients_of_mem_lieWeightSpace k I G b c χ X X.property
  · exact characterActionCoefficients_sum k I G b c


end splitTorus.FiniteLieWeights

namespace AutomorphicAction

open Classical in
/-- Every split torus acting through an actual automorphic action decomposes the
actual Lie algebra into its all-test-algebra differential weight spaces. -/
theorem isInternal_lieWeightSpace_of_finiteCoordinates
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] {d : ℕ} (cG : Lie.FiniteCoordinates G d)
    {H : GroupScheme (Spec (CommRingCat.of k))}
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (b : AutomorphicAction H G) (j : T.toGrp ⟶ H) :
    DirectSum.IsInternal (b.lieWeightSpace j) := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  let c := characterLattice.comapIso
    (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) e
  let a := b.restrict (e.inv ≫ j)
  let q := splitTorus.FiniteLieWeights.characterActionCoefficients k I G a cG
  let p := (Finsupp.lmapDomain (Additive (lieKernel G k)) k c).comp q
  have hp (X : Additive (lieKernel G k))
      (χ : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)) :
      p X (c χ) = q X χ := by
    exact Finsupp.mapDomain_apply_of_injective c.injective (q X) χ
  apply Langlands.LinearAlgebra.isInternal_of_finsupp _ p
  · intro X χ
    obtain ⟨ψ, rfl⟩ := c.surjective χ
    rw [hp, lieWeightSpace_comapIso]
    have h := splitTorus.FiniteLieWeights.characterActionCoefficients_mem k I G a cG X ψ
    simpa only [a, lieWeightSpace_restrict, Category.id_comp] using h
  · intro χ X
    have hX : (X : Additive (lieKernel G k)) ∈
        a.lieWeightSpace (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
          (𝟙 _) (c.symm χ) := by
      rw [lieWeightSpace_restrict, Category.id_comp, ← lieWeightSpace_comapIso]
      change (X : Additive (lieKernel G k)) ∈ b.lieWeightSpace j (c (c.symm χ))
      simpa only [AddEquiv.apply_symm_apply] using X.property
    change Finsupp.mapDomain c (q (X : Additive (lieKernel G k))) =
      Finsupp.single χ (X : Additive (lieKernel G k))
    rw [splitTorus.FiniteLieWeights.characterActionCoefficients_of_mem_lieWeightSpace k I G a cG
      (c.symm χ) X hX, Finsupp.mapDomain_single, AddEquiv.apply_symm_apply]
  · intro X
    change (Finsupp.mapDomain c (q X)).sum (fun _ y => y) = X
    rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
    exact splitTorus.FiniteLieWeights.characterActionCoefficients_sum k I G a cG X

end AutomorphicAction
end Langlands.GroupScheme
