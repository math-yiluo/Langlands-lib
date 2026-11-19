import Langlands.Algebra.BrauerScalarExtension
import Langlands.Algebra.BrauerSplitting
import Langlands.Algebra.DivisionFieldEmbeddingsProof
import Langlands.Algebra.LocalDivisionReducedDegree

noncomputable section

open scoped TensorProduct
open Langlands.Brauer ValuativeRel

namespace Langlands.CentralDivision

universe u

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D]

/-- The given finite-dimensional central division algebra as an actual Brauer representative. -/
def divisionAlgebraCSA : CSA.{u, u} K where
  toAlgCat := AlgCat.of K D

omit [Algebra.IsCentral K D] in
private theorem degree_pos {n : ℕ} (hd : Module.finrank K D = n * n) : 0 < n := by
  have h := Module.finrank_pos (R := K) (M := D)
  rw [hd] at h
  exact Nat.pos_of_mul_pos_left h

section EmbeddedField

variable (E : Type u) [Field E] [Algebra K E] [FiniteDimensional K E]

/-- An embedded field of dimension equal to the degree of a division algebra splits it. -/
theorem isSplit_baseChange_of_embeddedField (f : E →ₐ[K] D) {n : ℕ}
    (hd : Module.finrank K D = n * n) (he : Module.finrank K E = n) :
    IsSplit (baseChange E (divisionAlgebraCSA K D)) := by
  let T := E ⊗[K] D
  let W := Twist K D E f
  let : Module E W := Module.compHom W (algebraMap E T)
  let : IsScalarTower K E W := ⟨fun k e x => by
    change (algebraMap E T (k • e)) • x = k • (algebraMap E T e • x)
    have h : algebraMap E T (k • e) = k • algebraMap E T e :=
      map_smul (IsScalarTower.toAlgHom K E T) k e
    rw [h, smul_assoc]⟩
  let : SMulCommClass T E W := ⟨fun t e x => by
    change t • (algebraMap E T e • x) = algebraMap E T e • (t • x)
    rw [← mul_smul, ← mul_smul, Algebra.commutes]⟩
  let : FiniteDimensional E W := Module.Finite.of_restrictScalars_finite K E W
  let g : T →ₐ[E] Module.End E W :=
    { Module.toModuleEnd E W with
      commutes' e := by
        apply LinearMap.ext
        intro x
        rfl }
  let : IsSimpleRing T := CentralSimple.isSimpleRing_baseChange K D E
  have hnW : Module.finrank E W = n := by
    have h := Module.finrank_mul_finrank K E W
    rw [he, (show Module.finrank K W = n * n from hd)] at h
    exact Nat.eq_of_mul_eq_mul_left (degree_pos K D hd) h
  have hdim : Module.finrank E T = Module.finrank E (Module.End E W) := by
    change Module.finrank E (E ⊗[K] D) = Module.finrank E (W →ₗ[E] W)
    rw [Module.finrank_baseChange, Module.finrank_linearMap, hnW, hd]
  have hinj : Function.Injective g := g.toRingHom.injective
  have hsurj : Function.Surjective g :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := g.toLinearMap) hdim).mp hinj
  exact ⟨Module.finrank E W, Module.finrank_pos,
    ⟨(AlgEquiv.ofBijective g ⟨hinj, hsurj⟩).trans
      (LinearMap.toMatrixAlgEquiv (Module.finBasis E W))⟩⟩

end EmbeddedField

section SplittingDegree

variable (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The degree of every finite splitting field is divisible by the division degree. -/
theorem divisionDegree_dvd_splittingDegree {n : ℕ} (hd : Module.finrank K D = n * n)
    (hs : IsSplit (baseChange L (divisionAlgebraCSA K D))) : n ∣ Module.finrank K L := by
  obtain ⟨m, hm, ⟨c⟩⟩ := hs
  change (L ⊗[K] D) ≃ₐ[L] Matrix (Fin m) (Fin m) L at c
  have hdim := c.toLinearEquiv.finrank_eq
  rw [Module.finrank_baseChange, Module.finrank_matrix, Fintype.card_fin, Module.finrank_self,
    mul_one, hd] at hdim
  have hnm : n = m := Nat.mul_self_inj.mp hdim
  let V := Fin m → L
  let f : D →ₐ[K] Module.End L V :=
    ((c.trans Matrix.toLinAlgEquiv').restrictScalars K).toAlgHom.comp
      Algebra.TensorProduct.includeRight
  let : Module D V := Module.compHom V f.toRingHom
  let : IsScalarTower K D V := ⟨fun k d x => by
    change f (k • d) x = k • f d x
    rw [map_smul]
    rfl⟩
  let : FiniteDimensional D V := Module.Finite.of_restrictScalars_finite K D V
  have hV : Module.finrank K V = Module.finrank K L * n := by
    rw [← Module.finrank_mul_finrank K L V, hnm]
    simp [V]
  refine ⟨Module.finrank D V, ?_⟩
  apply Nat.eq_of_mul_eq_mul_right (degree_pos K D hd)
  rw [← hV, ← Module.finrank_mul_finrank K D V, hd]
  ac_rfl

/-- The same divisibility from vanishing of the actual scalar-extended Brauer class. -/
theorem divisionDegree_dvd_of_scalarExtension_eq_zero {n : ℕ}
    (hd : Module.finrank K D = n * n)
    (hs : scalarExtension L (classOf (divisionAlgebraCSA K D)) = 0) : n ∣ Module.finrank K L :=
  divisionDegree_dvd_splittingDegree K D L hd ((classOf_eq_zero_iff _).1 hs)

end SplittingDegree

/-- A central division algebra of degree two has a nonzero actual Brauer class. -/
theorem divisionBrauerClass_ne_zero_of_degree_two (hd : Module.finrank K D = 2 * 2) :
    classOf (divisionAlgebraCSA K D) ≠ 0 := by
  intro h
  have htwo := divisionDegree_dvd_of_scalarExtension_eq_zero K D K hd (by rw [h, map_zero])
  norm_num [Module.finrank_self] at htwo

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The original residue-generated subfield is a splitting field of exactly the division degree. -/
theorem exists_localDivision_splittingDegree {n : ℕ} (hd : Module.finrank K D = n * n) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : FiniteDimensional K E),
      Module.finrank K E = n ∧ scalarExtension E (classOf (divisionAlgebraCSA K D)) = 0 := by
  let b := localDivisionCyclicReducedDegreeGenerator K D
  let E := residueGeneratorSubalgebra K D (b : D)
  let : Field E := residueGeneratorField K D (b : D)
  obtain ⟨_, _, hdim, _, _⟩ := localDivisionCyclicReducedDegreeGenerator_spec K D
  have hdegree : CentralSimple.reducedDegree K D = n := Nat.mul_self_inj.mp
    ((CentralSimple.finrank_eq_reducedDegree_mul_self K D).symm.trans hd)
  have he : Module.finrank K E = n := hdim.trans hdegree
  exact ⟨E, inferInstance, inferInstance, inferInstance, he, (classOf_eq_zero_iff _).2
    (isSplit_baseChange_of_embeddedField K D E E.val hd he)⟩

end Langlands.CentralDivision
