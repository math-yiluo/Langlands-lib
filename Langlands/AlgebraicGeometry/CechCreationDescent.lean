import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
import Langlands.Cohomology.CechCup
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Homology

/-! # Degree-one cup creation and descent -/

noncomputable section

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.Cohomology.Cech

section Raising

variable {C : Type*} [Category* C] [Preadditive C]
  (K Q : CochainComplex C ℕ)
  (c : ∀ n, K.X n ⟶ Q.X (n + 1))
  (hc : ∀ n, K.d n (n + 1) ≫ c (n + 1) = -(c n ≫ Q.d (n + 1) (n + 2)))

set_option backward.isDefEq.respectTransparency false in
/-- The short-complex map of an anticommuting degree-raising map. -/
def creationShortComplexMap (n : ℕ) : K.sc n ⟶ Q.sc (n + 1) := by
  cases n with
  | zero =>
    refine (K.isoSc' 0 0 1 CochainComplex.prev_nat_zero (CochainComplex.next ℕ 0)).hom ≫
      ?_ ≫ (Q.isoSc' 0 1 2 (CochainComplex.prev_nat_succ 0) (CochainComplex.next ℕ 1)).inv
    exact
      { τ₁ := 0
        τ₂ := c 0
        τ₃ := -c 1
        comm₁₂ := by
          change (0 : K.X 0 ⟶ Q.X 0) ≫ Q.d 0 1 = K.d 0 0 ≫ c 0
          rw [zero_comp, K.shape 0 0 (by simp), zero_comp]
        comm₂₃ := by
          change c 0 ≫ Q.d 1 2 = K.d 0 1 ≫ (-c 1)
          rw [Preadditive.comp_neg, hc 0, neg_neg] }
  | succ n =>
    refine (K.isoSc' n (n + 1) (n + 2) (CochainComplex.prev_nat_succ n)
      (CochainComplex.next ℕ (n + 1))).hom ≫ ?_ ≫
      (Q.isoSc' (n + 1) (n + 2) (n + 3) (CochainComplex.prev_nat_succ (n + 1))
        (CochainComplex.next ℕ (n + 2))).inv
    exact
      { τ₁ := -c n
        τ₂ := c (n + 1)
        τ₃ := -c (n + 2)
        comm₁₂ := by
          change (-c n) ≫ Q.d (n + 1) (n + 2) = K.d n (n + 1) ≫ c (n + 1)
          simpa only [Preadditive.neg_comp] using (hc n).symm
        comm₂₃ := by
          change c (n + 1) ≫ Q.d (n + 2) (n + 3) =
            K.d (n + 1) (n + 2) ≫ (-c (n + 2))
          rw [Preadditive.comp_neg, hc (n + 1), neg_neg] }

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma creationShortComplexMap_τ₂ (n : ℕ) :
    (creationShortComplexMap K Q c hc n).τ₂ = c n := by
  cases n with
  | zero =>
    change 𝟙 (K.X 0) ≫ c 0 ≫ 𝟙 (Q.X 1) = c 0
    simp
  | succ n =>
    change 𝟙 (K.X (n + 1)) ≫ c (n + 1) ≫ 𝟙 (Q.X (n + 2)) = c (n + 1)
    simp

/-- Descent of an anticommuting degree-raising map to homology. -/
def creationHomologyMap (n : ℕ) [K.HasHomology n] [Q.HasHomology (n + 1)] :
    K.homology n ⟶ Q.homology (n + 1) :=
  ShortComplex.homologyMap (creationShortComplexMap K Q c hc n)

set_option backward.isDefEq.respectTransparency false in
lemma creationCyclesMap_i (n : ℕ) [K.HasHomology n] [Q.HasHomology (n + 1)] :
    ShortComplex.cyclesMap (creationShortComplexMap K Q c hc n) ≫ Q.iCycles (n + 1) =
      K.iCycles n ≫ c n := by
  change ShortComplex.cyclesMap (creationShortComplexMap K Q c hc n) ≫
    (Q.sc (n + 1)).iCycles = (K.sc n).iCycles ≫ c n
  simpa only [creationShortComplexMap_τ₂] using
    ShortComplex.cyclesMap_i (creationShortComplexMap K Q c hc n)

lemma creationHomologyMap_homologyπ (n : ℕ) [K.HasHomology n] [Q.HasHomology (n + 1)] :
    K.homologyπ n ≫ creationHomologyMap K Q c hc n =
      ShortComplex.cyclesMap (creationShortComplexMap K Q c hc n) ≫ Q.homologyπ (n + 1) :=
  ShortComplex.homologyπ_naturality _

end Raising

section Cochains

open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R)
  [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halg : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom π W).hom)
  {ι : Type w} (U : ι → X.Opens)

include halg in
lemma face_smul {p n : ℕ} (b : ∀ σ : Fin (p + 1) → ι, Γ(X, inter U σ))
    (τ : Fin n → ι) (θ : Fin (p + 1) → Fin n) (r : R) :
    face (P := ab X.presheaf) (U := U) (r • b) τ θ =
      r • (show Γ(X, inter U τ) from face (P := ab X.presheaf) (U := U) b τ θ) := by
  exact (resAlgHom π halg (inter_le_comp τ θ)).toLinearMap.map_smul r _

/-- The Alexander--Whitney product with a one-cochain as an R-linear map. -/
def cup₁LinearMap (z : C (ab X.presheaf) U 1) (n : ℕ) :
    (∀ σ : Fin (n + 1) → ι, Γ(X, inter U σ)) →ₗ[R]
      ∀ σ : Fin (n + 2) → ι, Γ(X, inter U σ) where
  toFun := cup₁ X.presheaf U z
  map_add' b b' := cup₁_add_right z b b'
  map_smul' r b := by
    funext τ
    simp only [cup₁_apply, face_smul π halg, Pi.smul_apply, RingHom.id_apply]
    exact mul_smul_comm (β := Γ(X, inter U τ)) r _ _

/-- The additive cochain map of cup creation. -/
def cup₁AddHom (z : C (ab X.presheaf) U 1) (n : ℕ) :
    (complex (ab X.presheaf) U).X n ⟶ (complex (ab X.presheaf) U).X (n + 1) :=
  AddCommGrpCat.ofHom (cup₁LinearMap π halg U z n).toAddMonoidHom

set_option backward.isDefEq.respectTransparency false in
/-- Cup creation by an actual one-cocycle on all-sequence Cech homology. -/
def cup₁HomologyMap (z : C (ab X.presheaf) U 1) (hz : d (ab X.presheaf) U 1 z = 0)
    (n : ℕ) :
    (complex (ab X.presheaf) U).homology n ⟶ (complex (ab X.presheaf) U).homology (n + 1) :=
  creationHomologyMap _ _ (cup₁AddHom π halg U z)
    (fun n => by
      change (complex (ab X.presheaf) U).d n (n + 1) ≫
        cup₁AddHom π halg U z (n + 1) =
          -(cup₁AddHom π halg U z n ≫
            (complex (ab X.presheaf) U).d (n + 1) ((n + 1) + 1))
      dsimp only [complex, AlgebraicTopology.alternatingCofaceMapComplex,
        AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      ext b
      change cup₁ X.presheaf U z (d (ab X.presheaf) U n b) =
        -d (ab X.presheaf) U (n + 1) (cup₁ X.presheaf U z b)
      rw [d_cup₁_of_cocycle hz b, neg_neg]) n

end Cochains

end Langlands.Cohomology.Cech
