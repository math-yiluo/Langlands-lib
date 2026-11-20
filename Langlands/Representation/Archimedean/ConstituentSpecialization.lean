import Langlands.Representation.Archimedean.ConstituentCompression
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Roots

/-!
# Specialization of a simple constituent of an algebra action

A finite-rank operator shared by two affine families of actions gives finite
matrices of polynomials. Generic intertwiners identify the compressed
determinants, which therefore agree at every parameter.
-/

noncomputable section

open scoped Polynomial
open Polynomial

set_option autoImplicit false

namespace Langlands.Archimedean.ConstituentCompression

variable {ι M N J : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup J]
variable [Module ℂ M] [Module ℂ N] [Module ℂ J]

/-- The free algebra action with a fixed extra generator and affine actions
of the other generators. -/
def affineAction (p : Module.End ℂ M) (L D : ι → Module.End ℂ M) (z : ℂ) :
    FreeAlgebra ℂ (Option ι) →ₐ[ℂ] Module.End ℂ M :=
  FreeAlgebra.lift ℂ (Option.elim · p (fun i => L i + z • D i))

@[simp]
theorem affineAction_none (p : Module.End ℂ M) (L D : ι → Module.End ℂ M) (z : ℂ) :
    affineAction p L D z (FreeAlgebra.ι ℂ none) = p := by
  simp [affineAction]

@[simp]
theorem affineAction_some (p : Module.End ℂ M) (L D : ι → Module.End ℂ M) (z : ℂ) (i : ι) :
    affineAction p L D z (FreeAlgebra.ι ℂ (some i)) = L i + z • D i := by
  simp [affineAction]

private def polynomialAction (p : Module.End ℂ M) (L D : ι → Module.End ℂ M) :
    FreeAlgebra ℂ (Option ι) →ₐ[ℂ] (Module.End ℂ M)[X] :=
  FreeAlgebra.lift ℂ (Option.elim · (C p) (fun i => C (L i) + C (D i) * X))

private def specialize (z : ℂ) : (Module.End ℂ M)[X] →ₐ[ℂ] Module.End ℂ M :=
  eval₂AlgHom (AlgHom.id ℂ _) (algebraMap ℂ _ z)
    (fun T => (Algebra.commute_algebraMap_left z T).symm)

private theorem specialize_polynomialAction (p : Module.End ℂ M)
    (L D : ι → Module.End ℂ M) (z : ℂ) :
    (specialize z).comp (polynomialAction p L D) = affineAction p L D z := by
  apply FreeAlgebra.hom_ext
  funext i
  cases i with
  | none =>
    simp only [Function.comp_apply, AlgHom.comp_apply, polynomialAction, FreeAlgebra.lift_ι_apply,
      Option.elim_none, affineAction_none]
    change (C p).eval₂ (AlgHom.id ℂ _).toRingHom (algebraMap ℂ _ z) = p
    exact eval₂_C _ _
  | some i =>
    simp [polynomialAction, specialize, eval₂AlgHom_apply,
      Algebra.algebraMap_eq_smul_one]

/-- An intertwining equation for the generators extends to the free algebra. -/
theorem intertwines_lift (F : M →ₗ[ℂ] N) (L : ι → Module.End ℂ M) (D : ι → Module.End ℂ N)
    (h : ∀ i x, F (L i x) = D i (F x)) (a : FreeAlgebra ℂ ι) (v : M) :
    F (FreeAlgebra.lift ℂ L a v) = FreeAlgebra.lift ℂ D a (F v) := by
  induction a generalizing v with
  | grade0 c => simp [Algebra.algebraMap_eq_smul_one]
  | grade1 i => simpa using h i v
  | mul a b ha hb => simp only [map_mul, Module.End.mul_apply, ha, hb]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

private theorem compressedDet_eq_of_equiv {A : Type*} [Ring A] [Algebra ℂ A]
    (ρ : A →ₐ[ℂ] Module.End ℂ M) (τ : A →ₐ[ℂ] Module.End ℂ N) (e : M ≃ₗ[ℂ] N)
    (h : ∀ a x, e (ρ a x) = τ a (e x)) (p a : A) :
    compressedDet ρ p a = compressedDet τ p a := by
  let W := LinearMap.range (ρ p)
  let V := LinearMap.range (τ p)
  let f : W →ₗ[ℂ] V := (e.toLinearMap.comp W.subtype).codRestrict V (by
    rintro ⟨_, x, rfl⟩
    exact ⟨e x, (h p x).symm⟩)
  let E : W ≃ₗ[ℂ] V := LinearEquiv.ofBijective f ⟨by
    intro x y hxy
    exact Subtype.ext (e.injective (congrArg Subtype.val hxy)), by
    rintro ⟨_, y, rfl⟩
    obtain ⟨x, rfl⟩ := e.surjective y
    exact ⟨⟨ρ p x, x, rfl⟩, Subtype.ext (h p x)⟩⟩
  let T : Module.End ℂ W := 1 - ((ρ p).rangeRestrict ∘ₗ ρ a ∘ₗ W.subtype)
  let U : Module.End ℂ V := 1 - ((τ p).rangeRestrict ∘ₗ τ a ∘ₗ V.subtype)
  change LinearMap.det T = LinearMap.det U
  have hE (x : W) : (E x : N) = e x := rfl
  have heq (x : W) : E (T x) = U (E x) := by
    apply Subtype.ext
    change e ((x : M) - ρ p (ρ a x)) = (E x : N) - τ p (τ a (E x))
    rw [map_sub, h p, h a, hE]
  have hconj : (E.toLinearMap ∘ₗ T ∘ₗ E.symm.toLinearMap) = U := by
    apply LinearMap.ext
    intro y
    change E (T (E.symm y)) = U y
    rw [heq, LinearEquiv.apply_symm_apply]
  rw [← hconj, LinearMap.det_conj]

private theorem exists_compressedDet_polynomial (p : Module.End ℂ M)
    [FiniteDimensional ℂ (LinearMap.range p)] (L D : ι → Module.End ℂ M)
    (a : FreeAlgebra ℂ (Option ι)) :
    ∃ P : ℂ[X], ∀ z : ℂ, P.eval z =
      compressedDet (affineAction p L D z) (FreeAlgebra.ι ℂ none) a := by
  classical
  let W := LinearMap.range p
  let b := Module.finBasis ℂ W
  let Q := polynomialAction p L D a
  let idx := Fin (Module.finrank ℂ W)
  let entry (i j : idx) : Module.End ℂ M →ₗ[ℂ] ℂ :=
    (b.coord i).comp (p.rangeRestrict.comp (LinearMap.applyₗ (b j : M)))
  let B : Matrix idx idx ℂ[X] := fun i j =>
    C (b.coord i (b j)) - Q.sum fun d T => monomial d (entry i j T)
  refine ⟨B.det, fun z => ?_⟩
  have hz : affineAction p L D z a = specialize z Q :=
    congrArg (fun f : FreeAlgebra ℂ (Option ι) →ₐ[ℂ] Module.End ℂ M => f a)
      (specialize_polynomialAction p L D z).symm
  let detCompression (p T : Module.End ℂ M) : ℂ :=
    LinearMap.det (1 - (p.rangeRestrict ∘ₗ T ∘ₗ (LinearMap.range p).subtype))
  change B.det.eval z = detCompression (affineAction p L D z (FreeAlgebra.ι ℂ none))
    (affineAction p L D z a)
  rw [affineAction_none]
  change Polynomial.evalRingHom z B.det =
    LinearMap.det (1 - (p.rangeRestrict ∘ₗ affineAction p L D z a ∘ₗ W.subtype))
  rw [RingHom.map_det, hz, ← LinearMap.det_toMatrix b]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
  change (B i j).eval z =
    b.coord i (b j - p.rangeRestrict (specialize z Q (b j)))
  rw [map_sub]
  change (C (b.coord i (b j)) - Q.sum (fun d T => monomial d (entry i j T))).eval z =
    b.coord i (b j) - entry i j (specialize z Q)
  rw [eval_sub, eval_C]
  congr 1
  change (Q.sum fun d T => monomial d (entry i j T)).eval z =
    entry i j (Q.eval₂ (RingHom.id _) (algebraMap ℂ _ z))
  simp only [eval₂_eq_sum, RingHom.id_apply,
    Polynomial.sum_def, Polynomial.eval_finsetSum, map_sum, eval_monomial]
  apply Finset.sum_congr rfl
  intro d _
  rw [← map_pow, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, map_smul,
    smul_eq_mul, mul_comm]

/-- Infinitely many intertwining isomorphisms between two affine families
imply transfer of a detected simple constituent at any parameter. -/
theorem isConstituent_of_affine_isomorphisms (p : Module.End ℂ M) (q : Module.End ℂ N)
    [FiniteDimensional ℂ (LinearMap.range p)] [FiniteDimensional ℂ (LinearMap.range q)]
    (L D : ι → Module.End ℂ M) (L' D' : ι → Module.End ℂ N)
    {S : Set ℂ} (hS : S.Infinite)
    (hiso : ∀ z ∈ S, ∃ e : M ≃ₗ[ℂ] N,
      (∀ x, e (p x) = q (e x)) ∧
      (∀ i x, e ((L i + z • D i) x) = (L' i + z • D' i) (e x)))
    (z₀ : ℂ) (σ : FreeAlgebra ℂ (Option ι) →ₐ[ℂ] Module.End ℂ J)
    (hJ : IsConstituent (affineAction p L D z₀) σ) (hsimple : IsSimple σ)
    {j : J} (hj : σ (FreeAlgebra.ι ℂ none) j ≠ 0) :
    IsConstituent (affineAction q L' D' z₀) σ := by
  have hp : FiniteDimensional ℂ
      (LinearMap.range (affineAction p L D z₀ (FreeAlgebra.ι ℂ none))) := by
    rw [affineAction_none]
    infer_instance
  have hq : FiniteDimensional ℂ
      (LinearMap.range (affineAction q L' D' z₀ (FreeAlgebra.ι ℂ none))) := by
    rw [affineAction_none]
    infer_instance
  refine isConstituent_of_compressedDet_eq _ _ σ (FreeAlgebra.ι ℂ none) ?_ hJ hsimple hj
  intro a
  obtain ⟨P, hP⟩ := exists_compressedDet_polynomial p L D a
  obtain ⟨Q, hQ⟩ := exists_compressedDet_polynomial q L' D' a
  rw [← hP z₀, ← hQ z₀]
  congr 1
  apply P.eq_of_infinite_eval_eq Q
  refine hS.mono fun z hz => ?_
  obtain ⟨e, he, he'⟩ := hiso z hz
  change P.eval z = Q.eval z
  rw [hP z, hQ z]
  apply compressedDet_eq_of_equiv _ _ e
  exact intertwines_lift e.toLinearMap _ _ (fun i => by
    cases i with
    | none => exact he
    | some i => exact he' i)

end Langlands.Archimedean.ConstituentCompression
