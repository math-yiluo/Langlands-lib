import Langlands.Automorphic.AssociatedContragredientStatement
import Langlands.Automorphic.ContragredientSphericalSpectrum
import Langlands.Automorphic.CuspidalDualPresentationExistenceStatement
import Langlands.Weil.Representation.DualClasses

/-! # Weak association of contragredients, presented form

The algebraic dual of a relative Weil representation is unramified wherever the
representation is, with the inverse Frobenius spectrum. Combined with the inverse
spherical spectra of contragredient cuspidal realizations, this proves the presented form
of Henniart (2000), §2.2, for the contragredient.
-/

noncomputable section

namespace Langlands.ClassField.Global

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.Unramified Polynomial
open scoped NumberField

universe u uV uP uQ

namespace RelativeWeilGroup

section EulerInverse

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

/-- If `B A = 1` and `det(1 - X A) = ∏ (1 - z X)`, then the transpose of `B` has Euler
polynomial `∏ (1 - z⁻¹ X)`. -/
theorem eulerPolynomial_transpose_of_mul_eq_one {n : ℕ} (A B : Module.End ℂ V)
    (hBA : B * A = 1) (s : Eigenvalues n)
    (hA : LocalFactor.eulerPolynomial A = s.eulerPolynomial) :
    LocalFactor.eulerPolynomial (Module.Dual.transpose (R := ℂ) B) =
      Eigenvalues.eulerPolynomial (s.map fun z => z⁻¹) := by
  classical
  let b := Module.Free.chooseBasis ℂ V
  let M := LinearMap.toMatrix b b A
  have hM : LinearMap.toMatrix b b B * M = 1 := by
    rw [← LinearMap.toMatrix_mul, hBA, LinearMap.toMatrix_one]
  have hinv : M⁻¹ = LinearMap.toMatrix b b B := Matrix.inv_eq_left_inv hM
  have hunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr
    (Matrix.isUnit_det_of_left_inverse hM)
  have hrev : M.charpolyRev = s.eulerPolynomial := by
    rw [← Matrix.reverse_charpoly, LinearMap.charpoly_toMatrix]
    exact hA
  obtain ⟨c, hchar⟩ : ∃ c : ℂ, LinearMap.charpoly (Module.Dual.transpose (R := ℂ) B) =
      C c * s.eulerPolynomial := by
    refine ⟨(-1 : ℂ) ^ Fintype.card (Module.Free.ChooseBasisIndex ℂ V) * Ring.inverse M.det, ?_⟩
    rw [← LinearMap.charpoly_toMatrix _ b.dualBasis, LinearMap.toMatrix_transpose,
      Matrix.charpoly_transpose, ← hinv, Matrix.charpoly_inv M hunit, hrev, map_mul, map_pow,
      map_neg, map_one]
  have key : LocalFactor.eulerPolynomial (Module.Dual.transpose (R := ℂ) B) =
      C c * (C (((s : Multiset ℂˣ).map fun z : ℂˣ => -(z : ℂ)).prod) *
        Eigenvalues.eulerPolynomial (s.map fun z => z⁻¹)) := by
    change (LinearMap.charpoly (Module.Dual.transpose (R := ℂ) B)).reverse = _
    rw [hchar, reverse_mul_of_domain, reverse_C, PairedHecke.C_mul_eulerPolynomial_map_inv]
  have h0 := congrArg (eval 0) key
  rw [LocalFactor.eulerPolynomial_eval_zero, eval_mul, eval_mul, eval_C, eval_C,
    Eigenvalues.eulerPolynomial_eval_zero, mul_one] at h0
  rw [key, ← mul_assoc, ← map_mul, ← h0, C_1, one_mul]

end EulerInverse

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] {c : FundamentalClass.ClassFamily.{u}} {v : FinitePlace F}

/-- With the default Krull topology on `E ≃ₐ[F] E`, discrete because `E/F` is finite, the
class-indexed extension is a topological group. -/
theorem isTopologicalGroup_krull : IsTopologicalGroup (RelativeWeilGroup c F E) :=
  letI := relativeIdeleClassAction F E
  haveI : ContinuousSMul (E ≃ₐ[F] E) (NumberField.IdeleClassGroup (𝓞 E) E) :=
    ⟨continuous_prod_of_discrete_left.mpr (continuous_relativeIdeleClassAut F E)⟩
  NormalizedTwoCocycle.Extension.topologicalGroup _ continuous_of_discreteTopology

attribute [local instance] isTopologicalGroup_krull

/-- The local component of the dual is unramified where that of `S` is. -/
theorem localComponent_dual_isUnramified
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (h : (localComponent S ι).IsUnramified (Weil.Local.localInertia (padicField v))) :
    (localComponent (FiniteRepresentation.dual S) ι).IsUnramified
      (Weil.Local.localInertia (padicField v)) := by
  intro i
  have hi : S.representation (ι (i⁻¹ : Weil.Local.localInertia (padicField v))) = 1 := h i⁻¹
  change Module.Dual.transpose (R := ℂ) (S.representation (ι i)⁻¹) = 1
  rw [← map_inv, ← Subgroup.coe_inv, hi]
  exact LinearMap.ext fun l => LinearMap.ext fun x => rfl

/-- The local Euler polynomial of the dual has the inverse spectrum. -/
theorem localEulerPolynomial_dual {n : ℕ}
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    {s : Eigenvalues n} (h : localEulerPolynomial S ι = s.eulerPolynomial) :
    localEulerPolynomial (FiniteRepresentation.dual S) ι =
      Eigenvalues.eulerPolynomial (s.map fun z => z⁻¹) := by
  let g := ι (Weil.Local.localGeometricFrobenius (padicField v))
  have hg : S.representation g⁻¹ * S.representation g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  exact eulerPolynomial_transpose_of_mul_eq_one (S.representation g) (S.representation g⁻¹)
    hg s h

/-- The unramified matching condition passes to the dual, with the inverse spectrum. -/
theorem IsUnramifiedMatchAt.dual {n : ℕ}
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)} {s : Eigenvalues n}
    (h : IsUnramifiedMatchAt S v s.eulerPolynomial) :
    IsUnramifiedMatchAt (FiniteRepresentation.dual S) v
      (Eigenvalues.eulerPolynomial (s.map fun z => z⁻¹)) :=
  fun w => ⟨(h w).1, fun e ι hι =>
    ⟨localComponent_dual_isUnramified ι ((h w).2 e ι hι).1,
      localEulerPolynomial_dual ι ((h w).2 e ι hι).2⟩⟩

/-- The presented form of Henniart (2000), §2.2, for the contragredient. -/
theorem presentedContragredientAssociation :
    PresentedContragredientAssociationStatement.{u, uV, uP, uQ} := by
  classical
  intro c F E _ _ _ _ _ _ _ r S T T' P P' h hS
  obtain ⟨hc, hn, U, hU, hm⟩ := (isWeaklyAssociated_iff_exists_finset S _).mp hS
  refine (isWeaklyAssociated_iff_exists_finset _ _).mpr
    ⟨(FiniteRepresentation.isContinuous_dual_iff S).mpr hc,
      (FiniteRepresentation.rank_dual S).trans hn, U ∪ P'.exceptional,
      Finset.subset_union_right, fun v hv => ?_⟩
  have hvU : v ∉ U := fun h' => hv (Finset.mem_union_left _ h')
  have hvP : v ∉ P.exceptional := fun h' => hvU (hU h')
  have hvP' : v ∉ P'.exceptional := fun h' => hv (Finset.mem_union_right _ h')
  have key := Automorphic.CuspidalOperatorRealization.eigenvalues_eq_map_inv_of_isContragredientOf
    T T' P P' h v hvP hvP'
  change IsUnramifiedMatchAt _ v (P'.spectralSystem.eigenvalues v hvP').eulerPolynomial
  rw [key]
  exact IsUnramifiedMatchAt.dual (hm v hvU)

/-- The class form, given that a supplied contragredient of a presented cusp object has a
presentation in the output universe. -/
theorem classContragredientAssociation_of_dualPresentationExistence
    (hex : Automorphic.CuspidalDualPresentationExistenceStatement.{u, uP, uQ}) :
    ClassContragredientAssociationStatement.{u, uV, uP, uQ} := by
  intro c F E _ _ _ _ _ _ _ r S π π' h hS
  obtain ⟨T, rfl⟩ := π.exists_representative
  obtain ⟨T', rfl⟩ := π'.exists_representative
  obtain ⟨P, hP⟩ := (isWeaklyAssociatedClass_isoClass_iff S T).mp hS
  have h' := (Automorphic.CuspidalOperatorRealization.isoClass_isContragredientOf_iff T' T).mp h
  obtain ⟨P'⟩ := hex F r T T' h' P
  exact (isWeaklyAssociatedClass_isoClass_iff _ T').mpr
    ⟨P', presentedContragredientAssociation c F E S T T' P P' h' hP⟩

end RelativeWeilGroup

end Langlands.ClassField.Global
