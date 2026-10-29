import Langlands.Representation.Whittaker.MixedFunctionalBilinearBoundsStatement
import Langlands.Representation.Filtration.MixedBilinearBoundsProof
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof

/-! Separate-group assembly from functional positions and finite exceptions. -/

noncomputable section

namespace Langlands.ObjectRepFiltration

universe uH uW

variable {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Admissibility passes to every actual graded quotient under compact-open
cofinality, through the upper step and its graded projection. -/
theorem isAdmissible_gradedRepresentation
    (hH : ∀ L : OpenSubgroup H, ∃ K : OpenSubgroup H, IsCompact (K : Set H) ∧ K ≤ L)
    {B : Rep.{uW} ℂ H} {n : ℕ} (g : ObjectRepFiltration B n)
    (hB : IsAdmissible B.ρ) (j : Fin n) :
    IsAdmissible (g.gradedRepresentation j).ρ := by
  let incl : (g.subrepresentation j.succ).toRepresentation.IntertwiningMap B.ρ :=
    { toLinearMap := (g.subrepresentation j.succ).toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  exact Unramified.SphericalExistence.isAdmissible_of_surjective hH
    (g.gradedProjection j).hom (g.gradedProjection_surjective j)
    (isAdmissible_of_injective incl (Submodule.injective_subtype _) hB)

end Langlands.ObjectRepFiltration

namespace Langlands.MixedBilinear

universe uG uH uI uS uZ uV uW

section FunctionalFactors

variable {G : Type uG} [Group G] {H : Type uH} [Group H] {I : Type uI}
variable {A : Rep.{uV} ℂ G} {B : Rep.{uW} ℂ H} {m n : ℕ}
variable (U : Subgroup G) (θ : U →* ℂˣ) (U' : Subgroup H) (θ' : U' →* ℂˣ)
variable (f : ObjectRepFiltration A m) (g : ObjectRepFiltration B n)
variable (a : I → G) (b : I → H)

/-- Unique actual functional positions reduce mixed pair control to length one. -/
theorem length_le_one_of_unique_functional_factors (η : I → ℂ)
    (hA : ∃! i : Fin m,
      Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ)
    (hB : ∃! j : Fin n,
      Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ)
    (hdetect : ∀ i j,
      length a b η (f.gradedRepresentation i).ρ (g.gradedRepresentation j).ρ ≠ 0 →
        Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ ∧
        Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ)
    (hbound : ∀ i j,
      Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ →
      Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ →
      length a b η (f.gradedRepresentation i).ρ (g.gradedRepresentation j).ρ ≤ 1) :
    length a b η A.ρ B.ρ ≤ 1 := by
  classical
  obtain ⟨i₀, hi₀, hi⟩ := hA
  obtain ⟨j₀, hj₀, hj⟩ := hB
  apply (length_le_of_single_pair f g a b η i₀ j₀ ?_).trans
    (hbound i₀ j₀ hi₀ hj₀)
  intro i j hij
  by_contra hne
  obtain ⟨hfi, hgj⟩ := hdetect i j hne
  exact hij.elim (fun h => h (hi i hfi)) (fun h => h (hj j hgj))

/-- The finite union over actual graded pairs is chosen before the parameter. -/
theorem exists_exception_length_le_one_of_unique_functional_factors
    {S : Type uS} {Z : Type uZ} (z : S → Z) (χ : S → I → ℂ)
    (hA : ∃! i : Fin m,
      Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ)
    (hB : ∃! j : Fin n,
      Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ)
    (hpair : ∀ i j, ∃ E : Finset Z, ∀ s : S, z s ∉ E →
      (length a b (χ s) (f.gradedRepresentation i).ρ (g.gradedRepresentation j).ρ ≠ 0 →
        Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ ∧
        Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ) ∧
      (Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ →
        Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ →
        length a b (χ s) (f.gradedRepresentation i).ρ
          (g.gradedRepresentation j).ρ ≤ 1)) :
    ∃ E : Finset Z, ∀ s : S, z s ∉ E → length a b (χ s) A.ρ B.ρ ≤ 1 := by
  classical
  choose E hE using hpair
  refine ⟨InvariantBilinear.gradedExceptionSet E, ?_⟩
  intro s hs
  have hp := fun i j => hE i j s
    (InvariantBilinear.not_mem_pair_of_not_mem_gradedExceptionSet E hs i j)
  exact length_le_one_of_unique_functional_factors U θ U' θ' f g a b (χ s) hA hB
    (fun i j => (hp i j).1) (fun i j => (hp i j).2)

end FunctionalFactors

section Smooth

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {I : Type uI}
variable (U : Subgroup G) (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U)
variable (θ : U →* ℂˣ) (hθ : IsLocallyConstant (fun u : U => (θ u : ℂ)))
variable (U' : Subgroup H) (hU' : Jacquet.Localization.IsLimitOfCompactSubgroups U')
variable (θ' : U' →* ℂˣ) (hθ' : IsLocallyConstant (fun u : U' => (θ' u : ℂ)))

include hU hθ hU' hθ'

/-- Functional exactness supplies the unique positions independently over both groups. -/
theorem exists_exception_length_le_one_of_functional_equiv
    {A : Rep.{uV} ℂ G} {B : Rep.{uW} ℂ H} {m n : ℕ}
    (f : ObjectRepFiltration A m) (g : ObjectRepFiltration B n)
    (a : I → G) (b : I → H) {S : Type uS} {Z : Type uZ}
    (z : S → Z) (χ : S → I → ℂ)
    (hA : IsSmooth A.ρ) (hB : IsSmooth B.ρ)
    (eA : Whittaker.functionals U θ A.ρ ≃ₗ[ℂ] ℂ)
    (eB : Whittaker.functionals U' θ' B.ρ ≃ₗ[ℂ] ℂ)
    (hpair : ∀ i j, ∃ E : Finset Z, ∀ s : S, z s ∉ E →
      (length a b (χ s) (f.gradedRepresentation i).ρ (g.gradedRepresentation j).ρ ≠ 0 →
        Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ ∧
        Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ) ∧
      (Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ →
        Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ →
        length a b (χ s) (f.gradedRepresentation i).ρ
          (g.gradedRepresentation j).ρ ≤ 1)) :
    ∃ E : Finset Z, ∀ s : S, z s ∉ E → length a b (χ s) A.ρ B.ρ ≤ 1 :=
  exists_exception_length_le_one_of_unique_functional_factors U θ U' θ' f g a b z χ
    (Whittaker.existsUnique_hasFunctional_factor U hU θ hθ f hA eA)
    (Whittaker.existsUnique_hasFunctional_factor U' hU' θ' hθ' g hB eB) hpair

/-- Finite length supplies simple filtrations; admissibility of the second total
representation supplies admissibility of its actual graded factors. -/
theorem exists_exception_length_le_one_of_admissibleSecond_finiteLength
    (hH : ∀ L : OpenSubgroup H, ∃ K : OpenSubgroup H, IsCompact (K : Set H) ∧ K ≤ L)
    (A : Rep.{uV} ℂ G) (B : Rep.{uW} ℂ H)
    (a : I → G) (b : I → H) {S : Type uS} {Z : Type uZ}
    (z : S → Z) (χ : S → I → ℂ)
    (hA : IsSmooth A.ρ) (hB : IsAdmissible B.ρ)
    (hfinA : IsFiniteLength (MonoidAlgebra ℂ G) A.ρ.asModule)
    (hfinB : IsFiniteLength (MonoidAlgebra ℂ H) B.ρ.asModule)
    (eA : Whittaker.functionals U θ A.ρ ≃ₗ[ℂ] ℂ)
    (eB : Whittaker.functionals U' θ' B.ρ ≃ₗ[ℂ] ℂ)
    (hpair : ∀ (C : Rep.{uV} ℂ G) (D : Rep.{uW} ℂ H),
      IsSmooth C.ρ → IsAdmissible D.ρ →
      Representation.IsIrreducible C.ρ → Representation.IsIrreducible D.ρ →
      ∃ E : Finset Z, ∀ s : S, z s ∉ E →
        (length a b (χ s) C.ρ D.ρ ≠ 0 →
          Whittaker.HasFunctional (N := U) (θ := θ) C.ρ ∧
          Whittaker.HasFunctional (N := U') (θ := θ') D.ρ) ∧
        (Whittaker.HasFunctional (N := U) (θ := θ) C.ρ →
          Whittaker.HasFunctional (N := U') (θ := θ') D.ρ →
          length a b (χ s) C.ρ D.ρ ≤ 1)) :
    ∃ E : Finset Z, ∀ s : S, z s ∉ E → length a b (χ s) A.ρ B.ρ ≤ 1 := by
  let f := ObjectRepFiltration.ofFiniteLength A hfinA
  let g := ObjectRepFiltration.ofFiniteLength B hfinB
  apply exists_exception_length_le_one_of_functional_equiv U hU θ hθ U' hU' θ' hθ'
    f.2.val g.2.val a b z χ hA hB.1 eA eB
  intro i j
  exact hpair (f.2.val.gradedRepresentation i) (g.2.val.gradedRepresentation j)
    (f.2.val.isSmooth_gradedRepresentation hA i)
    (g.2.val.isAdmissible_gradedRepresentation hH hB j)
    (f.2.property i) (g.2.property j)

end Smooth

/-- Proof of the uniform unique-functional-position length bound. -/
theorem uniqueFunctionalFactorsLengthBound :
    UniqueFunctionalFactorsLengthBoundStatement.{uG, uH, uI, uV, uW} := by
  intro G _ H _ I U θ U' θ' A B m n f g a b η hA hB hdetect hbound
  exact length_le_one_of_unique_functional_factors U θ U' θ' f g a b η
    hA hB hdetect hbound

/-- Proof of the uniform unique-position finite-exception statement. -/
theorem uniqueFunctionalFactorsFiniteException :
    UniqueFunctionalFactorsFiniteExceptionStatement.{uG, uH, uI, uS, uZ, uV, uW} := by
  intro G _ H _ I U θ U' θ' A B m n f g a b S Z z χ hA hB hpair
  exact exists_exception_length_le_one_of_unique_functional_factors U θ U' θ'
    f g a b z χ hA hB hpair

/-- Proof of the uniform functional-equivalence finite-exception statement. -/
theorem functionalEquivFiniteException :
    FunctionalEquivFiniteExceptionStatement.{uG, uH, uI, uS, uZ, uV, uW} := by
  intro G _ _ _ H _ _ _ I U hU θ hθ U' hU' θ' hθ'
    A B m n f g a b S Z z χ hA hB eA eB hpair
  exact exists_exception_length_le_one_of_functional_equiv U hU θ hθ U' hU' θ' hθ'
    f g a b z χ hA hB eA eB hpair

/-- Proof of the uniform finite-length assembly with admissible second factors. -/
theorem admissibleSecondFiniteLengthException :
    AdmissibleSecondFiniteLengthExceptionStatement.{uG, uH, uI, uS, uZ, uV, uW} := by
  intro G _ _ _ H _ _ _ I U hU θ hθ U' hU' θ' hθ' hH
    A B a b S Z z χ hA hB hfinA hfinB eA eB hpair
  exact exists_exception_length_le_one_of_admissibleSecond_finiteLength
    U hU θ hθ U' hU' θ' hθ' hH A B a b z χ hA hB hfinA hfinB eA eB hpair

/-- The exact closed seven-universe separate-group functional-factor assembly. -/
theorem functionalFactorAssembly :
    FunctionalFactorAssemblyStatement.{uG, uH, uI, uS, uZ, uV, uW} :=
  ⟨uniqueFunctionalFactorsLengthBound, uniqueFunctionalFactorsFiniteException,
    functionalEquivFiniteException, admissibleSecondFiniteLengthException⟩

end Langlands.MixedBilinear
