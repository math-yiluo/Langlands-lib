import Langlands.Representation.Compact.CompactMultiplicityIndependenceStatements
import Langlands.Representation.Compact.CompactGroupSmoothRepresentationProof
import Langlands.Representation.Compact.CoefficientLinearIndependenceProof
import Langlands.Representation.Smooth.Schur.Proof
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Renard IV.1.1 and IV.3.3: multiplicities and coefficient independence -/

noncomputable section
universe u v

namespace Langlands.Renard.CompactRepresentation

section Algebra

variable {R S M : Type*} [Ring R] [Algebra ℂ R]
  [AddCommGroup S] [Module R S] [Module ℂ S] [IsScalarTower ℂ R S]
  [AddCommGroup M] [Module R M] [Module ℂ M] [IsScalarTower ℂ R M]
  [IsSimpleModule R S]

omit [Algebra ℂ R] [Module ℂ S] [IsScalarTower ℂ R S]
  [Module ℂ M] [IsScalarTower ℂ R M] in
private theorem isotypic_eq_iSup_range :
    isotypicComponent R M S = ⨆ f : S →ₗ[R] M, f.range := by
  classical
  apply le_antisymm
  · refine sSup_le fun N ⟨e⟩ => ?_
    let f := N.subtype.comp e.symm.toLinearMap
    exact le_iSup_of_le f (by rintro x hx; exact ⟨e ⟨x, hx⟩, by simp [f]⟩)
  · refine iSup_le fun f => ?_
    rcases f.injective_or_eq_zero with hf | hf
    · exact le_sSup ⟨(LinearEquiv.ofInjective f hf).symm⟩
    · simp [hf]

private theorem finite_isotypic [FiniteDimensional ℂ S]
    [FiniteDimensional ℂ (S →ₗ[R] M)] :
    FiniteDimensional ℂ (isotypicComponent R M S) := by
  classical
  let b := Module.finBasis ℂ (S →ₗ[R] M)
  let J : Submodule R M := ⨆ i, (b i).range
  let hJ (i) : FiniteDimensional ℂ ((b i).range.restrictScalars ℂ) :=
    LinearMap.finiteDimensional_range ((b i).restrictScalars ℂ)
  have hfin : FiniteDimensional ℂ (J.restrictScalars ℂ) := by
    change FiniteDimensional ℂ ((⨆ i, (b i).range).restrictScalars ℂ)
    rw [Submodule.restrictScalars_iSup]
    infer_instance
  have hle : isotypicComponent R M S ≤ J := by
    rw [isotypic_eq_iSup_range]
    refine iSup_le fun f x ⟨y, hy⟩ => ?_
    rw [← hy, ← b.sum_repr f]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    exact Submodule.sum_mem _ fun i _ =>
      (J.restrictScalars ℂ).smul_mem _ (le_iSup (fun i => (b i).range) i ⟨y, rfl⟩)
  exact Submodule.finiteDimensional_of_le (S₂ := J.restrictScalars ℂ)
    (show (isotypicComponent R M S).restrictScalars ℂ ≤ J.restrictScalars ℂ from hle)

private theorem finrank_isotypic [FiniteDimensional ℂ S]
    [FiniteDimensional ℂ (S →ₗ[R] M)]
    (eEnd : Module.End R S ≃ₗ[ℂ] ℂ) :
    Module.finrank ℂ (isotypicComponent R M S) =
      Module.finrank ℂ (S →ₗ[R] M) * Module.finrank ℂ S := by
  classical
  let I := isotypicComponent R M S
  let : FiniteDimensional ℂ I := finite_isotypic
  let : Module.Finite R I := Module.Finite.of_restrictScalars_finite ℂ R I
  obtain ⟨n, ⟨e⟩⟩ := (IsIsotypicOfType.isotypicComponent R M S).linearEquiv_fun
  have hf (f : S →ₗ[R] M) (x : S) : f x ∈ I := by
    change f x ∈ isotypicComponent R M S
    rw [isotypic_eq_iSup_range]
    exact le_iSup (fun f : S →ₗ[R] M => f.range) f ⟨x, rfl⟩
  let L : (S →ₗ[R] M) →ₗ[ℂ] (Fin n → Module.End R S) :=
    { toFun := fun f i => (LinearMap.proj i).comp
        (e.toLinearMap.comp (f.codRestrict I (hf f)))
      map_add' := fun f g => by
        ext i x
        change e (⟨f x, hf f x⟩ + ⟨g x, hf g x⟩) i = _
        exact congrFun (e.map_add _ _) i
      map_smul' := fun a f => by
        ext i x
        change e (a • ⟨f x, hf f x⟩) i = _
        exact congrFun ((e.restrictScalars ℂ).map_smul a _) i }
  have hLinj : Function.Injective L := by
    intro f g h
    ext x
    have he : e ⟨f x, hf f x⟩ = e ⟨g x, hf g x⟩ := by
      funext i
      exact congrArg (fun t : Module.End R S => t x) (congrFun h i)
    exact congrArg Subtype.val (e.injective he)
  have hLsurj : Function.Surjective L := by
    intro t
    refine ⟨I.subtype.comp (e.symm.toLinearMap.comp (LinearMap.pi t)), ?_⟩
    ext i x
    change e ⟨(e.symm (fun i => t i x)).val, _⟩ i = t i x
    exact congrFun (e.apply_symm_apply (fun i => t i x)) i
  have hdim : Module.finrank ℂ (S →ₗ[R] M) = n := by
    rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective L ⟨hLinj, hLsurj⟩),
      LinearEquiv.finrank_eq (LinearEquiv.piCongrRight (fun _ : Fin n => eEnd))]
    simp
  rw [hdim]
  exact (e.restrictScalars ℂ).finrank_eq.trans (by simp [Module.finrank_pi_fintype])

end Algebra

/-- The finite compact-group isotypic part has the expected dimension. -/
theorem compactGroupMultiplicity : CompactGroupMultiplicityStatement.{u, v} := by
  classical
  intro K _ _ _ _ _ _ π σ hi hhom
  let R := MonoidAlgebra ℂ K
  let S := σ.representation.asModule
  let M := π.representation.asModule
  let : σ.representation.IsIrreducible := hi
  let : FiniteDimensional ℂ σ :=
    finiteDimensional_of_compact_irreducible σ.representation σ.isSmooth hi
  let : FiniteDimensional ℂ (σ.representation.IntertwiningMap π.representation) := hhom
  let E := Representation.IntertwiningMap.equivLinearMapAsModule
    σ.representation π.representation
  let : FiniteDimensional ℂ (S →ₗ[R] M) := Module.Finite.equiv E
  have ha : IsAdmissible σ.representation := ⟨σ.isSmooth, fun _ => inferInstance⟩
  obtain ⟨eSchur⟩ := admissibleSchur_homEquiv σ.representation ha hi σ.representation
    (Representation.Equiv.refl σ.representation)
  let eEnd : Module.End R S ≃ₗ[ℂ] ℂ :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      σ.representation σ.representation).symm.trans eSchur
  let I : Subrepresentation π.representation :=
    ⨆ f : σ.representation.IntertwiningMap π.representation, f.range
  let T := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := π.representation)
  have hI : T I = isotypicComponent R M S := by
    rw [isotypic_eq_iSup_range]
    change T (⨆ f : σ.representation.IntertwiningMap π.representation, f.range) = _
    rw [T.map_iSup]
    apply le_antisymm
    · refine iSup_le fun f => le_iSup_of_le (E f) ?_
      exact le_rfl
    · refine iSup_le fun f => le_iSup_of_le (E.symm f) ?_
      exact le_rfl
  have hfin : FiniteDimensional ℂ (T I) := by
    rw [hI]
    exact finite_isotypic
  have hdim := finrank_isotypic (M := M) eEnd
  rw [← hI] at hdim
  refine ⟨hfin, ?_⟩
  exact hdim.trans (by rw [← E.finrank_eq]; rfl)

/-- The compact coefficient assertion follows from the algebraic coefficient theorem. -/
theorem compactCoefficientLinearIndependence :
    CompactCoefficientLinearIndependenceStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ _ _ μ _ _ _ r π hi _ hne x ℓ hx hℓ
  exact coefficients_linearIndependent_of_irreducible π hi hne x (fun i => (ℓ i).val) hx
    (fun i h => hℓ i (Subtype.ext h))

/-- The exact published conjunction of Renard IV.1.1 and IV.3.3. -/
theorem compactMultiplicityIndependence : CompactMultiplicityIndependenceStatements.{u, v} :=
  ⟨compactGroupMultiplicity, compactCoefficientLinearIndependence⟩

end Langlands.Renard.CompactRepresentation
