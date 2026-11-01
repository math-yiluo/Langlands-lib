import Langlands.Global.ArchimedeanCompactHomSource
import Langlands.Global.ArchimedeanCartanFixedCentralGeneration

/-! # Central coverings of evaluated actual compact intertwiners -/

noncomputable section
universe u w
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

section Module

variable {V : Type w} [AddCommGroup V] [Module ℂ V]
  [Module (EnvelopingAlgebra K n) V] [IsScalarTower ℂ (EnvelopingAlgebra K n) V]

omit [NumberField K] in
/-- The full generated Hom source consists exactly of maps valued in the
full generated original source. The domain is finite dimensional. -/
theorem mem_enveloping_compactHomSource_iff (σ τ : ContinuousCompactRep K n)
    (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V) (F : (Fin σ.dim → ℂ) →ₗ[ℂ] V) :
    F ∈ (⊤ : Submodule ℂ (EnvelopingAlgebra K n)) •
        LinearMap.range (compactHomSourceMap K n σ τ j) ↔
      ∀ x, F x ∈ (⊤ : Submodule ℂ (EnvelopingAlgebra K n)) • LinearMap.range j := by
  classical
  constructor
  · intro hF x
    refine Submodule.smul_induction_on hF ?_ ?_
    · intro a ha G hG
      exact Submodule.smul_mem_smul ha
        ((mem_range_compactHomSourceMap_iff K n σ τ j G).mp hG x)
    · intro G H hG hH
      exact Submodule.add_mem _ hG hH
  · intro hF
    let e := LinearEquiv.piRing ℂ V (Fin σ.dim) (EnvelopingAlgebra K n)
    let L (i : Fin σ.dim) : V →ₗ[EnvelopingAlgebra K n] ((Fin σ.dim → ℂ) →ₗ[ℂ] V) :=
      e.symm.toLinearMap.comp (LinearMap.single _ (fun _ : Fin σ.dim => V) i)
    have hL (i : Fin σ.dim) {v : V}
        (hv : v ∈ (⊤ : Submodule ℂ (EnvelopingAlgebra K n)) • LinearMap.range j) :
        L i v ∈ (⊤ : Submodule ℂ (EnvelopingAlgebra K n)) •
          LinearMap.range (compactHomSourceMap K n σ τ j) := by
      refine Submodule.smul_induction_on hv ?_ ?_
      · intro a ha v hv
        rw [map_smul]
        apply Submodule.smul_mem_smul ha
        apply (mem_range_compactHomSourceMap_iff K n σ τ j _).mpr
        intro x
        have heq : L i v x = x i • v := by
          simp only [L, e, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
            LinearMap.single_apply, LinearEquiv.piRing_symm_apply]
          rw [Finset.sum_eq_single i]
          · simp
          · intro b hb hbi
            simp [Pi.single_eq_of_ne hbi]
          · intro hi
            exact (hi (Finset.mem_univ i)).elim
        rw [heq]
        exact (LinearMap.range j).smul_mem _ hv
      · intro v w hv hw
        simpa only [map_add] using Submodule.add_mem _ hv hw
    have hsum : ∑ i, L i (F (Pi.single i 1)) = F := by
      apply e.injective
      simp only [map_sum, L, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        LinearEquiv.apply_symm_apply, LinearMap.single_apply, e,
        Finset.univ_sum_single]
      rfl
    rw [← hsum]
    exact Submodule.sum_mem _ (fun i _ => hL i (hF _))

/-- Finite full-center orbits of the basis evaluations of a finite Hom family. -/
def compactHomCentralEvaluationSpan (σ : ContinuousCompactRep K n) {m : ℕ}
    (F : Fin m → (Fin σ.dim → ℂ) →ₗ[ℂ] V) : Submodule ℂ V :=
  ⨆ p : Fin m × Fin σ.dim, Submodule.span ℂ
    (Set.range fun z : EnvelopingCenter K n =>
      (z : EnvelopingAlgebra K n) • F p.1 (Pi.single p.2 1))

omit [NumberField K] in
/-- Evaluation of a finite central Hom covering lies in the finite covering
by the corresponding basis evaluations. -/
theorem hom_evaluation_mem_centralEvaluationSpan (σ : ContinuousCompactRep K n) {m : ℕ}
    (F : Fin m → (Fin σ.dim → ℂ) →ₗ[ℂ] V)
    (T : (Fin σ.dim → ℂ) →ₗ[ℂ] V)
    (hT : T ∈ ⨆ i : Fin m, Submodule.span ℂ
      (Set.range fun z : EnvelopingCenter K n => (z : EnvelopingAlgebra K n) • F i))
    (x : Fin σ.dim → ℂ) :
    T x ∈ compactHomCentralEvaluationSpan K n σ F := by
  classical
  let S := compactHomCentralEvaluationSpan K n σ F
  have hle : (⨆ i : Fin m, Submodule.span ℂ
      (Set.range fun z : EnvelopingCenter K n => (z : EnvelopingAlgebra K n) • F i)) ≤
      S.comap (LinearMap.applyₗ (R := ℂ) x) := by
    apply iSup_le
    intro i
    apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    change (z : EnvelopingAlgebra K n) • F i x ∈ S
    have hexp : F i x = ∑ a : Fin σ.dim, x a • F i (Pi.single a 1) := by
      have h := congrArg (fun G : (Fin σ.dim → ℂ) →ₗ[ℂ] V => G x)
        ((LinearEquiv.piRing ℂ V (Fin σ.dim) ℂ).symm_apply_apply (F i))
      simpa only [LinearEquiv.piRing_symm_apply, LinearEquiv.piRing_apply] using h.symm
    rw [hexp, Finset.smul_sum]
    apply Submodule.sum_mem
    intro a ha
    rw [smul_comm]
    apply S.smul_mem
    exact Submodule.mem_iSup_of_mem (i, a) (Submodule.subset_span ⟨z, rfl⟩)
  exact hle hT

/-- A single finite family covers all evaluated intertwiners whose values lie
in the enveloping-generated source. -/
theorem exists_finite_central_cover_of_intertwiner_values
    (σ τ : ContinuousCompactRep K n) (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V)
    (ρ : _root_.Representation ℂ (standardInfiniteCompact K n) V)
    (hj : ∀ k v, j (τ.toRepresentation k v) = ρ k (j v))
    (hρ : ∀ k a v, ρ k (a • v) = envelopingConjugation K n k.val a • ρ k v)
    (hstable : ∀ X : CompactComplexLieAlgebra K n, ∀ v ∈ LinearMap.range j,
      compactEnvelopingGenerator K n X • v ∈ LinearMap.range j) :
    ∃ (m : ℕ) (F : Fin m → (Fin σ.dim → ℂ) →ₗ[ℂ] V),
      ∀ T : σ.toRepresentation.IntertwiningMap ρ,
        (∀ x, T x ∈ (⊤ : Submodule ℂ (EnvelopingAlgebra K n)) • LinearMap.range j) →
        ∀ x, T x ∈ compactHomCentralEvaluationSpan K n σ F := by
  let ρH := _root_.Representation.linHom σ.toRepresentation ρ
  obtain ⟨m, F, hfixed, hcover⟩ :=
    exists_finite_central_orbit_cover_of_compact_fixed K n (σ.linHom K n τ)
      (compactHomSourceMap K n σ τ j) ρH
      (compactHomSourceMap_equivariant K n σ τ j ρ hj)
      (compactHomAction_enveloping_compatible K n σ ρ hρ)
      (compactHomSourceMap_range_stable K n σ τ j hstable)
  refine ⟨m, F, ?_⟩
  intro T hT x
  let t : ρH.invariants :=
    (_root_.Representation.invariantsEquivIntertwiningMap σ.toRepresentation ρ).symm T
  have ht : t.val ∈ (⊤ : Submodule ℂ (EnvelopingAlgebra K n)) •
      LinearMap.range (compactHomSourceMap K n σ τ j) :=
    (mem_enveloping_compactHomSource_iff K n σ τ j T.toLinearMap).mpr hT
  exact hom_evaluation_mem_centralEvaluationSpan K n σ F T.toLinearMap
    (hcover t ht) x

/-- If the original finite source generates the target module, every vector in
the algebraic isotypic span has the same finite central covering. -/
theorem exists_finite_central_cover_of_generated_isotypic
    (σ τ : ContinuousCompactRep K n) (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V)
    (ρ : _root_.Representation ℂ (standardInfiniteCompact K n) V)
    (hj : ∀ k v, j (τ.toRepresentation k v) = ρ k (j v))
    (hρ : ∀ k a v, ρ k (a • v) = envelopingConjugation K n k.val a • ρ k v)
    (hstable : ∀ X : CompactComplexLieAlgebra K n, ∀ v ∈ LinearMap.range j,
      compactEnvelopingGenerator K n X • v ∈ LinearMap.range j)
    (hgenerate : (⊤ : Submodule ℂ (EnvelopingAlgebra K n)) • LinearMap.range j = ⊤) :
    ∃ (m : ℕ) (F : Fin m → (Fin σ.dim → ℂ) →ₗ[ℂ] V),
      Langlands.CompactSplitting.isotypicPart σ.toRepresentation ρ ≤
        compactHomCentralEvaluationSpan K n σ F := by
  obtain ⟨m, F, hcover⟩ :=
    exists_finite_central_cover_of_intertwiner_values K n σ τ j ρ hj hρ hstable
  refine ⟨m, F, iSup_le fun T => ?_⟩
  rintro _ ⟨x, rfl⟩
  apply hcover T _ x
  intro y
  rw [hgenerate]
  exact Submodule.mem_top

end Module

end Langlands.Global.ArchimedeanGL
