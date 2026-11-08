import Langlands.Representation.Plancherel.CompactInductionPolynomialAction
import Langlands.Representation.Plancherel.CompactIntertwiningComposition

/-! # Actual changes between compact models of normalized induction -/

noncomputable section

open scoped NNReal

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily

universe uG uI uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (K₀ K₁ : OpenSubgroup G) (hP : IsClosed (P : Set G))
  (hK₀ : IsCompact (K₀ : Set G)) (hK₁ : IsCompact (K₁ : Set G))
  (hPK₀ : ∀ g : G, ∃ p : P, ∃ k : K₀, g = (p : G) * (k : G))
  (hPK₁ : ∀ g : G, ∃ p : P, ∃ k : K₁, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)

/-- Extend from the first compact subgroup to the actual normalized induction,
then restrict to the second compact subgroup. This intertwines the full
ambient group actions. -/
def unramifiedCompactModelEquiv (χ : unramifiedCharacters ν) :
    (unramifiedCompactRepresentation h hU hδ K₀ hP hK₀ hPK₀ ν hν hr A χ).Equiv
      (unramifiedCompactRepresentation h hU hδ K₁ hP hK₁ hPK₁ ν hν hr A χ) :=
  (unramifiedCompactRepresentationEquiv h hU hδ K₀ hP hK₀ hPK₀ ν hν hr A χ).symm.trans
    (unramifiedCompactRepresentationEquiv h hU hδ K₁ hP hK₁ hPK₁ ν hν hr A χ)

theorem unramifiedCompactModelEquiv_apply (χ : unramifiedCharacters ν)
    (f : CompactInductionPicture h K₀ A) :
    unramifiedCompactModelEquiv h hU hδ K₀ K₁ hP hK₀ hK₁ hPK₀ hPK₁ ν hν hr A χ f =
      unramifiedLeviInductionCompactEquiv h hU hδ K₁ hP hK₁ hPK₁ ν hν hr χ A
        ((unramifiedLeviInductionCompactEquiv h hU hδ K₀ hP hK₀ hPK₀ ν hν hr χ A).symm f) :=
  rfl

/-- Values on the second compact subgroup are values of the actual extension
from the first. -/
theorem unramifiedCompactModelEquiv_eval (χ : unramifiedCharacters ν)
    (f : CompactInductionPicture h K₀ A) (k : K₁) :
    eval _ _
        (unramifiedCompactModelEquiv h hU hδ K₀ K₁ hP hK₀ hK₁ hPK₀ hPK₁ ν hν hr A χ f) k =
      eval _ _
        ((unramifiedLeviInductionCompactEquiv h hU hδ K₀ hP hK₀ hPK₀ ν hν hr χ A).symm f)
        (k : G) := rfl

/-- An actual parabolic-times-compact factorization evaluates the transition
by the actual twisted normalized inducing action. -/
theorem unramifiedCompactModelEquiv_eval_factor (χ : unramifiedCharacters ν)
    (f : CompactInductionPicture h K₀ A) (k₁ : K₁) (p : P) (k₀ : K₀)
    (he : (k₁ : G) = (p : G) * (k₀ : G)) :
    eval _ _
        (unramifiedCompactModelEquiv h hU hδ K₀ K₁ hP hK₀ hK₁ hPK₀ hPK₁ ν hν hr A χ f) k₁ =
      inducingRepresentation h hU
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) p (eval _ _ f k₀) := by
  rw [unramifiedCompactModelEquiv_eval, he,
    unramifiedLeviInductionCompactEquiv_symm_mul]

/-- Restricting an ambient section directly or through the first compact
model gives the same second compact section. -/
theorem unramifiedCompactModelEquiv_restrict (χ : unramifiedCharacters ν)
    (F : UnramifiedLeviInduction h hU ν χ A) :
    unramifiedCompactModelEquiv h hU hδ K₀ K₁ hP hK₀ hK₁ hPK₀ hPK₁ ν hν hr A χ
        (unramifiedLeviInductionCompactEquiv h hU hδ K₀ hP hK₀ hPK₀ ν hν hr χ A F) =
      unramifiedLeviInductionCompactEquiv h hU hδ K₁ hP hK₁ hPK₁ ν hν hr χ A F := by
  rw [unramifiedCompactModelEquiv_apply, LinearEquiv.symm_apply_apply]

/-- Reversing the compact subgroups gives the inverse transition. -/
theorem unramifiedCompactModelEquiv_symm (χ : unramifiedCharacters ν) :
    (unramifiedCompactModelEquiv h hU hδ K₀ K₁ hP hK₀ hK₁ hPK₀ hPK₁ ν hν hr A χ).symm =
      unramifiedCompactModelEquiv h hU hδ K₁ K₀ hP hK₁ hK₀ hPK₁ hPK₀ ν hν hr A χ := by
  rfl

theorem unramifiedCompactModelEquiv_self (χ : unramifiedCharacters ν)
    (f : CompactInductionPicture h K₀ A) :
    unramifiedCompactModelEquiv h hU hδ K₀ K₀ hP hK₀ hK₀ hPK₀ hPK₀ ν hν hr A χ f = f := by
  rw [unramifiedCompactModelEquiv_apply, LinearEquiv.apply_symm_apply]

/-- A common open stabilizer in the first compact subgroup fixes every
transferred vector through its intersection with the second subgroup. -/
theorem unramifiedCompactModelEquiv_mem_compactFixed (χ : unramifiedCharacters ν)
    (H : OpenSubgroup G) (hHK₀ : H ≤ K₀) (w : CompactFixedVectors h K₀ A H) :
    unramifiedCompactModelEquiv h hU hδ K₀ K₁ hP hK₀ hK₁ hPK₀ hPK₁ ν hν hr A χ w.val ∈
      fixedVectors (compactPictureAction h K₁ A) (compactFixedSubgroup K₁ H) := by
  intro x
  change compactPictureAction h K₁ A x.val
    (unramifiedLeviInductionCompactEquiv h hU hδ K₁ hP hK₁ hPK₁ ν hν hr χ A
      ((unramifiedLeviInductionCompactEquiv h hU hδ K₀ hP hK₀ hPK₀ ν hν hr χ A).symm w.val)) = _
  rw [← unramifiedLeviInductionCompactEquiv_translate]
  exact congrArg (unramifiedLeviInductionCompactEquiv h hU hδ K₁ hP hK₁ hPK₁ ν hν hr χ A)
    ((compactFixedEquiv h hU hδ K₀ hP hK₀ hPK₀ ν hν hr A χ H hHK₀ w).property
      ⟨(x.val : G), x.property⟩)

/-- The actual transition family is polynomial on any parameter subset.
Neither admissibility nor finite-dimensionality of the inducing carrier is
required. -/
theorem unramifiedCompactModelEquiv_polynomial (Ω : Set (unramifiedCharacters ν)) :
    IsPolynomialOperatorOn Ω
      (fun χ => (unramifiedCompactModelEquiv h hU hδ K₀ K₁ hP hK₀ hK₁ hPK₀ hPK₁
        ν hν hr A χ.val).toLinearMap) := by
  intro f
  obtain ⟨H, hHK₀, hf⟩ := exists_compactPicture_stabilizer h K₀ A f
  let X : Ω → CompactFixedVectors h K₁ A H := fun χ =>
    ⟨unramifiedCompactModelEquiv h hU hδ K₀ K₁ hP hK₀ hK₁ hPK₀ hPK₁ ν hν hr A χ.val f,
      unramifiedCompactModelEquiv_mem_compactFixed h hU hδ K₀ K₁ hP hK₀ hK₁ hPK₀ hPK₁
        ν hν hr A χ.val H hHK₀ ⟨f, hf⟩⟩
  have hX : IsPolynomialOn Ω X := by
    apply isPolynomialOn_compactFixed_of_eval h K₁ hK₁ ν A H
    intro k
    change IsPolynomialOn Ω (fun χ => eval _ _
      (unramifiedCompactModelEquiv h hU hδ K₀ K₁ hP hK₀ hK₁ hPK₀ hPK₁ ν hν hr A χ.val f) k)
    simp_rw [unramifiedCompactModelEquiv_eval]
    exact unramifiedCompactExtension_eval_isPolynomialOn h hU hδ K₀ hP hK₀ hPK₀
      ν hν hr A Ω f (k : G)
  exact hX.linearMap (Submodule.subtype _)

/-- The inverse transition family is also polynomial on every subset. -/
theorem unramifiedCompactModelEquiv_symm_polynomial (Ω : Set (unramifiedCharacters ν)) :
    IsPolynomialOperatorOn Ω
      (fun χ => (unramifiedCompactModelEquiv h hU hδ K₀ K₁ hP hK₀ hK₁ hPK₀ hPK₁
        ν hν hr A χ.val).symm.toLinearMap) := by
  simp_rw [unramifiedCompactModelEquiv_symm]
  exact unramifiedCompactModelEquiv_polynomial h hU hδ K₁ K₀ hP hK₁ hK₀ hPK₁ hPK₀ ν hν hr A Ω

variable {P' U' : Subgroup G}
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  (hδ' : IsUnimodularModulus U' hU') (hP' : IsClosed (P' : Set G))
  (hP'K₀ : ∀ g : G, ∃ p : P', ∃ k : K₀, g = (p : G) * (k : G))
  (hP'K₁ : ∀ g : G, ∃ p : P', ∃ k : K₁, g = (p : G) * (k : G))
  (hr' : Continuous h'.projection)

/-- Compact conjugations of any actual ambient intertwiner commute with
the actual model transitions. No additional naturality square is assumed. -/
theorem compactIntertwiningOperator_modelChange (χ : unramifiedCharacters ν)
    (J : (UnramifiedLeviInduction h hU ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h' hU' ν χ A).representation)
    (f : CompactInductionPicture h K₀ A) :
    compactIntertwiningOperator h hU hδ K₁ hP hK₁ hPK₁ ν hν hr
        h' hU' hδ' hP' hP'K₁ hr' χ A J
        (unramifiedCompactModelEquiv h hU hδ K₀ K₁ hP hK₀ hK₁ hPK₀ hPK₁ ν hν hr A χ f) =
      unramifiedCompactModelEquiv h' hU' hδ' K₀ K₁ hP' hK₀ hK₁ hP'K₀ hP'K₁ ν hν hr' A χ
        (compactIntertwiningOperator h hU hδ K₀ hP hK₀ hPK₀ ν hν hr
          h' hU' hδ' hP' hP'K₀ hr' χ A J f) := by
  simp only [unramifiedCompactModelEquiv_apply, compactIntertwiningOperator,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

end Langlands.Plancherel
