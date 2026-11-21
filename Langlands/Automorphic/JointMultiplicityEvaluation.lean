import Langlands.Automorphic.UnitaryContragredientCriterion

/-!
# Evaluation of joint multiplicity spaces

Finite-level compact-type intertwiners can be bounded by a finite family of
coefficient-valued evaluations. Different evaluations may give different open
levels on the coefficient representation.
-/

noncomputable section

namespace Langlands

variable {G H K J V W I : Type*} [Group G] [Group H] [Group K] [Group J]
  [TopologicalSpace H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {κ : Representation ℂ K V}
  {ρ' : Representation ℂ H W} {κ' : Representation ℂ J W}
  {L : Subgroup G} {m : ℕ} {σ : Representation ℂ K (Fin m → ℂ)}
  (e : I → V →ₗ[ℂ] W) (L' : I → OpenSubgroup H) (j : J →* K)
  (hfix : ∀ i x, x ∈ fixedVectors ρ L → e i x ∈ fixedVectors ρ' (L' i).toSubgroup)
  (hcompact : ∀ i k x, e i (κ (j k) x) = κ' k (e i x))

/-- Evaluate each intertwiner followed by restriction of the test action to `J`. -/
def jointMultiplicityEvaluation : jointMultiplicitySpace ρ κ L σ →ₗ[ℂ]
    (∀ i, jointMultiplicitySpace ρ' κ' (L' i).toSubgroup (σ.comp j)) where
  toFun φ i := ⟨e i ∘ₗ φ.val, fun v => hfix i _ (φ.property.1 v), fun k v => by
    change e i (φ.val (σ (j k) v)) = κ' k (e i (φ.val v))
    rw [φ.property.2, hcompact]⟩
  map_add' φ ψ := by
    funext i
    exact Subtype.ext (LinearMap.comp_add _ _ _)
  map_smul' c φ := by
    funext i
    exact Subtype.ext (LinearMap.comp_smul _ _ _)

include hfix hcompact in
/-- A finite family of evaluations detecting the zero intertwiner suffices for
finiteness, if the coefficient representation is jointly admissible. -/
theorem jointMultiplicitySpace_finite_of_evaluations [Finite I]
    (hadm : IsJointlyAdmissible ρ' κ')
    (hdetect : ∀ φ : jointMultiplicitySpace ρ κ L σ,
      (∀ i v, e i (φ.val v) = 0) → φ = 0) :
    FiniteDimensional ℂ (jointMultiplicitySpace ρ κ L σ) := by
  let (i : I) := hadm (L' i) m (σ.comp j)
  let E := jointMultiplicityEvaluation e L' j hfix hcompact (σ := σ)
  apply Module.Finite.of_injective E
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ
  apply hdetect φ
  intro i v
  exact LinearMap.congr_fun (congrArg Subtype.val (congrFun hφ i)) v

end Langlands
