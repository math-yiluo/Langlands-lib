import Langlands.Automorphic.ArchimedeanTensorEvaluation

/-! # Commuting operators on compact and Lie multiplicities -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Archimedean.GKTensorEvaluation

open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

universe uK uL uV uW

variable {K : Type uK} [Group K] {L : Type uL} [LieRing L] [LieAlgebra ℂ L]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
  (ρ' : Representation ℂ K W) (π' : L →ₗ⁅ℂ⁆ Module.End ℂ W)

local instance gkActionsMultiplicityGroup : AddCommGroup (Multiplicity ρ π ρ' π') :=
  (gkHoms ρ π ρ' π').addCommGroup

/-- An operator commuting with the target compact and Lie actions acts on
simultaneous intertwiners by postcomposition. -/
def postcompose (T : Module.End ℂ W)
    (hk : ∀ k w, T (ρ' k w) = ρ' k (T w))
    (hl : ∀ X w, T (π' X w) = π' X (T w)) :
    Module.End ℂ (Multiplicity ρ π ρ' π') where
  toFun f := ⟨T.comp f.val,
    fun k v => (congrArg T (f.property.1 k v)).trans (hk k (f.val v)),
    fun X v => (congrArg T (f.property.2 X v)).trans (hl X (f.val v))⟩
  map_add' f g := Subtype.ext (LinearMap.ext fun v => T.map_add (f.val v) (g.val v))
  map_smul' c f := Subtype.ext (LinearMap.ext fun v => T.map_smul c (f.val v))

@[simp]
theorem postcompose_apply (T : Module.End ℂ W)
    (hk : ∀ k w, T (ρ' k w) = ρ' k (T w))
    (hl : ∀ X w, T (π' X w) = π' X (T w))
    (f : Multiplicity ρ π ρ' π') (v : V) :
    (postcompose ρ π ρ' π' T hk hl f).val v = T (f.val v) := rfl

theorem evaluation_postcompose (T : Module.End ℂ W)
    (hk : ∀ k w, T (ρ' k w) = ρ' k (T w))
    (hl : ∀ X w, T (π' X w) = π' X (T w))
    (t : V ⊗[ℂ] Multiplicity ρ π ρ' π') :
    evaluation ρ π ρ' π'
        (TensorProduct.map LinearMap.id (postcompose ρ π ρ' π' T hk hl) t) =
      T (evaluation ρ π ρ' π' t) := by
  induction t with
  | tmul v f => rfl
  | add t t' ht ht' => simp only [map_add, ht, ht']

/-- The tensor evaluation range is stable under the chosen local compact action. -/
theorem range_compact (k : K) (w : W)
    (hw : w ∈ LinearMap.range (evaluation ρ π ρ' π')) :
    ρ' k w ∈ LinearMap.range (evaluation ρ π ρ' π') := by
  obtain ⟨t, rfl⟩ := hw
  exact ⟨_, evaluation_compact ρ π ρ' π' k t⟩

/-- The same range is stable under the chosen local Lie action. -/
theorem range_lie (X : L) (w : W)
    (hw : w ∈ LinearMap.range (evaluation ρ π ρ' π')) :
    π' X w ∈ LinearMap.range (evaluation ρ π ρ' π') := by
  obtain ⟨t, rfl⟩ := hw
  exact ⟨_, evaluation_lie ρ π ρ' π' X t⟩

/-- Every operator commuting with both local action families preserves the range. -/
theorem range_commuting (T : Module.End ℂ W)
    (hk : ∀ k w, T (ρ' k w) = ρ' k (T w))
    (hl : ∀ X w, T (π' X w) = π' X (T w))
    (w : W) (hw : w ∈ LinearMap.range (evaluation ρ π ρ' π')) :
    T w ∈ LinearMap.range (evaluation ρ π ρ' π') := by
  obtain ⟨t, rfl⟩ := hw
  exact ⟨_, evaluation_postcompose ρ π ρ' π' T hk hl t⟩

end Langlands.Archimedean.GKTensorEvaluation
