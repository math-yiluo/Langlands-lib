import Langlands.Representation.Exponents.GeneralizedCentralCharacterSurjectivityProof
import Langlands.Representation.Exponents.RealCentralBlock

/-! Surjectivity on grouped generalized central characters. -/

noncomputable section

namespace Langlands.CentralCharacterSurjectivity

universe uG uV uW uF

/-- An onto intertwiner is onto on any group of generalized characters,
under the same finite source central-action hypothesis. -/
theorem groupedSurjectivity
    (G : Type uG) [Group G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hfin : Module.Finite ℂ
      (Submodule.span ℂ (Set.range (fun z : Subgroup.center G => ρ (z : G)))))
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f)
    (P : (Subgroup.center G →* ℂˣ) → Prop) :
    Function.Surjective (groupedCentralCharacterMap f P) := by
  intro y
  have hy := y.property
  change (y : W) ∈ ⨆ χ : {χ : Subgroup.center G →* ℂˣ // P χ},
    (generalizedCentralCharacterSpace σ χ.val).toSubmodule at hy
  have hex : ∃ v : V, v ∈ groupedCentralCharacterSpace ρ P ∧ f v = (y : W) := by
    refine Submodule.iSup_induction _ (motive := fun w =>
      ∃ v : V, v ∈ groupedCentralCharacterSpace ρ P ∧ f v = w) hy ?_ ?_ ?_
    · intro χ w hw
      obtain ⟨v, hv⟩ := generalizedCentralCharacterSurjectivity G V W ρ σ hfin f hf χ.val ⟨w, hw⟩
      exact ⟨v, generalizedCentralCharacterSpace_le_grouped ρ P χ.val
        χ.property v.property, congrArg Subtype.val hv⟩
    · exact ⟨0, Submodule.zero_mem _, map_zero f⟩
    · rintro w w' ⟨v, hv, hfv⟩ ⟨v', hv', hfv'⟩
      exact ⟨v + v', Submodule.add_mem _ hv hv', by rw [map_add, hfv, hfv']⟩
  obtain ⟨v, hv, hfv⟩ := hex
  exact ⟨⟨v, hv⟩, Subtype.ext hfv⟩

/-- The actual real-central-block restriction is onto under finite full-centre
source action. No source or target semisimplicity is assumed. -/
theorem realBlockSurjectivity
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (B : GeneralLinear.BlockShape n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (B.Levi F.Carrier) V)
    (σ : Representation ℂ (B.Levi F.Carrier) W)
    (hfin : Module.Finite ℂ
      (Submodule.span ℂ (Set.range
        (fun z : Subgroup.center (B.Levi F.Carrier) => ρ (z : _)))))
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f)
    (x : Fin B.length → ℝ) :
    Function.Surjective (T.realCentralBlockMap B f x) := by
  exact groupedSurjectivity (B.Levi F.Carrier) V W ρ σ hfin f hf _

end Langlands.CentralCharacterSurjectivity
