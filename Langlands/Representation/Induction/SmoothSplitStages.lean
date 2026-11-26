import Langlands.Representation.Induction.SmoothTransitivity
import Langlands.Representation.Induction.SmoothSplitQuotient
import Langlands.Representation.Geometric.ParabolicOrbitInductionTransport

/-! # Smooth induction in stages along a split projection -/

noncomputable section

namespace Langlands.Induction

universe uG uL uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {L : Type uL} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {Q P : Subgroup G} {H : Subgroup L} (hQP : Q ≤ P) (p : P →* L)
  (hQ : ∀ x : P, (x : G) ∈ Q ↔ p x ∈ H)

/-- The restriction of a split projection to the preimage of an inducing subgroup. -/
def splitStagesProjection : Q →* H where
  toFun g := ⟨p ⟨g, hQP g.2⟩, (hQ ⟨g, hQP g.2⟩).mp g.2⟩
  map_one' := Subtype.ext (map_one p)
  map_mul' g k := Subtype.ext (map_mul p ⟨g, hQP g.2⟩ ⟨k, hQP k.2⟩)

variable (hp : Continuous p) (s : L →* P) (hs : Continuous s)
  (hps : ∀ l, p (s l) = l) (ρ : Representation ℂ H V)

local notation "I" => Q.subgroupOf P
local notation "ι" => MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hQP)
local notation "ρQ" => ρ.comp (splitStagesProjection hQP p hQ)
local notation "ρI" => MonoidHom.comp ρQ ι
local notation "ρH" => smoothInduced H ρ
local notation "ρP" => MonoidHom.comp ρH p

include hQ in
omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace L] [IsTopologicalGroup L] in
private theorem splitStages_ker_le : p.ker ≤ I := by
  intro x hx
  apply (hQ x).mpr
  rw [show p x = 1 from hx]
  exact H.one_mem

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace L] [IsTopologicalGroup L] in
private theorem splitStages_ker_trivial (x : I) (hx : p (x : P) = 1) (v : V) :
    ρI x v = v := by
  have he : splitStagesProjection hQP p hQ (ι x) = 1 := Subtype.ext hx
  change ρ (splitStagesProjection hQP p hQ (ι x)) v = v
  rw [he, map_one, Module.End.one_apply]

include hQ hps in
omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace L] [IsTopologicalGroup L] in
private theorem splitStages_section_preimage : Subgroup.comap s I = H := by
  ext l
  exact (hQ (s l)).trans (by rw [hps])

private def splitStages_section_coeff :
    Representation.Equiv (MonoidHom.comp ρI (s.subgroupComap I))
      (ρ.comp (MulEquiv.subgroupCongr (splitStages_section_preimage p hQ s hps)).toMonoidHom) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ V) fun m => by
    change ρ (splitStagesProjection hQP p hQ (ι (s.subgroupComap I m))) =
      ρ ((MulEquiv.subgroupCongr (splitStages_section_preimage p hQ s hps)) m)
    exact congrArg ρ (Subtype.ext (hps m))

private def splitStages_innerEquiv : (smoothInduced I ρI).Equiv ρP := by
  let a := smoothSplitQuotientEquiv p hp s hs hps I (splitStages_ker_le p hQ)
    ρI (splitStages_ker_trivial hQP p hQ ρ)
  let b := (smoothInducedEquiv (Subgroup.comap s I)
    (splitStages_section_coeff hQP p hQ s hps ρ)).trans
    (Geometric.smoothInducedSubgroupCongr (Subgroup.comap s I) H
      (splitStages_section_preimage p hQ s hps) ρ)
  exact a.trans (Representation.Equiv.mk b.toLinearEquiv (fun g => b.isIntertwining' (p g)))

private theorem splitStages_innerEquiv_eval (f : SmoothFunctions I ρI) (l : L) :
    eval H ρ (splitStages_innerEquiv hQP p hQ hp s hs hps ρ f) l =
      eval I ρI f (s l) := by
  let f' := smoothSplitQuotientEquiv p hp s hs hps I (splitStages_ker_le p hQ)
    ρI (splitStages_ker_trivial hQP p hQ ρ) f
  change eval H ρ (Geometric.smoothInducedSubgroupCongr (Subgroup.comap s I) H
    (splitStages_section_preimage p hQ s hps) ρ
    (smoothInducedEquiv _ (splitStages_section_coeff hQP p hQ s hps ρ) f')) l = _
  rw [Geometric.smoothInducedSubgroupCongr_eval, smoothInducedEquiv_eval]
  rfl

/-- Direct smooth induction equals iterated smooth induction through the split projection. -/
def smoothSplitStagesEquiv :
    (smoothInduced Q ρQ).Equiv (smoothInduced P ρP) :=
  (smoothStagesEquiv Q P hQP ρQ).symm.trans
    (smoothInducedEquiv P (splitStages_innerEquiv hQP p hQ hp s hs hps ρ))

theorem smoothSplitStagesEquiv_eval (f : SmoothFunctions Q ρQ) (g : G) (l : L) :
    eval H ρ (eval P ρP (smoothSplitStagesEquiv hQP p hQ hp s hs hps ρ f) g) l =
      eval Q ρQ f ((s l : G) * g) := by
  unfold smoothSplitStagesEquiv
  rw [Representation.Equiv.trans_apply, smoothInducedEquiv_eval, splitStages_innerEquiv_eval,
    smoothStagesEquiv_symm_eval]

/-- The map from the iterated model to the direct model evaluates the inner section at one. -/
theorem smoothSplitStagesEquiv_symm_eval (f : SmoothFunctions P ρP) (g : G) :
    eval Q ρQ ((smoothSplitStagesEquiv hQP p hQ hp s hs hps ρ).symm f) g =
      eval H ρ (eval P ρP f g) 1 := by
  simpa only [Representation.Equiv.apply_symm_apply, map_one, Subgroup.coe_one, one_mul] using
    (smoothSplitStagesEquiv_eval hQP p hQ hp s hs hps ρ
      ((smoothSplitStagesEquiv hQP p hQ hp s hs hps ρ).symm f) g 1).symm

end Langlands.Induction
