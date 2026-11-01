import Langlands.Representation.Exponents.OppositeJacquetCentralAction
import Langlands.Representation.Exponents.GroupedCentralCharacterSurjectivity
import Mathlib.RepresentationTheory.Irreducible

/-! Actual quotient retractions from a selected generalized central block. -/

noncomputable section

namespace Langlands.QuotientRealBlockRetraction

universe uG uA uE uN

variable {G : Type uG} [Group G]
  {A : Type uA} [AddCommGroup A] [Module ℂ A]
  {E : Type uE} [AddCommGroup E] [Module ℂ E]
  {N : Type uN} [AddCommGroup N] [Module ℂ N]
  {α : Representation ℂ G A} {ε : Representation ℂ G E}
  {ν : Representation ℂ G N}

/-- Per-character projector identities extend to their actual grouped sum. -/
theorem projectorFixedOnGrouped
    (P : (Subgroup.center G →* ℂˣ) → Prop)
    (i : α.IntertwiningMap ε) (r : ε.IntertwiningMap α)
    (hfix : ∀ χ, P χ → ∀ v : E,
      v ∈ generalizedCentralCharacterSpace ε χ → i (r v) = v) :
    ∀ v : E, v ∈ groupedCentralCharacterSpace ε P → i (r v) = v := by
  intro v hv
  change v ∈ ⨆ χ : {χ : Subgroup.center G →* ℂˣ // P χ},
    (generalizedCentralCharacterSpace ε χ.val).toSubmodule at hv
  refine Submodule.iSup_induction _ (motive := fun v => i (r v) = v) hv ?_ ?_ ?_
  · intro χ v hv
    exact hfix χ.val χ.property v hv
  · rw [map_zero, map_zero]
  · intro v w hv hw
    rw [map_add, map_add, hv, hw]

/-- A nonzero map with selected image forces the quotient of the isolated
simple source to remain injective. -/
theorem quotientInjection
    (P : (Subgroup.center G →* ℂˣ) → Prop)
    (hε : Module.Finite ℂ
      (Submodule.span ℂ (Set.range (fun z : Subgroup.center G => ε (z : G)))))
    (f : ε.IntertwiningMap ν) (hf : Function.Surjective f)
    (i : α.IntertwiningMap ε) (r : ε.IntertwiningMap α)
    (hfix : ∀ v : E, v ∈ groupedCentralCharacterSpace ε P → i (r v) = v)
    (hirr : Representation.IsIrreducible α)
    (g : α.IntertwiningMap ν) (hg : g ≠ 0)
    (hgsel : ∀ v : A, g v ∈ groupedCentralCharacterSpace ν P) :
    Function.Injective (f.comp i) := by
  let := hirr
  let j := f.comp i
  have hj : j ≠ 0 := by
    intro hjzero
    apply hg
    ext v
    obtain ⟨w, hw⟩ :=
      CentralCharacterSurjectivity.groupedSurjectivity
        G E N ε ν hε f hf P ⟨g v, hgsel v⟩
    have hfw : f (w : E) = g v := congrArg Subtype.val hw
    calc
      g v = f (w : E) := hfw.symm
      _ = f (i (r (w : E))) := congrArg f (hfix w w.property).symm
      _ = j (r (w : E)) := rfl
      _ = 0 := by rw [hjzero]; rfl
  exact (Representation.IsIrreducible.injective_or_eq_zero j).resolve_right hj

/-- The quotient map has an actual equivariant inverse on its selected
target block, extended using a central-algebra retraction of that target. -/
theorem quotientProjector
    (P : (Subgroup.center G →* ℂˣ) → Prop)
    (hε : Module.Finite ℂ
      (Submodule.span ℂ (Set.range (fun z : Subgroup.center G => ε (z : G)))))
    (hν : Module.Finite ℂ
      (Submodule.span ℂ (Set.range (fun z : Subgroup.center G => ν (z : G)))))
    (f : ε.IntertwiningMap ν) (hf : Function.Surjective f)
    (i : α.IntertwiningMap ε) (r : ε.IntertwiningMap α)
    (hfix : ∀ v : E, v ∈ groupedCentralCharacterSpace ε P → i (r v) = v)
    (hj : Function.Injective (f.comp i)) :
    ∃ rQ : ν.IntertwiningMap α,
      ∀ v : N, v ∈ groupedCentralCharacterSpace ν P → f (i (rQ v)) = v := by
  classical
  let j := f.comp i
  have hpre : ∀ y : groupedCentralCharacterSpace ν P, ∃ a : A, j a = (y : N) := by
    intro y
    obtain ⟨w, hw⟩ :=
      CentralCharacterSurjectivity.groupedSurjectivity
        G E N ε ν hε f hf P y
    refine ⟨r (w : E), ?_⟩
    change f (i (r (w : E))) = (y : N)
    rw [hfix w w.property]
    exact congrArg Subtype.val hw
  let pre : groupedCentralCharacterSpace ν P → A :=
    fun y => Classical.choose (hpre y)
  have hpreval : ∀ y : groupedCentralCharacterSpace ν P, j (pre y) = (y : N) :=
    fun y => Classical.choose_spec (hpre y)
  obtain ⟨proj, hproj, _⟩ :=
    groupedCentralCharacterRetraction G N ν hν P
  let rQ : ν.IntertwiningMap α :=
    { toFun := fun v => pre (proj v)
      map_add' := fun v w => by
        apply hj
        change j (pre (proj (v + w))) = j (pre (proj v) + pre (proj w))
        rw [hpreval, map_add j, hpreval, hpreval]
        exact congrArg Subtype.val (map_add proj v w)
      map_smul' := fun c v => by
        apply hj
        change j (pre (proj (c • v))) = j (c • pre (proj v))
        rw [hpreval, map_smul j, hpreval]
        exact congrArg Subtype.val (map_smul proj c v)
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro v
        apply hj
        change j (pre (proj (ν g v))) = j (α g (pre (proj v)))
        rw [hpreval, Representation.IntertwiningMap.isIntertwining α ν j, hpreval]
        exact congrArg Subtype.val
          (Representation.IntertwiningMap.isIntertwining ν _ proj g v) }
  refine ⟨rQ, ?_⟩
  intro v hv
  change j (pre (proj v)) = v
  exact (hpreval (proj v)).trans (congrArg Subtype.val (hproj ⟨v, hv⟩))

/-- If the simple source itself lies in the selected block, the preceding
construction is a retraction on that entire source as well. -/
theorem quotientRetraction
    (P : (Subgroup.center G →* ℂˣ) → Prop)
    (hε : Module.Finite ℂ
      (Submodule.span ℂ (Set.range (fun z : Subgroup.center G => ε (z : G)))))
    (hν : Module.Finite ℂ
      (Submodule.span ℂ (Set.range (fun z : Subgroup.center G => ν (z : G)))))
    (f : ε.IntertwiningMap ν) (hf : Function.Surjective f)
    (i : α.IntertwiningMap ε) (r : ε.IntertwiningMap α)
    (hfix : ∀ v : E, v ∈ groupedCentralCharacterSpace ε P → i (r v) = v)
    (hirr : Representation.IsIrreducible α)
    (hα : groupedCentralCharacterSpace α P = ⊤)
    (g : α.IntertwiningMap ν) (hg : g ≠ 0) :
    ∃ rQ : ν.IntertwiningMap α,
      (∀ a : A, rQ (f (i a)) = a) ∧
      ∀ v : N, v ∈ groupedCentralCharacterSpace ν P → f (i (rQ v)) = v := by
  have hαmem : ∀ a : A, a ∈ groupedCentralCharacterSpace α P := by
    intro a
    rw [hα]
    trivial
  have hj := quotientInjection P hε f hf i r hfix hirr g hg
    (fun a => map_mem_groupedCentralCharacterSpace g P (hαmem a))
  obtain ⟨rQ, hQ⟩ := quotientProjector P hε hν f hf i r hfix hj
  refine ⟨rQ, ?_, hQ⟩
  intro a
  apply hj
  exact hQ (f (i a))
    (map_mem_groupedCentralCharacterSpace (f.comp i) P (hαmem a))

end Langlands.QuotientRealBlockRetraction
