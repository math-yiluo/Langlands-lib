import Langlands.Representation.Exponents.SplitComponentComparison
import Langlands.Representation.SubrepresentationLattice
import Mathlib.Order.CompactlyGenerated.Basic

/-! Selecting any collection of generalized weights of a central group action. -/

noncomputable section

namespace Langlands

universe uR uA uM uV uW

variable {R : Type uR} [Field R] {A : Type uA} [Group A]
  {M : Type uM} [Group M] [TopologicalSpace M] [NonarchimedeanGroup M]
  [WeaklyLocallyCompactSpace M]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module R W]
  (π : Representation R M V) (ι : A →* M)
  (hι : ∀ a : A, ι a ∈ Subgroup.center M) (P : (A →* Rˣ) → Prop)

/-- The sum of the generalized weight spaces selected by a character predicate. -/
def selectedWeightPart : Subrepresentation π :=
  ⨆ (χ : A →* Rˣ) (_ : P χ), generalizedWeightSpace π ι χ hι

omit [WeaklyLocallyCompactSpace M] in
theorem selectedWeightPart_toSubmodule :
    (selectedWeightPart π ι hι P).toSubmodule =
      ⨆ (χ : A →* Rˣ) (_ : P χ), (generalizedWeightSpace π ι χ hι).toSubmodule := by
  simp only [selectedWeightPart, Subrepresentation.toSubmodule_iSup]

/-- The two complementary selections are disjoint without admissibility. -/
theorem selectedWeightPart_disjoint (hπ : IsSmooth π) :
    Disjoint (selectedWeightPart π ι hι P).toSubmodule
      (selectedWeightPart π ι hι (fun χ => ¬ P χ)).toSubmodule := by
  rw [selectedWeightPart_toSubmodule, selectedWeightPart_toSubmodule]
  exact (generalizedWeightSpace_independent π ι hι hπ).disjoint_biSup_biSup
    (Set.disjoint_left.mpr fun _ hp hn => hn hp)

/-- Splitting the character index partitions the sum of all weight spaces. -/
theorem selectedWeightPart_sup_complement :
    (selectedWeightPart π ι hι P).toSubmodule ⊔
        (selectedWeightPart π ι hι (fun χ => ¬ P χ)).toSubmodule =
      ⨆ χ : A →* Rˣ, (generalizedWeightSpace π ι χ hι).toSubmodule := by
  rw [selectedWeightPart_toSubmodule, selectedWeightPart_toSubmodule]
  exact (iSup_split
    (fun χ : A →* Rˣ => (generalizedWeightSpace π ι χ hι).toSubmodule) P).symm

/-- Spanning supplies the decomposition into selected and unselected vectors. -/
theorem selectedWeightPart_codisjoint
    (hspan : (⨆ χ : A →* Rˣ,
      (generalizedWeightSpace π ι χ hι).toSubmodule) = ⊤) :
    Codisjoint (selectedWeightPart π ι hι P).toSubmodule
      (selectedWeightPart π ι hι (fun χ => ¬ P χ)).toSubmodule := by
  rw [codisjoint_iff, selectedWeightPart_sup_complement, hspan]

variable {π} {σ : Representation R M W}

/-- Every intertwiner preserves each selected sum. -/
theorem map_mem_selectedWeightPart (f : π.IntertwiningMap σ) {v : V}
    (hv : v ∈ selectedWeightPart π ι hι P) :
    f v ∈ selectedWeightPart σ ι hι P := by
  have hle : (selectedWeightPart π ι hι P).toSubmodule ≤
      (selectedWeightPart σ ι hι P).toSubmodule.comap f.toLinearMap := by
    rw [selectedWeightPart_toSubmodule]
    refine iSup_le fun χ => iSup_le fun hp => ?_
    intro v hv
    change f v ∈ (selectedWeightPart σ ι hι P).toSubmodule
    rw [selectedWeightPart_toSubmodule]
    exact (le_iSup₂_of_le χ hp le_rfl :
      (generalizedWeightSpace σ ι χ hι).toSubmodule ≤
        ⨆ (ψ : A →* Rˣ) (_ : P ψ),
          (generalizedWeightSpace σ ι ψ hι).toSubmodule)
      (map_mem_generalizedWeightSpace ι χ hι f hv)
  exact hle hv

/-- Restrict the given intertwiner to the literal selected subrepresentations. -/
def selectedWeightMap (f : π.IntertwiningMap σ) :
    (selectedWeightPart π ι hι P).toRepresentation.IntertwiningMap
      (selectedWeightPart σ ι hι P).toRepresentation where
  toFun v := ⟨f v, map_mem_selectedWeightPart ι hι P f v.property⟩
  map_add' _ _ := Subtype.ext (map_add f _ _)
  map_smul' _ _ := Subtype.ext (map_smul f _ _)
  isIntertwining' m := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining π σ f m (v : V)

@[simp]
theorem selectedWeightMap_apply (f : π.IntertwiningMap σ)
    (v : selectedWeightPart π ι hι P) :
    (selectedWeightMap ι hι P f v : W) = f (v : V) := rfl

/-- An onto map remains onto after selecting weights, provided the source
weights span. Target admissibility is not required. -/
theorem selectedWeightMap_surjective (hσ : IsSmooth σ)
    (hspan : (⨆ χ : A →* Rˣ,
      (generalizedWeightSpace π ι χ hι).toSubmodule) = ⊤)
    (f : π.IntertwiningMap σ) (hf : Function.Surjective f) :
    Function.Surjective (selectedWeightMap ι hι P f) := by
  intro w
  obtain ⟨v, hv⟩ := hf (w : W)
  obtain ⟨x, y, hx, hy, hxy⟩ :=
    Submodule.codisjoint_iff_exists_add_eq.mp
      (selectedWeightPart_codisjoint π ι hι P hspan) v
  have hfx := map_mem_selectedWeightPart ι hι P f hx
  have hfy := map_mem_selectedWeightPart ι hι (fun χ => ¬ P χ) f hy
  have heq : f x + f y = (w : W) := by rw [← map_add, hxy, hv]
  have hfy' : f y ∈ selectedWeightPart σ ι hι P := by
    have he : f y = (w : W) - f x := by rw [← heq]; abel
    rw [he]
    exact (selectedWeightPart σ ι hι P).toSubmodule.sub_mem w.property hfx
  have hy0 : f y = 0 :=
    Submodule.disjoint_def.mp (selectedWeightPart_disjoint σ ι hι P hσ) _ hfy' hfy
  refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
  change f x = (w : W)
  simpa only [hy0, add_zero] using heq

/-- An injective intertwiner reflects membership in the selected part when
the source weights span. -/
theorem mem_selectedWeightPart_iff_of_injective (hσ : IsSmooth σ)
    (hspan : (⨆ χ : A →* Rˣ,
      (generalizedWeightSpace π ι χ hι).toSubmodule) = ⊤)
    (f : π.IntertwiningMap σ) (hf : Function.Injective f) (v : V) :
    f v ∈ selectedWeightPart σ ι hι P ↔ v ∈ selectedWeightPart π ι hι P := by
  constructor
  · intro hv
    obtain ⟨x, y, hx, hy, hxy⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.mp
        (selectedWeightPart_codisjoint π ι hι P hspan) v
    have hfx := map_mem_selectedWeightPart ι hι P f hx
    have hfy := map_mem_selectedWeightPart ι hι (fun χ => ¬ P χ) f hy
    have heq : f x + f y = f v := by rw [← map_add, hxy]
    have hfy' : f y ∈ selectedWeightPart σ ι hι P := by
      have he : f y = f v - f x := by rw [← heq]; abel
      rw [he]
      exact (selectedWeightPart σ ι hι P).toSubmodule.sub_mem hv hfx
    have hy0 : f y = 0 :=
      Submodule.disjoint_def.mp (selectedWeightPart_disjoint σ ι hι P hσ) _ hfy' hfy
    have hyzero : y = 0 := hf (hy0.trans (map_zero f).symm)
    have hxv : x = v := by simpa only [hyzero, add_zero] using hxy
    exact hxv ▸ hx
  · exact map_mem_selectedWeightPart ι hι P f

end Langlands
