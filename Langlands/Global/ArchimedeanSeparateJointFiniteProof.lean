import Langlands.Global.ArchimedeanSeparateJointFiniteStatement

/-! # Separate center and compact differential finiteness imply joint finiteness -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The two finite differential orbits generate a finite joint orbit by centrality. -/
theorem separateJointFinite : SeparateJointFiniteStatement K n := by
  classical
  intro f hcenter hcompact
  have : Module.Finite ℂ (centerOrbitSpan K n f) := hcenter
  obtain ⟨s, hs, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset
      (Set.range fun b => compactEnvelopingRepresentation K n b f)).mp
      (Module.Finite.iff_fg.mp hcompact)
  let b : s → compactEnvelopingSubalgebra K n := fun i => (hs i.property).choose
  have hb (i : s) : compactEnvelopingAction K n (b i) f = i.val :=
    (hs i.property).choose_spec
  let S : Submodule ℂ (SmoothFunctions K n) :=
    ⨆ i : s, (centerOrbitSpan K n f).map (compactEnvelopingAction K n (b i))
  have : ∀ i : s, Module.Finite ℂ
      ((centerOrbitSpan K n f).map (compactEnvelopingAction K n (b i))) :=
    fun i => Module.Finite.map _ _
  have : Module.Finite ℂ S := Submodule.finite_iSup _
  apply Submodule.finiteDimensional_of_le (S₂ := S)
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨z, c⟩, rfl⟩
  change jointRepresentation K n (z, c) f ∈ S
  rw [jointRepresentation_apply_eq]
  have hle : Submodule.span ℂ (s : Set (SmoothFunctions K n)) ≤
      S.comap (centerAction K n z) := by
    apply Submodule.span_le.mpr
    intro y hy
    let i : s := ⟨y, hy⟩
    change centerAction K n z i.val ∈ S
    rw [← hb i]
    have hcomm : centerAction K n z (compactEnvelopingAction K n (b i) f) =
        compactEnvelopingAction K n (b i) (centerAction K n z f) := by
      change envelopingAction K n (centerInclusion K n z)
          (envelopingAction K n (b i).val f) =
        envelopingAction K n (b i).val
          (envelopingAction K n (centerInclusion K n z) f)
      rw [← envelopingAction_mul, ← centerInclusion_commute, envelopingAction_mul]
    rw [hcomm]
    apply (le_iSup (fun j : s =>
      (centerOrbitSpan K n f).map (compactEnvelopingAction K n (b j))) i)
    exact Submodule.mem_map_of_mem (centerAction_mem_centerOrbitSpan K n f z)
  apply hle
  rw [← hspan]
  exact Langlands.FiniteVectors.action_mem_orbitSpan
    (compactEnvelopingRepresentation K n) c f

end Langlands.Global.ArchimedeanGL
