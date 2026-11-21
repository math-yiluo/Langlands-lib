import Langlands.HarmonicAnalysis.SchwartzBruhatProduct
import Langlands.Representation.Hecke.TestFunction

/-! Finite tensor expansions that retain left and right subgroup invariance. -/

noncomputable section

namespace Langlands.Hecke.TestFunction

open Langlands.HarmonicAnalysis

universe u v

variable {G : Type u} {H : Type v} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H] [T2Space G] [T2Space H]

/-- A bi-invariant test function for product subgroups has a finite expansion
in tensor products of bi-invariant test functions on the factors. -/
theorem exists_biInvariant_tensor_expansion
    {K L : Subgroup G} {K' L' : Subgroup H} (f : SchwartzBruhat (G × H))
    (hf : f ∈ biInvariant (K.prod K') (L.prod L')) :
    ∃ (N : ℕ) (α : Fin N → biInvariant K L) (β : Fin N → biInvariant K' L'),
      ∀ x y, f (x, y) = ∑ j, (α j).val x * (β j).val y := by
  classical
  let row (x : G) (y : H) := f (x, y)
  have hLocal : IsLocallyConstant row := f.isLocallyConstant_curry
  have hCompact : HasCompactSupport row := f.hasCompactSupport_curry
  let S : Set (H → ℂ) := {w | w ∈ Set.range row ∧ w ≠ 0}
  have hFinite : S.Finite :=
    (finite_range_of_locallyConstant_of_hasCompactSupport hLocal hCompact).subset
      (fun _ hw => hw.1)
  let : Fintype S := hFinite.fintype
  let sample : S → G := fun w => w.property.1.choose
  have hSample (w : S) : row (sample w) = w.val := w.property.1.choose_spec
  have hLeft (k : K) (x : G) : row (k.val * x) = row x := by
    funext y
    have he := hf.1 ⟨(k.val, 1), k.property, K'.one_mem⟩ (x, y)
    change f (k.val * x, (1 : H) * y) = f (x, y) at he
    simpa only [one_mul] using he
  have hRight (l : L) (x : G) : row (x * l.val) = row x := by
    funext y
    have he := hf.2 ⟨(l.val, 1), l.property, L'.one_mem⟩ (x, y)
    change f (x * l.val, y * (1 : H)) = f (x, y) at he
    simpa only [mul_one] using he
  let α (w : S) : biInvariant K L :=
    ⟨⟨fun x => if row x = w.val then 1 else 0,
        hLocal.comp (fun r => if r = w.val then (1 : ℂ) else 0),
        hCompact.comp_left (g := fun r => if r = w.val then (1 : ℂ) else 0)
          (by simp [Ne.symm w.property.2])⟩,
      ⟨fun k x => by
        change (if row (k.val * x) = w.val then 1 else (0 : ℂ)) = _
        rw [hLeft], fun l x => by
        change (if row (x * l.val) = w.val then 1 else (0 : ℂ)) = _
        rw [hRight]⟩⟩
  let β (w : S) : biInvariant K' L' := ⟨f.sliceSnd (sample w), by
    constructor
    · intro k y
      have he := hf.1 ⟨(1, k.val), K.one_mem, k.property⟩ (sample w, y)
      change f ((1 : G) * sample w, k.val * y) = f (sample w, y) at he
      simpa only [SchwartzBruhat.sliceSnd_apply, one_mul] using he
    · intro l y
      have he := hf.2 ⟨(1, l.val), L.one_mem, l.property⟩ (sample w, y)
      change f (sample w * (1 : G), y * l.val) = f (sample w, y) at he
      simpa only [SchwartzBruhat.sliceSnd_apply, mul_one] using he⟩
  have hsum (x : G) (y : H) : row x y = ∑ w : S, (α w).val x * (β w).val y := by
    change row x y = ∑ w : S, (if row x = w.val then 1 else 0) * row (sample w) y
    by_cases hx : row x = 0
    · simp [hx, fun w : S => Ne.symm w.property.2]
    · let w : S := ⟨row x, ⟨⟨x, rfl⟩, hx⟩⟩
      rw [Finset.sum_eq_single w]
      · simp [w, hSample]
      · intro v _ hv
        have he : row x ≠ v.val := fun he => hv (Subtype.ext he.symm)
        simp [he]
      · simp
  let e := Fintype.equivFin S
  refine ⟨Fintype.card S, fun i => α (e.symm i), fun i => β (e.symm i), ?_⟩
  intro x y
  change row x y = _
  rw [hsum]
  exact Fintype.sum_equiv e _ _ (fun _ => by simp)

end Langlands.Hecke.TestFunction
