import Langlands.AlgebraicGeometry.Modules.IntegralIdealFiltration.Extension
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule

/-! # The ideal sheaf of admissible functions and its embedding into the module -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Langlands.Cohomology Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Modules

namespace IntegralIdealFiltration

open AffineVanishing QuasicoherentLocal Scheme.IdealSheafData

variable {X : Scheme.{u}} {Q : X.Modules}

namespace Witness

variable (w : Witness Q)

/-- A function on an open `V` of the closed subscheme is admissible if over every open of `X`
whose trace lies in `V` its multiple of `s` extends to a killed section. -/
def Mem (V : w.Z.Opens) (a : Γ(w.Z, V)) : Prop :=
  ∀ (W : X.Opens) (h : w.i ⁻¹ᵁ W ≤ V), w.InT W (rres h a)

variable {w}

lemma InT.mul {W : X.Opens} {a : Γ(w.Z, w.i ⁻¹ᵁ W)} (c : Γ(w.Z, w.i ⁻¹ᵁ W)) (h : w.InT W a) :
    w.InT W (c * a) := by
  apply inT_of_local
  intro x hx
  obtain ⟨V, hVa, hxV, hVW⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hx
  obtain ⟨r, hr⟩ := w.app_surjective ⟨V, hVa⟩ (rres (w.pre_le hVW) c)
  refine ⟨V, hVW, hxV, ?_⟩
  rw [map_mul, ← hr]
  exact (h.res hVW).smul r

lemma mem_res {V V' : w.Z.Opens} (hV : V' ≤ V) {a : Γ(w.Z, V)} (ha : w.Mem V a) :
    w.Mem V' (rres hV a) := fun W h => by
  rw [rres_rres]
  exact ha W (h.trans hV)

lemma mem_iff_inT (W : X.Opens) (a : Γ(w.Z, w.i ⁻¹ᵁ W)) : w.Mem (w.i ⁻¹ᵁ W) a ↔ w.InT W a :=
  (inT_iff_forall W a).symm

lemma mem_of_local {V : w.Z.Opens} {a : Γ(w.Z, V)}
    (h : ∀ z ∈ V, ∃ (V' : w.Z.Opens) (hV' : V' ≤ V), z ∈ V' ∧ w.Mem V' (rres hV' a)) :
    w.Mem V a := by
  intro W hW
  apply inT_of_local
  intro x hx
  by_cases hxZ : x ∈ w.Zc
  · have hx' : x ∈ Set.range w.i := by rw [w.range_i]; exact hxZ
    obtain ⟨z, rfl⟩ := hx'
    obtain ⟨V', hV', hzV', hmem⟩ := h z (hW hx)
    obtain ⟨O, hO, hOV⟩ := w.i.isClosedEmbedding.isInducing.isOpen_iff.1 V'.isOpen
    let O' : X.Opens := ⟨O, hO⟩
    have hle : w.i ⁻¹ᵁ (W ⊓ O') ≤ V' := fun y hy => by
      have : w.i y ∈ O := hy.2
      show y ∈ (V' : Set w.Z)
      rw [← hOV]
      exact this
    refine ⟨W ⊓ O', inf_le_left, ⟨hx, ?_⟩, ?_⟩
    · change w.i z ∈ O
      have : z ∈ (V' : Set w.Z) := hzV'
      rw [← hOV] at this
      exact this
    · have := hmem (W ⊓ O') hle
      rw [rres_rres] at this ⊢
      exact this
  · refine ⟨W ⊓ w.Zc.compl, inf_le_left, ⟨hx, hxZ⟩, ?_⟩
    exact inT_of_disjoint (fun y (hy : y ∈ W ⊓ w.Zc.compl) => hy.2) _

variable (w)

/-- The ideal sheaf of admissible functions on the closed subscheme. -/
def idealSub : SheafOfModules.Submodule (structureModule w.Z) where
  obj V :=
    { carrier := {a | w.Mem V.unop a}
      add_mem' := fun {a b} ha hb W h => by
        rw [show rres h (a + b) = rres h a + rres h b from map_add _ _ _]
        exact (ha W h).add (hb W h)
      zero_mem' := fun W h => by
        rw [show rres h (0 : Γ(w.Z, V.unop)) = 0 from map_zero _]
        exact inT_zero W
      smul_mem' := fun c a ha W h => by
        let c' : Γ(w.Z, V.unop) := c
        let a' : Γ(w.Z, V.unop) := a
        change w.InT W (rres h (c' * a'))
        rw [map_mul]
        exact (ha W h).mul _ }
  map {V V'} f a ha := by
    have hle : V'.unop ≤ V.unop := leOfHom f.unop
    have hf : f = (homOfLE hle).op := Subsingleton.elim _ _
    subst hf
    exact mem_res hle ha
  isSheaf V a ha := by
    apply mem_of_local
    intro z hz
    obtain ⟨V', f, hf, hzV'⟩ := ha z hz
    exact ⟨V', leOfHom f, hzV', hf⟩

/-- The ideal sheaf of admissible functions, as a module on the closed subscheme. -/
abbrev I : w.Z.Modules := (w.idealSub).toSheafOfModules

/-- The inclusion of the ideal sheaf into the structure sheaf. -/
abbrev ι : w.I ⟶ structureModule w.Z := (w.idealSub).ι

end Witness

end IntegralIdealFiltration

end Langlands.AlgebraicGeometry.Modules
