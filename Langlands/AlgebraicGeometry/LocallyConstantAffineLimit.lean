import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.Topology.LocallyConstant.Basic

/-! # Locally constant functions on affine inverse limits -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.LocallyConstantAffineLimit

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)] {A : Type*}

include hc

/-- A locally constant function into an arbitrary set descends to an affine stage. -/
theorem exists_level (f : LocallyConstant c.pt A) :
    ∃ (i : I) (g : LocallyConstant (D.obj i) A), ∀ x, g (c.π.app i x) = f x := by
  classical
  let : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  let B := Set.range f
  let : Fintype B := f.range_finite.fintype
  let V (a : B) : c.pt.Opens := ⟨{x | f x = a}, f.2.isOpen_fiber a⟩
  have hV (a : B) : IsCompact (V a : Set c.pt) := (f.2.isClosed_fiber a).isCompact
  choose i U hU hπ using fun a : B => exists_preimage_eq D c hc (V a) (hV a)
  obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  let r (a : B) : j ⟶ i a := (hj (Finset.mem_image_of_mem i (Finset.mem_univ a))).some
  let W (a : B) : (D.obj j).Opens := D.map (r a) ⁻¹ᵁ U a
  have hW (a : B) : IsCompact (W a : Set (D.obj j)) :=
    QuasiCompact.isCompact_preimage (f := D.map (r a)) _ (U a).2 (hU a)
  have hw (a : B) : c.π.app j ⁻¹ᵁ W a = V a := by
    simp only [W, ← Scheme.Hom.comp_preimage, c.w, hπ]
  have hcover : c.π.app j ⁻¹ᵁ (⨆ a, W a) = ⊤ := by
    rw [Scheme.Hom.preimage_iSup, ← top_le_iff]
    intro x _
    exact Opens.mem_iSup.mpr ⟨⟨f x, ⟨x, rfl⟩⟩, by rw [hw]; rfl⟩
  obtain ⟨j₀, r₀, hr₀⟩ := exists_map_eq_top D c hc _ hcover
  let P := {ab : B × B // ab.1 ≠ ab.2}
  have pair (p : P) : ∃ (l : I) (s : l ⟶ j),
      D.map s ⁻¹ᵁ (W p.1.1 ⊓ W p.1.2) = ⊥ := by
    have hp : c.π.app j ⁻¹ᵁ (W p.1.1 ⊓ W p.1.2) ≤ c.π.app j ⁻¹ᵁ ⊥ := by
      rw [Scheme.Hom.preimage_inf, hw, hw]
      intro x hx
      exact (p.2 (Subtype.ext (hx.1.symm.trans hx.2))).elim
    obtain ⟨l, s, hs⟩ := exists_map_preimage_le_map_preimage D c hc
      (QuasiSeparatedSpace.inter_isCompact _ _ (W p.1.1).2 (hW p.1.1)
        (W p.1.2).2 (hW p.1.2)) hp
    exact ⟨l, s, le_bot_iff.mp hs⟩
  choose l s hs using pair
  let K (p : Option P) : I := p.elim j₀ l
  let t (p : Option P) : K p ⟶ j := match p with
    | none => r₀
    | some p => s p
  obtain ⟨k, rj, rK, hK⟩ := IsCofiltered.wideCospan t
  let Z (a : B) : (D.obj k).Opens := D.map rj ⁻¹ᵁ W a
  have cover : ∀ x : D.obj k, ∃ a, x ∈ Z a := by
    intro x
    apply (Opens.mem_iSup (s := Z)).mp
    change x ∈ ⨆ a, D.map rj ⁻¹ᵁ W a
    rw [← Scheme.Hom.preimage_iSup, ← hK none, Functor.map_comp,
      Scheme.Hom.comp_preimage]
    exact hr₀.ge (Set.mem_univ (D.map (rK none) x))
  have unique (x : D.obj k) (a b : B) (ha : x ∈ Z a) (hb : x ∈ Z b) : a = b := by
    by_contra hab
    let p : P := ⟨(a, b), hab⟩
    have h : x ∈ D.map rj ⁻¹ᵁ (W a ⊓ W b) := ⟨ha, hb⟩
    rw [← hK (some p), Functor.map_comp, Scheme.Hom.comp_preimage] at h
    have hx : D.map (rK (some p)) x ∈ D.map (s p) ⁻¹ᵁ (W p.1.1 ⊓ W p.1.2) := h
    rw [hs p] at hx
    exact hx
  let g (x : D.obj k) : B := (cover x).choose
  have hg (x : D.obj k) : x ∈ Z (g x) := (cover x).choose_spec
  have gloc : IsLocallyConstant (fun x => (g x : A)) := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro x
    exact ⟨Z (g x), (Z (g x)).2, hg x, fun y hy => congrArg Subtype.val (unique y _ _ (hg y) hy)⟩
  refine ⟨k, ⟨fun x => g x, gloc⟩, ?_⟩
  intro x
  have hx : x ∈ c.π.app k ⁻¹ᵁ Z (g (c.π.app k x)) := hg _
  rw [show c.π.app k ⁻¹ᵁ Z (g (c.π.app k x)) = V (g (c.π.app k x)) by
    simp only [Z, ← Scheme.Hom.comp_preimage, c.w, hw]] at hx
  exact hx.symm

/-- Agreement on the inverse limit of two locally constant functions holds at a later stage. -/
theorem exists_level_eq {i : I} (f g : LocallyConstant (D.obj i) A)
    (h : ∀ x, f (c.π.app i x) = g (c.π.app i x)) :
    ∃ (j : I) (r : j ⟶ i), ∀ x, f (D.map r x) = g (D.map r x) := by
  let U : (D.obj i).Opens := ⟨{x | f x = g x},
    (f.2.prodMk g.2) {ab | ab.1 = ab.2}⟩
  have hU : c.π.app i ⁻¹ᵁ U = ⊤ := by
    rw [← top_le_iff]
    exact fun x _ => h x
  obtain ⟨j, r, hr⟩ := exists_map_eq_top D c hc U hU
  exact ⟨j, r, fun x => hr.ge (Set.mem_univ x)⟩

end Langlands.AlgebraicGeometry.LocallyConstantAffineLimit
