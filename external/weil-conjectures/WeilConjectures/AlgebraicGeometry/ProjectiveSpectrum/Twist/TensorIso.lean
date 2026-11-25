/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeGeneratorIso
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.TensorObj

/-!
# The canonical isomorphism `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` on a projective spectrum

When the basic opens `D₊(f)` of the homogeneous elements of degree `1` cover `Proj 𝒜`, the
local isomorphisms `fᵃ ⊗ fᵇ ↦ fᵃ⁺ᵇ` glue to an isomorphism
`AlgebraicGeometry.Proj.twistTensorIso: 𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)`, refining
`AlgebraicGeometry.Proj.nonempty_tensorObj_twist_iso`.
-/

@[expose] public section

noncomputable section
universe u

open CategoryTheory


namespace AlgebraicGeometry.Proj

open ProjectiveSpectrum.Twist MonoidalCategory Scheme.Modules

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- If every point of `Proj 𝒜` lies in some `D₊(f)` with `f` homogeneous of degree `1`, these
basic opens cover `Proj 𝒜`. -/
lemma iSup_basicOpen_degOne_eq_top (h : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ Proj.basicOpen 𝒜 f) :
    ⨆ i : {f : A // f ∈ 𝒜 1}, Proj.basicOpen 𝒜 i.1 = ⊤ :=
  eq_top_iff.mpr fun x _ ↦ by
    obtain ⟨f, hf, hx⟩ := h x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hf⟩, hx⟩

/-- **The transition functions of `fᵃ⁺ᵇ` and of `fᵃ ⊗ fᵇ` agree**: if
`α • fᵃ⁺ᵇ = β • gᵃ⁺ᵇ` on an open `W ⊆ D₊(f) ∩ D₊(g)`, then `α • fᵃ ⊗ fᵇ = β • gᵃ ⊗ gᵇ` on `W`,
for `f`, `g` homogeneous of degree `1`. -/
lemma twistTensor_transition (a b : ℤ) (i j : {f : A // f ∈ 𝒜 1}) (W : (Proj 𝒜).Opens)
    (hi : W ≤ Proj.basicOpen 𝒜 i.1) (hj : W ≤ Proj.basicOpen 𝒜 j.1) (α β : Γ(Proj 𝒜, W))
    (hαβ : α • (twist 𝒜 (a + b)).presheaf.map (homOfLE hi).op (twistPowSection (a + b) i.2) =
      β • (twist 𝒜 (a + b)).presheaf.map (homOfLE hj).op (twistPowSection (a + b) j.2)) :
    α • (twist 𝒜 a ⊗ twist 𝒜 b).presheaf.map (homOfLE hi).op
        (tmulSection (twistPowSection a i.2) (twistPowSection b i.2)) =
      β • (twist 𝒜 a ⊗ twist 𝒜 b).presheaf.map (homOfLE hj).op
        (tmulSection (twistPowSection a j.2) (twistPowSection b j.2)) := by
  obtain ⟨f, hf⟩ := i
  obtain ⟨g, hg⟩ := j
  obtain ⟨c, hc⟩ := ((isFreeGenerator_twistPowSection a hg).map hj).exists_smul_eq
    ((twist 𝒜 a).presheaf.map (homOfLE hi).op (twistPowSection a hf))
  obtain ⟨d, hd⟩ := ((isFreeGenerator_twistPowSection b hg).map hj).exists_smul_eq
    ((twist 𝒜 b).presheaf.map (homOfLE hi).op (twistPowSection b hf))
  have hcd := twistPowSection_map_eq_mul_smul hf hg hi hj hc hd
  have hβ : α * (c * d) = β := by
    refine ((isFreeGenerator_twistPowSection (a + b) hg).map hj).smul_left_injective ?_
    dsimp only
    rw [mul_smul, hcd]
    exact hαβ
  rw [tmulSection_map, tmulSection_map, ← hc, ← hd, smul_tmulSection, tmulSection_smul,
    smul_smul, smul_smul, ← hβ, mul_assoc]

variable (𝒜) in
/-- **The canonical isomorphism `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)`**, when the basic opens `D₊(f)` of
the homogeneous elements `f` of degree `1` cover `Proj 𝒜`: the isomorphism whose restriction to
each `D₊(f)` sends the free generator `fᵃ ⊗ fᵇ` to the free generator `fᵃ⁺ᵇ`
(`twistTensorIso_hom_app_tmulSection`). It is glued from these local isomorphisms, which agree
on overlaps because the transition functions of both sides are the same
(`twistTensor_transition`). -/
noncomputable def twistTensorIso (h : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ Proj.basicOpen 𝒜 f)
    (a b : ℤ) : twist 𝒜 a ⊗ twist 𝒜 b ≅ twist 𝒜 (a + b) :=
  (isoOfIsFreeGenerator (iSup_basicOpen_degOne_eq_top h)
    (fun i ↦ isFreeGenerator_twistPowSection (a + b) i.2)
    (fun i ↦ (isFreeGenerator_twistPowSection a i.2).tmulSection
      (isFreeGenerator_twistPowSection b i.2))
    (twistTensor_transition a b)).symm

/-- **Local basis property of `twistTensorIso`**: on `D₊(f)`, for `f` homogeneous of degree
`1`, the canonical isomorphism `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` sends `fᵃ ⊗ fᵇ` to `fᵃ⁺ᵇ`, i.e.
`e^{(a)} ⊗ e^{(b)} ↦ e^{(a+b)}`. -/
lemma twistTensorIso_hom_app_tmulSection
    (h : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ Proj.basicOpen 𝒜 f) (a b : ℤ) {f : A} (hf : f ∈ 𝒜 1) :
    (twistTensorIso 𝒜 h a b).hom.app (Proj.basicOpen 𝒜 f)
        (tmulSection (twistPowSection a hf) (twistPowSection b hf)) =
      twistPowSection (a + b) hf :=
  isoOfIsFreeGenerator_inv_app (iSup_basicOpen_degOne_eq_top h)
    (fun i ↦ isFreeGenerator_twistPowSection (a + b) i.2)
    (fun i ↦ (isFreeGenerator_twistPowSection a i.2).tmulSection
      (isFreeGenerator_twistPowSection b i.2))
    (twistTensor_transition a b) ⟨f, hf⟩

/-- **Local description of `twistTensorIso`**: on an open `W ⊆ D₊(f)`, for `f` homogeneous of
degree `1`, the canonical isomorphism sends `r • (fᵃ ⊗ fᵇ)|_W` to `r • fᵃ⁺ᵇ|_W`. -/
lemma twistTensorIso_hom_app_smul
    (h : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ Proj.basicOpen 𝒜 f) (a b : ℤ) {f : A} (hf : f ∈ 𝒜 1)
    {W : (Proj 𝒜).Opens} (hW : W ≤ Proj.basicOpen 𝒜 f) (r : Γ(Proj 𝒜, W)) :
    (twistTensorIso 𝒜 h a b).hom.app W (r • (twist 𝒜 a ⊗ twist 𝒜 b).presheaf.map (homOfLE hW).op
        (tmulSection (twistPowSection a hf) (twistPowSection b hf))) =
      r • (twist 𝒜 (a + b)).presheaf.map (homOfLE hW).op (twistPowSection (a + b) hf) := by
  rw [← isoOfIsFreeGenerator_hom_app_smul (iSup_basicOpen_degOne_eq_top h)
    (fun i ↦ isFreeGenerator_twistPowSection (a + b) i.2)
    (fun i ↦ (isFreeGenerator_twistPowSection a i.2).tmulSection
      (isFreeGenerator_twistPowSection b i.2))
    (twistTensor_transition a b) ⟨f, hf⟩ hW r]
  exact inv_app_hom_app_apply_of_iso _ _

end AlgebraicGeometry.Proj
