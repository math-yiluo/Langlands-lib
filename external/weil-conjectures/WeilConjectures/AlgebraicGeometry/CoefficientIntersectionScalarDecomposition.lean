/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # Products generating the ring of an affine base-change intersection

Source: Stacks Project, Tag 02KG, Lemma 30.5.1, affine tensor computation.
(blueprint: lem-pc-coefficient-intersection-scalar-decomposition).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry
noncomputable section
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every scalar on the intersection is a finite sum of products of scalars from
its two factors. Source: Stacks Project, Tag 02KG, Lemma 30.5.1.
(blueprint: lem-pc-coefficient-intersection-scalar-decomposition).

Proof: Put Y = f inverse image U and V = the image of Z under Y -> X.
The open immersion identifies Z with V. Restrict the given cartesian square
first to V and then to B. Its top left corner is I = W intersect f' inverse
image B, and the square identifies I with Z times_U B. All three factors
Z, U and B are affine, so the affine pullback ring is Gamma(B) tensor over
Gamma(U) Gamma(Z). The open immersion identifies Gamma(Z) with Gamma(X,V).
The maps from these two rings to Gamma(X',I) are precisely app followed by
restriction as displayed below. The canonical tensor map is surjective, and
its pure tensors are the displayed products. Tensor induction expresses any
preimage as a finite sum of pure tensors (scalar multiples are absorbed into
one factor). The empty intersection and zero rings obey the same tensor
calculation, and the zero scalar also admits the empty sum. -/
theorem coefficientIntersection_scalar_decomposition
    {X T : Scheme.{u}} (f : X ⟶ T) [IsSeparated f]
    (U : T.Opens) (hU : IsAffineOpen U)
    (Z : (f ⁻¹ᵁ U).toScheme.Opens) (hZ : IsAffineOpen Z)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (sq : IsPullback g' f' f (g ≫ U.ι))
    (W : X'.Opens) (hW : W = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z))
    (B : T'.Opens) (hB : IsAffineOpen B)
    (a : Γ(X', W ⊓ f' ⁻¹ᵁ B)) :
    ∃ (n : ℕ) (r : Fin n → Γ(T', B))
      (d : Fin n → Γ(X, (f ⁻¹ᵁ U).ι ''ᵁ Z)),
      a = ∑ j, (X'.presheaf.map (homOfLE
        (inf_le_right : W ⊓ f' ⁻¹ᵁ B ≤ f' ⁻¹ᵁ B)).op (f'.app B (r j))) *
        (X'.presheaf.map (homOfLE (show
          W ⊓ f' ⁻¹ᵁ B ≤ g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z) from
            inf_le_left.trans hW.le)).op
          (g'.app ((f ⁻¹ᵁ U).ι ''ᵁ Z) (d j))) := by
  let V := (f ⁻¹ᵁ U).ι ''ᵁ Z
  let I := W ⊓ f' ⁻¹ᵁ B
  have hVX : V ≤ f ⁻¹ᵁ U := (f ⁻¹ᵁ U).ι_image_le Z
  have hBT : B ≤ (g ≫ U.ι) ⁻¹ᵁ U := by
    simp [Scheme.Opens.ι_preimage_self]
  have hI : I = g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ B := by rw [← hW]
  have hV : IsAffineOpen V := hZ.image_of_isOpenImmersion (f ⁻¹ᵁ U).ι
  have hiso := isIso_pushoutSection_of_isAffineOpen sq hBT hVX hI hU hB hV
  have H := (isIso_pushoutSection_iff sq hBT hVX hI).mp hiso
  let α := f.appLE U V hVX
  let β := (g ≫ U.ι).appLE U B hBT
  let ρ := f'.appLE B I (by dsimp [I]; exact inf_le_right)
  let δ := g'.appLE V I (by rw [hI]; exact inf_le_left)
  change IsPushout α β δ ρ at H
  let : Algebra Γ(T, U) Γ(X, V) := α.hom.toAlgebra
  let : Algebra Γ(T, U) Γ(T', B) := β.hom.toAlgebra
  have HT := CommRingCat.isPushout_tensorProduct Γ(T, U) Γ(T', B) Γ(X, V)
  let e : CommRingCat.of (Γ(T', B) ⊗[Γ(T, U)] Γ(X, V)) ≅ Γ(X', I) :=
    HT.isoIsPushout _ _ H.flip
  have hleft (r : Γ(T', B)) : e.hom (r ⊗ₜ 1) = ρ r := by
    exact congrArg (fun m ↦ m r) (HT.inl_isoIsPushout_hom _ _ H.flip)
  have hright (d : Γ(X, V)) : e.hom (1 ⊗ₜ d) = δ d := by
    exact congrArg (fun m ↦ m d) (HT.inr_isoIsPushout_hom _ _ H.flip)
  have hpure (r : Γ(T', B)) (d : Γ(X, V)) :
      e.hom (r ⊗ₜ d) = ρ r * δ d := by
    rw [← hleft, ← hright, ← map_mul]
    simp
  obtain ⟨n, r, d, ha⟩ := TensorProduct.exists_sum_tmul_eq (e.inv a)
  refine ⟨n, r, d, ?_⟩
  have he := congrArg (fun x ↦ e.hom x) ha
  rw [Iso.inv_hom_id_apply, map_sum] at he
  simpa only [hpure, ρ, δ, Scheme.Hom.appLE, CommRingCat.comp_apply] using he


end
end AlgebraicGeometry
