/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeGeneratorIso
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

/-!
# The canonical isomorphism `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` on projective space

On the standard open `Uᵢ = D₊(xᵢ)` of `ℙ(n; S)` the twisting sheaf `𝒪(m)` has the free generator
`e_i^{(m)} = xᵢᵐ` (`AlgebraicGeometry.ProjectiveSpace.twistGenerator`), the pullback of the
section `Tᵢᵐ` of `𝒪(m)` on the integral model `Proj ℤ[Tᵢ]`. The transition functions are
`e_i^{(m)} = (xᵢ/xⱼ)ᵐ e_j^{(m)}`, which are multiplicative in `m`; hence the local isomorphisms
`e_i^{(a)} ⊗ e_i^{(b)} ↦ e_i^{(a+b)}` glue to an isomorphism
`AlgebraicGeometry.ProjectiveSpace.twistTensorIso: 𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- A relation `c₀ • s₂ = s₁` between sections of `M` over an open `V ⊆ U₁ ⊓ U₂` pulls back to
the relation `g^♯ c₀ • g^* s₂ = g^* s₁` over every open `W ⊆ g⁻¹ V`. -/
lemma pullbackSection_smul_map_eq {M : Y.Modules} {U₁ U₂ V : Y.Opens} (h₁ : V ≤ U₁)
    (h₂ : V ≤ U₂) {s₁ : Γ(M, U₁)} {s₂ : Γ(M, U₂)} {c₀ : Γ(Y, V)}
    (H : c₀ • M.presheaf.map (homOfLE h₂).op s₂ = M.presheaf.map (homOfLE h₁).op s₁)
    {W : X.Opens} (hW : W ≤ g ⁻¹ᵁ V) :
    X.presheaf.map (homOfLE hW).op (g.app V c₀) •
        ((pullback g).obj M).presheaf.map (homOfLE (hW.trans (g.preimage_mono h₂))).op
          (pullbackSection g s₂) =
      ((pullback g).obj M).presheaf.map (homOfLE (hW.trans (g.preimage_mono h₁))).op
        (pullbackSection g s₁) := by
  have h := congrArg (fun s ↦ ((pullback g).obj M).presheaf.map (homOfLE hW).op
    (pullbackSection g s)) H
  dsimp only at h
  rwa [pullbackSection_smul, pullbackSection_map, pullbackSection_map, map_smul,
    presheaf_map_homOfLE_map_homOfLE, presheaf_map_homOfLE_map_homOfLE] at h

end Scheme.Modules

namespace ProjectiveSpace

open Scheme.Modules MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : Type u) (S : Scheme.{u})

/-- **The free generator `e_i^{(m)} = xᵢᵐ` of `𝒪(m)` on the standard open `D₊(xᵢ)`** of
`ℙ(n; S)`: the pullback of the section `Tᵢᵐ` of `𝒪(m)` over `D₊(Tᵢ)` on the integral model. -/
def twistGenerator (m : ℤ) (i : n) : Γ(twist n S m, standardOpen n S i) :=
  pullbackSection (toProjInt n S)
    (Proj.twistPowSection m (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i))

/-- `e_i^{(m)}` is a free generator of `𝒪(m)` on `D₊(xᵢ)`. -/
lemma isFreeGenerator_twistGenerator (m : ℤ) (i : n) :
    IsFreeGenerator (twistGenerator n S m i) :=
  (Proj.isFreeGenerator_twistPowSection m _).pullback_unit_app (toProjInt n S)

/-- **The transition functions of the generators `e_i^{(m)}` are multiplicative in `m`**: on an
open `W ⊆ D₊(xᵢ) ∩ D₊(xⱼ)`, `e_i^{(a)} = c • e_j^{(a)}`, `e_i^{(b)} = d • e_j^{(b)}` and
`e_i^{(a+b)} = (c d) • e_j^{(a+b)}` for some functions `c` (namely `(xᵢ/xⱼ)ᵃ`) and `d`. -/
lemma exists_twistGenerator_transition (a b : ℤ) (i j : n) (W : (ℙ(n; S)).Opens)
    (hi : W ≤ standardOpen n S i) (hj : W ≤ standardOpen n S j) :
    ∃ c d : Γ(ℙ(n; S), W),
      c • (twist n S a).presheaf.map (homOfLE hj).op (twistGenerator n S a j) =
        (twist n S a).presheaf.map (homOfLE hi).op (twistGenerator n S a i) ∧
      d • (twist n S b).presheaf.map (homOfLE hj).op (twistGenerator n S b j) =
        (twist n S b).presheaf.map (homOfLE hi).op (twistGenerator n S b i) ∧
      (c * d) • (twist n S (a + b)).presheaf.map (homOfLE hj).op
          (twistGenerator n S (a + b) j) =
        (twist n S (a + b)).presheaf.map (homOfLE hi).op (twistGenerator n S (a + b) i) := by
  have hXi := X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i
  have hXj := X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) (σ := n) j
  let V := Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i) ⊓
    Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X j)
  have hVi : V ≤ _ := inf_le_left
  have hVj : V ≤ _ := inf_le_right
  obtain ⟨c₀, hc₀⟩ := ((Proj.isFreeGenerator_twistPowSection a hXj).map hVj).exists_smul_eq
    ((Proj.twist _ a).presheaf.map (homOfLE hVi).op (Proj.twistPowSection a hXi))
  obtain ⟨d₀, hd₀⟩ := ((Proj.isFreeGenerator_twistPowSection b hXj).map hVj).exists_smul_eq
    ((Proj.twist _ b).presheaf.map (homOfLE hVi).op (Proj.twistPowSection b hXi))
  have hcd₀ := Proj.twistPowSection_map_eq_mul_smul hXi hXj hVi hVj hc₀ hd₀
  have hW : W ≤ toProjInt n S ⁻¹ᵁ V := fun x hx ↦ ⟨hi hx, hj hx⟩
  refine ⟨_, _, pullbackSection_smul_map_eq (toProjInt n S) hVi hVj hc₀ hW,
    pullbackSection_smul_map_eq (toProjInt n S) hVi hVj hd₀ hW, ?_⟩
  have h := pullbackSection_smul_map_eq (toProjInt n S) hVi hVj hcd₀ hW
  rwa [map_mul, map_mul] at h

/-- **The canonical isomorphism `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)`** on `ℙ(n; S)`: the isomorphism whose
restriction to each standard open `D₊(xᵢ)` sends `e_i^{(a)} ⊗ e_i^{(b)}` to `e_i^{(a+b)}`
(`twistTensorIso_hom_app_tmulSection`). The local isomorphisms agree on the overlaps because the
transition functions `(xᵢ/xⱼ)ᵐ` are multiplicative in `m` (`exists_twistGenerator_transition`),
and they glue by the sheaf axiom (`Scheme.Modules.isoOfIsFreeGenerator`). -/
def twistTensorIso (a b : ℤ) : twist n S a ⊗ twist n S b ≅ twist n S (a + b) :=
  isoOfIsFreeGenerator (iSup_standardOpen n S)
    (fun i ↦ (isFreeGenerator_twistGenerator n S a i).tmulSection
      (isFreeGenerator_twistGenerator n S b i))
    (isFreeGenerator_twistGenerator n S (a + b))
    (tmulSection_transition_of_isFreeGenerator (isFreeGenerator_twistGenerator n S a)
      (isFreeGenerator_twistGenerator n S b) (exists_twistGenerator_transition n S a b))

/-- **Local basis property of `twistTensorIso`**: on the standard open `D₊(xᵢ)`, the canonical
isomorphism `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` sends `e_i^{(a)} ⊗ e_i^{(b)}` to `e_i^{(a+b)}`. -/
lemma twistTensorIso_hom_app_tmulSection (a b : ℤ) (i : n) :
    (twistTensorIso n S a b).hom.app (standardOpen n S i)
        (tmulSection (twistGenerator n S a i) (twistGenerator n S b i)) =
      twistGenerator n S (a + b) i :=
  isoOfIsFreeGenerator_hom_app _ _ _ _ i

/-- **Local description of `twistTensorIso`**: on an open `W ⊆ D₊(xᵢ)`, the canonical
isomorphism sends `r • (e_i^{(a)} ⊗ e_i^{(b)})|_W` to `r • e_i^{(a+b)}|_W`. -/
lemma twistTensorIso_hom_app_smul (a b : ℤ) (i : n) {W : (ℙ(n; S)).Opens}
    (hW : W ≤ standardOpen n S i) (r : Γ(ℙ(n; S), W)) :
    (twistTensorIso n S a b).hom.app W (r • (twist n S a ⊗ twist n S b).presheaf.map
        (homOfLE hW).op (tmulSection (twistGenerator n S a i) (twistGenerator n S b i))) =
      r • (twist n S (a + b)).presheaf.map (homOfLE hW).op (twistGenerator n S (a + b) i) :=
  isoOfIsFreeGenerator_hom_app_smul _ _ _ _ i hW r

end ProjectiveSpace

end AlgebraicGeometry
