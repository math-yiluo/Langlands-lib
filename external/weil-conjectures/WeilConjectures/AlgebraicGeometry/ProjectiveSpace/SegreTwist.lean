/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Segre
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

/-!
# The twisting sheaf and the Segre morphism

The pullback of `𝒪(1)` along the relative Segre morphism `ℙ(n; S) ×_S ℙ(m; S) ⟶ ℙ(n × m; S)`
is the external tensor product `𝒪(1) ⊠ 𝒪(1)`. This is what makes a tensor product of very ample
modules very ample (`AlgebraicGeometry.IsVeryAmple.tensorObj`).

Both sides are glued from free modules of rank one on the charts `D₊(Xₖ) ×_S D₊(Yₗ)`: the
pullback of the coordinate `W_{k,l}` and the tensor product of the pullbacks of `Xₖ` and `Yₗ` are
free generators there, with the same transition functions, because the Segre morphism pulls
`W_{k,l} / W_{k',l'}` back to `(Xₖ / Xₖ') · (Yₗ / Yₗ')`.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.segre_comp_toProjInt_appLE`: the Segre morphism on the
  transition functions.
- `AlgebraicGeometry.ProjectiveSpace.nonempty_twistRestrict_segre_iso`:
  `segre^* 𝒪(1) ≅ pr₁^* 𝒪(1) ⊗ pr₂^* 𝒪(1)`.

## References

* Stacks Project, Tag 01WD
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProjectiveSpace

variable (n m : Type u) (S : Scheme.{u})

open Scheme.Modules
open MvPolynomial (homogeneousSubmodule awayXRatio)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Morphisms which are equal have equal `appLE`. -/
private lemma appLE_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U V e) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h
  rfl

/-- The preimage under the relative Segre morphism of the locus where `W_{k,l}` does not vanish
is the locus where `Xₖ` and `Yₗ` do not vanish. -/
lemma segre_preimage_preimage_basicOpen (k : n) (l : m) :
    segre n m S ⁻¹ᵁ toProjInt (n × m) S ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule (n × m) (ULift.{u} ℤ)) (MvPolynomial.X (k, l)) =
      pullback.fst (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S) ⁻¹ᵁ toProjInt n S ⁻¹ᵁ
          Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X k) ⊓
        pullback.snd (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S) ⁻¹ᵁ toProjInt m S ⁻¹ᵁ
          Proj.basicOpen (homogeneousSubmodule m (ULift.{u} ℤ)) (MvPolynomial.X l) := by
  rw [← Scheme.Hom.comp_preimage, segre_toProjInt, Scheme.Hom.comp_preimage,
    Proj.segre_preimage_basicOpen, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
    ← Scheme.Hom.comp_preimage, prodToProjInt_fst, prodToProjInt_snd, Scheme.Hom.comp_preimage,
    Scheme.Hom.comp_preimage]

/-- **The relative Segre morphism on the transition functions**: on the locus where `Xₖ'` and
`Yₗ'` do not vanish, the function `W_{k,l} / W_{k',l'}` pulls back to `(Xₖ / Xₖ') · (Yₗ / Yₗ')`. -/
lemma segre_comp_toProjInt_appLE (k k' : n) (l l' : m)
    {W : (pullback (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S)).Opens}
    (hW : W ≤ pullback.fst (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S) ⁻¹ᵁ toProjInt n S ⁻¹ᵁ
          Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X k') ⊓
        pullback.snd (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S) ⁻¹ᵁ toProjInt m S ⁻¹ᵁ
          Proj.basicOpen (homogeneousSubmodule m (ULift.{u} ℤ)) (MvPolynomial.X l')) :
    (segre n m S ≫ toProjInt (n × m) S).appLE
        (Proj.basicOpen (homogeneousSubmodule (n × m) (ULift.{u} ℤ)) (MvPolynomial.X (k', l'))) W
        (hW.trans (segre_preimage_preimage_basicOpen n m S k' l').ge)
        (Proj.awayToSection _ _ (awayXRatio (ULift.{u} ℤ) (k', l') (k, l))) =
      (pullback.fst (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S) ≫ toProjInt n S).appLE
          (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X k')) W
          (hW.trans inf_le_left) (Proj.awayToSection _ _ (awayXRatio (ULift.{u} ℤ) k' k)) *
        (pullback.snd (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S) ≫ toProjInt m S).appLE
          (Proj.basicOpen (homogeneousSubmodule m (ULift.{u} ℤ)) (MvPolynomial.X l')) W
          (hW.trans inf_le_right) (Proj.awayToSection _ _ (awayXRatio (ULift.{u} ℤ) l' l)) := by
  have hle : W ≤ prodToProjInt n m S ⁻¹ᵁ
      (pullback.fst (terminal.from (Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ)))
          (terminal.from (Proj.projectiveSpaceOverAffine m (ULift.{u} ℤ))) ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X k') ⊓
      pullback.snd (terminal.from (Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ)))
          (terminal.from (Proj.projectiveSpaceOverAffine m (ULift.{u} ℤ))) ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule m (ULift.{u} ℤ)) (MvPolynomial.X l')) := by
    rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
      prodToProjInt_fst, prodToProjInt_snd, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
    exact hW
  rw [appLE_eq_of_eq (segre_toProjInt n m S), appLE_eq_of_eq (prodToProjInt_fst n m S).symm,
    appLE_eq_of_eq (prodToProjInt_snd n m S).symm,
    ← Scheme.Hom.appLE_comp_appLE _ _ _ _ _ (Proj.segre_preimage_basicOpen k' l').ge hle,
    ← Scheme.Hom.appLE_comp_appLE _ _ _ _ _ inf_le_left hle,
    ← Scheme.Hom.appLE_comp_appLE _ _ _ _ _ inf_le_right hle, ConcreteCategory.comp_apply,
    Proj.segre_appLE_awayToSection_awayXRatio, map_mul]
  rfl

/-- **The pullback of `𝒪(1)` along the relative Segre morphism is `𝒪(1) ⊠ 𝒪(1)`**, the tensor
product of the pullbacks of `𝒪(1)` along the two projections of `ℙ(n; S) ×_S ℙ(m; S)`
(Stacks 01WD). -/
theorem nonempty_twistRestrict_segre_iso :
    Nonempty (twistRestrict (segre n m S) 1 ≅
      twistRestrict (pullback.fst (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S)) 1 ⊗
        twistRestrict (pullback.snd (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S)) 1) := by
  set p₁ := pullback.fst (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S)
  set p₂ := pullback.snd (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S)
  set s := segre n m S
  let D (σ : Type u) (i : σ) : (ℙ(σ; S)).Opens :=
    toProjInt σ S ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule σ (ULift.{u} ℤ)) (MvPolynomial.X i)
  let U (kl : n × m) := s ⁻¹ᵁ D (n × m) kl
  have hU (kl : n × m) : U kl = p₁ ⁻¹ᵁ D n kl.1 ⊓ p₂ ⁻¹ᵁ D m kl.2 :=
    segre_preimage_preimage_basicOpen n m S kl.1 kl.2
  have hcov : ⨆ kl, U kl = ⊤ := by
    simp only [U, D, ← Scheme.Hom.preimage_iSup]
    rw [Proj.iSup_basicOpen_eq_top' (homogeneousSubmodule (n × m) (ULift.{u} ℤ))
      (MvPolynomial.X : n × m → MvPolynomial (n × m) (ULift.{u} ℤ))
      (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X _ i⟩) (MvPolynomial.adjoin_range_X_eq_top _ _)]
    rfl
  let L := (Scheme.Modules.pullback s).obj (twist (n × m) S 1)
  let A := (Scheme.Modules.pullback p₁).obj (twist n S 1)
  let B := (Scheme.Modules.pullback p₂).obj (twist m S 1)
  let e (kl : n × m) : Γ(L, U kl) := L.presheaf.map (homOfLE (s.preimage_mono
    (le_top : D (n × m) kl ≤ ⊤))).op (pullbackSection s (twistOneSection (n × m) S kl))
  let x (kl : n × m) : Γ(A, U kl) := A.presheaf.map (homOfLE (le_top : U kl ≤ p₁ ⁻¹ᵁ ⊤)).op
    (pullbackSection p₁ (twistOneSection n S kl.1))
  let y (kl : n × m) : Γ(B, U kl) := B.presheaf.map (homOfLE (le_top : U kl ≤ p₂ ⁻¹ᵁ ⊤)).op
    (pullbackSection p₂ (twistOneSection m S kl.2))
  have he (kl : n × m) : IsFreeGenerator (e kl) :=
    isFreeGenerator_pullbackSection_twistOneSection s kl
  have hx (kl : n × m) : IsFreeGenerator (x kl) := by
    have h := (isFreeGenerator_pullbackSection_twistOneSection p₁ kl.1).map
      ((hU kl).le.trans inf_le_left)
    rwa [presheaf_map_homOfLE_map_homOfLE] at h
  have hy (kl : n × m) : IsFreeGenerator (y kl) := by
    have h := (isFreeGenerator_pullbackSection_twistOneSection p₂ kl.2).map
      ((hU kl).le.trans inf_le_right)
    rwa [presheaf_map_homOfLE_map_homOfLE] at h
  refine nonempty_iso_of_isFreeGenerator hcov he ?_ fun kl ↦ (hx kl).tmulSection (hy kl)
  rintro ⟨k, l⟩ ⟨k', l'⟩ W hi hj a b hab
  have hW : W ≤ p₁ ⁻¹ᵁ D n k' ⊓ p₂ ⁻¹ᵁ D m l' := hj.trans (hU (k', l')).le
  have hE := presheaf_map_homOfLE_eq_smul _ hj
    (pullbackSection_twistOneSection_map_eq_smul s (k, l) (k', l'))
  have hX := presheaf_map_homOfLE_eq_smul _ (hW.trans inf_le_left)
    (pullbackSection_twistOneSection_map_eq_smul p₁ k k')
  have hY := presheaf_map_homOfLE_eq_smul _ (hW.trans inf_le_right)
    (pullbackSection_twistOneSection_map_eq_smul p₂ l l')
  have hc := segre_comp_toProjInt_appLE n m S k k' l l' hW
  have ee := (presheaf_map_homOfLE_map_homOfLE (M := L)
    (s.preimage_mono (le_top : D (n × m) (k, l) ≤ ⊤)) hi _).trans (hE.trans (congrArg _
    (presheaf_map_homOfLE_map_homOfLE (M := L)
      (s.preimage_mono (le_top : D (n × m) (k', l') ≤ ⊤)) hj _).symm))
  have xx := (presheaf_map_homOfLE_map_homOfLE (M := A) (le_top : U (k, l) ≤ p₁ ⁻¹ᵁ ⊤) hi
    _).trans (hX.trans (congrArg _
    (presheaf_map_homOfLE_map_homOfLE (M := A) (le_top : U (k', l') ≤ p₁ ⁻¹ᵁ ⊤) hj _).symm))
  have yy := (presheaf_map_homOfLE_map_homOfLE (M := B) (le_top : U (k, l) ≤ p₂ ⁻¹ᵁ ⊤) hi
    _).trans (hY.trans (congrArg _
    (presheaf_map_homOfLE_map_homOfLE (M := B) (le_top : U (k', l') ≤ p₂ ⁻¹ᵁ ⊤) hj _).symm))
  change a • L.presheaf.map (homOfLE hi).op (e (k, l)) =
    b • L.presheaf.map (homOfLE hj).op (e (k', l')) at hab
  rw [ee, smul_smul] at hab
  have hab' := ((he (k', l')).map hj).smul_left_injective hab
  change a • (A ⊗ B).presheaf.map (homOfLE hi).op (tmulSection (x (k, l)) (y (k, l))) =
    b • (A ⊗ B).presheaf.map (homOfLE hj).op (tmulSection (x (k', l')) (y (k', l')))
  rw [tmulSection_map, tmulSection_map, xx, yy, smul_tmulSection, tmulSection_smul, smul_smul,
    smul_smul, ← hab', mul_assoc]
  congr 2
  exact hc.symm

end AlgebraicGeometry.ProjectiveSpace
