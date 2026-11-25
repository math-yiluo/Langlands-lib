/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
public import WeilConjectures.DeligneLaumon.AffineLine.Constituent
public import WeilConjectures.DeligneLaumon.AffineLine.GeometricSMul
public import WeilConjectures.SixFunctors.ProEtale.Adic.InternalHom
public import WeilConjectures.WeilSheaf.LisseFiltration
public import WeilConjectures.WeilSheaf.ArtinSchreierDual
public import WeilConjectures.WeilSheaf.ArtinSchreierNeg
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.TateTwistCohomology

/-!
# Duals of the linear Artin–Schreier sheaves

The linear Artin–Schreier sheaves satisfy `(ℒ_{ψ(a x)})^∨ ≅ ℒ_{ψ(-a x)}` and
`ℒ_{ψ⁻¹(a x)} ≅ ℒ_{ψ(-a x)}` (blueprint `lemma-artin-schreier-character-sheaf`). On the
geometric line, the double dual of the geometric linear character `ℒ_{ψ⁻¹(b x)}` is the geometric
linear character `ℒ_{ψ(-b x)}`
(`AlgebraicGeometry.exists_iso_ihom_ihom_upperStar_geometricSMul_artinSchreier_inv`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **The inverse character**: `ℒ_{ψ⁻¹(a x)} ≅ ℒ_{ψ(-a x)}`.
(blueprint: `lemma-artin-schreier-character-sheaf`, the clause `ℒ_{ψ^{-1},f} ≅ ℒ_{ψ,-f}` for
`f = a x`) -/
theorem nonempty_iso_artinSchreier_inv (ψ : AddChar k₀ (PadicAlgCl l)) (a : k₀) :
    Nonempty (artinSchreier ψ⁻¹ a ≅ artinSchreier ψ (-a)) :=
  nonempty_artinSchreier_inv_iso ψ a

/-- **The inverse of a linear Artin–Schreier sheaf**: `(ℒ_{ψ(a x)})^∨ ≅ ℒ_{ψ⁻¹(a x)} ≅
ℒ_{ψ(-a x)}`. (blueprint: `lemma-artin-schreier-character-sheaf`, the clause `(ℒ_{ψ,f})^{-1} ≅
ℒ_{ψ,-f}` for `f = a x`) -/
theorem nonempty_iso_dual_artinSchreier_neg (ψ : AddChar k₀ (PadicAlgCl l)) (a : k₀) :
    Nonempty ((artinSchreier ψ a).dual (isLisse_artinSchreier ψ a) ≅ artinSchreier ψ (-a)) :=
  ⟨(nonempty_iso_dual_artinSchreier ψ a).some ≪≫ (nonempty_iso_artinSchreier_inv ψ a).some⟩

/-- The double dual of the inverse character is `ℒ_{ψ(-x)}`:
`(ℒ_{ψ⁻¹(x)})^∨∨ ≅ (ℒ_{ψ⁻¹(-x)})^∨ ≅ ℒ_{ψ⁻¹(x)} ≅ ℒ_{ψ(-x)}`. -/
theorem nonempty_iso_dual_dual_artinSchreier_inv (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty (((artinSchreier ψ⁻¹ 1).dual (isLisse_artinSchreier ψ⁻¹ 1)).dual
      (isLisse_artinSchreier ψ⁻¹ 1).dual ≅ artinSchreier ψ (-1)) := by
  obtain ⟨e₁⟩ := nonempty_iso_dual_artinSchreier_neg ψ⁻¹ 1
  obtain ⟨e₂⟩ := nonempty_iso_dual_artinSchreier_neg ψ⁻¹ (-1)
  obtain ⟨e₃⟩ := nonempty_iso_artinSchreier_inv ψ 1
  rw [neg_neg] at e₂
  exact ⟨WeilSheaf.dualIsoOfIso e₁ _ (isLisse_artinSchreier ψ⁻¹ (-1)) ≪≫ e₂ ≪≫ e₃⟩

/-- **The double dual of a geometric linear character.** For `b ∈ k̄`, the double dual of the
geometric sheaf `ℒ_{ψ⁻¹(b x)}` on `𝔸¹_{k̄}` is a geometric linear character `ℒ_{ψ(a x)}`, namely
for `a = -b`. For `b = 0` both are the constant sheaf; for `b ≠ 0` the multiplication by `b` is
an automorphism, along which pullback commutes with internal homs, and the double dual of
`ℒ_{ψ⁻¹(x)}` is `ℒ_{ψ(-x)}`. -/
theorem nonempty_iso_ihom_ihom_upperStar_geometricSMul_artinSchreier_inv
    (ψ : AddChar k₀ (PadicAlgCl l)) (b : AlgebraicClosure k₀) :
    Nonempty
      ((ProEtale.AdicSheaf.ihom ((ProEtale.AdicSheaf.ihom
          ((affineLine.geometricSMul k₀ b)^*ᵃ[l].obj (artinSchreier ψ⁻¹ 1).obj.carrier)).obj
            (ProEtale.AdicSheaf.unit l _))).obj (ProEtale.AdicSheaf.unit l _) ≅
        (affineLine.geometricSMul k₀ (-b))^*ᵃ[l].obj (artinSchreier ψ 1).obj.carrier) := by
  rcases eq_or_ne b 0 with rfl | hb
  · obtain ⟨e₁⟩ := WeilSheaf.nonempty_iso_upperStar_geometricSMul_zero_artinSchreier (l := l)
      ψ⁻¹ 1
    obtain ⟨e₂⟩ := WeilSheaf.nonempty_iso_upperStar_geometricSMul_zero_artinSchreier (l := l)
      ψ 1
    rw [neg_zero]
    refine ⟨?_⟩
    set U := ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber
    have e₃ : (ProEtale.AdicSheaf.ihom ((affineLine.geometricSMul k₀ 0)^*ᵃ[l].obj
        (artinSchreier ψ⁻¹ 1).obj.carrier)).obj U ≅ U :=
      (Mod.ihomMapIso e₁).symm.app U ≪≫ Mod.ihomRegularIso.app U
    exact (Mod.ihomMapIso e₃).symm.app U ≪≫ Mod.ihomRegularIso.app U ≪≫ e₂.symm
  · have := affineLine.isIso_geometricSMul k₀ hb
    set g := affineLine.geometricSMul k₀ b
    have : WeaklyEtale g := MorphismProperty.of_isIso _ g
    set U := ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber
    -- pullback along the automorphism `g` commutes with `𝓗om(-, ℚ̄_ℓ)`
    have eD (S : ProEtale.AdicSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
        (ProEtale.AdicSheaf.ihom ((g)^*ᵃ[l].obj S)).obj U ≅
          (g)^*ᵃ[l].obj ((ProEtale.AdicSheaf.ihom S).obj U) :=
      (ProEtale.AdicSheaf.ihom _).mapIso (ProEtale.adicUpperStarUnitIso l g).symm ≪≫
        ((ProEtale.adicUpperStarIhomIso l g S).app U).symm
    obtain ⟨eW⟩ := nonempty_iso_dual_dual_artinSchreier_inv (l := l) ψ
    have hs : g ≫ Scheme.Hom.geometricFiberMap (affineLine.smul k₀ (-1))
        (comp_over (affineLine.smul k₀ (-1)) _) =
          affineLine.geometricSMul k₀ (-b) ≫ Scheme.Hom.geometricFiberMap (affineLine.smul k₀ 1)
            (comp_over (affineLine.smul k₀ 1) _) := by
      rw [affineLine.geometricSMul_comp_geometricFiberMap_smul,
        affineLine.geometricSMul_comp_geometricFiberMap_smul]
      simp
    refine ⟨?_⟩
    exact (Mod.ihomMapIso (eD _)).symm.app U ≪≫ eD _ ≪≫
      (g)^*ᵃ[l].mapIso ((WeilSheaf.carrierFunctor k₀ l _).mapIso eW) ≪≫
      (ProEtale.adicUpperStarCompIso l hs).app _

/-- The double dual of the geometric sheaf `ℒ_{ψ⁻¹(b x)}` on `𝔸¹_{k̄}` is a geometric linear
character `ℒ_{ψ(a x)}`
(`AlgebraicGeometry.nonempty_iso_ihom_ihom_upperStar_geometricSMul_artinSchreier_inv`). -/
theorem exists_iso_ihom_ihom_upperStar_geometricSMul_artinSchreier_inv
    (ψ : AddChar k₀ (PadicAlgCl l)) (b : AlgebraicClosure k₀) :
    ∃ a : AlgebraicClosure k₀, Nonempty
      ((ProEtale.AdicSheaf.ihom ((ProEtale.AdicSheaf.ihom
          ((affineLine.geometricSMul k₀ b)^*ᵃ[l].obj (artinSchreier ψ⁻¹ 1).obj.carrier)).obj
            (ProEtale.AdicSheaf.unit l _))).obj (ProEtale.AdicSheaf.unit l _) ≅
        (affineLine.geometricSMul k₀ a)^*ᵃ[l].obj (artinSchreier ψ 1).obj.carrier) :=
  ⟨-b, nonempty_iso_ihom_ihom_upperStar_geometricSMul_artinSchreier_inv ψ b⟩

end AlgebraicGeometry
