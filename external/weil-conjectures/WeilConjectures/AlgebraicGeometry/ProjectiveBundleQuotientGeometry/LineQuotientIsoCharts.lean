/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.LineQuotientChartInverseData

/-! # LineQuotientIsoCharts

## References

* Stacks Project, Constructions, Tags 01OA and 01O4
* Stacks Project, Constructions, Tag 01OA, isomorphism classes of quotients
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.ProjectiveBundleQuotientGeometry
open Scheme.Modules

attribute [local irreducible] tensorPullback tensorPullbackObj

private theorem powIso_add {T : Scheme.{u}} {L L' : T.Modules}
    (v : L ≅ L') (a b : ℕ) :
    (L.tensorPowAddIso a b).inv ≫ (boundaryTensorPowIso v (a + b)).hom =
      ((boundaryTensorPowIso v a).hom ⊗ₘ (boundaryTensorPowIso v b).hom) ≫
        (L'.tensorPowAddIso a b).inv := by
  induction a with
  | zero =>
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      boundaryTensorPowIso, Iso.refl_hom, Category.assoc]
    erw [← eqToHom_iso_hom_naturality (fun k ↦ boundaryTensorPowIso v k)
      (Nat.zero_add b).symm]
    simp only [id_tensorHom]
    erw [leftUnitor_naturality_assoc]
  | succ a ih =>
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      Category.assoc]
    erw [← eqToHom_iso_hom_naturality (fun k ↦ boundaryTensorPowIso v k)
      (Nat.succ_add a b).symm]
    simp only [boundaryTensorPowIso, tensorIso_hom, tensorIso_inv, Iso.refl_inv]
    erw [associator_naturality_assoc]
    simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id, ih]

private theorem powIso_frame {T : Scheme.{u}} {L L' : T.Modules}
    (v : L ≅ L') (W : T.Opens) (l : Γ(L, W)) (d : ℕ) :
    (boundaryTensorPowIso v d).hom.app W (quotientFramePower l d) =
      quotientFramePower (v.hom.app W l) d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change (v.hom ⊗ₘ (boundaryTensorPowIso v d).hom).app W
      (tmulSection l (quotientFramePower l d)) = _
    rw [tensorHom_app_tmulSection, ih]
    rfl

private theorem powIso_one {T : Scheme.{u}} {L L' : T.Modules} (v : L ≅ L') :
    (boundaryTensorPowIso v 1).hom ≫ (ρ_ L').hom = (ρ_ L).hom ≫ v.hom := by
  change (v.hom ⊗ₘ 𝟙 _) ≫ (ρ_ L').hom = _
  rw [tensorHom_id, rightUnitor_naturality]

private theorem component_iso {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L L' : T.Modules)
    (q : (tensorPullback h).obj E ⟶ L)
    (q' : (tensorPullback h).obj E ⟶ L') (v : L ≅ L') (hv : q ≫ v.hom = q')
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (ψ' : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L')
    (hψ : ψ.ExtendsLineQuotient h E L q)
    (hψ' : ψ'.ExtendsLineQuotient h E L' q')
    (U : S.affineOpens) (d : ℕ)
    (c : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d) :
    (boundaryTensorPowIso v d).hom.app (h ⁻¹ᵁ U.1) (ψ.component U d c) =
      ψ'.component U d c := by
  obtain ⟨c, hc⟩ := c
  change c ∈ (SymmetricAlgebra.ι Γ(S, U.1) Γ(E, U.1)).range ^ d at hc
  induction hc using Submodule.pow_induction_on_right' with
  | algebraMap r =>
    have he : (⟨algebraMap Γ(S, U.1) _ r, Submodule.algebraMap_mem r⟩ :
        (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U 0) =
        r • ⟨1, SetLike.one_mem_graded _⟩ := by
      ext
      change algebraMap Γ(S, U.1) (SymmetricAlgebra Γ(S, U.1) Γ(E, U.1)) r =
        r • (1 : SymmetricAlgebra Γ(S, U.1) Γ(E, U.1))
      simp only [Algebra.smul_def, mul_one]
    simp only [he, ψ.smul, ψ'.smul, ψ.one, ψ'.one,
      boundaryTensorPowIso, Iso.refl_hom, Hom.id_app]
    rfl
  | add x y i hx hy ihx ihy =>
    change (boundaryTensorPowIso v i).hom.app _
      (ψ.component U i (⟨x, hx⟩ + ⟨y, hy⟩)) =
        ψ'.component U i (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [map_add, map_add, map_add, ihx, ihy]
  | mul_mem i x hx ih m hm =>
    obtain ⟨m, rfl⟩ := hm
    have hgen : (boundaryTensorPowIso v 1).hom.app (h ⁻¹ᵁ U.1)
        (ψ.component U 1 (quotientSymmetricGenerator E U m)) =
          ψ'.component U 1 (quotientSymmetricGenerator E U m) := by
      apply (ConcreteCategory.bijective_of_isIso ((ρ_ L').hom.app (h ⁻¹ᵁ U.1))).1
      have he := congrArg (fun f ↦ f.app (h ⁻¹ᵁ U.1)
        (ψ.component U 1 (quotientSymmetricGenerator E U m))) (powIso_one v)
      simp only [Hom.comp_app, ConcreteCategory.comp_apply] at he
      erw [he, hψ, hψ']
      exact (congrArg (fun f ↦ f.app (h ⁻¹ᵁ U.1)
        (tensorPullbackSection h E U.1 m)) hv)
    have hm := ψ.mul U i 1 ⟨x, hx⟩ (quotientSymmetricGenerator E U m)
    have hm' := ψ'.mul U i 1 ⟨x, hx⟩ (quotientSymmetricGenerator E U m)
    erw [hm, hm']
    have he := congrArg (fun f ↦ f.app (h ⁻¹ᵁ U.1)
      (tmulSection (ψ.component U i ⟨x, hx⟩)
        (ψ.component U 1 (quotientSymmetricGenerator E U m)))) (powIso_add v i 1)
    simp only [Hom.comp_app, ConcreteCategory.comp_apply] at he
    exact he.trans (congrArg ((L'.tensorPowAddIso i 1).inv.app (h ⁻¹ᵁ U.1))
      ((tensorHom_app_tmulSection _ _ _ _).trans (congrArg₂ tmulSection ih hgen)))

private theorem framePow_free {T : Scheme.{u}} {L : T.Modules} {W : T.Opens}
    {l : Γ(L, W)} (hl : IsFreeGenerator l) (d : ℕ) :
    IsFreeGenerator (quotientFramePower l d) := by
  induction d with
  | zero => exact isFreeGenerator_one W
  | succ d ih => exact hl.tmulSection ih

private theorem coefficient_smul {S T : Scheme.{u}} {h : T ⟶ S}
    {A : S.GradedAlgebraData} {L : T.Modules} (ψ : RelativeGradedLineMap h A L)
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)) (hl : IsFreeGenerator l) (d : ℕ) (c : A.grading U d) :
    ψ.quotientCoefficient U W hWU l d c • quotientFramePower l d =
      (L.tensorPow d).val.map (homOfLE hWU).op (ψ.component U d c) :=
  Function.invFun_eq ((framePow_free hl d).bijective.2 _)

private theorem coefficient_iso {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L L' : T.Modules)
    (q : (tensorPullback h).obj E ⟶ L)
    (q' : (tensorPullback h).obj E ⟶ L') (v : L ≅ L') (hv : q ≫ v.hom = q')
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (ψ' : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L')
    (hψ : ψ.ExtendsLineQuotient h E L q)
    (hψ' : ψ'.ExtendsLineQuotient h E L' q')
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)) (hl : IsFreeGenerator l) (d : ℕ)
    (c : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d) :
    ψ'.quotientCoefficient U W hWU (v.hom.app W.1 l) d c =
      ψ.quotientCoefficient U W hWU l d c := by
  apply (framePow_free (hl.app_hom v) d).smul_left_injective
  dsimp only
  rw [coefficient_smul ψ' U W hWU _ (hl.app_hom v)]
  have he := congrArg (fun z ↦ (boundaryTensorPowIso v d).hom.app W.1 z)
    (coefficient_smul ψ U W hWU l hl d c)
  erw [Hom.app_smul, powIso_frame, Hom.app_presheaf_map,
    component_iso h E L L' q q' v hv ψ ψ' hψ hψ'] at he
  exact he.symm

private theorem generatorCoefficient_iso {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) (L L' : T.Modules)
    (q : (tensorPullback h).obj E ⟶ L)
    (q' : (tensorPullback h).obj E ⟶ L') (v : L ≅ L') (hv : q ≫ v.hom = q')
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)) (hl : IsFreeGenerator l) (m : Γ(E, U.1)) :
    quotientGeneratorCoefficient h E L' q' U W hWU (v.hom.app W.1 l) m =
      quotientGeneratorCoefficient h E L q U W hWU l m := by
  apply (hl.app_hom v).smul_left_injective
  dsimp only
  have hq' : quotientGeneratorCoefficient h E L' q' U W hWU (v.hom.app W.1 l) m •
      v.hom.app W.1 l = q'.app W.1 (((tensorPullback h).obj E).val.map
        (homOfLE hWU).op (tensorPullbackSection h E U.1 m)) :=
    Function.invFun_eq ((hl.app_hom v).bijective.2 _)
  have hq0 : quotientGeneratorCoefficient h E L q U W hWU l m • l =
      q.app W.1 (((tensorPullback h).obj E).val.map (homOfLE hWU).op
        (tensorPullbackSection h E U.1 m)) :=
    Function.invFun_eq (hl.bijective.2 _)
  rw [hq']
  have he := congrArg (fun z ↦ v.hom.app W.1 z) hq0
  rw [Hom.app_smul] at he
  rw [← hv]
  exact he.symm

-- Coefficient functions are explicit parameters so denominator transport also
-- rewrites the dependent types of localization-valued chart maps.
private def fractionChartData {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (U : S.affineOpens) (W : T.affineOpens)
    (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (b : Γ(E, U.1) → Γ(T, W.1))
    (coeff : ∀ d : ℕ, (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d →
      Γ(T, W.1)) : Prop :=
  ∀ m : Γ(E, U.1), ∃ ρ : HomogeneousLocalization.Away
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
      (quotientSymmetricGenerator E U m).val →+* Localization.Away (b m),
  (∀ (d : ℕ) (a : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d),
      ρ (degreeOneQuotientFraction (SymmetricAlgebraSheaf.gradedAlgebraData E) U
        (quotientSymmetricGenerator E U m) d a) =
          Localization.mk (coeff d a)
            (⟨b m ^ d,
              ⟨d, rfl⟩⟩ : Submonoid.powers
                (b m))) ∧
    (∀ r : Γ(S, U.1),
      ρ (quotientFractionScalar (SymmetricAlgebraSheaf.gradedAlgebraData E) U
        (quotientSymmetricGenerator E U m).val r) =
          algebraMap Γ(T, W.1)
            (Localization.Away (b m))
            (h.appLE U.1 W.1 hWU r)) ∧
    quotientFractionSource W (b m) ≫ F =
      Spec.map (CommRingCat.ofHom ρ) ≫
        Proj.awayι ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
          (quotientSymmetricGenerator E U m).val (quotientSymmetricGenerator E U m).property
          (by decide : 0 < (1 : ℕ)) ≫
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ∧
    ∀ n : Γ(E, U.1),
      IsUnit (IsLocalization.Away.awayToAwayRight
        (S := Localization.Away (b m))
        (P := Localization.Away
          (b m *
            b n))
        (b m)
        (b n)
        (ρ (degreeOneQuotientFraction (SymmetricAlgebraSheaf.gradedAlgebraData E) U
          (quotientSymmetricGenerator E U m) 1 (quotientSymmetricGenerator E U n))))

/-- Isomorphic quotient lines have identical coefficient maps in corresponding frames,
and hence the same fraction charts. -/
theorem lineQuotient_iso_charts {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules) [L.IsInvertible]
    (q : (tensorPullback h).obj E ⟶ L) [Epi q]
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (hψ : ψ.ExtendsLineQuotient h E L q)
    (L' : T.Modules) (v : L ≅ L') (q' : (tensorPullback h).obj E ⟶ L')
    (hq : q ≫ v.hom = q')
    (ψ' : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L')
    (hψ' : ψ'.ExtendsLineQuotient h E L' q') :
    (∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
      (l : Γ(L, W.1)), IsFreeGenerator l →
      ∀ (d : ℕ) (c : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d),
        ψ'.quotientCoefficient U W hWU (v.hom.app W.1 l) d c =
          ψ.quotientCoefficient U W hWU l d c) ∧
    ∀ F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj,
      ψ.HasQuotientFractionCharts h E L q F →
        ψ'.HasQuotientFractionCharts h E L' q' F := by
  have hcoeff := coefficient_iso h E L L' q q' v hq ψ ψ' hψ hψ'
  have hgen := generatorCoefficient_iso h E L L' q q' v hq
  constructor
  · intro U W hWU l hl d c
    exact hcoeff U W hWU l hl d c
  · intro F hc
    refine ⟨hc.1, ?_⟩
    intro U W hWU l' hl'
    obtain ⟨l, rfl⟩ := (ConcreteCategory.bijective_of_isIso (v.hom.app W.1)).2 l'
    have hl : IsFreeGenerator l := by
      have he := hl'.app_hom v.symm
      have hi : v.inv.app W.1 (v.hom.app W.1 l) = l :=
        congrArg (fun f ↦ f.app W.1 l) v.hom_inv_id
      change IsFreeGenerator (v.inv.app W.1 (v.hom.app W.1 l)) at he
      rwa [hi] at he
    have hc0 := hcoeff
    have hg0 := hgen
    have hcoeff (U0 : S.affineOpens) (W0 : T.affineOpens)
        (hW0 : W0.1 ≤ h ⁻¹ᵁ U0.1) (l0 : Γ(L, W0.1))
        (hl0 : IsFreeGenerator l0) := hc0 U0 W0 hW0 l0 hl0
    have hgen (m : Γ(E, U.1)) := hg0 U W hWU l hl m
    obtain ⟨hnorm, hdegree, hcover, hchart, hframe, hres, hbase⟩ := hc.2 U W hWU l hl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro d c
      rw [hcoeff U W hWU l hl]
      have he := congrArg (fun z ↦ (boundaryTensorPowIso v d).hom.app W.1 z)
        (hnorm d c)
      erw [Hom.app_smul, powIso_frame, Hom.app_presheaf_map,
        component_iso h E L L' q q' v hq ψ ψ' hψ hψ'] at he
      exact he
    · intro m
      rw [hcoeff U W hWU l hl, hgen]
      exact hdegree m
    · simpa only [hgen] using hcover
    · change fractionChartData h E U W hWU F
        (quotientGeneratorCoefficient h E L' q' U W hWU (v.hom.app W.1 l))
        (ψ'.quotientCoefficient U W hWU (v.hom.app W.1 l))
      change fractionChartData h E U W hWU F
        (quotientGeneratorCoefficient h E L q U W hWU l)
        (ψ.quotientCoefficient U W hWU l) at hchart
      have hb : quotientGeneratorCoefficient h E L' q' U W hWU (v.hom.app W.1 l) =
          quotientGeneratorCoefficient h E L q U W hWU l := funext hgen
      have ha : ψ'.quotientCoefficient U W hWU (v.hom.app W.1 l) =
          ψ.quotientCoefficient U W hWU l :=
        funext fun d ↦ funext (hcoeff U W hWU l hl d)
      rw [hb, ha]
      exact hchart
    · intro b d c
      rw [← Hom.app_smul, hcoeff U W hWU _ (hl.units_smul b),
        hcoeff U W hWU l hl]
      exact hframe b d c
    · intro W' j hW'U d c
      erw [← Hom.app_presheaf_map, hcoeff U W' hW'U _ (hl.map j),
        hcoeff U W hWU l hl]
      exact hres W' j hW'U d c
    · intro U' j hWU' d c
      rw [hcoeff U' W hWU' l hl, hcoeff U W hWU l hl]
      exact hbase U' j hWU' d c

end AlgebraicGeometry.ProjectiveBundleQuotientGeometry
