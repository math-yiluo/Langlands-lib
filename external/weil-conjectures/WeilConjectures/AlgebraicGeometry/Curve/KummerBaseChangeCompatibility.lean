/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
import WeilConjectures.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange
import WeilConjectures.AlgebraicGeometry.BaseChangeCurve
import WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder

/-!
# Kummer compatibility under algebraically closed base change

Source: Weil conjectures blueprint, sec-curve-estimates/sbc-thm-algebraically-closed-invariance,
proper-case Kummer naturality sentence and affine-case Picard-torsion paragraph
(blueprint: lem-sc-kummer-base-change-compatibility).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

set_option autoImplicit false

namespace Scheme

open Opposite

private theorem terminal_naturality.{v, w}
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}] [HasExt (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w}) {T S : C}
    (hT : Limits.IsTerminal T) (hS : Limits.IsTerminal S) (x : Sheaf.H F 0) :
    F.obj.map (hT.from S).op (Sheaf.H.equiv₀ F hT x) = Sheaf.H.equiv₀ F hS x := by
  let φ := (sheafificationAdjunction J AddCommGrpCat.{w}).homEquiv _ F
    (Abelian.Ext.addEquiv₀ x)
  change F.obj.map (hT.from S).op (φ.app (op T) (ULift.up (1 : ℤ))) =
    φ.app (op S) (ULift.up (1 : ℤ))
  exact (ConcreteCategory.congr_hom (φ.naturality (hT.from S).op)
    (ULift.up (1 : ℤ))).symm


private theorem gm_units_cohomology_pullback (X Y : Scheme.{u}) (u : Y ⟶ X) (a : Γ(X, ⊤)ˣ) :
    Sheaf.H.equiv₀ Y.gmSheaf (MorphismProperty.Over.mkIdTerminal @Etale Y)
      (Sheaf.H.map (upperStarGmSheafToGmSheaf u) 0
        (Etale.cohomologyMap u X.gmSheaf 0
          ((Sheaf.H.equiv₀ X.gmSheaf
            (MorphismProperty.Over.mkIdTerminal @Etale X)).symm
              (ULift.up (Additive.ofMul a))))) =
      ULift.up (Additive.ofMul (Units.map u.appTop.hom.toMonoidHom a)) := by
  let hX := MorphismProperty.Over.mkIdTerminal @Etale X
  let hY := MorphismProperty.Over.mkIdTerminal @Etale Y
  let b := X.gmSheaf.obj.map (hX.from (⊤_ X.Etale)).op (ULift.up (Additive.ofMul a))
  let e := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
    Limits.terminalIsTerminal
  let g := e.inv.app X.gmSheaf b
  have hb : (Sheaf.H.equiv₀ X.gmSheaf Limits.terminalIsTerminal).symm b =
      (Sheaf.H.equiv₀ X.gmSheaf hX).symm (ULift.up (Additive.ofMul a)) := by
    apply (Sheaf.H.equiv₀ X.gmSheaf Limits.terminalIsTerminal).injective
    rw [AddEquiv.apply_symm_apply, ← terminal_naturality X.gmSheaf hX]
    rw [AddEquiv.apply_symm_apply]
  have h := Etale.cohomologyMap_zero_eq_globalSectionsUpperStarMap u X.gmSheaf g
  simp only [g, e, ← ConcreteCategory.comp_apply, Iso.inv_hom_id_app,
    ConcreteCategory.id_apply] at h
  rw [← hb, h, Sheaf.H.equiv₀_symm_naturality]
  rw [← terminal_naturality Y.gmSheaf Limits.terminalIsTerminal hY]
  rw [AddEquiv.apply_symm_apply]
  simp only [Etale.globalSectionsUpperStarMap, ConcreteCategory.comp_apply]
  simp only [← ConcreteCategory.comp_apply, Iso.inv_hom_id_app,
    ConcreteCategory.id_apply]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  let c := upperStarGmSheafToGmSheaf u
  let η := (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u).unit
  let U := (Etale.upperStar AddCommGrpCat.{u + 1} u).obj X.gmSheaf
  change Y.gmSheaf.obj.map (Limits.terminalIsTerminal.from (Etale.mk (𝟙 Y))).op
    (c.hom.app (op (⊤_ Y.Etale))
      (U.obj.map (Limits.PreservesTerminal.iso u.Etale).inv.op
        ((η.app X.gmSheaf).hom.app (op (⊤_ X.Etale)) b))) = _
  rw [NatTrans.naturality_apply c.hom]
  have hu := (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u).homEquiv
    X.gmSheaf Y.gmSheaf |>.apply_symm_apply (gmSheafToLowerStarGmSheaf u)
  change η.app X.gmSheaf ≫ (Etale.lowerStar AddCommGrpCat.{u + 1} u).map c =
    gmSheafToLowerStarGmSheaf u at hu
  have huv := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.hom.app (op (⊤_ X.Etale))) hu) b
  change c.hom.app _ ((η.app X.gmSheaf).hom.app _ b) =
    (gmSheafToLowerStarGmSheaf u).hom.app _ b at huv
  erw [huv]
  dsimp only [b]
  rw [NatTrans.naturality_apply (gmSheafToLowerStarGmSheaf u).hom]
  let p := MorphismProperty.Over.pullback @Etale ⊤ u
  let m : Etale.mk (𝟙 Y) ⟶ p.obj (Etale.mk (𝟙 X)) :=
    Limits.terminalIsTerminal.from (Etale.mk (𝟙 Y)) ≫
      (Limits.PreservesTerminal.iso u.Etale).inv ≫ p.map (hX.from (⊤_ X.Etale))
  change Y.gmSheaf.obj.map (Limits.terminalIsTerminal.from (Etale.mk (𝟙 Y))).op
    (Y.gmSheaf.obj.map (Limits.PreservesTerminal.iso u.Etale).inv.op
      (Y.gmSheaf.obj.map (p.map (hX.from (⊤_ X.Etale))).op
        ((gmSheafToLowerStarGmSheaf u).hom.app (op (Etale.mk (𝟙 X)))
          (ULift.up (Additive.ofMul a))))) = _
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  change Y.gmSheaf.obj.map m.op
    ((gmSheafToLowerStarGmSheaf u).hom.app (op (Etale.mk (𝟙 X)))
      (ULift.up (Additive.ofMul a))) = _
  have hm : m.left ≫ Limits.pullback.fst (𝟙 X) u = u := by
    have hf : Limits.pullback.fst (𝟙 X) u = Limits.pullback.snd (𝟙 X) u ≫ u := by
      simpa using (Limits.pullback.condition (f := 𝟙 X) (g := u))
    rw [hf, ← Category.assoc]
    have hw : m.left ≫ Limits.pullback.snd (𝟙 X) u = 𝟙 Y := m.w
    erw [hw, Category.id_comp]
  apply ULift.ext
  apply Additive.toMul.injective
  apply Units.ext
  change m.left.appTop ((Limits.pullback.fst (𝟙 X) u).appTop (a : Γ(X, ⊤))) =
    u.appTop (a : Γ(X, ⊤))
  erw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, hm]
  rfl

end Scheme

private theorem kummer_comparison (C P : Scheme.{u}) (π : P ⟶ C) (n : ℕ) :
    ∃ φ : ((Etale.upperStar AddCommGrpCat.{u + 1} π).mapShortComplex.obj
      (C.kummerSequence n)) ⟶ P.kummerSequence n,
      φ.τ₂ = upperStarGmSheafToGmSheaf π ∧
      φ.τ₃ = upperStarGmSheafToGmSheaf π := by
  let U := Etale.upperStar AddCommGrpCat.{u + 1} π
  let c := upperStarGmSheafToGmSheaf π
  have hg : U.map (C.kummerSequence n).g ≫ c = c ≫ (P.kummerSequence n).g := by
    change U.map (n • 𝟙 C.gmSheaf) ≫ c = c ≫ (n • 𝟙 P.gmSheaf)
    simp [U]
  have hz : (U.map (C.kummerSequence n).f ≫ c) ≫ (n • 𝟙 P.gmSheaf) = 0 := by
    change (U.map (C.kummerSequence n).f ≫ c) ≫ (P.kummerSequence n).g = 0
    rw [Category.assoc, ← hg, ← Category.assoc, ← U.map_comp]
    simp
  let a := kernel.lift (n • 𝟙 P.gmSheaf) (U.map (C.kummerSequence n).f ≫ c) hz
  refine ⟨{ τ₁ := a, τ₂ := c, τ₃ := c, comm₁₂ := ?_, comm₂₃ := hg.symm }, rfl, rfl⟩
  exact kernel.lift_ι _ _ _

/-- Kummer sequences, their connecting maps, and affine Picard torsion commute with extension of
algebraically closed ground fields. The proof follows the blueprint: base change preserves the
curve hypotheses; the comparison of units is adjoint to pullback; naturality of the derived
cohomology long exact sequence gives the ladder; degree zero is pullback of units and degree one
is pullback of invertible modules; in the affine case the Jacobian quotient and the abelian-variety
estimate give the isomorphism on `n`-torsion.

Source: Weil conjectures blueprint, sec-curve-estimates/sbc-thm-algebraically-closed-invariance,
proper-case Kummer naturality sentence and affine-case Picard-torsion paragraph
(blueprint: lem-sc-kummer-base-change-compatibility).

Proof: use `lem-sc-base-change-curve` for the hypotheses on the base change. The comparison map
of units and its restriction to roots of unity commute with the power maps, so the induced map of
short exact Kummer sequences is a `ShortComplex.Hom`. Apply `Sheaf.H.map_δSucc` and the
functoriality of the pullback maps to obtain the long-exact-sequence ladder. The degree-zero and
Picard assertions are the recorded pullback lemmas. For an affine curve, use the compactification
and Jacobian quotient from `proposition-cohomology-smooth-affine-curve--3`, clauses (c) and (d) of
`thm-av-final`, and `proposition-cohomology-smooth-affine-curve--3`.
-/
theorem kummer_base_change_compatibility
    (k k' : Type u) [Field k] [Field k'] [IsAlgClosed k] [IsAlgClosed k'] [Algebra k k']
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (P : Scheme.{u}) (π : P ⟶ C) (g : P ⟶ Spec (.of k'))
    (hπ : IsPullback π g f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (n : ℕ) [NeZero n] (hn : (n : k) ≠ 0) :
      ∃ (hC : (C.kummerSequence n).ShortExact)
        (hP : (P.kummerSequence n).ShortExact)
        (φ : ((Etale.upperStar AddCommGrpCat.{u + 1} π).mapShortComplex.obj
          (C.kummerSequence n)) ⟶ P.kummerSequence n),
        φ.τ₂ = upperStarGmSheafToGmSheaf π ∧
        φ.τ₃ = upperStarGmSheafToGmSheaf π ∧
        (∀ q : ℕ, ∀ x : Sheaf.H (C.kummerSequence n).X₃ q,
          Sheaf.H.map φ.τ₁ (q + 1)
              (Etale.cohomologyMap π (C.rootsOfUnitySheaf n) (q + 1)
                (Sheaf.H.δSucc hC q x)) =
            Sheaf.H.δSucc hP q
              (Sheaf.H.map φ.τ₃ q
                (Etale.cohomologyMap π C.gmSheaf q x))) ∧
        (∀ q : ℕ, ∀ x : Sheaf.H (C.kummerSequence n).X₁ q,
          Sheaf.H.map φ.τ₂ q
              (Etale.cohomologyMap π (C.kummerSequence n).X₂ q
                (Sheaf.H.map (C.kummerSequence n).f q x)) =
            Sheaf.H.map (P.kummerSequence n).f q
              (Sheaf.H.map φ.τ₁ q
                (Etale.cohomologyMap π (C.rootsOfUnitySheaf n) q x))) ∧
        (∀ q : ℕ, ∀ x : Sheaf.H (C.kummerSequence n).X₃ q,
          Sheaf.H.map φ.τ₃ q
              (Etale.cohomologyMap π C.gmSheaf q
                (Sheaf.H.map (C.kummerSequence n).g q x)) =
            Sheaf.H.map (P.kummerSequence n).g q
              (Sheaf.H.map φ.τ₂ q
                (Etale.cohomologyMap π C.gmSheaf q x))) ∧
        (∀ L : C.Pic,
          Pic.toCohomologicalPicardGroup P (Pic.map π L) =
            Sheaf.H.map (upperStarGmSheafToGmSheaf π) 1
              (Etale.cohomologyMap π C.gmSheaf 1
                (Pic.toCohomologicalPicardGroup C L))) ∧
        (∀ a : Γ(C, ⊤)ˣ,
          Sheaf.H.equiv₀ P.gmSheaf (MorphismProperty.Over.mkIdTerminal @Etale P)
            (Sheaf.H.map (upperStarGmSheafToGmSheaf π) 0
              (Etale.cohomologyMap π C.gmSheaf 0
                ((Sheaf.H.equiv₀ C.gmSheaf
                  (MorphismProperty.Over.mkIdTerminal @Etale C)).symm
                    (ULift.up (Additive.ofMul a))))) =
            ULift.up (Additive.ofMul (Units.map π.appTop.hom.toMonoidHom a))) ∧
        (IsAffine C →
          ∃ F : {x : C.Pic // x ^ n = 1} → {x : P.Pic // x ^ n = 1},
            Function.Bijective F ∧ ∀ x, (F x).1 = Pic.map π x.1)
      := by
  have hnC : IsUnit (n : Γ(C, ⊤)) := by
    simpa using hn.isUnit.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  have hnP : IsUnit (n : Γ(P, ⊤)) := by
    simpa using hnC.map π.appTop.hom
  let hC := C.kummerSequence_shortExact n hnC
  let hP := P.kummerSequence_shortExact n hnP
  obtain ⟨φ, h₂, h₃⟩ := kummer_comparison C P π n
  obtain ⟨hY, δC, δY, hδC, hδY, _, _, _, _, hf, hg, hδ⟩ :=
    Etale.pullbackCohomology_longExact_ladder π (C.kummerSequence n) hC
  have hδ' (q : ℕ) (x : Sheaf.H (C.kummerSequence n).X₃ q) :
      Etale.cohomologyMap π (C.kummerSequence n).X₁ (q + 1)
          (Sheaf.H.δSucc hC q x) =
        Sheaf.H.δSucc hY q (Etale.cohomologyMap π (C.kummerSequence n).X₃ q x) := by
    simpa only [hδC, hδY, Sheaf.H.δSucc_apply] using hδ q x
  let : C.Over (Spec (.of k)) := ⟨f⟩
  let : P.Over (Spec (.of k')) := ⟨g⟩
  let b := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  have hcurve := (baseChange_curve (k' := k') f).1
  have : IsCurve (pullback.snd f b) := hcurve
  have hdim : topologicalKrullDim P ≤ 1 := by
    rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso hπ.isoPullback).isHomeomorph]
    exact IsCurve.krullDim_le_one (f := pullback.snd f b)
  have : IsSeparated g := IsSeparated.isStableUnderBaseChange.of_isPullback hπ inferInstance
  have : LocallyOfFiniteType g :=
    locallyOfFiniteType_isStableUnderBaseChange.of_isPullback hπ inferInstance
  have : QuasiCompact g := quasiCompact_isStableUnderBaseChange.of_isPullback hπ inferInstance
  have : IsCurve g := { krullDim_le_one := hdim }
  have : IsCurve (C ↘ Spec (.of k)) := inferInstanceAs (IsCurve f)
  have : IsCurve (P ↘ Spec (.of k')) := inferInstanceAs (IsCurve g)
  have hUnits := Scheme.gm_units_cohomology_pullback C P π
  refine ⟨hC, hP, φ, h₂, h₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q x
    erw [hδ']
    exact Sheaf.H.map_δSucc hY hP φ q _
  · intro q x
    exact (congrArg (Sheaf.H.map φ.τ₂ q) (hf q x)).trans
      (by simpa only [Sheaf.H.map_comp_apply, Functor.mapShortComplex,
          ShortComplex.map, Scheme.kummerSequence, Scheme.rootsOfUnitySheaf] using
        congrArg (fun a => Sheaf.H.map a q
          (Etale.cohomologyMap π (C.kummerSequence n).X₁ q x)) φ.comm₁₂.symm)
  · intro q x
    exact (congrArg (Sheaf.H.map φ.τ₃ q) (hg q x)).trans
      (by simpa only [Sheaf.H.map_comp_apply, Functor.mapShortComplex,
          ShortComplex.map, Scheme.kummerSequence, Scheme.rootsOfUnitySheaf] using
        congrArg (fun a => Sheaf.H.map a q
          (Etale.cohomologyMap π C.gmSheaf q x)) φ.comm₂₃.symm)
  · intro L
    exact (Scheme.gmCohomologyMap_toCohomologicalPicardGroup π L).symm
  · exact hUnits
  · intro hAff
    let : IsAffine C := hAff
    refine ⟨fun x => ⟨Pic.map π x.1, ?_⟩, ?_, fun _ => rfl⟩
    · change (Pic.mapHom π x.1) ^ n = 1
      rw [← map_pow, x.2, map_one]
    · exact affine_picard_torsion_base_change k k' C f P π g hπ n hn

end AlgebraicGeometry
