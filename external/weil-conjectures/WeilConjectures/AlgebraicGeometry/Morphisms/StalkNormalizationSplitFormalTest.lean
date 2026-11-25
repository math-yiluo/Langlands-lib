/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization

public import WeilConjectures.RingTheory.Depth

public import Mathlib.RingTheory.MvPowerSeries.Basic

import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothSectionCompletionChart
import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationFormalSplit

/-!
# A split formal test for the local normalization

## References

* Stacks Project, Tag 0EYJ, the completion and splitting paragraphs
* Stacks Project, Tag 0EYJ, last three paragraphs
* Tags 05D5, 00MB, 0EY9 and 0EY6(2), (a), (b)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The section-ideal completion is a flat power-series test on which the finite
normalization is the coproduct of G copies of the test. This is the formal
calculation, before flatness descent
or construction of a target neighbourhood. -/
theorem GaloisCover.exists_stalk_normalization_split_formal_test {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη) (hsq : sη ≫ q = 𝟙 _)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : GaloisCover G Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη)
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := S.presheaf.stalk s) (S.presheaf.stalk s)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
      pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
    IsFinite n → ∃ (d : ℕ)
      (t : Spec (.of (MvPowerSeries (Fin d) (S.presheaf.stalk s))) ⟶ pullback c a),
      Flat t ∧
      (∃ e : pullback n t ≅
        ∐ (fun _ : G ↦ Spec (.of (MvPowerSeries (Fin d) (S.presheaf.stalk s)))),
        e.hom ≫ Sigma.desc (fun _ : G ↦ 𝟙 _) = pullback.snd n t) ∧
      t ((Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d))))
        (IsLocalRing.closedPoint (S.presheaf.stalk s))) =
        τ (IsLocalRing.closedPoint (S.presheaf.stalk s)) := by
  dsimp only
  intro hn
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  let a := S.fromSpecStalk s
  let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
  let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
    pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
  obtain ⟨d, t, ht, hbase, hsection⟩ :=
    exists_smooth_section_completion_chart (S.presheaf.stalk s)
      (pullback.snd c a) τ (by simp only [τ, pullback.lift_snd]; rfl)
  obtain ⟨e, he⟩ :=
    GaloisCover.exists_stalk_normalization_formal_split
      hS c σ hσ G q j hCη sη hsq hsj Z hZ U hηU jU PA ψ hjU hψ
      s hs hmin hdepth hn d t ht hbase hsection
  refine ⟨d, t, ht, ⟨e, he⟩, ?_⟩
  exact congrArg (fun f ↦ f (IsLocalRing.closedPoint (S.presheaf.stalk s))) hsection

end AlgebraicGeometry.Scheme
