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
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization

import WeilConjectures.RingTheory.NormalLocalDepthTwo
import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationNormalDense
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteNormalTraitPurity
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity

/-!
# Propagating etaleness across the local special fibre

## References

* Stacks Project, Tags 0EYE and 0EYB, as used in Tag 0EYJ
* Stacks Project, Tag 0EYE (purity across a regular Cartier divisor), Tag 0EYB (fibrewise dense
  etale open), and Tag 0EY6 (depth-two extension)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private theorem etale_pullback_restrict {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (g : T ⟶ Y) (U : Y.Opens) (hf : Etale (f ∣_ U)) :
    Etale (pullback.snd f g ∣_ (g ⁻¹ᵁ U)) := by
  let n := pullback.snd f g
  have hp := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g)
    (US := U) (UT := g ⁻¹ᵁ U) (UX := f ⁻¹ᵁ U)
    (UY := n ⁻¹ᵁ (g ⁻¹ᵁ U)) le_rfl le_rfl (by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
      exact (inf_idem _).symm)
  dsimp only [n] at hp
  simp only [Scheme.Hom.resLE_eq_morphismRestrict] at hp
  exact MorphismProperty.of_isPullback hp hf

/-- A finite normalization etale on the punctured open and on an open meeting
its missing fibre is etale everywhere on the local total space. -/
theorem stalk_normalization_etale_of_fibre_neighbourhood {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let f := PA.obj.hom ≫ (c ⁻¹ᵁ U).ι
    let l := pullback.fst c (S.fromSpecStalk s)
    let n := pullback.snd f.fromNormalization l
    IsFinite n → Etale (f.fromNormalization ∣_ (c ⁻¹ᵁ U)) →
    (∃ (W : (pullback c (S.fromSpecStalk s)).Opens)
      (x : (pullback c (S.fromSpecStalk s) : Scheme.{u})),
      x ∈ W ∧ (l ≫ c) x = s ∧ Etale (n ∣_ W)) → Etale n := by
  classical
  have _hU_nonempty : Set.Nonempty (U : Set S) := ⟨genericPoint S, hηU⟩
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  let f := PA.obj.hom ≫ (c ⁻¹ᵁ U).ι
  let l := pullback.fst c (S.fromSpecStalk s)
  let n := pullback.snd f.fromNormalization l
  let A := S.presheaf.stalk s
  let q := pullback.snd c (S.fromSpecStalk s)
  let V := S.fromSpecStalk s ⁻¹ᵁ U
  change IsFinite n → Etale (f.fromNormalization ∣_ (c ⁻¹ᵁ U)) →
    (∃ (W : (pullback c (S.fromSpecStalk s)).Opens)
      (x : (pullback c (S.fromSpecStalk s) : Scheme.{u})),
      x ∈ W ∧ (l ≫ c) x = s ∧ Etale (n ∣_ W)) → Etale n
  intro hn hU hW
  let : IsFinite n := hn
  let : IsIntegrallyClosed A := hS s
  have hclosed : S.fromSpecStalk s (IsLocalRing.closedPoint A) = s :=
    fromSpecStalk_closedPoint
  have hp := pullback.condition (f := c) (g := S.fromSpecStalk s)
  have hpre : l ⁻¹ᵁ (c ⁻¹ᵁ U) = q ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
    exact congrArg (fun k ↦ k ⁻¹ᵁ U) hp
  have hV : ∀ t : Spec (.of A), t ∈ V ↔ t ≠ IsLocalRing.closedPoint A := by
    intro t
    change S.fromSpecStalk s t ∈ U ↔ _
    constructor
    · intro ht heq
      subst t
      exact hs (by simpa only [hclosed] using ht)
    · intro ht
      by_contra hnot
      have hspec : S.fromSpecStalk s t ⤳ s := by
        have hr : S.fromSpecStalk s t ∈ Set.range (S.fromSpecStalk s) :=
          Set.mem_range_self t
        rw [S.range_fromSpecStalk] at hr
        exact hr
      have heq := hmin _ hspec hnot
      apply ht
      apply (S.fromSpecStalk s).isEmbedding.injective
      simpa only [hclosed] using heq
  have hnormal : ∀ z : (pullback f.fromNormalization l : Scheme.{u}),
      IsDomain ((pullback f.fromNormalization l : Scheme.{u}).presheaf.stalk z) ∧
      IsIntegrallyClosed ((pullback f.fromNormalization l : Scheme.{u}).presheaf.stalk z) :=
    (stalk_normalization_normal_and_dense hS c U PA s).1
  have hdense : Dense (↑(n ⁻¹ᵁ (l ⁻¹ᵁ (c ⁻¹ᵁ U))) :
      Set (pullback f.fromNormalization l : Scheme.{u})) :=
    (stalk_normalization_normal_and_dense hS c U PA s).2
  have hdense' : Dense (↑(n ⁻¹ᵁ (q ⁻¹ᵁ V)) :
      Set (pullback f.fromNormalization l : Scheme.{u})) :=
    (congrArg (fun O : (pullback c (S.fromSpecStalk s)).Opens ↦
      Dense (↑(n ⁻¹ᵁ O) : Set (pullback f.fromNormalization l : Scheme.{u}))) hpre).mp hdense
  have het : Etale (n ∣_ (q ⁻¹ᵁ V)) :=
    (congrArg (fun O : (pullback c (S.fromSpecStalk s)).Opens ↦ Etale (n ∣_ O)) hpre).mp
      (etale_pullback_restrict f.fromNormalization l (c ⁻¹ᵁ U) hU)
  obtain ⟨W, x, hx, hxs, hW⟩ := hW
  have hqx : q x = IsLocalRing.closedPoint A := by
    apply (S.fromSpecStalk s).isEmbedding.injective
    rw [hclosed]
    change (q ≫ S.fromSpecStalk s) x = s
    rw [← hp]
    exact hxs
  by_cases hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A
  · have hdepth := IsLocalRing.depth_two_of_normal A hdim
    exact finite_normal_etale_of_depth_two_neighbourhood A q V hV n hnormal
      hdense' het W x hx hqx hW hdepth
  · have hdim' : ringKrullDim A ≤ (1 : WithBot ℕ∞) :=
      ENat.WithBot.lt_add_one_iff.mp (lt_of_not_ge hdim)
    exact finite_normal_etale_of_trait_neighbourhood A q V hV n hnormal
      hdense' het W x hx hqx hW hdim'

end AlgebraicGeometry.Scheme
