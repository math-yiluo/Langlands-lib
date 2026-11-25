/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf
import WeilConjectures.AlgebraicGeometry.SiteCoveringIsomorphicFamily
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-! # Equivalence of sites gives morphisms of sites

Source: Stacks Project, Sites, Definitions 00VH, 00WV, 00X1 and Lemmas 00WW,
00WX (blueprint: lem-weil-pbc-site-equivalence-is-morphism-of-sites).
-/

private theorem covering_map_iso_id
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange]
    [J.HasPullbacks] (F : C ⥤ C) (e : F ≅ 𝟭 C)
    (X : C) (R : Presieve X) : R ∈ J X ↔ R.map F ∈ J (F.obj X) := by
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  rw [Presieve.map_ofArrows]
  constructor
  · intro hf
    exact (site_covering_isomorphic_family J f hf (e.hom.app X)
      (fun i => F.map (f i)) (fun i => e.hom.app (Y i))
      (fun i => inferInstance) (fun i => (e.hom.naturality (f i)).symm)).2
  · intro hf
    exact (site_covering_isomorphic_family J (fun i => F.map (f i)) hf
      (e.inv.app X) f (fun i => e.inv.app (Y i))
      (fun i => inferInstance) (fun i => (e.inv.naturality (f i)).symm)).2

-- The existential continuity witnesses in the unchanged statement are used by instance search.
set_option linter.unusedVariables false in
/-- An equivalence of Stacks sites `p : A ⥤ C` with quasi-inverse `p'` such that a family
is a covering of `A` iff its image is a covering of `C` satisfies: (1) a family is a
covering of `C` iff its image under `p'` is a covering of `A`; (2) `p` and `p'` are
continuous (Sites, Definition 00WV: coverings go to coverings, written by clause (1) and
the hypothesis `hcover`, and the fibre products `T ×_V V_i` along members of coverings are
preserved), so that the pushforwards `p^s`, `p'^s` are defined; (3) `p^s` and `p'^s` are
quasi-inverse on sheaves of sets and on abelian sheaves; (4) `p_s` and `p'_s` on sheaves
of sets are exact, so `p` and `p'` define morphisms of sites (Definition 00X1), and `p_s`
is a quasi-inverse of `p^s`, `p'_s` a quasi-inverse of `p'^s`.

Proof: (1) by the isomorphic-family lemma and naturality of `epsilon`, which makes the
hypotheses symmetric in `(p, p')`; fibre products are preserved since `p` is a right
adjoint of `p'` (`Equivalence.mk` and `toAdjunction`) and right adjoints preserve limits;
continuity follows; `p^s`, `p'^s` are quasi-inverse via Lemma 00WW and `epsilon`, `eta`;
`p_s` is isomorphic to `p'^s` by uniqueness of left adjoints, hence a quasi-inverse of
`p^s`; exactness: `p_s` is a left adjoint, so preserves colimits, and is isomorphic to the
right adjoint `p'^s`, so preserves limits; `p'` by symmetry.

Source: Stacks Project, Sites, Definitions 00VH, 00WV, 00X1 and Lemmas 00WW,
00WX; Categories, Definitions 001J and 0034.
(blueprint: lem-weil-pbc-site-equivalence-is-morphism-of-sites)
-/
theorem site_equivalence_is_morphism_of_sites
    {A C : Type u} [SmallCategory A] [SmallCategory C]
    (JA : Precoverage A) (JC : Precoverage C)
    [JA.HasIsos] [JA.IsStableUnderComposition] [JA.IsStableUnderBaseChange]
    [JA.HasPullbacks]
    [JC.HasIsos] [JC.IsStableUnderComposition] [JC.IsStableUnderBaseChange]
    [JC.HasPullbacks]
    (p : A ⥤ C) [p.IsEquivalence]
    (p' : C ⥤ A)
    (eta : 𝟭 A ≅ p ⋙ p') (epsilon : p' ⋙ p ≅ 𝟭 C)
    (hcover : ∀ (X : A) (R : Presieve X), R ∈ JA X ↔
      R.map p ∈ JC (p.obj X)) :
    (∀ (Y : C) (R : Presieve Y), R ∈ JC Y ↔
      R.map p' ∈ JA (p'.obj Y)) ∧
    (∀ (X Y Z : A) (R : Presieve X), R ∈ JA X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) p) ∧
    (∀ (X Y Z : C) (R : Presieve X), R ∈ JC X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) p') ∧
    ∃ (hp : p.IsContinuous JA.toGrothendieck JC.toGrothendieck),
      ∃ (hp' : p'.IsContinuous JC.toGrothendieck JA.toGrothendieck),
      Nonempty (p.sheafPushforwardContinuous (Type u)
        JA.toGrothendieck JC.toGrothendieck ⋙
        p'.sheafPushforwardContinuous (Type u)
          JC.toGrothendieck JA.toGrothendieck ≅ 𝟭
            (Sheaf JC.toGrothendieck (Type u))) ∧
      Nonempty (p'.sheafPushforwardContinuous (Type u)
        JC.toGrothendieck JA.toGrothendieck ⋙
        p.sheafPushforwardContinuous (Type u)
          JA.toGrothendieck JC.toGrothendieck ≅ 𝟭
            (Sheaf JA.toGrothendieck (Type u))) ∧
      Nonempty (p.sheafPushforwardContinuous (AddCommGrpCat.{u})
        JA.toGrothendieck JC.toGrothendieck ⋙
        p'.sheafPushforwardContinuous (AddCommGrpCat.{u})
          JC.toGrothendieck JA.toGrothendieck ≅ 𝟭
            (Sheaf JC.toGrothendieck (AddCommGrpCat.{u}))) ∧
      Nonempty (p'.sheafPushforwardContinuous (AddCommGrpCat.{u})
        JC.toGrothendieck JA.toGrothendieck ⋙
        p.sheafPushforwardContinuous (AddCommGrpCat.{u})
          JA.toGrothendieck JC.toGrothendieck ≅ 𝟭
            (Sheaf JA.toGrothendieck (AddCommGrpCat.{u}))) ∧
      PreservesFiniteLimits (Functor.sheafPullback p (Type u)
        JA.toGrothendieck JC.toGrothendieck) ∧
      PreservesFiniteColimits (Functor.sheafPullback p (Type u)
        JA.toGrothendieck JC.toGrothendieck) ∧
      PreservesFiniteLimits (Functor.sheafPullback p' (Type u)
        JC.toGrothendieck JA.toGrothendieck) ∧
      PreservesFiniteColimits (Functor.sheafPullback p' (Type u)
        JC.toGrothendieck JA.toGrothendieck) ∧
      Nonempty (Functor.sheafPullback p (Type u)
        JA.toGrothendieck JC.toGrothendieck ⋙
        p.sheafPushforwardContinuous (Type u)
          JA.toGrothendieck JC.toGrothendieck ≅ 𝟭
            (Sheaf JA.toGrothendieck (Type u))) ∧
      Nonempty (p.sheafPushforwardContinuous (Type u)
        JA.toGrothendieck JC.toGrothendieck ⋙
        Functor.sheafPullback p (Type u)
          JA.toGrothendieck JC.toGrothendieck ≅ 𝟭
            (Sheaf JC.toGrothendieck (Type u))) ∧
      Nonempty (Functor.sheafPullback p' (Type u)
        JC.toGrothendieck JA.toGrothendieck ⋙
        p'.sheafPushforwardContinuous (Type u)
          JC.toGrothendieck JA.toGrothendieck ≅ 𝟭
            (Sheaf JC.toGrothendieck (Type u))) ∧
      Nonempty (p'.sheafPushforwardContinuous (Type u)
        JC.toGrothendieck JA.toGrothendieck ⋙
        Functor.sheafPullback p' (Type u)
          JC.toGrothendieck JA.toGrothendieck ≅ 𝟭
            (Sheaf JA.toGrothendieck (Type u))) := by
  let e := Equivalence.mk p p' eta epsilon
  have : p'.IsEquivalence := inferInstanceAs e.inverse.IsEquivalence
  have hcover' : ∀ (Y : C) (R : Presieve Y), R ∈ JC Y ↔
      R.map p' ∈ JA (p'.obj Y) := by
    intro Y R
    rw [hcover]
    obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
    simpa only [Presieve.map_ofArrows, Functor.comp_obj, Functor.comp_map] using
      covering_map_iso_id JC (p' ⋙ p) epsilon Y (Presieve.ofArrows V f)
  have hpull : ∀ (X Y Z : A) (R : Presieve X), R ∈ JA X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) p := by
    intros
    infer_instance
  have hpull' : ∀ (X Y Z : C) (R : Presieve X), R ∈ JC X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) p' := by
    intros
    infer_instance
  have hp : p.IsContinuous JA.toGrothendieck JC.toGrothendieck := by
    constructor
    intro G
    rw [← isSheaf_iff_isSheaf_of_type]
    exact ((siteContinuous_pushforward_isSheaf JA JC p
      (fun X R hR => (hcover X R).mp hR) hpull).1 G).1
  have hp' : p'.IsContinuous JC.toGrothendieck JA.toGrothendieck := by
    constructor
    intro G
    rw [← isSheaf_iff_isSheaf_of_type]
    exact ((siteContinuous_pushforward_isSheaf JC JA p'
      (fun X R hR => (hcover' X R).mp hR) hpull').1 G).1
  refine ⟨hcover', hpull, hpull', hp, hp', ?_⟩
  have : (p' ⋙ p).IsContinuous JC.toGrothendieck JC.toGrothendieck :=
    Functor.isContinuous_comp p' p JC.toGrothendieck JA.toGrothendieck JC.toGrothendieck
  have : (p ⋙ p').IsContinuous JA.toGrothendieck JA.toGrothendieck :=
    Functor.isContinuous_comp p p' JA.toGrothendieck JC.toGrothendieck JA.toGrothendieck
  have ec (B : Type (u + 1)) [Category.{u} B] :
      p.sheafPushforwardContinuous B JA.toGrothendieck JC.toGrothendieck ⋙
      p'.sheafPushforwardContinuous B JC.toGrothendieck JA.toGrothendieck ≅ 𝟭 _ :=
    p'.sheafPushforwardContinuousComp p B _ _ _ ≪≫
      Functor.sheafPushforwardContinuousId' epsilon B _
  have ea (B : Type (u + 1)) [Category.{u} B] :
      p'.sheafPushforwardContinuous B JC.toGrothendieck JA.toGrothendieck ⋙
      p.sheafPushforwardContinuous B JA.toGrothendieck JC.toGrothendieck ≅ 𝟭 _ :=
    p.sheafPushforwardContinuousComp p' B _ _ _ ≪≫
      Functor.sheafPushforwardContinuousId' eta.symm B _
  have : (p.sheafPushforwardContinuous (Type u)
      JA.toGrothendieck JC.toGrothendieck).IsEquivalence :=
    Functor.IsEquivalence.mk' _ (ec (Type u)).symm (ea (Type u))
  have : (p'.sheafPushforwardContinuous (Type u)
      JC.toGrothendieck JA.toGrothendieck).IsEquivalence :=
    Functor.IsEquivalence.mk' _ (ea (Type u)).symm (ec (Type u))
  let adj := Functor.sheafAdjunctionContinuous p (Type u)
    JA.toGrothendieck JC.toGrothendieck
  let adj' := Functor.sheafAdjunctionContinuous p' (Type u)
    JC.toGrothendieck JA.toGrothendieck
  have : (p.sheafPullback (Type u)
      JA.toGrothendieck JC.toGrothendieck).IsEquivalence :=
    adj.isEquivalence_left_of_isEquivalence_right
  have : (p'.sheafPullback (Type u)
      JC.toGrothendieck JA.toGrothendieck).IsEquivalence :=
    adj'.isEquivalence_left_of_isEquivalence_right
  have : PreservesLimitsOfSize.{0, 0} (p.sheafPullback (Type u)
      JA.toGrothendieck JC.toGrothendieck) :=
    adj.toEquivalence.symm.toAdjunction.rightAdjoint_preservesLimits
  have : PreservesLimitsOfSize.{0, 0} (p'.sheafPullback (Type u)
      JC.toGrothendieck JA.toGrothendieck) :=
    adj'.toEquivalence.symm.toAdjunction.rightAdjoint_preservesLimits
  exact ⟨⟨ec (Type u)⟩, ⟨ea (Type u)⟩, ⟨ec AddCommGrpCat.{u}⟩,
    ⟨ea AddCommGrpCat.{u}⟩,
    PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _, inferInstance,
    PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _, inferInstance,
    ⟨(asIso adj.unit).symm⟩, ⟨asIso adj.counit⟩,
    ⟨(asIso adj'.unit).symm⟩, ⟨asIso adj'.counit⟩⟩

end CategoryTheory
