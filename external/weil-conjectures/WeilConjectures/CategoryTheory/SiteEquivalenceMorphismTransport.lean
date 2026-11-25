/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import WeilConjectures.CategoryTheory.SiteMorphismComposition
public import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.SiteEquivalenceMorphismOfSites
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.SiteCoveringIsomorphicFamily

/-!
# Transport of morphisms of sites across equivalences

Source: literature/stacks-project/sites.tex, Definitions 00VH, 00WV, 00X1 and
Lemma 03CB (blueprint: lem-weil-pbc-site-equivalence-morphism-transport).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: literature/stacks-project/sites.tex, Definitions 00VH, 00WV, 00X1
and Lemma 03CB (blueprint: lem-weil-pbc-site-equivalence-morphism-transport).

The proof transports continuity and exactness through the two equivalences, using
site-equivalence-is-morphism, site-morphism-composition, and invariance under
isomorphic covering families.  The natural isomorphism identifies the two
functors and hence identifies their sheaf pullbacks; exactness is invariant under
that identification.
-/
theorem site_equivalence_morphism_transport
    {A B C D : Type u}
    [SmallCategory A] [SmallCategory B] [SmallCategory C] [SmallCategory D]
    (JA : Precoverage A) (JB : Precoverage B)
    (JC : Precoverage C) (JD : Precoverage D)
    [JA.HasIsos] [JA.IsStableUnderComposition] [JA.IsStableUnderBaseChange]
    [JA.HasPullbacks]
    [JB.HasIsos] [JB.IsStableUnderComposition] [JB.IsStableUnderBaseChange]
    [JB.HasPullbacks]
    [JC.HasIsos] [JC.IsStableUnderComposition] [JC.IsStableUnderBaseChange]
    [JC.HasPullbacks]
    [JD.HasIsos] [JD.IsStableUnderComposition] [JD.IsStableUnderBaseChange]
    [JD.HasPullbacks]
    (p : A ⥤ C) (q : B ⥤ D)
    [p.IsEquivalence] [q.IsEquivalence]
    (hpcover : ∀ (X : A) (R : Presieve X),
      R ∈ JA X ↔ R.map p ∈ JC (p.obj X))
    (hqcover : ∀ (X : B) (R : Presieve X),
      R ∈ JB X ↔ R.map q ∈ JD (q.obj X))
    (u : C ⥤ D)
    (hucover : ∀ (X : C) (R : Presieve X),
      R ∈ JC X → R.map u ∈ JD (u.obj X))
    (hupullback : ∀ (X Y Z : C) (R : Presieve X), R ∈ JC X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) u)
    [u.IsContinuous JC.toGrothendieck JD.toGrothendieck]
    [PreservesFiniteLimits (sheafPullback u (Type u)
      JC.toGrothendieck JD.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback u (Type u)
      JC.toGrothendieck JD.toGrothendieck)]
    (u' : A ⥤ B)
    (α : u' ⋙ q ≅ p ⋙ u) :
    (∀ (X : A) (R : Presieve X), R ∈ JA X →
      R.map u' ∈ JB (u'.obj X)) ∧
    (∀ (X Y Z : A) (R : Presieve X), R ∈ JA X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) u') ∧
    ∃ (_ : u'.IsContinuous JA.toGrothendieck JB.toGrothendieck),
      PreservesFiniteLimits (sheafPullback u' (Type u)
        JA.toGrothendieck JB.toGrothendieck) ∧
      PreservesFiniteColimits (sheafPullback u' (Type u)
        JA.toGrothendieck JB.toGrothendieck) := by
  obtain ⟨_, hpull, _, hp, _, _, _, _, _, hplim, hpcolim, _⟩ :=
    site_equivalence_is_morphism_of_sites JA JC p p.inv
      p.asEquivalence.unitIso p.asEquivalence.counitIso hpcover
  obtain ⟨hqcover', _, hqpull', _, hq', _, _, _, _, _, _, hqlim', hqcolim', _⟩ :=
    site_equivalence_is_morphism_of_sites JB JD q q.inv
      q.asEquivalence.unitIso q.asEquivalence.counitIso hqcover
  have := hplim
  have := hpcolim
  have := hqlim'
  have := hqcolim'
  have : PreservesFiniteLimits (sheafPullback p (Type u)
      JA.toGrothendieck JC.toGrothendieck) :=
    preservesFiniteLimits_of_natIso (sheafPullbackIso p (Type u) _ _)
  have : PreservesFiniteColimits (sheafPullback p (Type u)
      JA.toGrothendieck JC.toGrothendieck) :=
    preservesFiniteColimits_of_natIso (sheafPullbackIso p (Type u) _ _)
  have : PreservesFiniteLimits (sheafPullback q.inv (Type u)
      JD.toGrothendieck JB.toGrothendieck) :=
    preservesFiniteLimits_of_natIso (sheafPullbackIso q.inv (Type u) _ _)
  have : PreservesFiniteColimits (sheafPullback q.inv (Type u)
      JD.toGrothendieck JB.toGrothendieck) :=
    preservesFiniteColimits_of_natIso (sheafPullbackIso q.inv (Type u) _ _)
  obtain ⟨hpucover, hpupull, hpu, _, _, _, _, ⟨hpulim⟩, ⟨hpucolim⟩⟩ :=
    siteMorphism_composition JD JC JA u p hucover hupullback
      (fun X R hR => (hpcover X R).mp hR) hpull
  have := hpulim
  have := hpucolim
  obtain ⟨hwcover, hwpull, hw, _, _, _, _, ⟨hwlim⟩, ⟨hwcolim⟩⟩ :=
    siteMorphism_composition JB JD JA q.inv (p ⋙ u)
      (fun X R hR => (hqcover' X R).mp hR) hqpull' hpucover hpupull
  have := hwlim
  have := hwcolim
  let θ : u' ≅ (p ⋙ u) ⋙ q.inv :=
    u'.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft u' q.asEquivalence.unitIso ≪≫
      (Functor.associator u' q q.inv).symm ≪≫ Functor.isoWhiskerRight α q.inv
  have hcover : ∀ (X : A) (R : Presieve X), R ∈ JA X →
      R.map u' ∈ JB (u'.obj X) := by
    intro X R hR
    obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
    have hf := hwcover X (Presieve.ofArrows Y f) hR
    rw [Presieve.map_ofArrows] at hf ⊢
    exact (site_covering_isomorphic_family JB (fun i => ((p ⋙ u) ⋙ q.inv).map (f i))
      hf (θ.hom.app X) (fun i => u'.map (f i)) (fun i => θ.hom.app (Y i))
      (fun i => inferInstance) (fun i => (θ.hom.naturality (f i)).symm)).2
  have hpull' : ∀ (X Y Z : A) (R : Presieve X), R ∈ JA X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) u' := by
    intro X Y Z R hR f g hf
    have := hwpull X Y Z R hR f g hf
    exact preservesLimit_of_natIso (cospan f g) θ.symm
  have hu' : u'.IsContinuous JA.toGrothendieck JB.toGrothendieck :=
    Functor.isContinuous_of_iso θ.symm JA.toGrothendieck JB.toGrothendieck
  let δ := Functor.sheafPushforwardContinuousIso θ (Type u)
    JA.toGrothendieck JB.toGrothendieck
  let e := ((sheafAdjunctionContinuous u' (Type u)
      JA.toGrothendieck JB.toGrothendieck).ofNatIsoRight δ).leftAdjointUniq
    (sheafAdjunctionContinuous ((p ⋙ u) ⋙ q.inv) (Type u)
      JA.toGrothendieck JB.toGrothendieck)
  exact ⟨hcover, hpull', hu', preservesFiniteLimits_of_natIso e.symm,
    preservesFiniteColimits_of_natIso e.symm⟩

end CategoryTheory
