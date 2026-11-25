/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesTestFiniteExtensionFlat
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.MvPowerSeries.Equiv
import WeilConjectures.RingTheory.FlatLocalDepthFormula

/-!
# Formal flatness at a closed boundary point of the closed fibre

## References

* Stacks Project, Tag 0EYB, closed-point formal-completion calculation
* Stacks Project, Tag 0EYB, from the choice of a closed point through the completion argument
* Tags 0EY6(2), (a), (b), 07NE, 057G, 05D5, 00MB, and 0EYA
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

open TensorProduct in
private theorem flat_of_faithfullyFlat_comp {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hg : g.FaithfullyFlat) (hfg : (g.comp f).Flat) : f.Flat := by
  algebraize [f, g, g.comp f]
  change Module.Flat R S
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ l hl
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective S T
    (AlgebraTensorModule.lTensor S S l)).mp
  have h : Function.Injective (LinearMap.lTensor T l) :=
    Module.Flat.lTensor_preserves_injective_linearMap l hl
  have heq := AlgebraTensorModule.lTensor_comp_cancelBaseChange R S S (M := T) l
  have hh : Function.Injective ((AlgebraTensorModule.lTensor S T l).comp
      (AlgebraTensorModule.cancelBaseChange R S S T N).toLinearMap) :=
    h.comp (AlgebraTensorModule.cancelBaseChange R S S T N).injective
  rw [heq] at hh
  intro a b hab
  apply hh
  exact congrArg (AlgebraTensorModule.cancelBaseChange R S S T P) hab

/-- Flatness at a point descends from a flat test morphism meeting its image. -/
private theorem flat_stalk_of_flat_test {L E T : Scheme.{u}} (p : E ⟶ L) (t : T ⟶ L)
    [Flat t] [Flat (Limits.pullback.snd p t)] (z : E) (b : T) (hzb : p z = t b) :
    (p.stalkMap z).hom.Flat := by
  obtain ⟨w, hw, _⟩ := Pullback.exists_preimage_pullback (f := p) (g := t) z b hzb
  let g := Limits.pullback.fst p t
  have hcomp : ((g ≫ p).stalkMap w).hom.Flat := by
    rw [Limits.pullback.condition, Hom.stalkMap_comp, CommRingCat.hom_comp]
    exact (Flat.stalkMap t _).comp (Flat.stalkMap (Limits.pullback.snd p t) w)
  rw [Hom.stalkMap_comp, CommRingCat.hom_comp] at hcomp
  have hg : (g.stalkMap w).hom.FaithfullyFlat := by
    algebraize [(g.stalkMap w).hom]
    have : Module.Flat _ _ := Flat.stalkMap g w
    have : IsLocalHom (algebraMap (E.presheaf.stalk (g w))
        ((Limits.pullback p t).presheaf.stalk w)) := inferInstanceAs (IsLocalHom (g.stalkMap w).hom)
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hp := flat_of_faithfullyFlat_comp (p.stalkMap (g w)).hom (g.stalkMap w).hom
    hg hcomp
  change g w = z at hw
  rw [hw] at hp
  exact hp


private theorem etale_restrict_pullback {E L T : Scheme.{u}} (p : E ⟶ L) (t : T ⟶ L)
    (U : L.Opens) [Etale (p ∣_ U)] : Etale ((Limits.pullback.snd p t) ∣_ (t ⁻¹ᵁ U)) := by
  have heq : (Limits.pullback.fst p t) ⁻¹ᵁ (p ⁻¹ᵁ U) =
      (Limits.pullback.snd p t) ⁻¹ᵁ (t ⁻¹ᵁ U) := by
    simp only [← Hom.comp_preimage, Limits.pullback.condition]
  have H := Hom.isPullback_resLE (IsPullback.of_hasPullback p t)
    (US := U) (UT := t ⁻¹ᵁ U) (UX := p ⁻¹ᵁ U) le_rfl le_rfl
    (UY := (Limits.pullback.snd p t) ⁻¹ᵁ (t ⁻¹ᵁ U)) (by rw [heq, inf_idem])
  simpa only [Hom.resLE_eq_morphismRestrict] using
    (MorphismProperty.of_isPullback (P := @Etale) H (by
      simpa only [Hom.resLE_eq_morphismRestrict] using (inferInstance : Etale (p ∣_ U))))

private theorem depth_two_pullback {E L T : Scheme.{u}} [IsLocallyNoetherian L]
    [IsLocallyNoetherian T] (p : E ⟶ L) [IsFinite p] (t : T ⟶ L) [Flat t]
    (U : L.Opens)
    (hboundary : ∀ z : E, p z ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z)) :
    ∀ w : ↥(Limits.pullback p t), (Limits.pullback.snd p t) w ∉ t ⁻¹ᵁ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := (Limits.pullback p t).presheaf.stalk w)
        ((Limits.pullback p t).presheaf.stalk w) := by
  have : IsLocallyNoetherian E := LocallyOfFiniteType.isLocallyNoetherian p
  intro w hw
  have hw' : p ((Limits.pullback.fst p t) w) ∉ U := by
    change t ((Limits.pullback.snd p t) w) ∉ U at hw
    rwa [← Hom.comp_apply, ← Limits.pullback.condition, Hom.comp_apply] at hw
  obtain ⟨_, hlocal, _, hd⟩ := IsLocalRing.depth_eq_add_of_flat_local
    ((Limits.pullback.fst p t).stalkMap w).hom (Flat.stalkMap _ _)
  rw [hd]
  exact (hboundary _ hw').trans le_self_add

/-- Formal completion gives flatness at source points over a closed boundary point. -/
theorem flat_stalk_of_smooth_local_depth_two_closed_fiber
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {L : Scheme.{u}} (q : L ⟶ Spec (.of A)) [Smooth q]
    (U : L.Opens)
    (haway : ∀ y : L, q y ≠ IsLocalRing.closedPoint A → y ∈ U)
    (hclosed : Dense (↑((q.fiberι (IsLocalRing.closedPoint A)) ⁻¹ᵁ U) :
      Set (q.fiber (IsLocalRing.closedPoint A))))
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    {E : Scheme.{u}} (p : E ⟶ L) [IsFinite p] [Etale (p ∣_ U)]
    (hboundary : ∀ z : E, p z ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z))
    (x : q.fiber (IsLocalRing.closedPoint A)) (hx : IsClosed ({x} : Set _))
    (hout : q.fiberι (IsLocalRing.closedPoint A) x ∉ U)
    (z : E) (hz : p z = q.fiberι (IsLocalRing.closedPoint A) x) :
    (p.stalkMap z).hom.Flat := by
  obtain ⟨B, hB, hlocal, hnoeth, hBdepth, n, hn, t, ht, ⟨b, hb⟩, hawayB, hgeneric⟩ :=
    exists_closed_fiber_power_series_test A q U haway hclosed hdepth x hx hout
  let := hB
  let := hlocal
  let := hnoeth
  let := ht
  have : IsLocallyNoetherian L := LocallyOfFiniteType.isLocallyNoetherian q
  have : Etale ((Limits.pullback.snd p t) ∣_ (t ⁻¹ᵁ U)) := etale_restrict_pullback p t U
  have : Flat (Limits.pullback.snd p t) :=
    flat_of_power_series_depth_two_finite_extension B hBdepth n hn (t ⁻¹ᵁ U)
      (Limits.pullback.snd p t) (depth_two_pullback p t U hboundary) hawayB hgeneric
  exact flat_stalk_of_flat_test p t z b (hz.trans hb.symm)

end AlgebraicGeometry.Scheme
