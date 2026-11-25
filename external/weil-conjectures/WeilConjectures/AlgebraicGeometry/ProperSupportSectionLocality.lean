/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
import WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport

/-! # Restriction and locality of proper support

Source: Stacks Project, Tag 0F4X
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false

private theorem germ_zero_congr
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale)
    (s : F.obj.obj (op V)) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (p q : Spec (.of Ω) ⟶ X) (hpq : p = q) (v : Spec (.of Ω) ⟶ V.left)
    (hv : v ≫ V.hom = p) (hv' : v ≫ V.hom = q) :
    (Scheme.pointSmallEtale p).toPresheafFiber V (Over.homMk v hv) F.obj s = 0 ↔
      (Scheme.pointSmallEtale q).toPresheafFiber V (Over.homMk v hv') F.obj s = 0 := by
  cases hpq
  rfl

/-- Restriction preserves the vanishing of the germ at a specified geometric point.
Source: Stacks Project, Tag 04FR.
(auxiliary; not a blueprint node). -/
theorem etaleModuleGerm_restrict_zero
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {V W : X.Etale} (h : W ⟶ V) (s : F.obj.obj (op V))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (v : Spec (.of Ω) ⟶ W.left) :
    (Scheme.pointSmallEtale (v ≫ W.hom)).toPresheafFiber W
        (Over.homMk v) F.obj (F.obj.map h.op s) = 0 ↔
      (Scheme.pointSmallEtale ((v ≫ h.left) ≫ V.hom)).toPresheafFiber V
        (Over.homMk (v ≫ h.left)) F.obj s = 0 := by
  have e := ConcreteCategory.congr_hom
    ((Scheme.pointSmallEtale (v ≫ W.hom)).toPresheafFiber_w h
      (Over.homMk v) F.obj) s
  have hw : h.left ≫ V.hom = W.hom := h.w
  have hb : (v ≫ h.left) ≫ V.hom = v ≫ W.hom := by
    rw [Category.assoc, hw]
  change (Scheme.pointSmallEtale (v ≫ W.hom)).toPresheafFiber W
      (Over.homMk v) F.obj (F.obj.map h.op s) =
    (Scheme.pointSmallEtale (v ≫ W.hom)).toPresheafFiber V
      (Over.homMk (v ≫ h.left)) F.obj s at e
  exact (show _ ↔ _ from ⟨fun hz => e.symm.trans hz, fun hz => e.trans hz⟩).trans
    (germ_zero_congr Λ F V s Ω (v ≫ W.hom) ((v ≫ h.left) ≫ V.hom)
      hb.symm (v ≫ h.left) hb rfl)

/-- The natural restriction square between two base-changed etale objects is Cartesian.
Source: Stacks Project, Tag 0F4X.
(auxiliary; not a blueprint node). -/
theorem etaleObjectPullbackSquare {X Y : Scheme.{u}} (f : X ⟶ Y)
    {V W : Y.Etale} (h : W ⟶ V) :
    IsPullback (f.Etale.map h).left (pullback.fst W.hom f)
      (pullback.fst V.hom f) h.left := by
  have hp : (f.Etale.map h).left ≫ pullback.fst V.hom f =
      pullback.fst W.hom f ≫ h.left := by
    simp [Scheme.Hom.Etale, MorphismProperty.Over.pullback_map_left]
  apply IsPullback.of_right (h₁₂ := pullback.snd V.hom f) (v₁₃ := f) ?_ hp
    (IsPullback.of_hasPullback V.hom f).flip
  simpa [Scheme.Hom.Etale, MorphismProperty.Over.pullback_map_left, h.w] using
    (IsPullback.of_hasPullback W.hom f).flip

/-- Transport properness of a closed support across an isomorphism over the base.
Source: Stacks Project, Tag 0F4X, invariance of proper support under isomorphisms.
(auxiliary; not a blueprint node)

Proof: The proper-image assertion gives a closed image proper over the base. The inverse
isomorphism identifies that image with the inverse image of the original support. -/
theorem proper_iso_image {T U S : Scheme.{u}} (p : T ⟶ S)
    [LocallyOfFiniteType p] (q : U ⟶ S) [LocallyOfFiniteType q] [IsSeparated q]
    (e : T ≅ U) (he : e.hom ≫ q = p) (C : TopologicalSpace.Closeds T)
    (hp : Scheme.IsClosedSubsetProperOver p C) :
    Scheme.IsClosedSubsetProperOver q (C.preimage e.inv.continuous) := by
  obtain ⟨D, hD, hDp⟩ := (Scheme.closed_subset_proper_over_base_properties p C).2.2.2
    e.hom q he hp
  have hDC : D = C.preimage e.inv.continuous := by
    apply TopologicalSpace.Closeds.ext
    ext x
    change x ∈ (D : Set U) ↔ e.inv x ∈ C
    rw [hD]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change (e.hom ≫ e.inv) y ∈ C
      rw [e.hom_inv_id]
      exact hy
    · intro hx
      refine ⟨e.inv x, hx, ?_⟩
      change (e.inv ≫ e.hom) x = x
      rw [e.inv_hom_id]
      rfl
  rwa [hDC] at hDp

private theorem proper_restriction_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] {V W : Y.Etale} (h : W ⟶ V)
    (C : TopologicalSpace.Closeds (f.Etale.obj V).left) :
    Scheme.IsClosedSubsetProperOver (pullback.fst W.hom f)
        (C.preimage (f.Etale.map h).left.continuous) ↔
      Scheme.IsClosedSubsetProperOver (pullback.snd (pullback.fst V.hom f) h.left)
        (C.preimage (pullback.fst (pullback.fst V.hom f) h.left).continuous) := by
  let sq := etaleObjectPullbackSquare f h
  let e := sq.isoPullback
  constructor
  · intro hp
    have hh := proper_iso_image (pullback.fst W.hom f)
      (pullback.snd (pullback.fst V.hom f) h.left) e sq.isoPullback_hom_snd
      (C.preimage (f.Etale.map h).left.continuous) hp
    have hC : (C.preimage (f.Etale.map h).left.continuous).preimage e.inv.continuous =
        C.preimage (pullback.fst (pullback.fst V.hom f) h.left).continuous := by
      apply TopologicalSpace.Closeds.ext
      ext x
      change (f.Etale.map h).left (e.inv x) ∈ C ↔
        pullback.fst (pullback.fst V.hom f) h.left x ∈ C
      change (e.inv ≫ (f.Etale.map h).left) x ∈ C ↔ _
      rw [sq.isoPullback_inv_fst]
      rfl
    rwa [hC] at hh
  · intro hp
    have hh := proper_iso_image (pullback.snd (pullback.fst V.hom f) h.left)
      (pullback.fst W.hom f) e.symm sq.isoPullback_inv_snd
      (C.preimage (pullback.fst (pullback.fst V.hom f) h.left).continuous) hp
    have hC : (C.preimage (pullback.fst (pullback.fst V.hom f) h.left).continuous).preimage
        e.hom.continuous = C.preimage (f.Etale.map h).left.continuous := by
      apply TopologicalSpace.Closeds.ext
      ext x
      change pullback.fst (pullback.fst V.hom f) h.left (e.hom x) ∈ C ↔
        (f.Etale.map h).left x ∈ C
      change (e.hom ≫ pullback.fst (pullback.fst V.hom f) h.left) x ∈ C ↔ _
      rw [sq.isoPullback_hom_fst]
      rfl
    rwa [hC] at hh

private theorem closeds_eq_of_geom_iff {T : Scheme.{u}}
    (C D : TopologicalSpace.Closeds T)
    (h : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (v : Spec (.of Ω) ⟶ T),
      v default ∈ C ↔ v default ∈ D) : C = D := by
  apply TopologicalSpace.Closeds.ext
  ext x
  change x ∈ C ↔ x ∈ D
  let Ω := AlgebraicClosure (T.residueField x)
  let v : Spec (.of Ω) ⟶ T := T.algClosurePoint x
  have hv : v default = x := Scheme.algClosurePoint_base _ _ _
  simpa only [hv] using h Ω v

private theorem restriction_support_iff
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : Y.Etale) (s : F.obj.obj (op (f.Etale.obj V)))
    (C : TopologicalSpace.Closeds (f.Etale.obj V).left)
    (hC : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (v : Spec (.of Ω) ⟶ (f.Etale.obj V).left),
      v default ∈ C ↔
        (Scheme.pointSmallEtale (v ≫ (f.Etale.obj V).hom)).toPresheafFiber
          (f.Etale.obj V) (Over.homMk v) F.obj s ≠ 0)
    (W : Y.Etale) (h : W ⟶ V) :
    SectionHasProperSupport Λ F (f.Etale.obj W) (pullback.fst W.hom f)
        (F.obj.map (f.Etale.map h).op s) ↔
      Scheme.IsClosedSubsetProperOver (pullback.fst W.hom f)
        (C.preimage (f.Etale.map h).left.continuous) := by
  have hcrit (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (v : Spec (.of Ω) ⟶ (f.Etale.obj W).left) :
      v default ∈ C.preimage (f.Etale.map h).left.continuous ↔
        (Scheme.pointSmallEtale (v ≫ (f.Etale.obj W).hom)).toPresheafFiber
          (f.Etale.obj W) (Over.homMk v) F.obj (F.obj.map (f.Etale.map h).op s) ≠ 0 := by
    change (f.Etale.map h).left (v default) ∈ C ↔ _
    have hCv := hC Ω (v ≫ (f.Etale.map h).left)
    rw [Scheme.Hom.comp_apply] at hCv
    exact hCv.trans (not_congr (etaleModuleGerm_restrict_zero Λ F (f.Etale.map h) s Ω v)).symm
  rw [sectionHasProperSupport_iff]
  constructor
  · rintro ⟨D, hD, hp⟩
    have he : D = C.preimage (f.Etale.map h).left.continuous :=
      closeds_eq_of_geom_iff _ _ (fun Ω _ _ v => (hD Ω v).trans (hcrit Ω v).symm)
    rwa [he] at hp
  · exact fun hp => ⟨_, hcrit, hp⟩

/-- Proper support is preserved by restriction and can be checked on a covering sieve.

Source: Stacks Project, Tag 0F4X, restriction and sheaf-condition paragraphs.
(auxiliary; not a blueprint node)

Proof:
For h : W -> V in the target's small etale site, the induced map X_W -> X_V
is the base change of h.left. The geometric-germ restriction formula says that the
support of s restricted to X_W is the inverse image of the support of s in X_V.
Apply closed_proper_support_locality to the support of s over V, and transport
along the canonical isomorphism of these two descriptions of X_W. This proves
restriction stability. A covering sieve contains a jointly surjective etale family
W_i -> V. The same support calculation identifies the supports of its restrictions
with these inverse images. Their properness descends along that family by the second
clause of closed_proper_support_locality, proving membership for s itself. -/
theorem properSupportSectionLocality (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] :
    (∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (V W : Y.Etale) (h : W ⟶ V) s,
      SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) s →
      SectionHasProperSupport Λ F (f.Etale.obj W) (pullback.fst W.hom f)
        (F.obj.map (f.Etale.map h).op s)) ∧
    (∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (V : Y.Etale) s (S : Sieve V), S ∈ Y.smallEtaleTopology V →
      (∀ (W : Y.Etale) (h : W ⟶ V), S h →
        SectionHasProperSupport Λ F (f.Etale.obj W) (pullback.fst W.hom f)
          (F.obj.map (f.Etale.map h).op s)) →
      SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) s) := by
  constructor
  · intro F V W h s hs
    obtain ⟨C, hC, hCa⟩ := etaleModuleSection_closedSupport Λ F (f.Etale.obj V) s
    obtain ⟨D, hD, hp⟩ := hs
    have he : D = C := TopologicalSpace.Closeds.ext (hD.trans hCa.symm)
    subst D
    apply (restriction_support_iff Λ f F V s C hC W h).2
    apply (proper_restriction_iff f h C).2
    exact (Scheme.closed_proper_support_locality.{u, u} (pullback.fst V.hom f) C).1
      W.left h.left hp
  · intro F V s S hcov hs
    obtain ⟨C, hC, _⟩ := etaleModuleSection_closedSupport Λ F (f.Etale.obj V) s
    apply (sectionHasProperSupport_iff Λ F (f.Etale.obj V) (pullback.fst V.hom f) s).2
    refine ⟨C, hC, ?_⟩
    obtain ⟨U, hU, pU, hS⟩ := (Scheme.mem_smallGrothendieckTopology V S).1 hcov
    let := hU
    let W (i : U.I₀) : Y.Etale := (U.X i).asOverProp Y (pU i)
    let h (i : U.I₀) : W i ⟶ V := (U.f i).asOverProp Y
    apply (Scheme.closed_proper_support_locality.{u, u} (pullback.fst V.hom f) C).2
      U.I₀ U.X U.f (fun y => U.exists_eq y)
    intro i
    have hsi := hs (W i) (h i) (hS _ _ ⟨i⟩)
    exact (proper_restriction_iff f (h i) C).1
      ((restriction_support_iff Λ f F V s C hC (W i) (h i)).1 hsi)

end AlgebraicGeometry.Etale
