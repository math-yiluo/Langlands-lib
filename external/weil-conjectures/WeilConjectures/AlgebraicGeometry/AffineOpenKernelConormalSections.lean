/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import WeilConjectures.AlgebraicGeometry.AffineConormalSectionsExistence
import WeilConjectures.AlgebraicGeometry.OpenKernelConormalTransport

/-! # Conormal sections on an affine closed chart

Source: Stacks Project, Tags 01R3 and 0096.
(blueprint: lem-sc-affine-open-kernel-conormal-sections).
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Compose the conormal equivalences and their unit formulas on abstract modules, so the
scalar calculation and witness elimination do not unfold the sheaf constructions. -/
private theorem affineOpen_conormal_transport_comp
    {R A B S : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing S]
    (r : R ≃+* A) (w : B ≃+* A) (ρ : A →+* S) (I : Ideal R)
    {C D H Q : Type*} [AddCommGroup C] [Module B C] [AddCommGroup D] [Module S D]
    (κ : H → A) (κ' : Q → B) (η : H → D) (η' : Q → C)
    (hc : ∃ c : LinearEquiv (r.trans w.symm : R →+* B)
        (σ' := ((r.trans w.symm).symm : B →+* R)) I.Cotangent C,
      ∀ (a : I) (t : Q), κ' t = (r.trans w.symm) (a : R) →
        c (I.toCotangent a) = η' t)
    (hd : letI : Module B D := Module.compHom _ (ρ.comp w.toRingHom)
      ∃ d : C ≃ₗ[B] D, ∀ s : H, ∃ t : Q,
        κ' t = w.symm (κ s) ∧ d (η' t) = η s) :
    letI : Module R D := Module.compHom _ (ρ.comp r.toRingHom)
    ∃ e : I.Cotangent ≃ₗ[R] D, ∀ (a : I) (s : H),
      κ s = r (a : R) → e (I.toCotangent a) = η s := by
  let : Module B D := Module.compHom _ (ρ.comp w.toRingHom)
  obtain ⟨c, hc⟩ := hc
  obtain ⟨d, hd⟩ := hd
  let : Module R D := Module.compHom _ (ρ.comp r.toRingHom)
  let e : I.Cotangent ≃ₗ[R] D :=
    { c.toAddEquiv.trans d.toAddEquiv with
      map_smul' := by
        intro a x
        change d (c (a • x)) = a • d (c x)
        refine (congrArg d (c.map_smulₛₗ a x)).trans
          ((d.map_smul ((r.trans w.symm) a) (c x)).trans ?_)
        change ρ (w (w.symm (r a))) • d (c x) = ρ (r a) • d (c x)
        exact congrArg (fun b ↦ ρ b • d (c x)) (w.apply_symm_apply (r a)) }
  refine ⟨e, ?_⟩
  intro a s hs
  obtain ⟨t, ht, hu⟩ := hd s
  exact (congrArg d (hc a t (ht.trans (congrArg w.symm hs)))).trans hu

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual kernel conormal on an affine closed chart, with its original unit.
Source: Stacks Project, Tag 01R3 (1), (2), and Tag 0096.
(blueprint: lem-sc-affine-open-kernel-conormal-sections).

Proof: Restrict g to i : U → W. The preimage equality gives a Cartesian square
with the two open inclusions. The section map of i is the displayed map, after
identifying global sections of the open subschemes with sections on the opens.
Its surjectivity makes i a closed immersion, since both charts are affine.
Open restriction preserves kernels: on an open T of W, the original structure
module map and i's structure module map are identified by the section maps of
the open inclusions; their kernels and inclusions therefore agree. The kernel
of the closed immersion is its ideal module, so the restricted actual kernel
is i.ker.toModules. Tensor pullback commutes with these restrictions. Indeed,
compose the inverse-image/direct-image adjunctions with extension of scalars;
the resulting left adjoints are canonically isomorphic. The canonical units
commute with the isomorphism: on a section s both are the sheafification of
1 ⊗ s, by the unit formula of exists_tensorPullbackAdjunction. Apply
affine_conormal_sections_existence to i on the top affine open of W, using
r followed by the inverse open-section isomorphism. Transport this equivalence
back across the open-section and kernel identifications. Its unit formula is
the displayed restriction of the original unit. Scalars act through g.appLE
composed with r, giving R-linearity. Different inclusion proofs give identical
maps by proof irrelevance. Empty charts reduce to the same zero-module maps. -/
theorem affineOpen_kernel_conormal_sections {X Y : Scheme.{u}} (g : X ⟶ Y)
    (W : Y.affineOpens) (U : X.affineOpens)
    (h : U.1 ≤ g ⁻¹ᵁ W.1) (hpre : g ⁻¹ᵁ W.1 = U.1)
    (R : Type v) [CommRing R] (r : R ≃+* Γ(Y, W.1)) (I : Ideal R)
    (hI : I = RingHom.ker ((g.appLE W.1 U.1 h).hom.comp r.toRingHom))
    (hsurj : Function.Surjective ((g.appLE W.1 U.1 h).hom.comp r.toRingHom)) :
    let K := kernel (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)
    let N := (tensorPullback g).obj K
    letI : Module R Γ(N, U.1) :=
      Module.compHom _ ((g.appLE W.1 U.1 h).hom.comp r.toRingHom)
    ∃ e : I.Cotangent ≃ₗ[R] Γ(N, U.1),
      ∀ (a : I) (s : Γ(K, W.1)),
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          g.toRingCatSheafHom)).val.app (op W.1) s = r a →
        e (I.toCotangent a) =
          N.presheaf.map (homOfLE h).op
            (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app K).val.app
              (op W.1) s) := by
  classical
  let i := g.resLE W.1 U.1 h
  let w := W.1.topIso.commRingCatIsoToRingEquiv
  let r' := r.trans w.symm
  have : IsAffine W.1.toScheme := W.2
  have : IsAffine U.1.toScheme := U.2
  have hiSurj : Function.Surjective i.appTop := by
    change Function.Surjective ((g.resLE W.1 U.1 h).app ⊤)
    rw [Scheme.Hom.resLE_app_top]
    intro b
    obtain ⟨a, ha⟩ := hsurj (U.1.topIso.hom b)
    refine ⟨r' a, ?_⟩
    change U.1.topIso.inv ((g.appLE W.1 U.1 h) (W.1.topIso.hom (r' a))) = b
    have hw : W.1.topIso.hom (r' a) = r a := w.apply_symm_apply _
    rw [hw]
    change U.1.topIso.inv _ = b
    rw [show (g.appLE W.1 U.1 h) (r a) = U.1.topIso.hom b from ha]
    exact Iso.hom_inv_id_apply _ _
  have : IsClosedImmersion i := IsClosedImmersion.of_surjective_of_isAffine i hiSurj
  have hI' : I = RingHom.ker ((i.app ⊤).hom.comp r'.toRingHom) := by
    rw [hI]
    apply Ideal.ext
    intro a
    simp only [RingHom.mem_ker, RingHom.comp_apply]
    change (g.appLE W.1 U.1 h) (r a) = 0 ↔ i.app ⊤ (r' a) = 0
    rw [show i.app ⊤ = W.1.topIso.hom ≫ g.appLE W.1 U.1 h ≫ U.1.topIso.inv from
      Scheme.Hom.resLE_app_top g h]
    change _ = 0 ↔ U.1.topIso.inv ((g.appLE W.1 U.1 h)
      (W.1.topIso.hom (r' a))) = 0
    rw [show W.1.topIso.hom (r' a) = r a from w.apply_symm_apply _]
    exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso U.1.topIso.inv).1).symm
  let K := kernel (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)
  let N := (tensorPullback g).obj K
  exact affineOpen_conormal_transport_comp r w (g.appLE W.1 U.1 h).hom I
    (C := Γ((pushforward i).obj ((tensorPullback i).obj i.ker.toModules), ⊤))
    (D := Γ(N, U.1)) (H := Γ(K, W.1)) (Q := Γ(i.ker.toModules, ⊤))
    (fun s ↦ (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      g.toRingCatSheafHom)).val.app (op W.1) s)
    (fun t ↦ i.ker.toModulesι.app ⊤ t)
    (fun s ↦ N.presheaf.map (homOfLE h).op
      (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app K).val.app
        (op W.1) s))
    (fun t ↦ ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app
      i.ker.toModules).app ⊤ t)
    (affine_conormal_sections_existence i ⟨⊤, isAffineOpen_top _⟩ R r' I hI')
    (open_kernel_conormal_transport g W.1 U.1 h hpre)

end AlgebraicGeometry.Scheme.Modules
