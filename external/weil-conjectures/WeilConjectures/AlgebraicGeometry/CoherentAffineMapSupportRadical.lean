/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import Mathlib.RingTheory.Support

/-! # Support of a coherent affine map invertible off a closed set

Source: Stacks Project, Lemma 01Y9 and the last paragraph of Lemma 088B.
(blueprint: lem-weil-pbc-coherent-affine-map-support-radical)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem mem_radical_annihilator_of_pow_torsion
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (a : R) (h : ∀ x : M, ∃ n : ℕ, a ^ n • x = 0) :
    a ∈ (Module.annihilator R M).radical := by
  have hz : Subsingleton (LocalizedModule.Away a M) :=
    LocalizedModule.subsingleton_iff.mpr fun x ↦ by
      obtain ⟨n, hn⟩ := h x
      exact ⟨a ^ n, ⟨n, rfl⟩, hn⟩
  have hs := LocalizedModule.subsingleton_iff_support_subset.mp hz
  rw [Module.support_eq_zeroLocus, ← PrimeSpectrum.zeroLocus_span {a}] at hs
  exact (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp hs
    (Ideal.subset_span (Set.mem_singleton a))

private theorem finite_spec_sections
    (R : Type u) [CommRing R] (A : CoherentModules (Spec (CommRingCat.of R))) :
    Module.Finite R ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj A.obj) := by
  have : Module.Finite Γ(Spec (CommRingCat.of R), ⊤) Γ(A.obj, ⊤) :=
    Scheme.Modules.coherent_affine_sections_finite _ _ A.property _ (isAffineOpen_top _)
  let e : Γ(A.obj, ⊤) →ₛₗ[(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom]
      ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj A.obj) :=
    { toFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by
        change r • x = ((Scheme.ΓSpecIso (CommRingCat.of R)).inv
          ((Scheme.ΓSpecIso (CommRingCat.of R)).hom r)) • x
        simp }
  exact Module.Finite.of_surjective e (fun x ↦ ⟨x, rfl⟩)

set_option backward.isDefEq.respectTransparency false in
private theorem bijective_app_of_restrict_iso
    {X : Scheme.{u}} {A D : X.Modules} (c : A ⟶ D) (V W : X.Opens) (hWV : W ≤ V)
    (hc : IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι V)).map c)) :
    Function.Bijective (c.val.app (Opposite.op W)) := by
  have hi : IsIso ((Scheme.Modules.overEquiv V).functor.map
      ((SheafOfModules.overFunctor X.ringCatSheaf V).map c)) :=
    (NatIso.isIso_map_iff (Scheme.Modules.overFunctorEquiv V) c).mpr hc
  have : IsIso ((SheafOfModules.overFunctor X.ringCatSheaf V).map c) :=
    isIso_of_reflects_iso _ (Scheme.Modules.overEquiv V).functor
  let W' : Over V := Over.mk (homOfLE hWV)
  let E := SheafOfModules.evaluation (X.ringCatSheaf.over V) (Opposite.op W')
  have := E.map_isIso ((SheafOfModules.overFunctor X.ringCatSheaf V).map c)
  exact ConcreteCategory.bijective_of_isIso
    (E.map ((SheafOfModules.overFunctor X.ringCatSheaf V).map c))

/-- A coherent map invertible outside V(L) has affine section kernel and cokernel
whose annihilator radicals contain L. This involves no formal system or proper map.

Source: Stacks Project, Lemma 01Y9, its affine support criterion (Algebra, Lemma 00L6),
and the last paragraph of Lemma 088B.
(blueprint: lem-weil-pbc-coherent-affine-map-support-radical)

Proof: Kernels and cokernels of coherent maps over the Noetherian Spec R are
coherent. Restriction to an open is exact. Thus the hypothesis makes both vanish
on the complement of V(L), so their supports lie in V(L). On an affine, sections
are exact on quasi-coherent modules, and identify these sheaf kernels and cokernels
with the linear kernel and quotient by the range of the section map. Coherence
makes these finite R-modules; their supports are V of their annihilators. The
zero-locus containment V(Ann) subset V(L) is equivalent to L subset radical(Ann).
The zero ring causes no exception: its spectrum and all modules are zero. L = 0
makes the asserted inclusions automatic, and L = top says c itself is invertible,
so both section kernel and cokernel are zero with unit annihilators.
-/
theorem coherentAffineMap_support_radical
    (R : Type u) [CommRing R] [IsNoetherianRing R] (L : Ideal R)
    (A D : CoherentModules (Spec (CommRingCat.of R))) (c : A.obj ⟶ D.obj)
    (hc : IsIso ((Scheme.Modules.restrictFunctor
      (Scheme.Opens.ι (Scheme.IdealSheafData.ofIdealTop
        (L.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).support.compl)).map c)) :
    L ≤ (Module.annihilator R
      (LinearMap.ker ((moduleSpecΓFunctor (R := CommRingCat.of R)).map c).hom)).radical ∧
    L ≤ (Module.annihilator R
      (((moduleSpecΓFunctor (R := CommRingCat.of R)).obj D.obj) ⧸
        LinearMap.range ((moduleSpecΓFunctor (R := CommRingCat.of R)).map c).hom)).radical :=
  by
    classical
    let X := Spec (CommRingCat.of R)
    let Q := Scheme.IdealSheafData.ofIdealTop
      (L.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    have : A.obj.IsQuasicoherent :=
      ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X A.obj).mp
        A.property).1
    have : D.obj.IsQuasicoherent :=
      ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X D.obj).mp
        D.property).1
    let S := modulesSpecToSheaf.obj A.obj
    let T := modulesSpecToSheaf.obj D.obj
    let φ := modulesSpecToSheaf.map c
    let v := ((moduleSpecΓFunctor (R := CommRingCat.of R)).map c).hom
    have : Module.Finite R ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj A.obj) :=
      finite_spec_sections R A
    have : Module.Finite R ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj D.obj) :=
      finite_spec_sections R D
    have hS : IsLocalizing S := (isIso_fromTildeΓ_iff_isLocalizing A.obj).mp
      (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent A.obj)
    have hT : IsLocalizing T := (isIso_fromTildeΓ_iff_isLocalizing D.obj).mp
      (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent D.obj)
    have hlocal (a : R) (ha : a ∈ L) :
        Function.Bijective (φ.hom.app (Opposite.op (PrimeSpectrum.basicOpen a))) := by
      have hWV : X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) ≤
          Q.support.compl := by
        intro x hx
        change x ∉ Q.support
        intro hq
        have hz : x ∈ X.zeroLocus
            (L.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom : Set Γ(X, ⊤)) := by
          change x ∈ (Q.support : Set X) at hq
          dsimp [Q] at hq
          rw [Scheme.IdealSheafData.coe_support_ofIdealTop] at hq
          exact hq
        exact (Scheme.mem_zeroLocus_iff X _ x).mp hz _ (Ideal.mem_map_of_mem _ ha) hx
      have hb := bijective_app_of_restrict_iso c Q.support.compl
        (X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) hWV hc
      rw [basicOpen_eq_of_affine] at hb
      exact hb
    constructor
    · intro a ha
      apply mem_radical_annihilator_of_pow_torsion a
      intro x
      let lS := (S.obj.map (homOfLE le_top : PrimeSpectrum.basicOpen a ⟶ ⊤).op).hom
      let lT := (T.obj.map (homOfLE le_top : PrimeSpectrum.basicOpen a ⟶ ⊤).op).hom
      have : IsLocalizedModule (Submonoid.powers a) lS := hS a
      have hz : lS x.val = 0 := by
        apply (hlocal a ha).1
        have hn := congrArg (fun k ↦ k x.val)
          (φ.hom.naturality (homOfLE le_top : PrimeSpectrum.basicOpen a ⟶ ⊤).op)
        change (φ.hom.app _) (lS x.val) = lT (v x.val) at hn
        rw [x.property, map_zero] at hn
        exact hn.trans (map_zero _).symm
      obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
        (IsLocalizedModule.eq_zero_iff (Submonoid.powers a) lS).mp hz
      exact ⟨n, Subtype.ext hn⟩
    · intro a ha
      apply mem_radical_annihilator_of_pow_torsion a
      intro q
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range v) q
      let lS := (S.obj.map (homOfLE le_top : PrimeSpectrum.basicOpen a ⟶ ⊤).op).hom
      let lT := (T.obj.map (homOfLE le_top : PrimeSpectrum.basicOpen a ⟶ ⊤).op).hom
      have : IsLocalizedModule (Submonoid.powers a) lS := hS a
      have : IsLocalizedModule (Submonoid.powers a) lT := hT a
      obtain ⟨z, hz⟩ := (hlocal a ha).2 (lT y)
      obtain ⟨⟨x, _, n, rfl⟩, hx⟩ := IsLocalizedModule.surj (Submonoid.powers a) lS z
      have hw : lT (a ^ n • y - v x) = 0 := by
        have hn := congrArg (fun k ↦ k x)
          (φ.hom.naturality (homOfLE le_top : PrimeSpectrum.basicOpen a ⟶ ⊤).op)
        change (φ.hom.app _) (lS x) = lT (v x) at hn
        change a ^ n • z = lS x at hx
        rw [map_sub, map_smul, ← hn, ← hx, map_smul, hz, sub_self]
      obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
        (IsLocalizedModule.eq_zero_iff (Submonoid.powers a) lT).mp hw
      refine ⟨k + n, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      refine ⟨a ^ k • x, ?_⟩
      change a ^ k • (a ^ n • y - v x) = 0 at hk
      rw [smul_sub, sub_eq_zero] at hk
      rw [map_smul, pow_add, mul_smul]
      exact hk.symm

end AlgebraicGeometry
