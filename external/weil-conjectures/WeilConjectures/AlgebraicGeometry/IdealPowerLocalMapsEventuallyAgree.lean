/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import all WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.RingTheory.Support
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.FormalPolynomialPowerLifts
/-! # Eventual agreement of local ideal-power maps

Source: Stacks Project, Properties, Lemmas 01PM and 01PQ, injectivity arguments.
(blueprint: lem-weil-pbc-ideal-power-local-maps-eventually-agree).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private theorem powers_range {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [I.IsQuasicoherent]
    (V : X.affineOpens) (n : ℕ) :
    (LinearMap.range ((idealSheafPower ι n).2.val.app (op V.1)).hom :
      Ideal Γ(X, V.1)) =
      (LinearMap.range (ι.val.app (op V.1)).hom : Ideal Γ(X, V.1)) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => change LinearMap.range LinearMap.id = _; simp
  | one => simp [idealSheafPower]
  | more n _ ih =>
    have := Modules.powers_qc ι (n + 1)
    change LinearMap.range
      (((idealSheafPower ι (n + 1)).2.val.app (op V.1)).hom.comp
        ((idealModuleProductι ι (idealSheafPower ι (n + 1)).1).val.app (op V.1)).hom) = _
    rw [LinearMap.range_comp]
    have hr : LinearMap.range ((idealModuleProductι ι
        (idealSheafPower ι (n + 1)).1).val.app (op V.1)).hom =
        (LinearMap.range (ι.val.app (op V.1)).hom : Ideal Γ(X, V.1)) •
          (⊤ : Submodule Γ(X, V.1) Γ((idealSheafPower ι (n + 1)).1, V.1)) :=
      SetLike.coe_injective (Modules.multiplication_range ι
        (idealSheafPower ι (n + 1)).1 V)
    rw [hr, Submodule.map_smul'', Submodule.map_top, ih, Ideal.smul_eq_mul]
    change (LinearMap.range (ι.val.app (op V.1)).hom : Ideal Γ(X, V.1)) *
      (LinearMap.range (ι.val.app (op V.1)).hom : Ideal Γ(X, V.1)) ^ (n + 1) =
      (LinearMap.range (ι.val.app (op V.1)).hom : Ideal Γ(X, V.1)) ^ (n + 2)
    exact (pow_succ' _ _).symm

set_option backward.isDefEq.respectTransparency false in
private theorem basicOpen_le_surjective_stalk {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    (V : X.Opens) (f : Γ(X, V))
    (hf : f ∈ LinearMap.range (ι.val.app (op V)).hom)
    (U : X.Opens) (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom) :
    X.basicOpen f ≤ U := by
  intro x hx
  have hxV : x ∈ V := X.basicOpen_le f hx
  obtain ⟨s, hs⟩ := hf
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  obtain ⟨e, he, _⟩ := ideal_module_product_stalk ι
    (SheafOfModules.unit X.ringCatSheaf) x
  let t : S.obj I := TopCat.Presheaf.germ I.val.presheaf V x hxV s
  have ht : e.hom ((S.map ι).hom t) = X.presheaf.germ V x hxV f := by
    dsimp [t, S]
    change e.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf _).map ι.val)
        (TopCat.Presheaf.germ I.val.presheaf V x hxV s)) = _
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    exact (he V hxV _).trans (congrArg (fun a ↦ X.presheaf.germ V x hxV a) hs)
  have hu : IsUnit (X.presheaf.germ V x hxV f) := (X.mem_basicOpen f x hxV).mp hx
  apply (hU x).mpr
  intro y
  have hy : e.hom y = (e.hom y * ↑hu.unit⁻¹) * X.presheaf.germ V x hxV f := by
    calc
      _ = e.hom y * (↑hu.unit⁻¹ * ↑hu.unit) := by simp
      _ = _ := by simp only [hu.unit_spec, mul_assoc]
  refine ⟨(e.hom y * ↑hu.unit⁻¹) • t, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  rw [map_smul, map_smul]
  change (e.hom y * ↑hu.unit⁻¹) * e.hom ((S.map ι).hom t) = e.hom y
  rw [ht]
  exact hy.symm

set_option backward.isDefEq.respectTransparency false in
private theorem app_res {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) {U W : X.Opens} (i : W ⟶ U) (s : Γ(M, U)) :
    f.app W (M.presheaf.map i.op s) = N.presheaf.map i.op (f.app U s) :=
  PresheafOfModules.naturality_apply f.val i.op s

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
private theorem local_app_res {X : Scheme.{u}} {M N : X.Modules}
    {T A W : X.Opens} (φ : M.over T ⟶ N.over T)
    (hAT : A ≤ T) (hWA : W ≤ A) (s : Γ(M, A)) :
    φ.val.app (op (Over.mk (homOfLE (hWA.trans hAT))))
        (M.presheaf.map (homOfLE hWA).op s) =
      N.presheaf.map (homOfLE hWA).op
        (φ.val.app (op (Over.mk (homOfLE hAT))) s) := by
  exact PresheafOfModules.naturality_apply φ.val
    (Over.homMk (homOfLE hWA) :
      Over.mk (homOfLE (hWA.trans hAT)) ⟶ Over.mk (homOfLE hAT)).op s

set_option backward.isDefEq.respectTransparency false in
private theorem local_affine_zero {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] {T : X.Opens} (φ : M.over T ⟶ N.over T)
    (A : X.affineOpens) (hAT : A.1 ≤ T)
    (hφ : ∀ s : Γ(M, A.1), φ.val.app (op (Over.mk (homOfLE hAT))) s = 0) :
    ∀ (W : X.Opens) (hWA : W ≤ A.1),
      φ.val.app (op (Over.mk (homOfLE (hWA.trans hAT)))) = 0 := by
  have hb (g : Γ(X, A.1)) (s : Γ(M, X.basicOpen g)) :
      φ.val.app (op (Over.mk (homOfLE ((X.basicOpen_le g).trans hAT)))) s = 0 := by
    obtain ⟨k, t, ht⟩ := Modules.exists_map_eq_pow_smul_of_isAffineOpen M A.2 g s
    have h := congrArg
      (fun z ↦ φ.val.app (op (Over.mk
        (homOfLE ((X.basicOpen_le g).trans hAT)))) z) ht
    rw [map_smul, local_app_res φ hAT, hφ, map_zero] at h
    have hu := X.toRingedSpace.isUnit_res_basicOpen g
    exact (hu.pow k).smul_left_cancel.mp (h.symm.trans (smul_zero _).symm)
  intro W hWA
  ext s
  let B := {g : Γ(X, A.1) // X.basicOpen g ≤ W}
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun i : B ↦ X.basicOpen i.1) W (fun i ↦ homOfLE i.2) ?_ _ _ ?_
  · intro x hx
    obtain ⟨g, hg, hxg⟩ := A.2.exists_basicOpen_le ⟨x, hx⟩ (hWA hx)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hg⟩, hxg⟩
  · intro i
    change N.presheaf.map (homOfLE i.2).op
      (φ.val.app (op (Over.mk (homOfLE (hWA.trans hAT)))) s) =
      N.presheaf.map (homOfLE i.2).op (0 : Γ(N, W))
    rw [← local_app_res φ (hWA.trans hAT), map_zero]
    exact hb i.1 _

set_option backward.isDefEq.respectTransparency false in
-- Allow elaboration of repeated restrictions to the over-site.
private theorem local_affine_eventually_zero
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (one : ∀ n : ℕ, Γ((idealSheafPower ι n).1, U))
    (r : ∀ (n m : ℕ), n ≤ m →
      ((idealSheafPower ι m).1 ⟶ (idealSheafPower ι n).1))
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
    (hone : ∀ n : ℕ, (idealSheafPower ι n).2.app U (one n) = (1 : Γ(X, U)))
    (hr : ∀ (n m : ℕ) (h : n ≤ m),
      r n m h ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2)
    (T : X.Opens) (A : X.affineOpens) (hAT : A.1 ≤ T) (n : ℕ)
    (φ : ((idealSheafPower ι n).1).over T ⟶ F.over T)
    (hφ : ∀ (W : X.Opens) (hWU : W ≤ U) (hWT : W ≤ T),
      φ.val.app (op (Over.mk (homOfLE hWT)))
        (((idealSheafPower ι n).1).presheaf.map (homOfLE hWU).op (one n)) = 0) :
    ∃ (m : ℕ) (h : n ≤ m), ∀ (W : X.Opens) (hWA : W ≤ A.1),
      (r n m h).val.app (op W) ≫
        φ.val.app (op (Over.mk (homOfLE (hWA.trans hAT)))) = 0 := by
  let J : Ideal Γ(X, A.1) := LinearMap.range (ι.val.app (op A.1)).hom
  let ψ : Γ((idealSheafPower ι n).1, A.1) →ₗ[Γ(X, A.1)] Γ(F, A.1) :=
    (φ.val.app (op (Over.mk (homOfLE hAT)))).hom
  have : Module.Finite Γ(X, A.1) Γ(I, A.1) := Modules.finite_sections_of_finiteType I A.2
  let i : Γ(I, A.1) →ₗ[Γ(X, A.1)] Γ(X, A.1) := (ι.val.app (op A.1)).hom
  have hfg : J.FG := Submodule.fg_range i
  have : Module.Finite Γ(X, A.1) Γ((idealSheafPower ι n).1, A.1) := by
    apply Module.Finite.of_fg_top
    apply Submodule.fg_of_fg_map_injective
      ((idealSheafPower ι n).2.val.app (op A.1)).hom
      (formalPolynomial_power_injective ι n A.1)
    rw [Submodule.map_top, powers_range ι A n]
    exact hfg.pow
  have : Module.Finite Γ(X, A.1) (LinearMap.range ψ) :=
    Module.Finite.of_fg (Submodule.fg_range ψ)
  have hrad : J ≤ (LinearMap.range ψ).annihilator.radical := by
    intro f hf
    apply mem_radical_annihilator_of_pow_torsion f
    intro y
    have hBU := basicOpen_le_surjective_stalk ι A.1 f hf U hU
    have hBT := (X.basicOpen_le f).trans hAT
    let oneB : Γ((idealSheafPower ι n).1, X.basicOpen f) :=
      (idealSheafPower ι n).1.presheaf.map (homOfLE hBU).op (one n)
    have hj : (idealSheafPower ι n).2.app (X.basicOpen f) oneB =
        (1 : Γ(X, X.basicOpen f)) := by
      dsimp [oneB]
      rw [app_res, hone]
      exact map_one (X.presheaf.map (homOfLE hBU).op).hom
    have hz (s : Γ((idealSheafPower ι n).1, X.basicOpen f)) :
        φ.val.app (op (Over.mk (homOfLE hBT))) s = 0 := by
      let j : Γ((idealSheafPower ι n).1, X.basicOpen f) →ₗ[Γ(X, X.basicOpen f)]
          Γ(X, X.basicOpen f) :=
        ((idealSheafPower ι n).2.val.app (op (X.basicOpen f))).hom
      have hs : s = j s • oneB := by
        apply formalPolynomial_power_injective ι n (X.basicOpen f)
        change j s = j (j s • oneB)
        have hj' : j oneB = 1 := hj
        rw [map_smul, hj']
        exact (mul_one _).symm
      rw [hs, map_smul, hφ (X.basicOpen f) hBU hBT, smul_zero]
    have hy : F.presheaf.map (homOfLE (X.basicOpen_le f)).op y.val = 0 := by
      obtain ⟨s, hs⟩ := y.property
      rw [← hs]
      change F.presheaf.map (homOfLE (X.basicOpen_le f)).op
        (φ.val.app (op (Over.mk (homOfLE hAT))) s) = 0
      rw [← local_app_res φ hAT]
      exact hz _
    obtain ⟨k, hk⟩ := Modules.exists_pow_smul_eq_zero_of_isAffineOpen F A.2 f y.val hy
    exact ⟨k, Subtype.ext hk⟩
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hfg
  have hnm : n ≤ n + k := Nat.le_add_right n k
  have hrange : LinearMap.range ((r n (n + k) hnm).val.app (op A.1)).hom ≤
      J ^ k • (⊤ : Submodule Γ(X, A.1) Γ((idealSheafPower ι n).1, A.1)) := by
    intro t ht
    obtain ⟨s, rfl⟩ := ht
    let j := ((idealSheafPower ι n).2.val.app (op A.1)).hom
    have hinj := formalPolynomial_power_injective ι n A.1
    have hmap : Submodule.map j
        (J ^ k • (⊤ : Submodule Γ(X, A.1) Γ((idealSheafPower ι n).1, A.1))) =
        J ^ (n + k) := by
      rw [Submodule.map_smul'', Submodule.map_top, powers_range ι A n,
        Ideal.smul_eq_mul, ← pow_add, Nat.add_comm k n]
    have hmem : j (((r n (n + k) hnm).val.app (op A.1)).hom s) ∈ J ^ (n + k) := by
      have he := congrArg (fun f ↦ f.app A.1 s) (hr n (n + k) hnm)
      change (r n (n + k) hnm ≫ (idealSheafPower ι n).2).app A.1 s ∈ _
      rw [he]
      exact powers_range ι A (n + k) ▸ LinearMap.mem_range_self _ s
    rw [← hmap] at hmem
    obtain ⟨t, ht, he⟩ := hmem
    exact hinj he ▸ ht
  let χ := (r n (n + k) hnm).over T ≫ φ
  have hzero : ∀ s : Γ((idealSheafPower ι (n + k)).1, A.1),
      χ.val.app (op (Over.mk (homOfLE hAT))) s = 0 := by
    intro s
    have hmem := hrange (LinearMap.mem_range_self
      ((r n (n + k) hnm).val.app (op A.1)).hom s)
    have hker : J ^ k • (⊤ : Submodule Γ(X, A.1)
        Γ((idealSheafPower ι n).1, A.1)) ≤ LinearMap.ker ψ := by
      apply Submodule.smul_le.mpr
      intro a ha t _
      change ψ (a • t) = 0
      rw [map_smul]
      exact Submodule.mem_annihilator.mp (hk ha) _ (LinearMap.mem_range_self ψ t)
    exact hker hmem
  have := Modules.powers_qc ι (n + k)
  exact ⟨n + k, hnm, local_affine_zero χ A hAT hzero⟩

private theorem exists_overlap_difference {X : Scheme.{u}} {M N : X.Modules}
    {V V' : X.Opens} (α : M.over V ⟶ N.over V) (β : M.over V' ⟶ N.over V') :
    ∃ φ : M.over (V ⊓ V') ⟶ N.over (V ⊓ V'),
      ∀ (W : X.Opens) (hWT : W ≤ V ⊓ V'),
        φ.val.app (op (Over.mk (homOfLE hWT))) =
          (show M.val.obj (op W) ⟶ N.val.obj (op W) from
            α.val.app (op (Over.mk (homOfLE (hWT.trans inf_le_left))))) -
          (show M.val.obj (op W) ⟶ N.val.obj (op W) from
            β.val.app (op (Over.mk (homOfLE (hWT.trans inf_le_right))))) := by
  let a : M.over (V ⊓ V') ⟶ N.over (V ⊓ V') :=
    (SheafOfModules.overMap X.ringCatSheaf
      (homOfLE inf_le_left : V ⊓ V' ⟶ V)).map α
  let b : M.over (V ⊓ V') ⟶ N.over (V ⊓ V') :=
    (SheafOfModules.overMap X.ringCatSheaf
      (homOfLE inf_le_right : V ⊓ V' ⟶ V')).map β
  exact ⟨a - b, fun _ _ ↦ rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- Two local maps with equal evaluation agree on a sufficiently high ideal power
on their quasi-compact overlap. No lifting or quotient construction is asserted.

Source: Stacks Project, Properties, Lemma 01PM (injectivity) and Lemma 01PQ
(finite covering argument).
(blueprint: lem-weil-pbc-ideal-power-local-maps-eventually-agree).

Proof: Restrict both maps to V intersect V' and subtract them. Cover this
quasi-compact open by finitely many affine opens. On each, write I as a finitely
generated ideal J=(f_1,...,f_t) and F=M~. The difference is a linear map
J^n -> M by the affine tilde/Gamma equivalence. On D(f_i), heval says that its
value on f_i^n divided by f_i^n is zero, since one n is the unique preimage
of the unit under the monic power inclusion. Localization therefore gives
f_i^k_i phi(f_i^n)=0. Choose one k for all i, with n+k positive. Linearity
shows phi(f_i^(n+k))=0. Every monomial of degree t*(n+k-1)+1 contains one
such factor, so phi kills that power. Enlarge the degree to at least n.
If J=0, use any positive degree at least n. Take the maximum of the degrees
on the finite cover (and n). The equations hr and monicity of the power
inclusions identify all r with the genuine inclusions and give their
composition law; restriction to the maximum preserves vanishing. Sheaf
separation now makes the two restricted maps equal on the whole overlap,
hence on every W contained in it. An empty overlap needs no affine opens
and the same separation argument works at degree n. -/
theorem ideal_power_local_maps_eventually_agree
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (one : ∀ n : ℕ, Γ((idealSheafPower ι n).1, U))
    (r : ∀ (n m : ℕ), n ≤ m →
      ((idealSheafPower ι m).1 ⟶ (idealSheafPower ι n).1))
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
    (hone : ∀ n : ℕ, (idealSheafPower ι n).2.app U (one n) = (1 : Γ(X, U)))
    (hr : ∀ (n m : ℕ) (h : n ≤ m),
      r n m h ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2)
    (V V' : X.Opens) (hcompact : IsCompact ((V : Set X) ∩ (V' : Set X)))
    (n : ℕ)
    (α : ((idealSheafPower ι n).1).over V ⟶ F.over V)
    (β : ((idealSheafPower ι n).1).over V' ⟶ F.over V')
    (heval : ∀ (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V) (hWV' : W ≤ V'),
      α.val.app (op (Over.mk (homOfLE hWV)))
          (((idealSheafPower ι n).1).presheaf.map (homOfLE hWU).op (one n)) =
        β.val.app (op (Over.mk (homOfLE hWV')))
          (((idealSheafPower ι n).1).presheaf.map (homOfLE hWU).op (one n))) :
    ∃ (m : ℕ) (h : n ≤ m),
      ∀ (W : X.Opens) (hWV : W ≤ V) (hWV' : W ≤ V'),
        (r n m h).val.app (op W) ≫ α.val.app (op (Over.mk (homOfLE hWV))) =
          (r n m h).val.app (op W) ≫ β.val.app (op (Over.mk (homOfLE hWV'))) := by
  classical
  let T := V ⊓ V'
  obtain ⟨φ, hφapp⟩ := exists_overlap_difference α β
  have hφ (W : X.Opens) (hWU : W ≤ U) (hWT : W ≤ T) :
      φ.val.app (op (Over.mk (homOfLE hWT)))
        (((idealSheafPower ι n).1).presheaf.map (homOfLE hWU).op (one n)) = 0 := by
    rw [hφapp]
    exact sub_eq_zero.mpr (heval W hWU _ _)
  obtain ⟨S, hfin, hcover⟩ :=
    isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
      ⟨hcompact, T.isOpen⟩
  have hAT (A : S) : A.1.1 ≤ T := by
    intro x hx
    change x ∈ (V : Set X) ∩ (V' : Set X)
    rw [hcover]
    exact Set.mem_iUnion.mpr ⟨A.1, Set.mem_iUnion.mpr ⟨A.2, hx⟩⟩
  have hcover' : (⨆ A : S, A.1.1) = T := by
    ext x
    simpa [T] using (Set.ext_iff.mp hcover x).symm
  have hlocal (A : S) :=
    local_affine_eventually_zero ι F U one r hU hone hr T A.1 (hAT A) n φ hφ
  choose k hk hzero using hlocal
  have := hfin.to_subtype
  let := Fintype.ofFinite S
  let m := max n (Finset.univ.sup k)
  have hnm : n ≤ m := le_max_left _ _
  have hzlocal (A : S) (W : X.Opens) (hWA : W ≤ A.1.1) :
      (r n m hnm).val.app (op W) ≫
        φ.val.app (op (Over.mk (homOfLE (hWA.trans (hAT A))))) = 0 := by
    have hkm : k A ≤ m := (Finset.le_sup (Finset.mem_univ A)).trans (le_max_right _ _)
    have : Mono (idealSheafPower ι n).2 := formalPolynomial_power_mono ι n
    have hcomp : r (k A) m hkm ≫ r n (k A) (hk A) = r n m hnm := by
      apply (cancel_mono (idealSheafPower ι n).2).mp
      rw [Category.assoc, hr, hr, hr]
    rw [← hcomp]
    change ((r (k A) m hkm).val.app (op W) ≫
      (r n (k A) (hk A)).val.app (op W)) ≫ _ = 0
    rw [Category.assoc, hzero A W hWA, comp_zero]
  have hz (W : X.Opens) (hWT : W ≤ T) :
      (r n m hnm).val.app (op W) ≫
        φ.val.app (op (Over.mk (homOfLE hWT))) = 0 := by
    let χ := (r n m hnm).over T ≫ φ
    change χ.val.app (op (Over.mk (homOfLE hWT))) = 0
    ext s
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨F.presheaf, F.isSheaf⟩
      (fun A : S ↦ W ⊓ A.1.1) W (fun _ ↦ homOfLE inf_le_left) ?_ _ _ ?_
    · rw [← inf_iSup_eq, hcover', inf_eq_left.mpr hWT]
    · intro A
      change F.presheaf.map (homOfLE inf_le_left).op
        (χ.val.app (op (Over.mk (homOfLE hWT))) s) =
        F.presheaf.map (homOfLE inf_le_left).op (0 : Γ(F, W))
      erw [← local_app_res χ hWT (inf_le_left : W ⊓ A.1.1 ≤ W), map_zero]
      have hh := ConcreteCategory.congr_hom (hzlocal A (W ⊓ A.1.1) inf_le_right)
        ((idealSheafPower ι m).1.presheaf.map (homOfLE inf_le_left).op s)
      exact hh
  refine ⟨m, hnm, ?_⟩
  intro W hWV hWV'
  have hh := hz W (le_inf hWV hWV')
  rw [hφapp, Preadditive.comp_sub] at hh
  exact sub_eq_zero.mp hh


end AlgebraicGeometry.Scheme
