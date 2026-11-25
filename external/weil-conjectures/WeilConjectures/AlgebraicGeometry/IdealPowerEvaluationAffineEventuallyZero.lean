/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
import WeilConjectures.AlgebraicGeometry.FormalPolynomialPowerLifts
import all WeilConjectures.AlgebraicGeometry.AffineSectionCoverTwistGeneration
import all WeilConjectures.AlgebraicGeometry.CoherentAffineMapSupportRadical
import all WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine local vanishing of ideal-power evaluation

Source: Stacks Project, Properties, Lemma 01PM, injectivity argument, as used in 01PQ.
(blueprint: lem-weil-pbc-ideal-power-evaluation-affine-eventually-zero).
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

private theorem app_res {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) {U W : X.Opens} (i : W ⟶ U) (s : Γ(M, U)) :
    f.app W (M.presheaf.map i.op s) = N.presheaf.map i.op (f.app U s) :=
  PresheafOfModules.naturality_apply f.val i.op s

set_option backward.isDefEq.respectTransparency false in
private theorem evaluation_zero_on_open {X : Scheme.{u}} {I F : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    (n : ℕ) (φ : (idealSheafPower ι n).1 ⟶ F) (U W : X.Opens) (hWU : W ≤ U)
    (one : Γ((idealSheafPower ι n).1, U))
    (hone : (idealSheafPower ι n).2.app U one = (1 : Γ(X, U)))
    (hφ : φ.app U one = 0) (s : Γ((idealSheafPower ι n).1, W)) :
    φ.app W s = 0 := by
  let oneW : Γ((idealSheafPower ι n).1, W) :=
    (idealSheafPower ι n).1.presheaf.map (homOfLE hWU).op one
  have hj : (idealSheafPower ι n).2.app W oneW = (1 : Γ(X, W)) := by
    dsimp [oneW]
    rw [app_res, hone]
    exact map_one (X.presheaf.map (homOfLE hWU).op).hom
  have hp : φ.app W oneW = 0 := by
    dsimp [oneW]
    rw [app_res, hφ, map_zero]
  let j : Γ((idealSheafPower ι n).1, W) →ₗ[Γ(X, W)] Γ(X, W) :=
    ((idealSheafPower ι n).2.val.app (op W)).hom
  let a : Γ(X, W) := j s
  have hs : s = a • oneW := by
    apply formalPolynomial_power_injective ι n W
    change j s = j (a • oneW)
    have hj' : j oneW = 1 := hj
    rw [map_smul, hj']
    exact (mul_one a).symm
  rw [hs, Modules.Hom.app_smul, hp, smul_zero]

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
/-- The affine ideal is finitely generated, and evaluation vanishing forces it into
 the radical of the annihilator of the image of the affine section map.

Source: Stacks Project, Properties, Lemma 01PM, proof of injectivity, and 01PQ,
first proof paragraph.
(blueprint: lem-weil-pbc-ideal-power-evaluation-affine-eventually-zero).

Proof: put A = Gamma(V, O_X) and J = image(Gamma(V, I) -> A). Quasi-coherence
and finite type identify Gamma(V, I) with a finite A-module; its image J is
therefore finitely generated. On V every recursive power P_n is quasi-coherent,
its inclusion is monic with section image J^n, and J^n is finitely generated.
For any f in J, the basic open D(f) lies in U: at each point of D(f), the germ
of f belongs to the image ideal and is a unit, so the stalk inclusion is surjective.
On any open W contained in U, restrict the given section one to W. Its image
under the power inclusion is 1. Every section s of P_n on W equals j_n(s) times
this restricted section: apply the injective j_n and use linearity. Naturality
and the evaluation hypothesis thus show that phi vanishes on W, hence on D(f).
Choose finitely many generators of Gamma(V, P_n). Each image under phi restricts
to zero on D(f), so the localization zero criterion gives a power of f killing
it. The maximum of these finitely many exponents kills every generator image,
hence by linearity the entire image of phi on V. Thus f belongs to the radical
of its annihilator. This holds for every f in J. For an empty generating set the
image is zero and exponent zero suffices; for n=0 the power module is the unit.
The zero ring and empty affine open are covered by the same argument. -/
private theorem ideal_power_evaluation_affine_radical
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (n : ℕ) (one : Γ((idealSheafPower ι n).1, U))
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
    (hone : (idealSheafPower ι n).2.app U one = (1 : Γ(X, U)))
    (V : X.affineOpens) (φ : (idealSheafPower ι n).1 ⟶ F)
    (hφ : φ.app U one = 0) :
    let J : Ideal Γ(X, V.1) := LinearMap.range (ι.val.app (op V.1)).hom
    J.FG ∧ J ≤ (LinearMap.range (φ.val.app (op V.1)).hom).annihilator.radical := by
  let J : Ideal Γ(X, V.1) := LinearMap.range (ι.val.app (op V.1)).hom
  have : Module.Finite Γ(X, V.1) Γ(I, V.1) := Modules.finite_sections_of_finiteType I V.2
  let i : Γ(I, V.1) →ₗ[Γ(X, V.1)] Γ(X, V.1) := (ι.val.app (op V.1)).hom
  have hfg : J.FG := Submodule.fg_range i
  let j : Γ((idealSheafPower ι n).1, V.1) →ₗ[Γ(X, V.1)] Γ(X, V.1) :=
    ((idealSheafPower ι n).2.val.app (op V.1)).hom
  have : Module.Finite Γ(X, V.1) Γ((idealSheafPower ι n).1, V.1) := by
    apply Module.Finite.of_fg_top
    apply Submodule.fg_of_fg_map_injective j (formalPolynomial_power_injective ι n V.1)
    rw [Submodule.map_top, powers_range ι V n]
    exact hfg.pow
  let ψ : Γ((idealSheafPower ι n).1, V.1) →ₗ[Γ(X, V.1)] Γ(F, V.1) :=
    (φ.val.app (op V.1)).hom
  have : Module.Finite Γ(X, V.1) (LinearMap.range ψ) :=
    Module.Finite.of_fg (Submodule.fg_range ψ)
  refine ⟨hfg, ?_⟩
  intro f hf
  change f ∈ (LinearMap.range ψ).annihilator.radical
  apply AlgebraicGeometry.mem_radical_annihilator_of_pow_torsion f
  intro y
  have hWU : X.basicOpen f ≤ U := basicOpen_le_surjective_stalk ι V.1 f hf U hU
  have hy : F.presheaf.map (homOfLE (X.basicOpen_le f)).op y.val = 0 := by
    obtain ⟨s, hs⟩ := y.property
    rw [← hs]
    change F.presheaf.map (homOfLE (X.basicOpen_le f)).op (φ.app V.1 s) = 0
    rw [← app_res]
    exact evaluation_zero_on_open ι n φ U (X.basicOpen f) hWU one hone hφ _
  obtain ⟨k, hk⟩ := Modules.exists_pow_smul_eq_zero_of_isAffineOpen F V.2 f y.val hy
  exact ⟨k, Subtype.ext hk⟩


set_option backward.isDefEq.respectTransparency false in
private theorem affine_hom_zero {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] (V : X.affineOpens) (f : M ⟶ N)
    (hf : ∀ s : Γ(M, V.1), f.app V.1 s = 0) : f.over V.1 = 0 := by
  have hb (g : Γ(X, V.1)) (s : Γ(M, X.basicOpen g)) :
      f.app (X.basicOpen g) s = 0 := by
    obtain ⟨k, t, ht⟩ :=
      Modules.exists_map_eq_pow_smul_of_isAffineOpen M V.2 g s
    have h := congrArg (fun z ↦ f.app (X.basicOpen g) z) ht
    rw [Modules.Hom.app_smul, app_res, hf, map_zero] at h
    have hu : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom g) :=
      X.toRingedSpace.isUnit_res_basicOpen g
    exact (hu.pow k).smul_left_cancel.mp (h.symm.trans (smul_zero _).symm)
  apply SheafOfModules.hom_ext
  ext W s
  change f.app W.unop.left s = 0
  let T := {g : Γ(X, V.1) // X.basicOpen g ≤ W.unop.left}
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun i : T ↦ X.basicOpen i.1) W.unop.left
    (fun i ↦ homOfLE i.2) ?_ _ _ ?_
  · intro x hx
    obtain ⟨g, hg, hxg⟩ := V.2.exists_basicOpen_le ⟨x, hx⟩
      ((leOfHom W.unop.hom) hx)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hg⟩, hxg⟩
  · intro i
    rw [← app_res, map_zero]
    exact hb i.1 _

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation zero forces eventual vanishing on a single affine open. No compactness
of the ambient scheme is required.

Source: Stacks Project, Properties, Lemma 01PM, proof of injectivity, and Lemma 01PQ,
first proof paragraph.
(blueprint: lem-weil-pbc-ideal-power-evaluation-affine-eventually-zero).

Proof: On V put A = Γ(V, O_X) and let J be the image of the ideal inclusion on
sections. Tensor and image sections identify the section image of P_n with J^n,
including n = 0. Finite type makes J finitely generated; injectivity of the
power inclusion and finite generation of J^n make Gamma(P_n,V) finite over A.
For f in J, D(f) lies in U by the stalk description. The restricted section one n
maps to 1 under the injective power inclusion, so linearity and naturality make
phi zero on D(f). Localization then makes every element of the finite image of
phi_V killed by some power of f. The support-annihilator criterion gives
J contained in the radical of the image annihilator. Finite generation gives
k with J^k contained in that annihilator. Set m = n+k. Under the injective
power inclusion, J^k times Gamma(P_n,V) has image J^m; compatibility of r with
the power inclusions puts its section image in this multiple. Thus phi composed
with r is zero on sections over V. Clear denominators on basic opens using
quasi-coherence of P_m, then use sheaf separation on their covers of every
subopen of V to obtain the zero restricted morphism. This also covers the zero
ideal, the zero ring, the empty affine open, and n = 0. -/
theorem ideal_power_evaluation_affine_eventually_zero
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
      r n m h ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2) :
    ∀ (V : X.affineOpens) (n : ℕ) (φ : (idealSheafPower ι n).1 ⟶ F),
      φ.app U (one n) = 0 →
      ∃ (m : ℕ) (h : n ≤ m), (r n m h ≫ φ).over V.1 = 0 := by
  intro V n φ hφ
  let J : Ideal Γ(X, V.1) := LinearMap.range (ι.val.app (op V.1)).hom
  let ψ := (φ.val.app (op V.1)).hom
  obtain ⟨hfg, hrad⟩ :=
    ideal_power_evaluation_affine_radical ι F U n (one n) hU (hone n) V φ hφ
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hfg
  have hnm : n ≤ n + k := Nat.le_add_right n k
  have hrange : LinearMap.range ((r n (n + k) hnm).val.app (op V.1)).hom ≤
      J ^ k • (⊤ : Submodule Γ(X, V.1) Γ((idealSheafPower ι n).1, V.1)) := by
    intro t ht
    obtain ⟨s, rfl⟩ := ht
    let j := ((idealSheafPower ι n).2.val.app (op V.1)).hom
    have hinj := formalPolynomial_power_injective ι n V.1
    have hmap : Submodule.map j
        (J ^ k • (⊤ : Submodule Γ(X, V.1) Γ((idealSheafPower ι n).1, V.1))) =
        J ^ (n + k) := by
      rw [Submodule.map_smul'', Submodule.map_top, powers_range ι V n,
        Ideal.smul_eq_mul, ← pow_add, Nat.add_comm k n]
    have hmem : j (((r n (n + k) hnm).val.app (op V.1)).hom s) ∈ J ^ (n + k) := by
      have he := congrArg (fun f ↦ f.app V.1 s) (hr n (n + k) hnm)
      change (r n (n + k) hnm ≫ (idealSheafPower ι n).2).app V.1 s ∈ _
      rw [he]
      exact powers_range ι V (n + k) ▸ LinearMap.mem_range_self _ s
    rw [← hmap] at hmem
    obtain ⟨t, ht, he⟩ := hmem
    exact hinj he ▸ ht
  have hzero : ∀ s : Γ((idealSheafPower ι (n + k)).1, V.1),
      (r n (n + k) hnm ≫ φ).app V.1 s = 0 := by
    intro s
    have hmem := hrange (LinearMap.mem_range_self
      ((r n (n + k) hnm).val.app (op V.1)).hom s)
    have hker : J ^ k • (⊤ : Submodule Γ(X, V.1)
        Γ((idealSheafPower ι n).1, V.1)) ≤ LinearMap.ker ψ := by
      apply Submodule.smul_le.mpr
      intro a ha t _
      change ψ (a • t) = 0
      rw [map_smul]
      exact Submodule.mem_annihilator.mp (hk ha) _ (LinearMap.mem_range_self ψ t)
    exact hker hmem
  have := Modules.powers_qc ι (n + k)
  exact ⟨n + k, hnm, affine_hom_zero V _ hzero⟩

end AlgebraicGeometry.Scheme
