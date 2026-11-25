/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.AlgebraicGeometry.AffineScheme

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.IdealPowerAffineDenominatorMap
import WeilConjectures.AlgebraicGeometry.AffineSectionLinearMapExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.AffineScheme
/-! # Affine lifting into ideal-power annihilator quotients

Source: Stacks Project, Properties, Lemmas 01PM and 01PQ.
(blueprint: lem-weil-pbc-ideal-power-quotient-affine-lifting-section).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- A section over the ideal complement has a lift on a single affine open.

Source: Stacks Project, Properties, Lemma 01PM (affine denominator construction)
and Lemma 01PQ (annihilator quotients).
(blueprint: lem-weil-pbc-ideal-power-quotient-affine-lifting-section).

Proof: Write V = Spec R, I|V = J~ with J finitely generated, and F|V = M~.
Finite generation of J^n identifies A_n|V with Ann_M(J^n)~: clearing a common
localization denominator for a finite set of generators proves this on principal
opens, and hann identifies the subsheaf. Thus Q_n|V = (M/Ann_M(J^n))~.
Choose J = (f_1,...,f_t). Its complement is the union of D(f_i). Represent s
there by x_i/f_i^k, with one positive k. Clear the finitely many overlap
relations with one exponent e, and replace x_i by f_i^e x_i and k by k+e,
so f_j^k x_i = f_i^k x_j in M. Put d = t*(k-1)+1 and
K = {x in M : f_i^k x = 0 for all i}. Every degree-d monomial contains f_i^k;
send it to the remaining monomial times x_i modulo K. For any relation,
multiplication of its image by f_j^k is the original relation times x_j,
hence zero. This proves independence of the chosen factor and of all relations,
giving a linear map J^d -> M/K. The same monomial bound gives
K <= Ann_M(J^d), so compose into M/Ann_M(J^d). On D(f_i), linearity gives
phi(f_i^d)/f_i^d = x_i/f_i^k; for t positive the bound d is at least k.
The affine tilde functor produces
the local sheaf morphism. The section one d maps to 1 under j_d, hence equals
the localized unit; naturality gives the displayed identity on every W.
For J=0 the complement is empty; use d=1 and the zero map. The empty affine
open is covered by this case. For J=R, degree zero and the section map work.

Formal reduction: ideal_power_affine_denominator_map supplies a section map
P_n(V) -> F(V)/K with K contained in the image of a_n(V). Cokernel.condition
puts K in the kernel of the quotient projection, so Submodule.liftQ descends
that projection and gives P_n(V) -> Q_n(V). Extend this affine section map
using affine_section_linear_map_extension. The scalar formula holds on
restrictions of global affine sections. For a local section on D(r), the
proved affine localization lemma supplies c and k with c|D(r)=r^k b.
Naturality and linearity give the formula after multiplying by r^k; this is
a unit on D(r), so cancel it. Sheaf separation gives the formula on arbitrary
W inside U intersect V. Apply it to one n and use hone and naturality. -/
theorem ideal_power_quotient_affine_lifting_section
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (one : ∀ n : ℕ, Γ((idealSheafPower ι n).1, U))
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
    (hone : ∀ n : ℕ, (idealSheafPower ι n).2.app U (one n) = (1 : Γ(X, U)))
    (A : ℕ → X.Modules) (a : ∀ n : ℕ, A n ⟶ F)
    (hmono : ∀ n : ℕ, Mono (a n))
    (hqc : ∀ n : ℕ, (A n).IsQuasicoherent)
    (hann : ∀ (n : ℕ) (W : X.Opens) (s : Γ(F, W)),
      s ∈ Set.range ((a n).app W) ↔
        ∀ (W' : X.Opens) (h : W' ≤ W)
          (b : Γ((idealSheafPower ι n).1, W')),
          (F.smul (U := W') ((idealSheafPower ι n).2.val.app (op W') b)).asHom.hom
            (F.presheaf.map (homOfLE h).op s) = 0)
    (hquot : ∀ (n : ℕ) (W : X.Opens), W ≤ U →
      Function.Bijective ((cokernel.π (a n)).app W))
    (V : X.affineOpens) :
    ∀ s : Γ(F, U), ∃ (n : ℕ)
      (φ : ((idealSheafPower ι n).1).over V.1 ⟶ (cokernel (a n)).over V.1),
      ∀ (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V.1),
        (cokernel.π (a n)).app W (F.presheaf.map (homOfLE hWU).op s) =
          φ.val.app (op (Over.mk (homOfLE hWV)))
            (((idealSheafPower ι n).1).presheaf.map (homOfLE hWU).op (one n)) := by
  intro s
  obtain ⟨n, K, hP, hK, f, hf⟩ := ideal_power_affine_denominator_map
    ι F U hU A a hmono hqc hann hquot V s
  have := hP
  let π : Γ(F, V.1) →ₗ[Γ(X, V.1)] Γ(cokernel (a n), V.1) :=
    ((cokernel.π (a n)).val.app (op V.1)).hom
  have hker : K ≤ LinearMap.ker π := by
    intro x hx
    obtain ⟨y, hy⟩ := hK hx
    change π x = 0
    rw [← hy]
    have hz := congrArg (fun g : A n ⟶ cokernel (a n) => g.app V.1 y)
      (cokernel.condition (a n))
    exact hz
  let q : (Γ(F, V.1) ⧸ K) →ₗ[Γ(X, V.1)] Γ(cokernel (a n), V.1) :=
    K.liftQ π hker
  let g := q.comp f
  have hg (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V.1)
      (b : Γ((idealSheafPower ι n).1, V.1)) :
      (cokernel (a n)).presheaf.map (homOfLE hWV).op (g b) =
        ((cokernel (a n)).smul (U := W) ((idealSheafPower ι n).2.val.app (op W)
          (((idealSheafPower ι n).1).presheaf.map (homOfLE hWV).op b))).asHom.hom
          ((cokernel (a n)).presheaf.map (homOfLE hWU).op
            ((cokernel.π (a n)).app U s)) := by
    obtain ⟨x, hx⟩ := K.mkQ_surjective (f b)
    change (cokernel (a n)).presheaf.map (homOfLE hWV).op (q (f b)) = _
    rw [← hx]
    change (cokernel (a n)).presheaf.map (homOfLE hWV).op (π x) = _
    have hnat (T : X.Opens) (h : T ≤ U) :
        (cokernel.π (a n)).app T (F.presheaf.map (homOfLE h).op s) =
          (cokernel (a n)).presheaf.map (homOfLE h).op
            ((cokernel.π (a n)).app U s) :=
      congrArg (fun g => g s) ((cokernel.π (a n)).val.naturality
        (homOfLE h).op)
    have hnatV := congrArg (fun g => g x) ((cokernel.π (a n)).val.naturality
      (homOfLE hWV).op)
    change (cokernel.π (a n)).app W (F.presheaf.map (homOfLE hWV).op x) =
      (cokernel (a n)).presheaf.map (homOfLE hWV).op (π x) at hnatV
    rw [← hnatV]
    rw [← hnat W hWU]
    exact hf W hWU hWV b x hx.symm
  obtain ⟨φ, hφV⟩ := affine_section_linear_map_extension
    (idealSheafPower ι n).1 (cokernel (a n)) V g
  let P := (idealSheafPower ι n).1
  let Q := cokernel (a n)
  let j := (idealSheafPower ι n).2
  let sQ : Γ(Q, U) := (cokernel.π (a n)).app U s
  let app (W : X.Opens) (h : W ≤ V.1) : Γ(P, W) →ₗ[Γ(X, W)] Γ(Q, W) :=
    (φ.val.app (op (Over.mk (homOfLE h)))).hom
  change ∀ b : Γ(P, V.1), app V.1 (le_refl V.1) b = g b at hφV
  have app_nat (W T : X.Opens) (hWV : W ≤ V.1) (hTW : T ≤ W) (b : Γ(P, W)) :
      app T (hTW.trans hWV) (P.presheaf.map (homOfLE hTW).op b) =
        Q.presheaf.map (homOfLE hTW).op (app W hWV b) := by
    exact congrArg (fun f => f b) (φ.val.naturality
      (Over.homMk (homOfLE hTW) : Over.mk (homOfLE (hTW.trans hWV)) ⟶
        Over.mk (homOfLE hWV)).op)
  have hφ (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V.1) (b : Γ(P, W)) :
      app W hWV b =
        (Q.smul (U := W) (j.val.app (op W) b)).asHom.hom
          (Q.presheaf.map (homOfLE hWU).op sQ) := by
    apply TopCat.Presheaf.IsSheaf.section_ext (Modules.isSheaf Q)
    intro x hxW
    obtain ⟨r, hrW, hxr⟩ := V.2.exists_basicOpen_le ⟨x, hxW⟩ (hWV hxW)
    let D := X.basicOpen r
    have hDV : D ≤ V.1 := X.basicOpen_le r
    have hDU : D ≤ U := hrW.trans hWU
    let bD : Γ(P, D) := P.presheaf.map (homOfLE hrW).op b
    obtain ⟨k, c, hc⟩ := Modules.exists_map_eq_pow_smul_of_isAffineOpen P V.2 r bD
    change P.presheaf.map (homOfLE hDV).op c =
      X.presheaf.map (homOfLE hDV).op r ^ k • bD at hc
    refine ⟨D, hrW, hxr, ?_⟩
    have hglobal : app D hDV (P.presheaf.map (homOfLE hDV).op c) =
        (Q.smul (U := D) (j.val.app (op D)
          (P.presheaf.map (homOfLE hDV).op c))).asHom.hom
          (Q.presheaf.map (homOfLE hDU).op sQ) := by
      rw [app_nat V.1 D (le_refl V.1) hDV, hφV]
      exact hg D hDU hDV c
    have hu : IsUnit (X.presheaf.map (homOfLE hDV).op r ^ k) :=
      (X.toRingedSpace.isUnit_res_basicOpen r).pow k
    apply hu.smul_left_cancel.mp
    rw [← app_nat W D hWV hrW]
    simp only [Modules.smul_apply]
    rw [Modules.map_smul]
    have hjnat : j.val.app (op D) (P.presheaf.map (homOfLE hrW).op b) =
        X.presheaf.map (homOfLE hrW).op (j.val.app (op W) b) :=
      congrArg (fun f => f b) (j.val.naturality (homOfLE hrW).op)
    rw [← hjnat]
    have hs : Q.presheaf.map (homOfLE hrW).op
        (Q.presheaf.map (homOfLE hWU).op sQ) =
          Q.presheaf.map (homOfLE hDU).op sQ := by
      rw [← Functor.map_comp_apply]
      rfl
    rw [hs]
    change (X.presheaf.map (homOfLE hDV).op r ^ k) • app D hDV bD = _
    rw [← (app D hDV).map_smul, ← hc, hglobal]
    simp only [Modules.smul_apply]
    rw [hc]
    rw [(j.val.app (op D)).hom.map_smul]
    exact mul_smul _ _ _
  refine ⟨n, φ, ?_⟩
  intro W hWU hWV
  change (cokernel.π (a n)).app W (F.presheaf.map (homOfLE hWU).op s) =
    app W hWV (P.presheaf.map (homOfLE hWU).op (one n))
  rw [hφ W hWU hWV]
  have hunit := congrArg (fun g => g (one n))
    ((idealSheafPower ι n).2.val.naturality (homOfLE hWU).op)
  change (idealSheafPower ι n).2.val.app (op W)
      (((idealSheafPower ι n).1).presheaf.map (homOfLE hWU).op (one n)) =
    X.presheaf.map (homOfLE hWU).op ((idealSheafPower ι n).2.app U (one n))
    at hunit
  rw [hone n, map_one] at hunit
  rw [hunit]
  simp only [Modules.smul_apply, one_smul]
  exact congrArg (fun g => g s)
    ((cokernel.π (a n)).val.naturality (homOfLE hWU).op)


end AlgebraicGeometry.Scheme
