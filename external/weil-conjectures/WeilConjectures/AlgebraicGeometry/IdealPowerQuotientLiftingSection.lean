/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.IdealPowerQuotientAffineLiftingSection
import WeilConjectures.AlgebraicGeometry.IdealPowerLocalMapsEventuallyAgree
import WeilConjectures.AlgebraicGeometry.FormalPolynomialPowerLifts
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.Topology.GlueSheavesOfModules
import WeilConjectures.AlgebraicGeometry.IdealPowerEvaluationEventuallyZero
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings

/-! # Lifting sections into ideal-power annihilator quotients

Source: Stacks Project, Properties, Lemmas 01PQ and 01PM.
(blueprint: lem-weil-pbc-ideal-power-quotient-local-lifting-section).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem over_comp_over_app {X : Scheme.{u}} {M N P Q : X.Modules}
    (f : M ⟶ N) {V : X.Opens} (g : N.over V ⟶ P.over V) (h : P ⟶ Q)
    (W : X.Opens) (hWV : W ≤ V) :
    (f.over V ≫ g ≫ h.over V).val.app (op (Over.mk (homOfLE hWV))) =
      f.val.app (op W) ≫ g.val.app (op (Over.mk (homOfLE hWV))) ≫
        h.val.app (op W) := rfl

private theorem over_app_eq {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) {V : X.Opens} (W : X.Opens) (hWV : W ≤ V) :
    (f.over V).val.app (op (Over.mk (homOfLE hWV))) = f.val.app (op W) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every section on the ideal complement lifts into an ideal-power annihilator quotient.

Proof: On an affine open write I = (f_1,...,f_t) and F = M~. The condition hann
identifies A_n with Ann_M(I^n)~: localization commutes with this annihilator because
I^n is finitely generated. Hence the cokernel is (M/Ann_M(I^n))~.
Represent the section on D(f_i) as x_i/f_i^k with k positive. Equality on overlaps
means (f_i f_j)^e (f_j^k x_i - f_i^k x_j) = 0. A common e works for all pairs;
replace x_i by f_i^e x_i and k by k+e. Now f_j^k x_i = f_i^k x_j.
Put d = t*(k-1)+1 and K = {x : f_i^k x = 0 for every i}. A degree-d monomial
has an exponent at least k; lower that exponent by k and multiply by x_i.
Multiplication of any resulting relation by f_j^k gives the original relation
multiplied by x_j, so it lies in K. This defines I^d -> M/K, and K is contained
in Ann_M(I^d). The induced map into M/Ann_M(I^d) evaluates to the section.

Choose a finite affine cover of X and use these maps locally. Pass to one degree
using r and q; their equations over the inclusions and projections ensure that
evaluation still represents the same section. On each affine member of a finite
cover of a pairwise overlap, the difference has zero evaluation. Its target is
quasi-coherent by cokernel closure. Apply ideal_power_evaluation_eventually_zero
to this target, then compose with q to kill the difference at a later degree.
Take a common upper bound for the finitely many degrees. Naturality of r and q,
whose composition laws follow by cancellation of monic power inclusions and epic
cokernel projections, preserves the equalities. Glue the maps by sheaf descent;
sectionwise uniqueness proves the required evaluation identity. Quasi-separatedness
is used only for finite affine covers of overlaps. An empty cover uses the unique
zero map; if the ideal is zero use a positive power and the empty complement;
for the unit ideal take degree zero and the map corresponding to the section.

Source: Stacks Project, Properties, Lemma 01PM (affine denominator construction)
and Lemma 01PQ (finite affine gluing), https://stacks.math.columbia.edu/tag/01PM
and https://stacks.math.columbia.edu/tag/01PQ.
(blueprint: lem-weil-pbc-ideal-power-quotient-local-lifting-section). -/
theorem ideal_power_quotient_local_lifting_section
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType] [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (one : ∀ n : ℕ, Γ((idealSheafPower ι n).1, U))
    (r : ∀ (n m : ℕ), n ≤ m →
      ((idealSheafPower ι m).1 ⟶ (idealSheafPower ι n).1))
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
    (hone : ∀ n : ℕ, (idealSheafPower ι n).2.app U (one n) = (1 : Γ(X, U)))
    (hr : ∀ (n m : ℕ) (h : n ≤ m),
      r n m h ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2)
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
    (q : ∀ (n m : ℕ), n ≤ m → (cokernel (a n) ⟶ cokernel (a m)))
    (hq : ∀ (n m : ℕ) (h : n ≤ m),
      cokernel.π (a n) ≫ q n m h = cokernel.π (a m)) :
    ∀ s : Γ(F, U), ∃ (n : ℕ) (φ : (idealSheafPower ι n).1 ⟶ cokernel (a n)),
      (cokernel.π (a n)).app U s = φ.app U (one n) := by
  classical
  intro s
  have rcomp (n k m : ℕ) (hnk : n ≤ k) (hkm : k ≤ m) :
      r k m hkm ≫ r n k hnk = r n m (hnk.trans hkm) := by
    have := formalPolynomial_power_mono ι n
    apply (cancel_mono (idealSheafPower ι n).2).mp
    rw [Category.assoc, hr, hr, hr]
  have rone (n m : ℕ) (h : n ≤ m) (W : X.Opens) (hWU : W ≤ U) :
      (r n m h).val.app (op W)
          (((idealSheafPower ι m).1).presheaf.map (homOfLE hWU).op (one m)) =
        ((idealSheafPower ι n).1).presheaf.map (homOfLE hWU).op (one n) := by
    apply formalPolynomial_power_injective ι n W
    have he := congrArg (fun f ↦ f.val.app (op W)) (hr n m h)
    have hone' (k : ℕ) :
        (idealSheafPower ι k).2.val.app (op W)
            (((idealSheafPower ι k).1).presheaf.map (homOfLE hWU).op (one k)) =
          X.presheaf.map (homOfLE hWU).op (1 : Γ(X, U)) := by
      have hn := PresheafOfModules.naturality_apply
        (idealSheafPower ι k).2.val (homOfLE hWU).op (one k)
      exact hn.trans (congrArg (X.presheaf.map (homOfLE hWU).op) (hone k))
    change ((r n m h ≫ (idealSheafPower ι n).2).val.app (op W)) _ = _
    rw [he, hone', hone']
  obtain ⟨S, hfin, hcover⟩ :=
    isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
      ⟨isCompact_univ (X := X), isOpen_univ⟩
  have hcover' : (⨆ V : S, V.1.1) = ⊤ := by
    ext x
    simpa using (Set.ext_iff.mp hcover x).symm
  have := hfin.to_subtype
  let := Fintype.ofFinite S
  have hlift (V : S) := ideal_power_quotient_affine_lifting_section
    ι F U one hU hone A a hmono hqc hann hquot V.1 s
  choose k φ hφ using hlift
  let n := Finset.univ.sup k
  have hkn (V : S) : k V ≤ n := Finset.le_sup (Finset.mem_univ V)
  let α (V : S) : ((idealSheafPower ι n).1).over V.1.1 ⟶
      (cokernel (a n)).over V.1.1 :=
    (r (k V) n (hkn V)).over V.1.1 ≫ φ V ≫ (q (k V) n (hkn V)).over V.1.1
  have hα (V : S) (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V.1.1) :
      (α V).val.app (op (Over.mk (homOfLE hWV)))
          (((idealSheafPower ι n).1).presheaf.map (homOfLE hWU).op (one n)) =
        (cokernel.π (a n)).app W (F.presheaf.map (homOfLE hWU).op s) := by
    dsimp only [α]
    rw [over_comp_over_app]
    change (q (k V) n (hkn V)).val.app (op W)
      ((φ V).val.app (op (Over.mk (homOfLE hWV)))
        ((r (k V) n (hkn V)).val.app (op W) _)) = _
    rw [rone, ← hφ V W hWU hWV]
    exact congrArg (fun f ↦ f.app W (F.presheaf.map (homOfLE hWU).op s))
      (hq (k V) n (hkn V))
  have : (A n).IsQuasicoherent := hqc n
  have : (cokernel (a n)).IsQuasicoherent := Modules.isQuasicoherent_cokernel (a n)
  have hagree (V V' : S) := ideal_power_local_maps_eventually_agree
    ι (cokernel (a n)) U one r hU hone hr V.1.1 V'.1.1
    (QuasiSeparatedSpace.inter_isCompact _ _ V.1.1.isOpen V.1.2.isCompact
      V'.1.1.isOpen V'.1.2.isCompact) n (α V) (α V')
    (fun W hWU hWV hWV' ↦ (hα V W hWU hWV).trans (hα V' W hWU hWV').symm)
  choose l hnl hl using hagree
  let m := max n (Finset.univ.sup (fun p : S × S ↦ l p.1 p.2))
  have hnm : n ≤ m := le_max_left _ _
  let β (V : S) : ((idealSheafPower ι m).1).over V.1.1 ⟶
      (cokernel (a m)).over V.1.1 :=
    (r n m hnm).over V.1.1 ≫ α V ≫ (q n m hnm).over V.1.1
  have hβ (V V' : S) (W : X.Opens) (hWV : W ≤ V.1.1) (hWV' : W ≤ V'.1.1) :
      (β V).val.app (op (Over.mk (homOfLE hWV))) =
        (β V').val.app (op (Over.mk (homOfLE hWV'))) := by
    have hlm : l V V' ≤ m :=
      (show l V V' ≤ Finset.univ.sup (fun p : S × S ↦ l p.1 p.2) from
        Finset.le_sup (f := fun p : S × S ↦ l p.1 p.2)
          (Finset.mem_univ (V, V'))).trans (le_max_right _ _)
    have he : (r (l V V') m hlm).val.app (op W) ≫
        (r n (l V V') (hnl V V')).val.app (op W) = (r n m hnm).val.app (op W) :=
      congrArg (fun f ↦ f.val.app (op W)) (rcomp n (l V V') m (hnl V V') hlm)
    dsimp only [β]
    rw [over_comp_over_app (r n m hnm) (α V) (q n m hnm) W hWV,
      over_comp_over_app (r n m hnm) (α V') (q n m hnm) W hWV']
    rw [← he]
    rw [Category.assoc, Category.assoc]
    rw [← Category.assoc ((r n (l V V') (hnl V V')).val.app (op W)),
      hl V V' W hWV hWV', Category.assoc]
  obtain ⟨ψ, hψ, _⟩ := (glue_sheaves_of_modules X.toRingedSpace S
    (fun V ↦ V.1.1) hcover').1 _ _ β hβ
  refine ⟨m, ψ, ?_⟩
  let T : TopCat.Sheaf Ab X := ⟨(cokernel (a m)).presheaf, (cokernel (a m)).isSheaf⟩
  apply T.eq_of_locally_eq' (fun V : S ↦ U ⊓ V.1.1) U
    (fun V ↦ homOfLE inf_le_left)
    (by simp only [← inf_iSup_eq, hcover', inf_top_eq, le_refl])
  intro V
  have hp := PresheafOfModules.naturality_apply (cokernel.π (a m)).val
    (homOfLE (inf_le_left : U ⊓ V.1.1 ≤ U)).op s
  have hs := PresheafOfModules.naturality_apply ψ.val
    (homOfLE (inf_le_left : U ⊓ V.1.1 ≤ U)).op (one m)
  change (cokernel (a m)).presheaf.map (homOfLE inf_le_left).op
      ((cokernel.π (a m)).app U s) =
    (cokernel (a m)).presheaf.map (homOfLE inf_le_left).op (ψ.val.app (op U) (one m))
  apply hp.symm.trans
  apply Eq.trans _ hs
  have he := congrArg (fun f ↦ f.val.app
    (op (Over.mk (homOfLE (inf_le_right : U ⊓ V.1.1 ≤ V.1.1))))) (hψ V)
  rw [over_app_eq] at he
  change (cokernel.π (a m)).app (U ⊓ V.1.1)
      (F.presheaf.map (homOfLE inf_le_left).op s) =
    ψ.val.app (op (U ⊓ V.1.1))
      (((idealSheafPower ι m).1).presheaf.map (homOfLE inf_le_left).op (one m))
  rw [he]
  dsimp only [β]
  rw [over_comp_over_app]
  change _ = (q n m hnm).val.app (op (U ⊓ V.1.1))
    ((α V).val.app (op (Over.mk (homOfLE inf_le_right)))
      ((r n m hnm).val.app (op (U ⊓ V.1.1)) _))
  rw [rone, hα]
  exact (congrArg (fun f ↦ f.app (U ⊓ V.1.1)
    (F.presheaf.map (homOfLE inf_le_left).op s)) (hq n m hnm)).symm

end AlgebraicGeometry.Scheme
