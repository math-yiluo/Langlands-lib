/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.EtaleLocalFiniteAtPoint
import WeilConjectures.AlgebraicGeometry.FinitePiecePersistence
import WeilConjectures.AlgebraicGeometry.IsolatedFibrePointBaseChange

/-!
# Finitely many isolated fibre points become finite pieces after an elementary étale base change

Source: Stacks Project, More on Morphisms, Lemma 02LL, lines 11974--12011.
(blueprint: lem-weil-pbc-etale-local-finite-multiple-points-elementary)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
private theorem point_of_section_fromSpec
    {Y X : Scheme.{u}} (p : Y ⟶ X) (x : X)
    (a : Spec (X.residueField x) ⟶ Y) (ha : a ≫ p = X.fromSpecResidueField x) :
    IsIso (p.residueFieldMap (a (IsLocalRing.closedPoint (X.residueField x)))) := by
  let y := a (IsLocalRing.closedPoint (X.residueField x))
  have hp : p y = x := by
    simpa [y, Scheme.Hom.comp_apply] using
      congrArg (fun h : Spec (X.residueField x) ⟶ X ↦
        h (IsLocalRing.closedPoint (X.residueField x))) ha
  let : IsLocalHom (Scheme.stalkClosedPointTo a).hom :=
    Scheme.isLocalHom_stalkClosedPointTo a
  let b : Y.residueField y ⟶ X.residueField x :=
    Y.descResidueField (K := X.residueField x) (Scheme.stalkClosedPointTo a)
  have hb : Spec.map b ≫ Y.fromSpecResidueField y = a :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField _ _ _
  let c := (X.residueFieldCongr hp).inv ≫ p.residueFieldMap y
  have hc : c ≫ b = 𝟙 (X.residueField x) := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecResidueField x)).mp
    simp only [Spec.map_comp, Spec.map_id, Category.id_comp, Category.assoc]
    dsimp only [c]
    rw [Spec.map_comp, Category.assoc]
    rw [Scheme.residueFieldCongr_inv, Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Category.assoc, hb, ha]
  have : Mono b := ConcreteCategory.mono_of_injective b (RingHom.injective b.hom)
  have : IsSplitEpi b := ⟨⟨c, hc⟩⟩
  have : IsIso b := isIso_of_mono_of_isSplitEpi b
  have : IsIso (c ≫ b) := hc ▸ inferInstance
  have : IsIso c := (isIso_comp_right_iff c b).mp inferInstance
  have : IsIso (p.residueFieldMap y) := (isIso_comp_left_iff _ _).mp this
  exact this

private theorem elementary_pullback_point
    {X S U : Scheme.{u}} (f : X ⟶ S) (φ : U ⟶ S)
    (x : X) (t : U) (hxt : f x = φ t) [IsIso (φ.residueFieldMap t)] :
    ∃ z : ↥(pullback f φ), pullback.fst f φ z = x ∧
      pullback.snd f φ z = t ∧ IsIso ((pullback.fst f φ).residueFieldMap z) := by
  let b := (S.residueFieldCongr hxt).inv ≫ f.residueFieldMap x
  let a := Spec.map (inv (φ.residueFieldMap t) ≫ b) ≫ U.fromSpecResidueField t
  have ha : a ≫ φ = X.fromSpecResidueField x ≫ f := by
    dsimp only [a]
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Spec.map_comp_assoc]
    simp only [IsIso.hom_inv_id_assoc]
    simp only [b, Spec.map_comp, Category.assoc]
    rw [Scheme.residueFieldCongr_inv, Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  let l := pullback.lift (X.fromSpecResidueField x) a ha.symm
  let z := l (IsLocalRing.closedPoint (X.residueField x))
  have hz : pullback.fst f φ z = x := by
    simp [z, ← Scheme.Hom.comp_apply, l]
  have hres := point_of_section_fromSpec (pullback.fst f φ) x l
    (pullback.lift_fst _ _ _)
  have hzt : pullback.snd f φ z = t := by
    change (l ≫ pullback.snd f φ) (IsLocalRing.closedPoint (X.residueField x)) = t
    rw [pullback.lift_snd]
    simp [a]
  exact ⟨z, hz, hzt, hres⟩

private theorem transport_finite_open_piece
    {A B T P : Scheme.{u}} (e : A ≅ B) (q : A ⟶ T) (r : B ⟶ T)
    (p : A ⟶ P) (hq : e.hom ≫ r = q)
    (V : A.Opens) (v : V.toScheme) (t : T) (y : P)
    (hfin : IsFinite (V.ι ≫ q)) (hv : (V.ι ≫ q) v = t)
    (hunique : ∀ w : V.toScheme, (V.ι ≫ q) w = t → w = v)
    (hy : (V.ι ≫ p) v = y) (hres : IsIso ((V.ι ≫ p).residueFieldMap v)) :
    ∃ (W : B.Opens) (w : W.toScheme),
      IsFinite (W.ι ≫ r) ∧ (W.ι ≫ r) w = t ∧
      (∀ z : W.toScheme, (W.ι ≫ r) z = t → z = w) ∧
      (W.ι ≫ e.inv ≫ p) w = y ∧
      IsIso ((W.ι ≫ e.inv ≫ p).residueFieldMap w) ∧ W = e.hom ''ᵁ V := by
  let W := e.hom ''ᵁ V
  let d : V.toScheme ≅ W.toScheme := e.hom.isoImage V
  let w := d.hom v
  have hd : d.inv w = v := by simp [w, ← Scheme.Hom.comp_apply]
  have hq' : W.ι ≫ r = d.inv ≫ V.ι ≫ q := by
    apply (cancel_epi d.hom).mp
    simp [d, W, hq]
  have hp' : W.ι ≫ e.inv ≫ p = d.inv ≫ (V.ι ≫ p) := by
    apply (cancel_epi d.hom).mp
    simp [d, W]
  have := hfin
  have := hres
  refine ⟨W, w, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hq']
    infer_instance
  · rw [hq', Scheme.Hom.comp_apply, hd]
    exact hv
  · intro z hz
    apply d.inv.homeomorph.injective
    change d.inv z = d.inv w
    rw [hd]
    apply hunique
    simpa [hq', Scheme.Hom.comp_apply] using hz
  · rw [hp', Scheme.Hom.comp_apply, hd]
    exact hy
  · constructor
    · have : IsIso ((V.ι ≫ p).residueFieldMap (d.inv w)) := hd.symm ▸ hres
      rw [hp', Scheme.residueFieldMap_comp]
      infer_instance
    · rfl

/-- Finitely many isolated points of a fibre become finite pieces after an elementary étale
base change. Source: Stacks Project, More on Morphisms, Lemma 02LL, lines 11974--12011
(blueprint: lem-weil-pbc-etale-local-finite-multiple-points-elementary).

Proof (the six steps of the node, following Stacks 02LL):
1. Induct on `n`; the zero case uses `U = S`, the identity, and no opens.
2. In the successor case, construct a point of the pullback over the last `x` and the
   inductive point `t` directly from canonical residue-field spectrum maps. The pullback
   lift has first projection `x`, second projection `t`, and an isomorphic residue-field
   map, by the section-from-`Spec` split-field argument.
3. The second projection is locally of finite type, and the constructed point is isolated
   in its fibre by `lem-weil-pbc-isolated-fibre-point-base-change`.
4. Apply the one-point 02LK theorem and identify the iterated pullback with the pullback
   over the composite etale map using `pullbackLeftPullbackSndIso`.
5. Transport the new finite open across this isomorphism, preserving finiteness,
   uniqueness, the point, and the residue-field isomorphism.
6. Apply `lem-weil-pbc-elementary-etale-finite-piece-persistence` to all earlier opens and
   combine them with the transported last open.
-/
theorem exists_etale_local_finite_multiple_points_elementary
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (s : S) (n : ℕ) (x : Fin n → X) (hx : ∀ i, f (x i) = s)
    (hisolated : ∀ i, IsOpen ({f.asFiber (x i)} : Set (f.fiber (f (x i))))) :
    ∃ (U : Scheme.{u}) (φ : U ⟶ S) (u : U),
      Etale φ ∧ φ u = s ∧ IsIso (φ.residueFieldMap u) ∧
      ∃ (V : Fin n → (pullback f φ).Opens) (v : (i : Fin n) → (V i).toScheme),
        ∀ i : Fin n,
          IsFinite ((V i).ι ≫ pullback.snd f φ) ∧
          ((V i).ι ≫ pullback.snd f φ) (v i) = u ∧
          (∀ w : (V i).toScheme, ((V i).ι ≫ pullback.snd f φ) w = u → w = v i) ∧
          ((V i).ι ≫ pullback.fst f φ) (v i) = x i ∧
          IsIso (((V i).ι ≫ pullback.fst f φ).residueFieldMap (v i)) := by
  classical
  induction n with
  | zero =>
      refine ⟨S, 𝟙 S, s, inferInstance, rfl, inferInstance,
        Fin.elim0, (fun i ↦ Fin.elim0 i), ?_⟩
      intro i
      exact i.elim0
  | succ n ih =>
      obtain ⟨U, φ, t, hφ, ht, hφres, V, v, hV⟩ :=
        ih (fun i ↦ x i.castSucc) (fun i ↦ hx i.castSucc)
          (fun i ↦ hisolated i.castSucc)
      let : Etale φ := hφ
      let : IsIso (φ.residueFieldMap t) := hφres
      obtain ⟨z, hz, hzt, hzres⟩ := elementary_pullback_point f φ (x (Fin.last n)) t
        ((hx (Fin.last n)).trans ht.symm)
      have hisoz := isolated_fiber_point_base_change f φ z
        (Eq.rec (motive := fun a _ ↦ IsOpen ({f.asFiber a} : Set (f.fiber (f a))))
          (hisolated (Fin.last n)) hz.symm)
      let q := pullback.snd f φ
      have : LocallyOfFiniteType q := inferInstance
      obtain ⟨U', ψ, t', hψ, ht', hψres, W₀, hW₀fin, w₀, hw₀, hW₀uniq,
        hw₀z, hW₀res⟩ := exists_etale_finite_open_of_isolated_fiber_point q z hisoz
      have ht't : ψ t' = t := ht'.trans hzt
      let : Etale ψ := hψ
      let : IsIso (ψ.residueFieldMap t') := hψres
      let e := pullbackLeftPullbackSndIso f φ ψ
      let π := e.inv ≫ pullback.fst q ψ
      have hπp : π ≫ pullback.fst f φ = pullback.fst f (ψ ≫ φ) := by
        simp [π, e, q]
      have hπq : π ≫ q = pullback.snd f (ψ ≫ φ) ≫ ψ := by
        simp [π, e, q]
      have earlier (i : Fin n) := finitePiece_persistence_of_isIso_residueFieldMap
        f φ t (x i.castSucc) ((hx i.castSucc).trans ht.symm) (V i) (v i)
        (hV i).1 (hV i).2.1 (hV i).2.2.1 (hV i).2.2.2.1 (hV i).2.2.2.2
        ψ t' ht't hψres π hπp hπq
      choose v' hv' using fun i ↦ (earlier i).2
      obtain ⟨W, w, hWfin, hw, hWuniq, hwz, hWres, _hWset⟩ :=
        transport_finite_open_piece e (pullback.snd q ψ) (pullback.snd f (ψ ≫ φ))
          (pullback.fst q ψ) (by simp [e, q]) W₀ w₀ t' z
          hW₀fin hw₀ hW₀uniq hw₀z hW₀res
      have hwx : (W.ι ≫ pullback.fst f (ψ ≫ φ)) w = x (Fin.last n) := by
        rw [← hπp]
        change pullback.fst f φ ((W.ι ≫ π) w) = x (Fin.last n)
        rw [hwz, hz]
      have hWresX : IsIso ((W.ι ≫ pullback.fst f (ψ ≫ φ)).residueFieldMap w) := by
        have : IsIso ((W.ι ≫ π).residueFieldMap w) := hWres
        have : IsIso ((pullback.fst f φ).residueFieldMap ((W.ι ≫ π) w)) :=
          hwz.symm ▸ hzres
        rw [← hπp, ← Category.assoc, Scheme.residueFieldMap_comp]
        infer_instance
      let good (y : X) (a : Σ V : (pullback f (ψ ≫ φ)).Opens, V.toScheme) : Prop :=
        IsFinite (a.1.ι ≫ pullback.snd f (ψ ≫ φ)) ∧
          (a.1.ι ≫ pullback.snd f (ψ ≫ φ)) a.2 = t' ∧
          (∀ b : a.1.toScheme, (a.1.ι ≫ pullback.snd f (ψ ≫ φ)) b = t' → b = a.2) ∧
          (a.1.ι ≫ pullback.fst f (ψ ≫ φ)) a.2 = y ∧
          IsIso ((a.1.ι ≫ pullback.fst f (ψ ≫ φ)).residueFieldMap a.2)
      let pieces : Fin (n + 1) → Σ V : (pullback f (ψ ≫ φ)).Opens, V.toScheme :=
        Fin.lastCases ⟨W, w⟩ (fun i ↦ ⟨π ⁻¹ᵁ V i, v' i⟩)
      let V' := fun i ↦ (pieces i).1
      let w' := fun i ↦ (pieces i).2
      refine ⟨U', ψ ≫ φ, t', inferInstance, ?_, ?_, V', w', ?_⟩
      · simpa only [Scheme.Hom.comp_apply, ht't] using ht
      · rw [Scheme.residueFieldMap_comp]
        have : IsIso (φ.residueFieldMap (ψ t')) := ht't.symm ▸ hφres
        infer_instance
      · intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · change good (x (Fin.last n)) (pieces (Fin.last n))
          rw [show pieces (Fin.last n) = ⟨W, w⟩ from Fin.lastCases_last]
          exact ⟨hWfin, hw, hWuniq, hwx, hWresX⟩
        · change good (x j.castSucc) (pieces j.castSucc)
          rw [show pieces j.castSucc = ⟨π ⁻¹ᵁ V j, v' j⟩ from
            Fin.lastCases_castSucc j]
          exact ⟨(earlier j).1, (hv' j).1, (hv' j).2.1,
            (hv' j).2.2.1, (hv' j).2.2.2.1⟩

end AlgebraicGeometry
