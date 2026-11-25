/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.AlgebraicGeometry.EtaleLocalFiniteMultiplePointsElementary

/-!
# Elementary localization of already split fibre points

Source: Stacks Project, More on Morphisms, proof of Lemma 02LM, lines 12083--12089.
(blueprint: lem-weil-pbc-elementary-localize-split-points).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem elementary_pullback_point_injective
    {P X T S : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ T}
    {q : X ⟶ S} {ψ : T ⟶ S} (h : IsPullback a b q ψ)
    (t : T) [IsIso (ψ.residueFieldMap t)]
    (w z : P) (hw : b w = t) (hz : b z = t) (ha : a w = a z) : w = z := by
  let F := pullback.map b (T.fromSpecResidueField t) q
    (S.fromSpecResidueField (ψ t)) a (Spec.map (ψ.residueFieldMap t)) ψ
    h.w.symm (by simp)
  have hF := isPullback_fiberToSpecResidueField_of_isPullback h t
  have : IsIso F := hF.isIso_fst_of_isIso
  let w' : b.fiber t := (b.fiberHomeo t).symm ⟨w, hw⟩
  let z' : b.fiber t := (b.fiberHomeo t).symm ⟨z, hz⟩
  have he : F w' = F z' := by
    apply (q.fiberι (ψ t)).isEmbedding.injective
    change (F ≫ pullback.fst q _) w' = (F ≫ pullback.fst q _) z'
    dsimp only [F]
    rw [pullback.lift_fst]
    change a (b.fiberι t w') = a (b.fiberι t z')
    simpa [w', z'] using ha
  have he' : w' = z' := F.homeomorph.injective he
  simpa [w', z'] using congrArg (b.fiberι t) he'

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
      (W.ι ≫ e.inv ≫ p) w = y ∧ IsIso ((W.ι ≫ e.inv ≫ p).residueFieldMap w) := by
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
  · have : IsIso ((V.ι ≫ p).residueFieldMap (d.inv w)) := hd.symm ▸ hres
    rw [hp', Scheme.residueFieldMap_comp]
    infer_instance

private theorem finite_purelyInseparable_of_field_square
    {k K k' K' : Type u} [Field k] [Field K] [Field k'] [Field K']
    (g : k →+* K) (g' : k' →+* K') (a : k →+* k') (e : K ≃+* K')
    (he : e.toRingHom.comp g = g'.comp a)
    (h : letI := g.toAlgebra; Module.Finite k K ∧ IsPurelyInseparable k K) :
    let := g'.toAlgebra; Module.Finite k' K' ∧ IsPurelyInseparable k' K' := by
  let := g.toAlgebra
  let := g'.toAlgebra
  let := a.toAlgebra
  let := (e.toRingHom.comp g).toAlgebra
  let E : K ≃ₐ[k] K' := { __ := e, commutes' := fun _ ↦ rfl }
  have : Module.Finite k K := h.1
  have : IsPurelyInseparable k K := h.2
  have : Module.Finite k K' := Module.Finite.equiv E.toLinearEquiv
  have : IsPurelyInseparable k K' := E.isPurelyInseparable
  have : IsScalarTower k k' K' := IsScalarTower.of_algebraMap_eq' he
  exact ⟨Module.Finite.of_restrictScalars_finite k k' K',
    IsPurelyInseparable.tower_top k k' K'⟩

private theorem finite_purelyInseparable_residue_square
    {Y X T S : Scheme.{u}} (a : Y ⟶ X) (r : Y ⟶ T) (q : X ⟶ S) (ψ : T ⟶ S)
    (hsq : a ≫ q = r ≫ ψ) (v : Y) (y : X) (hy : a v = y) (s : S) (t : T)
    (hs : q y = s) (ht : r v = t) [IsIso (a.residueFieldMap v)]
    (h : letI := ((S.residueFieldCongr hs.symm).hom ≫ q.residueFieldMap y).hom.toAlgebra
      Module.Finite (S.residueField s) (X.residueField y) ∧
        IsPurelyInseparable (S.residueField s) (X.residueField y)) :
    letI := ((T.residueFieldCongr ht.symm).hom ≫ r.residueFieldMap v).hom.toAlgebra
    Module.Finite (T.residueField t) (Y.residueField v) ∧
      IsPurelyInseparable (T.residueField t) (Y.residueField v) := by
  subst y
  subst s
  subst t
  change (letI := (q.residueFieldMap (a v)).hom.toAlgebra;
    Module.Finite _ _ ∧ IsPurelyInseparable _ _) at h
  let hb : q (a v) = ψ (r v) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun f : Y ⟶ S ↦ f v) hsq
  let b := ((S.residueFieldCongr hb).hom ≫ ψ.residueFieldMap (r v)).hom
  let e := (asIso (a.residueFieldMap v)).commRingCatIsoToRingEquiv
  apply finite_purelyInseparable_of_field_square (q.residueFieldMap (a v)).hom
    (r.residueFieldMap v).hom b e _ h
  have H := (Scheme.Hom.residueFieldMap_congr hsq v)
  simp only [Scheme.residueFieldMap_comp] at H
  exact congrArg CommRingCat.Hom.hom H

/-- Source: Stacks Project, More on Morphisms, proof of Lemma 02LM,
lines 12083--12089 and its omitted verification using Schemes, Lemma 01JT
(blueprint: lem-weil-pbc-elementary-localize-split-points).

Proof:
1. Regard the finite sigma family `y` as a list `Fin N` using a finite-type equivalence.
   Apply `exists_etale_local_finite_multiple_points_elementary` to `pullback.snd f φ`.
   Its local-finite-type instance comes from base change. The result is an elementary
   étale neighborhood `ψ : U' → U`, with `ψ u' = u`, and one finite open for each `y i j`,
   with a unique point over `u'` and an unchanged residue field over `y i j`.
2. Identify the iterated pullback with `pullback f (ψ ≫ φ)` by pullback pasting. Transport
   the opens, points, finiteness and unique-fibre-point assertions along this isomorphism.
   The first projection sends the chosen point to `y i j` and then to `x i`.
3. The residue-field square commutes and its base and point vertical maps are isomorphisms.
   Transport the given finite purely inseparable extension across these isomorphisms.
4. Distinct output points follow by projecting to the injective sigma family `y`.
   Any point of the final pullback above `u'` and `x i` projects to `y i j` by `hex`.
   Its lifts over `(y i j,u')` correspond to primes of
   `κ(y i j) ⊗[κ(u)] κ(u')`. Since the second factor map is an isomorphism, this is a
   field, hence has one prime. The chosen point is that sole lift, proving exhaustion.
For an empty sigma family the identity neighborhood and no opens work. These hypotheses
explicitly retain the purely inseparable residue extensions; uniqueness alone is insufficient. -/
theorem exists_elementary_localize_split_points
    {X S U : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (φ : U ⟶ S) (u : U) (n : ℕ) (x : Fin n → X) (m : Fin n → ℕ)
    (y : (i : Fin n) → Fin (m i) → ↥(pullback f φ))
    (hyx : ∀ i j, pullback.fst f φ (y i j) = x i)
    (hy : ∀ i j, ∃ (h : pullback.snd f φ (y i j) = u),
      letI := ((U.residueFieldCongr h.symm).hom ≫
        (pullback.snd f φ).residueFieldMap (y i j)).hom.toAlgebra
      Module.Finite (U.residueField u) ((pullback f φ).residueField (y i j)) ∧
        IsPurelyInseparable (U.residueField u) ((pullback f φ).residueField (y i j)))
    (hisolated : ∀ i j, IsOpen ({(pullback.snd f φ).asFiber (y i j)} :
      Set ((pullback.snd f φ).fiber ((pullback.snd f φ) (y i j)))))
    (hinj : Function.Injective (fun a : (i : Fin n) × Fin (m i) ↦ y a.1 a.2))
    (hex : ∀ (i : Fin n) (w : ↥(pullback f φ)),
      pullback.snd f φ w = u → pullback.fst f φ w = x i →
        ∃ j : Fin (m i), w = y i j) :
    ∃ (U' : Scheme.{u}) (ψ : U' ⟶ U) (u' : U'), Etale ψ ∧ ψ u' = u ∧
      ∃ (V : (i : Fin n) → Fin (m i) → (pullback f (ψ ≫ φ)).Opens)
        (v : (i : Fin n) → (j : Fin (m i)) → (V i j).toScheme),
        (∀ (i : Fin n) (j : Fin (m i)),
          IsFinite ((V i j).ι ≫ pullback.snd f (ψ ≫ φ)) ∧
          ∃ (hv : ((V i j).ι ≫ pullback.snd f (ψ ≫ φ)) (v i j) = u'),
            (∀ w : (V i j).toScheme,
              ((V i j).ι ≫ pullback.snd f (ψ ≫ φ)) w = u' → w = v i j) ∧
            (letI := ((U'.residueFieldCongr hv.symm).hom ≫
              ((V i j).ι ≫ pullback.snd f (ψ ≫ φ)).residueFieldMap (v i j)).hom.toAlgebra
             Module.Finite (U'.residueField u') ((V i j).toScheme.residueField (v i j)) ∧
               IsPurelyInseparable (U'.residueField u')
                 ((V i j).toScheme.residueField (v i j))) ∧
            ((V i j).ι ≫ pullback.fst f (ψ ≫ φ)) (v i j) = x i) ∧
        Function.Injective
          (fun a : (i : Fin n) × Fin (m i) ↦ (V a.1 a.2).ι (v a.1 a.2)) ∧
        (∀ (i : Fin n) (w : ↥(pullback f (ψ ≫ φ))),
          pullback.snd f (ψ ≫ φ) w = u' → pullback.fst f (ψ ≫ φ) w = x i →
            ∃ j : Fin (m i), w = (V i j).ι (v i j)) := by
  classical
  let I := (i : Fin n) × Fin (m i)
  let E : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let q := pullback.snd f φ
  have : LocallyOfFiniteType q := inferInstance
  obtain ⟨U', ψ, u', hψ, hψu, hψres, V₀, v₀, hV₀⟩ :=
    exists_etale_local_finite_multiple_points_elementary q u (Fintype.card I)
      (fun k ↦ y (E.symm k).1 (E.symm k).2)
      (fun k ↦ (hy (E.symm k).1 (E.symm k).2).choose)
      (fun k ↦ hisolated (E.symm k).1 (E.symm k).2)
  let e := pullbackLeftPullbackSndIso f φ ψ
  let a := e.inv ≫ pullback.fst q ψ
  let r := pullback.snd f (ψ ≫ φ)
  have haX : a ≫ pullback.fst f φ = pullback.fst f (ψ ≫ φ) := by simp [a, e, q]
  have haU : a ≫ q = r ≫ ψ := by simp [a, e, q, r]
  have pieces (i : Fin n) (j : Fin (m i)) :=
    transport_finite_open_piece e (pullback.snd q ψ) r (pullback.fst q ψ)
      (by simp [e, q, r]) (V₀ (E ⟨i, j⟩)) (v₀ (E ⟨i, j⟩)) u' (y i j)
      (hV₀ (E ⟨i, j⟩)).1 (hV₀ (E ⟨i, j⟩)).2.1
      (hV₀ (E ⟨i, j⟩)).2.2.1
      ((hV₀ (E ⟨i, j⟩)).2.2.2.1.trans
        (congrArg (fun b : I ↦ y b.1 b.2) (E.symm_apply_apply ⟨i, j⟩)))
      (hV₀ (E ⟨i, j⟩)).2.2.2.2
  choose V v hV using pieces
  have hvU (i : Fin n) (j : Fin (m i)) : r ((V i j).ι (v i j)) = u' := by
    simpa only [Scheme.Hom.comp_apply] using (hV i j).2.1
  have hvP (i : Fin n) (j : Fin (m i)) : a ((V i j).ι (v i j)) = y i j := by
    exact (hV i j).2.2.2.1
  refine ⟨U', ψ, u', hψ, hψu, V, v, ?_, ?_, ?_⟩
  · intro i j
    refine ⟨(hV i j).1, (hV i j).2.1, (hV i j).2.2.1, ?_, ?_⟩
    · obtain ⟨hh, hp⟩ := hy i j
      have : IsIso (((V i j).ι ≫ a).residueFieldMap (v i j)) :=
        (hV i j).2.2.2.2
      apply finite_purelyInseparable_residue_square ((V i j).ι ≫ a)
        ((V i j).ι ≫ r) q ψ (by simp [Category.assoc, haU])
        (v i j) (y i j) (hV i j).2.2.2.1 u u' hh (hV i j).2.1 hp
    · have H := hyx i j
      rw [← hvP i j] at H
      simpa only [← Scheme.Hom.comp_apply, Category.assoc, haX] using H
  · intro b c hbc
    apply hinj
    exact (hvP b.1 b.2).symm.trans ((congrArg a hbc).trans (hvP c.1 c.2))
  · intro i w hw hx
    have hwu : q (a w) = u := by
      rw [← Scheme.Hom.comp_apply, haU, Scheme.Hom.comp_apply, hw, hψu]
    have hwx : pullback.fst f φ (a w) = x i := by
      simpa only [← Scheme.Hom.comp_apply, haX] using hx
    obtain ⟨j, hj⟩ := hex i (a w) hwu hwx
    refine ⟨j, ?_⟩
    have : IsIso (ψ.residueFieldMap u') := hψres
    apply e.inv.homeomorph.injective
    change e.inv w = e.inv ((V i j).ι (v i j))
    apply elementary_pullback_point_injective (IsPullback.of_hasPullback q ψ) u'
    · simpa only [← Scheme.Hom.comp_apply, e, q,
        pullbackLeftPullbackSndIso_inv_snd_snd] using hw
    · change (e.inv ≫ pullback.snd q ψ) ((V i j).ι (v i j)) = u'
      simpa only [e, q, pullbackLeftPullbackSndIso_inv_snd_snd] using hvU i j
    · exact hj.trans (hvP i j).symm

end AlgebraicGeometry
