/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.Triangle
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.Compactification.CategoryBaseChange

/-!
# Compatible compactification towers over arbitrary bases

Source: Stacks Project, Tag 0F7J, proof of `lemma-shriek-composition`, with supplied
compactifications over arbitrary bases as in `WeilConjectures.Compactification.Comp` and
`WeilConjectures.Compactification.Triangle`
(blueprint: lem-cbc-compactifiable-compatible-tower).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Supplied compactifications extend to a compatible tower; towers survive arbitrary base
change and any two have a common refinement. `Triangle` records the intermediate scheme up to
its unique isomorphism with the displayed fibre product; the first clause uses the literal
fibre product via `restrict`. Its field `q` is the arrow called `b` in the node.

Source: Stacks Project, Tag 0F7J, proof of `lemma-shriek-composition`, and the supplied-data
construction in upstream `Compactification/Comp.lean` and `Triangle.lean`.
(blueprint: lem-cbc-compactifiable-compatible-tower)

Proof plan:
1. Embed `X` in `W ×_Z Ybar` by `(a₀, f ≫ i)`. The projection to `W` is separated;
   quasi-compact immersion cancellation (`lem-cbc-qc-immersion-cancellation`) applies.
2. Take its scheme-theoretic image, using `lemma-schematic-closure-uniqueness--1` and
   `lemma-nagata-immersion-into-proper`. The closed image inclusion and proper projections
   make both ambient maps proper (`lem-pc-proper-base-change`,
   `lem-weil-pbc-closed-immersion-proper`, `lem-weil-pbc-proper-composition`).
3. Restrict over `Y`. Fibre-product uniqueness (`def-pc-fibre-product`) and monicity of `i`
   identify the induced open map as a base change of `a`; openness and quasi-compactness
   follow from `lem-weil-pbc-open-immersion-base-change` and `lem-pc-quasi-compact-base-change`.
4. Pull back the diagram over any `Z'`. The same properties and equations survive;
   `lem-pod-separated-finite-type-base-change` supplies the properties of `f'` and `h'`.
   No claim that scheme-theoretic image commutes with arbitrary base change is needed.
5. For two towers, `lem-cbc-compactifiable-cofiltered` gives a common compactification `D`
   of `Y` over `Z`, with proper maps to both original ambient schemes of `Y`.
6. Close `X` in the product over `D` of the two pulled-back ambient schemes of `X`.
   Cancellation and the immersion construction again give the new compactification.
   Maps to the old ambient schemes are proper by `lemma-nagata-proper-to-separated-target`.
7. Restrict to `Y`. The projection identities give all seven refinement equations;
   properness of the intermediate maps follows from the same proper-to-separated lemma.
-/
theorem exists_compactifiable_compatible_tower
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (d : Compactification h) (c : Compactification (f ≫ h)) :
    (∃ (e : Compactification (f ≫ d.i)) (v : e.Z ⟶ c.Z),
      IsProper v ∧ e.i ≫ v = c.i ∧ v ≫ c.g = e.g ≫ d.g ∧
      QuasiCompact e.i ∧ QuasiCompact (pullback.fst e.g d.i) ∧
      QuasiCompact e.restrict.i ∧ IsOpenImmersion (pullback.fst e.g d.i) ∧
      IsOpenImmersion e.restrict.i ∧ IsProper e.restrict.g ∧
      e.restrict.i ≫ pullback.fst e.g d.i = e.i ∧
      e.restrict.i ≫ e.restrict.g = f ∧ IsProper (e.g ≫ d.g) ∧
      IsPullback e.restrict.g (pullback.fst e.g d.i) d.i e.g) ∧
    (∀ (T : Compactification.Triangle f h) (v : T.cfg.Z ⟶ c.Z),
      IsProper v → T.cfg.i ≫ v = c.i → v ≫ c.g = T.cfg.g →
      ∀ (Z' : Scheme.{u}) (k : Z' ⟶ Z),
      ∃ (f' : pullback (f ≫ h) k ⟶ pullback h k),
        IsPullback (pullback.fst (f ≫ h) k) f' f (pullback.fst h k) ∧
        IsSeparated f' ∧ LocallyOfFiniteType f' ∧ QuasiCompact f' ∧
        IsSeparated (pullback.snd h k) ∧ LocallyOfFiniteType (pullback.snd h k) ∧
        QuasiCompact (pullback.snd h k) ∧
        ∃ (T' : Compactification.Triangle f' (pullback.snd h k))
          (rA : T'.cfg.Z ⟶ T.cfg.Z) (rB : T'.cg.Z ⟶ T.cg.Z)
          (rU : T'.cf.Z ⟶ T.cf.Z) (v' : T'.cfg.Z ⟶ (c.baseChange k).Z),
          IsPullback rA T'.cfg.g T.cfg.g k ∧
          IsPullback rB T'.cg.g T.cg.g k ∧
          IsPullback rU (T'.cf.g ≫ pullback.snd h k) (T.cf.g ≫ h) k ∧
          T'.cfg.i ≫ rA = pullback.fst (f ≫ h) k ≫ T.cfg.i ∧
          T'.cg.i ≫ rB = pullback.fst h k ≫ T.cg.i ∧
          T'.cf.i ≫ rU = pullback.fst (f ≫ h) k ≫ T.cf.i ∧
          T'.q ≫ rA = rU ≫ T.q ∧ T'.p ≫ rB = rA ≫ T.p ∧
          T'.cf.g ≫ pullback.fst h k = rU ≫ T.cf.g ∧
          QuasiCompact T'.cfg.i ∧ QuasiCompact T'.cg.i ∧
          QuasiCompact T'.cf.i ∧ QuasiCompact T'.q ∧
          IsProper v' ∧ T'.cfg.i ≫ v' = (c.baseChange k).i ∧
          v' ≫ (c.baseChange k).g = T'.cfg.g ∧
          v' ≫ pullback.fst c.g k = rA ≫ v) ∧
    (∀ (T : Fin 2 → Compactification.Triangle f h),
      ∃ (R : Compactification.Triangle f h),
      ∀ (j : Fin 2), ∃ (v : R.cfg.Z ⟶ (T j).cfg.Z)
        (u : R.cg.Z ⟶ (T j).cg.Z) (w : R.cf.Z ⟶ (T j).cf.Z),
        IsProper v ∧ IsProper u ∧ IsProper w ∧
        R.cfg.i ≫ v = (T j).cfg.i ∧ R.cg.i ≫ u = (T j).cg.i ∧
        R.cf.i ≫ w = (T j).cf.i ∧ R.q ≫ v = w ≫ (T j).q ∧
        v ≫ (T j).p = R.p ≫ u ∧ w ≫ (T j).cf.g = R.cf.g ∧
        u ≫ (T j).cg.g = R.cg.g) := by
  constructor
  · let e := c.ofComp d
    let v : e.Z ⟶ c.Z := (c.ofCompLift d).imageι ≫ pullback.fst c.g d.g
    have hd : QuasiCompact d.i := d.quasiCompact_openImmersion inferInstance
    have he : QuasiCompact e.i := e.quasiCompact_openImmersion inferInstance
    have hr : QuasiCompact e.restrict.i := e.restrict.quasiCompact_openImmersion inferInstance
    refine ⟨e, v, inferInstance, ?_, ?_, he, inferInstance, hr,
      inferInstance, inferInstance, inferInstance, e.restrict_i_fst,
      e.restrict.comm.symm, inferInstance, e.isPullback_restrict⟩
    · change (c.ofCompLift d).toImage ≫ _ = _
      rw [Scheme.Hom.toImage_imageι_assoc, Compactification.ofCompLift_fst]
    · change ((c.ofCompLift d).imageι ≫ pullback.fst c.g d.g) ≫ c.g =
        ((c.ofCompLift d).imageι ≫ pullback.snd c.g d.g) ≫ d.g
      simp only [Category.assoc, pullback.condition]
  constructor
  · intro T v hv hvi hvg Z' k
    let f' : pullback (f ≫ h) k ⟶ pullback h k :=
      pullback.lift (pullback.fst (f ≫ h) k ≫ f) (pullback.snd (f ≫ h) k)
        (by simp only [Category.assoc, pullback.condition])
    have hf' : IsPullback (pullback.fst (f ≫ h) k) f' f (pullback.fst h k) := by
      apply IsPullback.of_bot (v₂₁ := pullback.snd h k) (v₂₂ := h)
      · simpa only [f', pullback.lift_snd] using IsPullback.of_hasPullback (f ≫ h) k
      · simp [f']
      · exact IsPullback.of_hasPullback h k
    have hs : IsSeparated f' := MorphismProperty.of_isPullback hf' inferInstance
    have hl : LocallyOfFiniteType f' := MorphismProperty.of_isPullback hf' inferInstance
    have hq : QuasiCompact f' := MorphismProperty.of_isPullback hf' inferInstance
    refine ⟨f', hf', hs, hl, hq, inferInstance, inferInstance, inferInstance, ?_⟩
    let cf := T.cf.ofIsPullback hf'
    let cg := T.cg.baseChange k
    let cfg : Compactification (f' ≫ pullback.snd h k) :=
      (T.cfg.baseChange k).copy (by simp [f'])
    let rU : cf.Z ⟶ T.cf.Z := pullback.fst T.cf.g (pullback.fst h k)
    let rB : cg.Z ⟶ T.cg.Z := pullback.fst T.cg.g k
    let rA : cfg.Z ⟶ T.cfg.Z := pullback.fst T.cfg.g k
    have hU : IsPullback rU cf.g T.cf.g (pullback.fst h k) :=
      (T.cf.isPullback_g_ofIsPullback hf').flip
    have hUZ := hU.paste_vert (IsPullback.of_hasPullback h k)
    have hqg : T.q ≫ T.cfg.g = T.cf.g ≫ h := by
      rw [← T.p_g, ← Category.assoc, ← T.isPullback.w, Category.assoc, ← T.cg.comm]
    let p' : cfg.Z ⟶ cg.Z := pullback.lift (rA ≫ T.p) cfg.g
      (by simp only [Category.assoc, T.p_g]; exact pullback.condition)
    let q' : cf.Z ⟶ cfg.Z := pullback.lift (rU ≫ T.q) (cf.g ≫ pullback.snd h k)
      (by rw [Category.assoc, hqg]; exact hUZ.w)
    have hqA : q' ≫ rA = rU ≫ T.q := pullback.lift_fst _ _ _
    have hqZ : q' ≫ cfg.g = cf.g ≫ pullback.snd h k := pullback.lift_snd _ _ _
    have hpB : p' ≫ rB = rA ≫ T.p := pullback.lift_fst _ _ _
    have hpZ : p' ≫ cg.g = cfg.g := pullback.lift_snd _ _ _
    have hqPB : IsPullback rU q' T.q rA := by
      apply IsPullback.of_bot (v₂₁ := cfg.g) (v₂₂ := T.cfg.g)
      · rw [hqZ, hqg]; exact hUZ
      · exact hqA.symm
      · exact IsPullback.of_hasPullback T.cfg.g k
    have hqo : IsOpenImmersion q' := MorphismProperty.of_isPullback hqPB inferInstance
    have hsq : IsPullback cf.g q' cg.i p' := by
      apply IsPullback.of_right (h₁₂ := pullback.fst h k) (h₂₂ := rB)
      · rw [hpB, ← hU.w]
        exact hqPB.paste_horiz T.isPullback
      · apply pullback.hom_ext
        · change cf.g ≫ cg.i ≫ rB = q' ≫ p' ≫ rB
          calc
            cf.g ≫ cg.i ≫ rB = (cf.g ≫ pullback.fst h k) ≫ T.cg.i := by
              rw [T.cg.baseChange_i_fst, Category.assoc]
            _ = (rU ≫ T.cf.g) ≫ T.cg.i := by rw [hU.w]
            _ = (rU ≫ T.q) ≫ T.p := by rw [Category.assoc, T.isPullback.w,
                Category.assoc]
            _ = (q' ≫ rA) ≫ T.p := by rw [hqA]
            _ = q' ≫ p' ≫ rB := by rw [Category.assoc, hpB]
        · change cf.g ≫ cg.i ≫ cg.g = q' ≫ p' ≫ cg.g
          rw [← cg.comm, hpZ, hqZ]
      · exact T.cg.isPullback_i_ofIsPullback (IsPullback.of_hasPullback h k)
    let T' : Compactification.Triangle f' (pullback.snd h k) :=
      { cf := cf, cg := cg, cfg := cfg, q := q', p := p',
        i_q := by
          apply pullback.hom_ext
          · change cf.i ≫ q' ≫ rA = cfg.i ≫ rA
            rw [hqA, Compactification.ofIsPullback_i_fst_assoc, T.i_q]
            exact (T.cfg.baseChange_i_fst k).symm
          · change cf.i ≫ q' ≫ cfg.g = cfg.i ≫ cfg.g
            rw [hqZ, ← Category.assoc, ← cf.comm, ← cfg.comm],
        p_g := hpZ, isPullback := hsq }
    let vr : T.cfg.Refinement c := ⟨v, hvi, hvg⟩
    let v' := (vr.baseChange k).hom
    refine ⟨T', rA, rB, rU, v', ?_, ?_, hUZ, ?_, ?_, ?_, hqA, hpB,
      hU.w.symm, ?_, ?_, ?_, ?_, inferInstance, ?_, ?_, ?_⟩
    · exact IsPullback.of_hasPullback T.cfg.g k
    · exact IsPullback.of_hasPullback T.cg.g k
    · exact T.cfg.baseChange_i_fst k
    · exact T.cg.baseChange_i_fst k
    · exact T.cf.ofIsPullback_i_fst hf'
    · exact cfg.quasiCompact_openImmersion inferInstance
    · exact cg.quasiCompact_openImmersion inferInstance
    · exact cf.quasiCompact_openImmersion inferInstance
    · have : QuasiCompact T.q :=
        MorphismProperty.of_isPullback T.isPullback
          (T.cg.quasiCompact_openImmersion inferInstance)
      exact MorphismProperty.of_isPullback hqPB inferInstance
    · exact (vr.baseChange k).i_hom
    · exact (vr.baseChange k).hom_g
    · change (vr.baseChange k).hom ≫ pullback.fst c.g k = rA ≫ v
      simp [Compactification.Refinement.baseChange, rA, vr]
  · intro T
    let R := (T 0).inf (T 1)
    refine ⟨R, ?_⟩
    intro j
    have φ : R.Hom (T j) := by
      by_cases hj : j = 0
      · subst j; exact (T 0).infFst (T 1)
      · have hj : j = 1 := by omega
        subst j; exact (T 0).infSnd (T 1)
    exact ⟨φ.rfg.hom, φ.rg.hom, φ.rf.hom, inferInstance, inferInstance,
      inferInstance, φ.rfg.i_hom, φ.rg.i_hom, φ.rf.i_hom, φ.q_comm.symm,
      φ.p_comm.symm, φ.rf.hom_g, φ.rg.hom_g⟩

end AlgebraicGeometry
