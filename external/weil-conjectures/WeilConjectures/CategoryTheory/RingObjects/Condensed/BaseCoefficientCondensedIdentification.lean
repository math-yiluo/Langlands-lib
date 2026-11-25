/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic
public import WeilConjectures.NumberTheory.Padics.Extension

/-!
# Condensed realizations of the base p-adic coefficients

Source: blueprint `main-20261015`, `theorem-exceptional-inverse-image`, opening paragraphs of
`det-existence-localizing.proof.md` and `det-existence-restriction.proof.md`
(blueprint: lem-sfb-base-coefficient-condensed-identification).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace Profinite

private noncomputable def coefficientIso {R T : Type}
    [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
    [TopologicalSpace T] [Ring T] [IsTopologicalRing T]
    (e : R ≃+* T) (hc : Continuous e) (hs : Continuous e.symm) :
    (Mon.mk (continuousMapRingObj.{u} R) : CondensedRing.{u}) ≅
      Mon.mk (continuousMapRingObj T) := by
  let i : continuousMapRingSheaf.{u} R ≅ continuousMapRingSheaf T :=
    { hom := continuousMapRingSheafMap e.toRingHom hc
      inv := continuousMapRingSheafMap e.symm.toRingHom hs
      hom_inv_id := by
        ext S a
        apply ULift.ext
        apply ContinuousMap.ext
        intro s
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S a
        apply ULift.ext
        apply ContinuousMap.ext
        intro s
        exact e.apply_symm_apply _ }
  let F := sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})
  have : IsMonHom (F.mapIso i).hom :=
    inferInstanceAs (IsMonHom (F.map (continuousMapRingSheafMap e.toRingHom hc)))
  exact Mon.mkIso' (F.mapIso i)

/-- The structural image of the base field and its unit ball give the usual rational and
integral condensed coefficients, compatibly with inclusion. The bottom intermediate field
has its inherited subspace norm; `PadicAlgCl.integers` is the unit ball for precisely this
norm. Ring objects here use the tensor product of condensed abelian groups.

Source: blueprint `main-20261015`, `theorem-exceptional-inverse-image`, introductory coefficient
specializations in `det-existence-localizing.proof.md` and
`det-existence-restriction.proof.md`
(blueprint: lem-sfb-base-coefficient-condensed-identification).

Proof: (1) Restrict the structural embedding to its image, the bottom intermediate field.
Its inverse sends an image element to its unique preimage; this is
`IntermediateField.botEquiv`. Both maps preserve the ring operations by injectivity.
(2) The ambient norm extends the p-adic norm, so this ring equivalence preserves norms and
distances. Substituting inverse images proves that its inverse is also an isometry.
(3) Norm preservation identifies the two unit balls. Restrict the equivalence and its
inverse to obtain an isometric ring equivalence of the integer rings, using
`def-weil-l-adic-coefficient-extension` and the explicitly prescribed subspace norm.
(4) Apply the continuous-map construction of `sk-def-sfb-condensed-ring` to these four
continuous ring maps. Their components are postcomposition, preserve the pointwise ring
operations, and are inverse pointwise; hence they give isomorphisms of ring objects.
(5) Precomposition with a profinite map commutes with each of the four postcomposition
maps, giving naturality for both isomorphisms and both inverses. The integral equivalence
is the restriction of the rational equivalence, so composing with inclusion gives the
same scalar map. Postcomposition on sections proves the compatibility square below. -/
theorem base_coefficient_condensed_identification (l : ℕ) [Fact l.Prime] :
    ∃ (e : ℚ_[l] ≃+* (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)))
      (eInt : ℤ_[l] ≃+*
        PadicAlgCl.integers l (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l))),
      e.toRingHom = algebraMap ℚ_[l] (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)) ∧
      eInt.toRingHom = AlgebraicGeometry.ProEtale.padicIntToIntegers l
        (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)) ∧
      Isometry e ∧ Isometry e.symm ∧ Isometry eInt ∧ Isometry eInt.symm ∧
      ∃ (qIso : (Mon.mk (continuousMapRingObj.{u} ℚ_[l]) : CondensedRing.{u}) ≅
          Mon.mk (continuousMapRingObj
            (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l))))
        (zIso : (Mon.mk (continuousMapRingObj.{u} ℤ_[l]) : CondensedRing.{u}) ≅
          Mon.mk (continuousMapRingObj
            (PadicAlgCl.integers l (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l))))),
        (∀ (S : Profinite.{u}) (a : C(S, ℚ_[l])) (s : S),
          ((qIso.hom.hom.hom.app (op S)) (ULift.up a)).down s = e (a s)) ∧
        (∀ (S : Profinite.{u})
          (a : C(S, (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)))) (s : S),
          ((qIso.inv.hom.hom.app (op S)) (ULift.up a)).down s = e.symm (a s)) ∧
        (∀ (S : Profinite.{u}) (a : C(S, ℤ_[l])) (s : S),
          ((zIso.hom.hom.hom.app (op S)) (ULift.up a)).down s = eInt (a s)) ∧
        (∀ (S : Profinite.{u})
          (a : C(S, PadicAlgCl.integers l
            (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)))) (s : S),
          ((zIso.inv.hom.hom.app (op S)) (ULift.up a)).down s = eInt.symm (a s)) ∧
        zIso.hom.hom ≫
            (sheafCompose (coherentTopology Profinite.{u})
              (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
              (continuousMapRingSheafMap
                (PadicAlgCl.integers l
                  (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l))).subtype
                continuous_subtype_val) =
          (sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
            (padicIntCondensedRingToPadicCondensedRing l) ≫ qIso.hom.hom := by
  classical
  let E := (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l))
  let e : ℚ_[l] ≃+* E := (IntermediateField.botEquiv ℚ_[l] (PadicAlgCl l)).symm.toRingEquiv
  have he (x : ℚ_[l]) : e x = algebraMap ℚ_[l] E x :=
    IntermediateField.botEquiv_symm x
  have hn (x : ℚ_[l]) : ‖e x‖ = ‖x‖ := by
    rw [he]
    change ‖algebraMap ℚ_[l] (PadicAlgCl l) x‖ = ‖x‖
    exact PadicAlgCl.norm_extends l x
  have hi : Isometry e := by
    intro x y
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, ← map_sub, hn]
  let f := AlgebraicGeometry.ProEtale.padicIntToIntegers l E
  have hf (z : ℤ_[l]) : (f z : E) = e (z : ℚ_[l]) := by
    exact (he _).symm
  have hbij : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply e.injective
      simpa only [← hf] using congrArg Subtype.val h
    · intro y
      have hy : ‖(y : E)‖ ≤ 1 := by
        exact_mod_cast y.property
      have hx : ‖e.symm (y : E)‖ ≤ 1 := by
        rwa [← hn, e.apply_symm_apply]
      refine ⟨⟨e.symm (y : E), hx⟩, ?_⟩
      apply Subtype.ext
      rw [hf, e.apply_symm_apply]
  let eInt : ℤ_[l] ≃+* PadicAlgCl.integers l E := RingEquiv.ofBijective f hbij
  have hiInt : Isometry eInt := by
    intro x y
    change edist (e (x : ℚ_[l])) (e (y : ℚ_[l])) = edist (x : ℚ_[l]) (y : ℚ_[l])
    exact hi _ _
  have his : Isometry e.symm := by
    intro x y
    simpa only [e.apply_symm_apply] using (hi (e.symm x) (e.symm y)).symm
  have hisInt : Isometry eInt.symm := by
    intro x y
    simpa only [eInt.apply_symm_apply] using (hiInt (eInt.symm x) (eInt.symm y)).symm
  refine ⟨e, eInt, RingHom.ext he, rfl, hi, his, hiInt, hisInt,
    coefficientIso e hi.continuous his.continuous,
    coefficientIso eInt hiInt.continuous hisInt.continuous, ?_⟩
  refine ⟨fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl, ?_⟩
  ext S a
  apply ULift.ext
  apply ContinuousMap.ext
  intro s
  exact hf _

end Profinite
