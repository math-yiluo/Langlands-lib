/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiberDegreeBound
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.EtaleSplitsOffQuasiFinitePart
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant

/-!
# Étale neighbourhoods of points of maximal fibre degree

Source: Stacks Project, More on Morphisms, Tag 07RY, proof, second paragraph.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

set_option backward.isDefEq.respectTransparency false in
/-- The global sections of a finite scheme over a field form a finite module. -/
private theorem finite_globalSections_of_isFinite
    {K : Type u} [Field K] {Y : Scheme.{u}} (h : Y ⟶ Spec (.of K)) [IsFinite h] :
    let := h.ΓAlgebra
    Module.Finite K Γ(Y, ⊤) := by
  let := h.ΓAlgebra
  apply RingHom.finite_algebraMap.mp
  change (((Scheme.ΓSpecIso (.of K)).inv ≫ h.appTop).hom).Finite
  rw [CommRingCat.hom_comp, RingHom.finite_respectsIso.cancel_left_isIso]
  exact h.finite_appTop

set_option backward.isDefEq.respectTransparency false in
/-- A cartesian square preserves finiteness and degree of a finite fibre.
The affine fibre comparison gives scalar extension, whose dimension is unchanged. -/
private theorem finite_fiber_degree_of_pullback
    {Y T X S : Scheme.{u}} {g : Y ⟶ T} {p : Y ⟶ X} {f : X ⟶ S} {φ : T ⟶ S}
    (H : IsPullback p g f φ) (t : T) (hf : IsFinite (f.fiberToSpecResidueField (φ t))) :
    IsFinite (g.fiberToSpecResidueField t) ∧ g.fiberDegree t = f.fiberDegree (φ t) := by
  have := hf
  have H' := isPullback_fiberToSpecResidueField_of_isPullback H t
  have hg : IsFinite (g.fiberToSpecResidueField t) := MorphismProperty.of_isPullback H' hf
  refine ⟨hg, ?_⟩
  have hX : IsAffine (f.fiber (φ t)) :=
    isAffine_of_isAffineHom (f.fiberToSpecResidueField (φ t))
  let := (φ.residueFieldMap t).hom.toAlgebra
  obtain ⟨e⟩ := nonempty_algEquiv_tensorProduct_Γ_of_isPullback
    (X := f.fiber (φ t)) (Y := g.fiber t) (φ.residueFieldMap t) H'
  change Module.finrank _ _ = Module.finrank _ _
  rw [← e.toLinearEquiv.finrank_eq]
  exact Module.finrank_baseChange

set_option backward.isDefEq.respectTransparency false in
/-- Compute additivity on the finite fibre, where the affine additivity theorem applies.
The fibre restriction isomorphisms identify the two summands with the restricted degrees. -/
private theorem fiberDegree_add_of_finite_fiber
    {Y T : Scheme.{u}} (g : Y ⟶ T) (t : T)
    (hg : IsFinite (g.fiberToSpecResidueField t))
    (W V : Y.Opens) (hWV : IsCompl W V) :
    g.fiberDegree t = (W.ι ≫ g).fiberDegree t + (V.ι ≫ g).fiberDegree t := by
  have := hg
  let h := g.fiberToSpecResidueField t
  let A := g.fiberι t ⁻¹ᵁ W
  let B := g.fiberι t ⁻¹ᵁ V
  have hAB : IsCompl A B := by
    constructor
    · rw [disjoint_iff]
      change g.fiberι t ⁻¹ᵁ W ⊓ g.fiberι t ⁻¹ᵁ V = ⊥
      rw [← Scheme.Hom.preimage_inf, hWV.inf_eq_bot]
      rfl
    · rw [codisjoint_iff]
      change g.fiberι t ⁻¹ᵁ W ⊔ g.fiberι t ⁻¹ᵁ V = ⊤
      rw [← Scheme.Hom.preimage_sup, hWV.sup_eq_top]
      rfl
  have := isClosedImmersion_ι_of_isCompl_left hAB
  have := isClosedImmersion_ι_of_isCompl_right hAB
  let z : Spec (T.residueField t) := IsLocalRing.closedPoint _
  have hmod : Module.Finite ((Spec (T.residueField t)).residueField z)
      Γ(h.fiber z, ⊤) := finite_globalSections_of_isFinite (h.fiberToSpecResidueField z)
  have he := h.fiberDegree_of_isCompl z hAB
  rw [fiberDegree_eq_finrankΓ h z, fiberDegree_eq_finrankΓ (A.ι ≫ h) z,
    fiberDegree_eq_finrankΓ (B.ι ≫ h) z] at he
  have hc (O : Y.Opens) : (O.ι ≫ g).fiberDegree t =
      ((g.fiberι t ⁻¹ᵁ O).ι ≫ h).finrankΓ := by
    exact finrankΓ_eq_of_iso _ _ (g.fiberRestrictIso t O) (Iso.refl _) (by
      simpa [h] using g.fiberRestrictIso_hom_ι_fiberToSpecResidueField t O)
  rw [hc W, hc V]
  exact he

set_option backward.isDefEq.respectTransparency false in
/-- A clopen part of a finite fibre is finite; transport along the fibre restriction iso. -/
private theorem finite_fiber_of_clopen
    {Y T : Scheme.{u}} (g : Y ⟶ T) (t : T) (hg : IsFinite (g.fiberToSpecResidueField t))
    (W V : Y.Opens) (hWV : IsCompl W V) :
    IsFinite ((W.ι ≫ g).fiberToSpecResidueField t) := by
  have := hg
  have hAB : IsCompl (g.fiberι t ⁻¹ᵁ W) (g.fiberι t ⁻¹ᵁ V) := by
    constructor
    · rw [disjoint_iff, ← Scheme.Hom.preimage_inf, hWV.inf_eq_bot]
      rfl
    · rw [codisjoint_iff, ← Scheme.Hom.preimage_sup, hWV.sup_eq_top]
      rfl
  have := isClosedImmersion_ι_of_isCompl_left hAB
  have he := g.fiberRestrictIso_hom_ι_fiberToSpecResidueField t W
  rw [← he]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- A finite fibre of degree zero has the zero ring of sections, hence empty spectrum. -/
private theorem isEmpty_fiber_of_finite_degree_zero
    {Y T : Scheme.{u}} (g : Y ⟶ T) (t : T) [IsFinite (g.fiberToSpecResidueField t)]
    (hzero : g.fiberDegree t = 0) : IsEmpty (g.fiber t) := by
  have : IsAffine (g.fiber t) := isAffine_of_isAffineHom (g.fiberToSpecResidueField t)
  have : Module.Finite (T.residueField t) Γ(g.fiber t, ⊤) :=
    finite_globalSections_of_isFinite (g.fiberToSpecResidueField t)
  have : Subsingleton Γ(g.fiber t, ⊤) := Module.finrank_zero_iff.mp hzero
  have : IsEmpty (Spec Γ(g.fiber t, ⊤)) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum Γ(g.fiber t, ⊤)))
  exact Function.isEmpty (g.fiber t).isoSpec.hom

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- A point of maximal degree has an étale neighbourhood on which the pullback is finite
locally free of that degree.
Source: Stacks Project, More on Morphisms, Tag 07RY, proof, second paragraph.
(blueprint: lem-weil-pbc-flat-fp-lqf-maximal-degree-etale-neighborhood)

Proof: the finite fibre over `s` has finitely many points. An elementary étale
neighbourhood splits the pullback into complementary open parts `W` and `V`, with `V`
finite and `W` having empty fibre at the distinguished point (Tag 02LP). The finite
part is flat and locally of finite presentation by base change and restriction, hence
finite locally free. Shrink the neighbourhood to the locus where its degree equals
its degree at the distinguished point, using local constancy of degree (Tag 04MH).
That degree is `m`: finite fibre degrees are invariant under residue-field extension,
and the fibre of `W` is empty. At any point of the shrunken neighbourhood, the fibre of
the whole pullback is finite of degree at most `m`. Its decomposition into the fibres
of `W` and `V` gives a product of rings of global sections, and therefore an additive
degree formula. Since the `V` degree is `m`, the `W` degree is zero. A finite scheme
over a field with zero-dimensional global sections is empty: its ring of global
sections is the zero ring, and it is the spectrum of this ring. Thus every fibre of
`W` is empty, and every point of `W` would belong to one of these fibres; hence `W` is
empty. The whole pullback equals the finite locally free part of degree `m`.
Restriction preserves the distinguished point and étaleness, giving the result.
For `m = 0` the same argument makes both parts empty. An unattained bound and an empty
base have no point satisfying the hypotheses, so impose no additional assertion. -/
theorem exists_etale_isFiniteLocallyFreeOfDegree_of_maximal_fiber_degree
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [IsSeparated f] (h_lqf : IsLocallyQuasiFinite f) (m : ℕ)
    (hm : BoundsFiberDegrees f m) (s : S)
    (hs : (f.fiberToSpecResidueField s).finrankΓ = m) :
    ∃ (T : Scheme.{u}) (φ : T ⟶ S) (t : T), Etale φ ∧ φ t = s ∧
      (pullback.snd f φ).IsFiniteLocallyFreeOfDegree m := by
  classical
  have hfin : Finite (f.fiber s) := by
    have := (hm s).1
    let h := f.fiberToSpecResidueField s
    have hh : (Set.univ : Set (f.fiber s)).Finite :=
      (h.finite_preimage_singleton (IsLocalRing.closedPoint _)).subset
        (by intro x _; exact Subsingleton.elim _ _)
    exact Set.finite_univ_iff.mp hh
  have hisolated : Set.Finite {x : f.fiber s | IsOpen ({x} : Set (f.fiber s))} :=
    Set.toFinite _
  obtain ⟨U, φ, u, hφ, hu, _, W, V, hWV, hV, _, hW⟩ :=
    exists_etale_splits_off_quasiFinitePart f s hisolated
  have := hφ
  have := hV
  let g := pullback.fst φ f
  have : (V.ι ≫ g).IsFiniteLocallyFree := {}
  obtain ⟨_, _, _, O, hO, hdegree⟩ :=
    finiteLocallyFree_fiberDimension_isLocallyConstant (V.ι ≫ g)
  have hbase (x : U) : IsFinite (g.fiberToSpecResidueField x) ∧
      g.fiberDegree x = f.fiberDegree (φ x) :=
    finite_fiber_degree_of_pullback (IsPullback.of_hasPullback φ f).flip x (hm (φ x)).1
  have hempty : IsEmpty ((W.ι ≫ g).fiber u) := hW (by
    have : Finite (f ⁻¹' ({s} : Set S)) :=
      Finite.of_equiv (f.fiber s) (f.fiberHomeo s).toEquiv
    exact Set.toFinite _)
  have hdu : (V.ι ≫ g).fiberDegree u = m := by
    have hadd := fiberDegree_add_of_finite_fiber g u (hbase u).1 W V hWV
    have hzero : (W.ι ≫ g).fiberDegree u = 0 := by
      exact Module.finrank_zero_of_subsingleton
    have hmax : g.fiberDegree u = m := by
      rw [(hbase u).2, hu]
      exact hs
    omega
  let Oₘ := O m
  let uₘ : Oₘ := ⟨u, (hO m u).mpr hdu⟩
  let g' := g ∣_ Oₘ
  let j := (g ⁻¹ᵁ Oₘ).ι
  let W' := j ⁻¹ᵁ W
  let V' := j ⁻¹ᵁ V
  have hWV' : IsCompl W' V' := by
    constructor
    · rw [disjoint_iff]
      change j ⁻¹ᵁ W ⊓ j ⁻¹ᵁ V = ⊥
      rw [← Scheme.Hom.preimage_inf, hWV.inf_eq_bot]
      rfl
    · rw [codisjoint_iff]
      change j ⁻¹ᵁ W ⊔ j ⁻¹ᵁ V = ⊤
      rw [← Scheme.Hom.preimage_sup, hWV.sup_eq_top]
      rfl
  have H₀ : IsPullback j g' g Oₘ.ι := (isPullback_morphismRestrict g Oₘ).flip
  have HV : IsPullback (j ∣_ V) (V'.ι ≫ g') (V.ι ≫ g) Oₘ.ι :=
    (isPullback_morphismRestrict j V).paste_vert H₀
  let v := (V.ι ≫ g) ∣_ Oₘ
  let e := HV.isoPullback ≪≫
    ((isPullback_morphismRestrict (V.ι ≫ g) Oₘ).flip).isoPullback.symm
  have he : e.hom ≫ v = V'.ι ≫ g' := by simp [e, v]
  have hv : v.IsFiniteLocallyFreeOfDegree m := hdegree m
  have := hv
  have hv' : IsFinite (V'.ι ≫ g') := by rw [← he]; infer_instance
  have hdeg' (x : Oₘ) : (V'.ι ≫ g').fiberDegree x = m := by
    rw [← he, fiberDegree_comp_left_of_isIso]
    exact hv.fiberDegree_eq x
  have hbase' (x : Oₘ) : IsFinite (g'.fiberToSpecResidueField x) ∧
      g'.fiberDegree x = g.fiberDegree (Oₘ.ι x) :=
    finite_fiber_degree_of_pullback H₀ x (hbase (Oₘ.ι x)).1
  have hzero (x : Oₘ) : (W'.ι ≫ g').fiberDegree x = 0 := by
    have hadd := fiberDegree_add_of_finite_fiber g' x (hbase' x).1 W' V' hWV'
    have hbound : g'.fiberDegree x ≤ m := by
      rw [(hbase' x).2, (hbase (Oₘ.ι x)).2]
      exact (hm (φ (Oₘ.ι x))).2
    have hd := hdeg' x
    omega
  have hempty' : IsEmpty W'.toScheme := by
    refine ⟨fun w ↦ ?_⟩
    let x := (W'.ι ≫ g') w
    have := finite_fiber_of_clopen g' x (hbase' x).1 W' V' hWV'
    have := isEmpty_fiber_of_finite_degree_zero (W'.ι ≫ g') x (hzero x)
    exact isEmptyElim ((W'.ι ≫ g').asFiber w)
  have hVtop : V' = ⊤ := by
    have hWbot : W' = ⊥ := by
      ext y
      constructor
      · intro hy
        exact isEmptyElim (show W'.toScheme from ⟨y, hy⟩)
      · simp
    simpa [hWbot] using hWV'.sup_eq_top
  have hVi : IsIso V'.ι := by
    rw [hVtop]
    exact (g ⁻¹ᵁ Oₘ).toScheme.topIso.isIso_hom
  have hfinite : IsFinite g' :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) V'.ι g').mp hv'
  have hfree : g'.IsFiniteLocallyFreeOfDegree m :=
    { fiberDegree_eq := fun x ↦ by
        rw [← fiberDegree_comp_left_of_isIso V'.ι g' x]
        exact hdeg' x }
  let ψ := Oₘ.ι ≫ φ
  have H := H₀.paste_horiz (IsPullback.of_hasPullback φ f).flip
  let a := H.isoPullback
  have ha : a.inv ≫ g' = pullback.snd f ψ := by simp [a, ψ]
  have hp : IsFinite (pullback.snd f ψ) := by rw [← ha]; infer_instance
  refine ⟨Oₘ.toScheme, ψ, uₘ, inferInstance, ?_, ?_⟩
  · exact hu
  · refine { fiberDegree_eq := fun x ↦ ?_ }
    rw [← ha, fiberDegree_comp_left_of_isIso]
    exact hfree.fiberDegree_eq x

end AlgebraicGeometry.Scheme.Hom
