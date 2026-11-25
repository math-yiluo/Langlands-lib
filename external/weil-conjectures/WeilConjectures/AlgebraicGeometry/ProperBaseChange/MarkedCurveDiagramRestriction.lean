/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.Curve.GenericModelAux

/-!
# Final shrinking of an existing marked curve diagram

## References

* Stacks Project, Tag 0GK7, final shrinking paragraphs
* Stacks Project, Tag 0GK7, the base restrictions in the final paragraphs
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem restriction_map_isPullback {A B V V' : Scheme.{u}}
    (h : A ⟶ B) (b : B ⟶ V) (a : V' ⟶ V) :
    IsPullback (pullback.fst (h ≫ b) a)
      (pullback.lift (pullback.fst (h ≫ b) a ≫ h) (pullback.snd (h ≫ b) a)
        (by simp [pullback.condition])) h (pullback.fst b a) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback b a)
  simpa only [pullback.lift_snd] using IsPullback.of_hasPullback (h ≫ b) a

private theorem restriction_fiber_properties {A B A' B' : Scheme.{u}}
    {a : A' ⟶ A} {p' : A' ⟶ B'} {p : A ⟶ B} {b : B' ⟶ B}
    (H : IsPullback a p' p b) [IsOpenImmersion b] (s : B')
    (hc : GeometricallyConnected (p.fiberToSpecResidueField (b s)))
    (hd : topologicalKrullDim (p.fiber (b s)) ≤ 1) :
    GeometricallyConnected (p'.fiberToSpecResidueField s) ∧
      topologicalKrullDim (p'.fiber s) ≤ 1 := by
  let φ : p'.fiber s ⟶ p.fiber (b s) :=
    pullback.map _ _ _ _ a (Spec.map (b.residueFieldMap s)) b H.w.symm (by simp)
  have Hf : IsPullback φ (p'.fiberToSpecResidueField s)
      (p.fiberToSpecResidueField (b s)) (Spec.map (b.residueFieldMap s)) :=
    isPullback_fiberToSpecResidueField_of_isPullback H s
  have hgc : GeometricallyConnected (p'.fiberToSpecResidueField s) :=
    MorphismProperty.of_isPullback Hf hc
  have hiso := Hf.isIso_fst_of_isIso
  exact ⟨hgc, (IsHomeomorph.topologicalKrullDim_eq _
    φ.homeomorph.isHomeomorph).le.trans hd⟩

/-- Restrict a marked curve diagram to a specified base open on which all its
fibres and marks already have the desired properties. The conclusion records the
cartesian comparisons needed to retain an independently supplied generic diagram.
-/
theorem exists_marked_curve_diagram_restriction
    {X S V Z : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (η : S) (hη : η ∈ U)
    (g : V ⟶ U.toScheme) [IsFinite g] [Surjective g] [UniversallyInjective g]
    (U₀ : U.toScheme.Opens) (hη₀ : (⟨η, hη⟩ : U.toScheme) ∈ U₀)
    (σ : Z ⟶ V) (hσ : ∀ z : Z, g (σ z) ∈ U₀)
    (n : ℕ) (T Y B : Fin n → Scheme.{u}) (t : ∀ i, T i ⟶ V)
    (j : ∀ i, Y i ⟶ B i) (p : ∀ i, B i ⟶ T i)
    (ν : (∐ Y) ⟶ pullback f (g ≫ U.ι)) [IsFinite ν] [Surjective ν]
    (hcomm : ∀ i, Sigma.ι Y i ≫ ν ≫ pullback.snd f (g ≫ U.ι) = j i ≫ p i ≫ t i)
    (ht : ∀ i, IsFinite (t i) ∧ Etale (t i))
    (hj : ∀ i, IsOpenImmersion (j i)) (hp : ∀ i, Smooth (p i) ∧ IsProper (p i))
    (W : (pullback f (g ≫ U.ι)).Opens) (hW : IsThickening (pullback.snd ν W.ι))
    (hgood : ∀ i (s : T i), (t i ≫ g) s ∈ U₀ →
      GeometricallyConnected ((p i).fiberToSpecResidueField s) ∧
      topologicalKrullDim ((p i).fiber s) ≤ 1 ∧
      s ∈ Set.range (((Sigma.ι Y i ≫ ν) ⁻¹ᵁ W).ι ≫ j i ≫ p i)) :
    ∃ (U' : S.Opens) (_ : η ∈ U') (V' : Scheme.{u}) (g' : V' ⟶ U'.toScheme),
      IsFinite g' ∧ Surjective g' ∧ UniversallyInjective g' ∧
      ∃ (aV : V' ⟶ V) (σ' : Z ⟶ V'),
        IsOpenImmersion aV ∧ σ' ≫ aV = σ ∧
        aV ≫ g ≫ U.ι = g' ≫ U'.ι ∧
        ∃ (T' Y' B' : Fin n → Scheme.{u})
          (t' : ∀ i, T' i ⟶ V') (j' : ∀ i, Y' i ⟶ B' i)
          (p' : ∀ i, B' i ⟶ T' i)
          (ν' : (∐ Y') ⟶ pullback f (g' ≫ U'.ι)),
          IsFinite ν' ∧ Surjective ν' ∧
          (∀ i, Sigma.ι Y' i ≫ ν' ≫ pullback.snd f (g' ≫ U'.ι) =
            j' i ≫ p' i ≫ t' i) ∧
          (∀ i, IsFinite (t' i) ∧ Etale (t' i)) ∧
          (∀ i, IsOpenImmersion (j' i)) ∧
          (∀ i, Smooth (j' i ≫ p' i) ∧ Surjective (j' i ≫ p' i)) ∧
          (∀ i, Smooth (p' i) ∧ IsProper (p' i) ∧
            ∀ s : T' i, GeometricallyConnected ((p' i).fiberToSpecResidueField s) ∧
              topologicalKrullDim ((p' i).fiber s) ≤ 1) ∧
          (∃ W' : (pullback f (g' ≫ U'.ι)).Opens,
            (∀ i, Surjective (((Sigma.ι Y' i ≫ ν') ⁻¹ᵁ W').ι ≫ j' i ≫ p' i)) ∧
            IsThickening (pullback.snd ν' W'.ι)) ∧
          ∃ (aY : ∀ i, Y' i ⟶ Y i) (aB : ∀ i, B' i ⟶ B i)
            (aT : ∀ i, T' i ⟶ T i),
            ∀ i,
              IsPullback (aY i) (j' i ≫ p' i ≫ t' i) (j i ≫ p i ≫ t i) aV ∧
              IsPullback (aB i) (p' i ≫ t' i) (p i ≫ t i) aV ∧
              IsPullback (aT i) (t' i) (t i) aV ∧
              j' i ≫ aB i = aY i ≫ j i ∧ p' i ≫ aT i = aB i ≫ p i := by
  classical
  let V₀ := g ⁻¹ᵁ U₀
  let aV : V₀.toScheme ⟶ V := V₀.ι
  let U' := U.ι ''ᵁ U₀
  let e := U.ι.isoImage U₀
  let g' : V₀.toScheme ⟶ U'.toScheme := g ∣_ U₀ ≫ e.hom
  have hη' : η ∈ U' := ⟨⟨η, hη⟩, hη₀, rfl⟩
  have hgr : IsFinite (g ∣_ U₀) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict g U₀).flip inferInstance
  have hgs : Surjective (g ∣_ U₀) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict g U₀).flip inferInstance
  have hgu : UniversallyInjective (g ∣_ U₀) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict g U₀).flip inferInstance
  have hg' : IsFinite g' := by dsimp [g']; infer_instance
  have hgs' : Surjective g' := by dsimp [g']; infer_instance
  have hgu' : UniversallyInjective g' := by
    let : MorphismProperty.RespectsIso (@UniversallyInjective.{u}) :=
      UniversallyInjective.respectsIso
    exact MorphismProperty.RespectsIso.postcomp @UniversallyInjective e.hom _ hgu
  have hbase : aV ≫ g ≫ U.ι = g' ≫ U'.ι := by
    dsimp [g', e, U', aV, V₀]
    rw [Category.assoc, Scheme.Hom.isoImage_hom_ι, morphismRestrict_ι_assoc]
  have hσrange : Set.range σ ⊆ Set.range aV := by
    rintro _ ⟨z, rfl⟩
    exact (Scheme.Opens.range_ι V₀).symm ▸ hσ z
  let σ' := IsOpenImmersion.lift aV σ hσrange
  let T' (i : Fin n) := pullback (t i) aV
  let B' (i : Fin n) := pullback (p i ≫ t i) aV
  let Y' (i : Fin n) := pullback (j i ≫ p i ≫ t i) aV
  let aT (i : Fin n) : T' i ⟶ T i := pullback.fst (t i) aV
  let aB (i : Fin n) : B' i ⟶ B i := pullback.fst (p i ≫ t i) aV
  let aY (i : Fin n) : Y' i ⟶ Y i := pullback.fst (j i ≫ p i ≫ t i) aV
  let t' (i : Fin n) : T' i ⟶ V₀.toScheme := pullback.snd (t i) aV
  let q' (i : Fin n) : B' i ⟶ V₀.toScheme := pullback.snd (p i ≫ t i) aV
  let r' (i : Fin n) : Y' i ⟶ V₀.toScheme := pullback.snd (j i ≫ p i ≫ t i) aV
  let p' (i : Fin n) : B' i ⟶ T' i :=
    pullback.lift (aB i ≫ p i) (q' i) (by simp [aB, q', pullback.condition])
  let j' (i : Fin n) : Y' i ⟶ B' i :=
    pullback.lift (aY i ≫ j i) (r' i) (by simp [aY, r', pullback.condition])
  have hpT (i : Fin n) : p' i ≫ t' i = q' i := by simp [p', t']
  have hjT (i : Fin n) : j' i ≫ p' i ≫ t' i = r' i := by
    rw [hpT]; simp [j', q']
  have hpB (i : Fin n) : IsPullback (aB i) (p' i) (p i) (aT i) :=
    restriction_map_isPullback (p i) (t i) aV
  have hjB (i : Fin n) : IsPullback (aY i) (j' i) (j i) (aB i) :=
    restriction_map_isPullback (j i) (p i ≫ t i) aV
  have hjp (i : Fin n) : IsPullback (aY i) (j' i ≫ p' i) (j i ≫ p i) (aT i) :=
    (hjB i).paste_vert (hpB i)
  have ht' (i : Fin n) : IsFinite (t' i) ∧ Etale (t' i) :=
    ⟨MorphismProperty.of_isPullback (.of_hasPullback _ _) (ht i).1,
      MorphismProperty.of_isPullback (.of_hasPullback _ _) (ht i).2⟩
  have hj' (i : Fin n) : IsOpenImmersion (j' i) :=
    MorphismProperty.of_isPullback (hjB i) (hj i)
  have hp' (i : Fin n) : Smooth (p' i) ∧ IsProper (p' i) :=
    ⟨MorphismProperty.of_isPullback (hpB i) (hp i).1,
      MorphismProperty.of_isPullback (hpB i) (hp i).2⟩
  let F := pullback.snd f (g ≫ U.ι)
  let F' := pullback.snd f (g' ≫ U'.ι)
  let aX : pullback f (g' ≫ U'.ι) ⟶ pullback f (g ≫ U.ι) :=
    pullback.lift (pullback.fst _ _) (F' ≫ aV) (by
      calc
        _ = F' ≫ (g' ≫ U'.ι) := pullback.condition
        _ = (F' ≫ aV) ≫ g ≫ U.ι := by
          simpa only [Category.assoc] using
            congrArg (fun k ↦ F' ≫ k) hbase.symm)
  have HX : IsPullback aX F' F aV := by
    apply IsPullback.of_right (h₁₂ := pullback.fst f (g ≫ U.ι))
      (h₂₂ := g ≫ U.ι)
    · simpa only [aX, pullback.lift_fst, Category.assoc, hbase] using
        (IsPullback.of_hasPullback f (g' ≫ U'.ι))
    · simp [aX, F]
    · exact .of_hasPullback _ _
  let v' (i : Fin n) : Y' i ⟶ pullback f (g' ≫ U'.ι) :=
    HX.lift (aY i ≫ Sigma.ι Y i ≫ ν) (r' i) (by
      rw [Category.assoc, Category.assoc, hcomm i]
      exact pullback.condition)
  let ν' : (∐ Y') ⟶ pullback f (g' ≫ U'.ι) := Sigma.desc v'
  have hνcomm (i : Fin n) : Sigma.ι Y' i ≫ ν' ≫ F' = j' i ≫ p' i ≫ t' i := by
    simp only [ν', Sigma.ι_comp_desc_assoc, v', IsPullback.lift_snd]
    exact (hjT i).symm
  have HY (i : Fin n) : IsPullback (aY i) (r' i) (j i ≫ p i ≫ t i) aV :=
    .of_hasPullback _ _
  have HV (i : Fin n) : IsPullback (aY i) (r' i) (Sigma.ι Y i ≫ ν ≫ F) aV := by
    simpa only [F, hcomm i] using HY i
  have Hνi (i : Fin n) : IsPullback (aY i) (v' i) (Sigma.ι Y i ≫ ν) aX :=
    by
      refine IsPullback.of_bot ?_ (by simp [v']) HX
      simpa only [v', IsPullback.lift_snd, Category.assoc] using HV i
  have Hν : IsPullback (Limits.Sigma.map aY) ν' ν aX := by
    have H := isPullback_sigmaDesc (fun i ↦ Sigma.ι Y i ≫ ν) v' aY aX Hνi
    have he : Sigma.desc (fun i ↦ Sigma.ι Y i ≫ ν) = ν := by
      apply Sigma.hom_ext
      intro i
      exact Sigma.ι_comp_desc _ _
    simpa only [he] using H
  have hνfinite : IsFinite ν' := MorphismProperty.of_isPullback Hν inferInstance
  have hνsurjective : Surjective ν' := MorphismProperty.of_isPullback Hν inferInstance
  have hpoint (i : Fin n) (s : T' i) : (t i ≫ g) (aT i s) ∈ U₀ := by
    have he := congrArg (fun h : T' i ⟶ V ↦ h s) (pullback.condition (f := t i) (g := aV))
    change g (t i (aT i s)) ∈ U₀
    rw [show t i (aT i s) = aV (t' i s) from he]
    exact (t' i s).2
  have hpfib (i : Fin n) : Smooth (p' i) ∧ IsProper (p' i) ∧
      ∀ s : T' i, GeometricallyConnected ((p' i).fiberToSpecResidueField s) ∧
        topologicalKrullDim ((p' i).fiber s) ≤ 1 := by
    refine ⟨(hp' i).1, (hp' i).2, fun s ↦ ?_⟩
    obtain ⟨hc, hd, _⟩ := hgood i (aT i s) (hpoint i s)
    exact restriction_fiber_properties (hpB i) s hc hd
  let W' := aX ⁻¹ᵁ W
  have hmark (i : Fin n) :
      Surjective (((Sigma.ι Y' i ≫ ν') ⁻¹ᵁ W').ι ≫ j' i ≫ p' i) := by
    refine ⟨fun s ↦ ?_⟩
    obtain ⟨y, hy⟩ := (hgood i (aT i s) (hpoint i s)).2.2
    obtain ⟨y', hya, hys⟩ := Scheme.exists_preimage_of_isPullback (hjp i) y.1 s hy
    have hymem : y' ∈ (Sigma.ι Y' i ≫ ν') ⁻¹ᵁ W' := by
      change ((Sigma.ι Y' i ≫ ν') ≫ aX) y' ∈ W
      simp only [ν', Sigma.ι_comp_desc]
      rw [(Hνi i).w.symm]
      have hyW : (Sigma.ι Y i ≫ ν) y.1 ∈ W := y.2
      simpa only [Scheme.Hom.comp_apply, hya] using hyW
    exact ⟨⟨y', hymem⟩, hys⟩
  have hjp' (i : Fin n) : Smooth (j' i ≫ p' i) ∧ Surjective (j' i ≫ p' i) := by
    have : IsOpenImmersion (j' i) := hj' i
    have : Smooth (p' i) := (hp' i).1
    refine ⟨inferInstance, ⟨fun s ↦ ?_⟩⟩
    obtain ⟨y, hy⟩ := (hmark i).surj s
    exact ⟨y.1, hy⟩
  have hthick : IsThickening (pullback.snd ν' W'.ι) := by
    have hc : IsClosedImmersion (ν ∣_ W) := by
      have : IsClosedImmersion (pullback.snd ν W.ι) := hW.1
      dsimp [morphismRestrict]; infer_instance
    have hs : Surjective (ν ∣_ W) := by
      have : Surjective (pullback.snd ν W.ι) := hW.2
      dsimp [morphismRestrict]; infer_instance
    obtain ⟨_, _, HW⟩ := AlgebraicGeometry.IsPullback.exists_isPullback_morphismRestrict Hν W
    have hc' : IsClosedImmersion (ν' ∣_ W') := MorphismProperty.of_isPullback HW hc
    have hs' : Surjective (ν' ∣_ W') := MorphismProperty.of_isPullback HW hs
    have he : pullback.snd ν' W'.ι = (pullbackRestrictIsoRestrict ν' W').hom ≫ ν' ∣_ W' :=
      (pullbackRestrictIsoRestrict_hom_morphismRestrict _ _).symm
    rw [he]
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨U', hη', V₀.toScheme, g', hg', hgs', hgu', aV, σ', inferInstance,
    IsOpenImmersion.lift_fac _ _ _, hbase, T', Y', B', t', j', p', ν',
    hνfinite, hνsurjective, hνcomm, ht', hj', hjp', hpfib, ⟨W', hmark, hthick⟩,
    aY, aB, aT, fun i ↦ ?_⟩
  refine ⟨?_, ?_, .of_hasPullback _ _, (hjB i).w.symm, (hpB i).w.symm⟩
  · rw [hjT]; exact HY i
  · rw [hpT]; exact .of_hasPullback _ _

end AlgebraicGeometry
