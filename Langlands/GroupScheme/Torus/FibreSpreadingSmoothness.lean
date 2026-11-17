import Langlands.GroupScheme.RelativeIdentityComponent
import Langlands.GroupScheme.Lie.SmoothOpenChart
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Smooth.Fiber

/-! # Smoothness of a flat group spreads from one residue fibre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace FibreSpreadingSmoothness

variable {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Restricting the source along an open immersion keeps a fibre smooth. -/
theorem smooth_fiber_comp_openImmersion {P : Scheme.{u}} (j : P ⟶ X) [IsOpenImmersion j]
    (f : X ⟶ Y) (y : Y) (h : Smooth (f.fiberToSpecResidueField y)) :
    Smooth ((j ≫ f).fiberToSpecResidueField y) := by
  have : Smooth (pullback.snd f (Y.fromSpecResidueField y)) := h
  rw [Scheme.Hom.fiberToSpecResidueField, ← pullbackRightPullbackFstIso_inv_snd_snd]
  infer_instance

/-- Fibres of a base change are base changes of fibres. -/
theorem smooth_fiber_of_isPullback {P Z W : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ W}
    {f : X ⟶ Z} {g : W ⟶ Z} (hp : IsPullback fst snd f g) (w : W)
    (h : Smooth (f.fiberToSpecResidueField (g w))) :
    Smooth (snd.fiberToSpecResidueField w) :=
  MorphismProperty.of_isPullback (isPullback_fiberToSpecResidueField_of_isPullback hp w) h

set_option backward.isDefEq.respectTransparency false in
/-- A flat, locally finitely presented morphism is smooth at every point of a smooth fibre. -/
theorem mem_smoothLocus_of_smooth_fiber (f : X ⟶ Y) [LocallyOfFinitePresentation f] [Flat f]
    (x : X) (h : Smooth (f.fiberToSpecResidueField (f x))) : x ∈ f.smoothLocus := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have hU : IsAffineOpen U := hU
  have hV : IsAffineOpen V := hV
  -- The fibre of the affine chart `Spec Γ(X, V) ⟶ Spec Γ(Y, U)` is smooth.
  let y : Spec Γ(Y, U) := hU.primeIdealOf ⟨f x, hVU hxV⟩
  have hy : hU.fromSpec y = f x := hU.fromSpec_primeIdealOf ⟨f x, hVU hxV⟩
  have hsq : hV.fromSpec ≫ f = Spec.map (f.appLE U V hVU) ≫ hU.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU).symm
  let l : Spec Γ(X, V) ⟶ pullback f hU.fromSpec := pullback.lift hV.fromSpec _ hsq
  have : IsOpenImmersion l := by
    have : IsOpenImmersion (l ≫ pullback.fst f hU.fromSpec) := by
      rw [pullback.lift_fst]; infer_instance
    exact IsOpenImmersion.of_comp l (pullback.fst f hU.fromSpec)
  have hfib : Smooth ((Spec.map (f.appLE U V hVU)).fiberToSpecResidueField y) := by
    have h₁ : Smooth ((pullback.snd f hU.fromSpec).fiberToSpecResidueField y) :=
      smooth_fiber_of_isPullback (IsPullback.of_hasPullback f hU.fromSpec) y (hy ▸ h)
    have h₂ := smooth_fiber_comp_openImmersion l _ y h₁
    rwa [pullback.lift_snd] at h₂
  have := f.finitePresentation_appLE hU hV hVU
  have := f.flat_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff U hU V hV hVU hxV]
  let p := y.asIdeal
  let q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV).1).symm⟩
  have : Algebra.FormallySmooth p.ResidueField (p.Fiber Γ(X, V)) := by
    rw [← RingHom.formallySmooth_algebraMap]
    refine RingHom.Smooth.formallySmooth ?_
    rw [← CommRingCat.hom_ofHom (algebraMap p.ResidueField (p.Fiber Γ(X, V))),
      ← HasRingHomProperty.Spec_iff (P := @Smooth),
      ← MorphismProperty.arrow_mk_iso_iff (P := @Smooth.{u})
        (Spec.fiberToSpecResidueFieldIso Γ(Y, U) Γ(X, V) y)]
    exact hfib
  exact Algebra.IsSmoothAt.of_formallySmooth_fiber p q

end FibreSpreadingSmoothness

open FibreSpreadingSmoothness in
set_option backward.isDefEq.respectTransparency false in
/-- **Smoothness spreads from a residue fibre.** If `G → S` is a flat, locally finitely
presented group scheme whose residue fibre at `s` is smooth, then `G` is smooth over an
open neighbourhood of `s`. -/
theorem exists_smooth_nhd_of_smooth_residueFiber {S : Scheme.{u}} (G : GroupScheme S)
    [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom] (s : S)
    (hs : Smooth (RelativeIdentityComponent.residueFiber G s).X.hom) :
    ∃ U : S.Opens, s ∈ U ∧ Smooth ((GroupScheme.baseChange U.ι).obj G).X.hom := by
  let e : S ⟶ G.X.left := η[G.X].left
  have he : e ≫ G.X.hom = 𝟙 S := Over.w η[G.X]
  have he' (t : S) : G.X.hom (e t) = t := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  let W := G.X.hom.smoothLocus
  have hW : Smooth (W.ι ≫ G.X.hom) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact W.ι_preimage_self
  -- Every residue fibre over `e ⁻¹ W` is smooth, by translating the smooth open chart.
  have hfib (t : S) (ht : e t ∈ W) : Smooth (G.X.hom.fiberToSpecResidueField t) := by
    let g := S.fromSpecResidueField t
    let H := RelativeIdentityComponent.residueFiber G t
    let C : Over (Spec (S.residueField t)) :=
      Over.mk (pullback.snd W.ι (pullback.fst G.X.hom g) ≫ pullback.snd G.X.hom g)
    let j : C ⟶ H.X := Over.homMk (pullback.snd W.ι (pullback.fst G.X.hom g)) rfl
    have : Smooth C.hom := by
      change Smooth (pullback.snd W.ι (pullback.fst G.X.hom g) ≫ pullback.snd G.X.hom g)
      rw [← pullbackRightPullbackFstIso_hom_snd]
      infer_instance
    have : Nonempty C.left := by
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.X.hom) (g := g)
        (e t) (IsLocalRing.closedPoint _) (by rw [he', Scheme.fromSpecResidueField_apply])
      obtain ⟨c, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := W.ι)
        (g := pullback.fst G.X.hom g) ⟨e t, ht⟩ z (by rw [hz]; rfl)
      exact ⟨c⟩
    have : IsOpenImmersion j.left :=
      inferInstanceAs (IsOpenImmersion (pullback.snd W.ι (pullback.fst G.X.hom g)))
    have : LocallyOfFiniteType H.X.hom :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom g))
    exact smooth_of_nonempty_smooth_open_chart (k := S.residueField t) H C j
  refine ⟨e ⁻¹ᵁ W, ?_, ?_⟩
  · change e s ∈ W
    refine mem_smoothLocus_of_smooth_fiber G.X.hom (e s) ?_
    rw [he' s]
    exact hs
  · change Smooth (pullback.snd G.X.hom (e ⁻¹ᵁ W).ι)
    refine Smooth.of_smooth_fiberToSpecResidueField _ fun y ↦ ?_
    exact smooth_fiber_of_isPullback (IsPullback.of_hasPullback G.X.hom (e ⁻¹ᵁ W).ι) y
      (hfib _ y.2)

end Langlands.GroupScheme
