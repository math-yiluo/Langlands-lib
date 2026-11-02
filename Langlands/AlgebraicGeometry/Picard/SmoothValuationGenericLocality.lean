import Langlands.AlgebraicGeometry.Picard.SmoothValuationGenericNeighbourhood

/-! # Locality of total generic trivializing neighbourhoods -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- A neighbourhood on an open chart gives a neighbourhood of the
corresponding total point in a cartesian square of open immersions. -/
theorem nonempty_genericTrivializingNeighbourhood_of_isPullback
    {X Y U V : Scheme.{u}} (q : Y ⟶ X) (q' : V ⟶ U)
    (i : V ⟶ Y) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
    (H : IsPullback q' i j q) (D : LineBundle Y) (x : U)
    (a : GenericTrivializingNeighbourhood q' ((LineBundle.pullback i).obj D) x) :
    Nonempty (GenericTrivializingNeighbourhood q D (j x)) := by
  let W := q' ⁻¹ᵁ a.neighbourhood
  let T := j ''ᵁ a.neighbourhood
  let S := q ⁻¹ᵁ T
  let f := W.ι ≫ i
  have hf : Set.range f = Set.range S.ι := by
    change Set.range (W.ι ≫ i) = Set.range S.ι
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    simpa only [Scheme.Opens.range_ι, Scheme.Hom.coe_image] using
      congrArg SetLike.coe
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H a.neighbourhood)
  let e := IsOpenImmersion.isoOfRangeEq f S.ι hf
  have he : e.hom ≫ S.ι = f := IsOpenImmersion.isoOfRangeEq_hom_fac f S.ι hf
  have h : Nonempty ((Scheme.Modules.pullback e.hom).obj (D.obj.restrict S.ι) ≅
      SheafOfModules.unit W.toScheme.ringCatSheaf) :=
    ⟨(Scheme.Modules.pullback e.hom).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback S.ι).app D.obj) ≪≫
      (Scheme.Modules.pullbackComp e.hom S.ι).app D.obj ≪≫
      (Scheme.Modules.pullbackCongr he).app D.obj ≪≫
      ((Scheme.Modules.pullbackComp W.ι i).app D.obj).symm ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app
        ((Scheme.Modules.pullback i).obj D.obj)).symm ≪≫ a.trivialization⟩
  obtain ⟨t⟩ := nonempty_trivialization_of_pullback_iso e (D.obj.restrict S.ι) h
  exact ⟨⟨T, ⟨x, a.mem, rfl⟩, t⟩⟩

/-- A result for the actual base change of an open chart yields
neighbourhoods of the chart's points in the original base change. -/
theorem nonempty_genericTrivializingNeighbourhood_of_baseChange_chart
    {S T X U : Scheme.{u}} (p : X ⟶ S) (b : T ⟶ S)
    (j : U ⟶ X) [IsOpenImmersion j]
    (h : ∀ E : LineBundle (pullback (j ≫ p) b),
      HasGenericTrivializingNeighbourhoods (pullback.fst _ _) E)
    (D : LineBundle (pullback p b)) (x : U) :
    Nonempty (GenericTrivializingNeighbourhood (pullback.fst p b) D (j x)) := by
  let q := pullback.fst p b
  let i := pullback.fst q j
  let q' := pullback.snd q j
  have H : IsPullback q' i j q := (IsPullback.of_hasPullback q j).flip
  have H' := H.paste_vert (IsPullback.of_hasPullback p b)
  let e := H'.isoPullback
  have he : e.inv ≫ q' = pullback.fst (j ≫ p) b := H'.isoPullback_inv_fst
  let D' := (LineBundle.pullback i).obj D
  have ht : HasGenericTrivializingNeighbourhoods q' D' := by
    apply hasGenericTrivializingNeighbourhoods_of_iso q' e.symm D'
    simpa only [Iso.symm_hom, he] using
      h ((LineBundle.pullback e.inv).obj D')
  obtain ⟨a⟩ := ht x
  exact nonempty_genericTrivializingNeighbourhood_of_isPullback q q' i j H D x a

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The affine result applies to any actual smooth morphism of spectra,
with the coefficient algebra recovered from that morphism. -/
theorem hasGenericTrivializingNeighbourhoods_specSource
    {A : Type u} [CommRing A]
    (p : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) [Smooth p]
    (D : LineBundle (pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    HasGenericTrivializingNeighbourhoods (pullback.fst _ _) D := by
  let g := Spec.homEquiv p
  let : Algebra R A := g.hom.toAlgebra
  have hp : Spec.map (CommRingCat.ofHom (algebraMap R A)) = p :=
    Spec.homEquiv.symm_apply_apply p
  have hs : g.hom.Smooth := (HasRingHomProperty.Spec_iff (P := @Smooth)).mp
    (show Smooth (Spec.map g) from hp.symm ▸ inferInstance)
  have : Algebra.Smooth R A := RingHom.smooth_algebraMap.mp hs
  revert D
  rw [← hp]
  exact hasGenericTrivializingNeighbourhoods_affinePullback (R := R) (A := A) K

/-- Any generic line bundle on a smooth scheme over an arbitrary
valuation domain is trivial over inverse images of total open
neighbourhoods of all total points. -/
theorem hasGenericTrivializingNeighbourhoods_of_smooth
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R)) [Smooth p]
    (D : LineBundle (pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    HasGenericTrivializingNeighbourhoods (pullback.fst _ _) D := by
  intro x
  obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
  let U := X.affineCover.X i
  let j := U.isoSpec.inv ≫ X.affineCover.f i
  have : IsOpenImmersion j := inferInstance
  have : Smooth (j ≫ p) := inferInstance
  have h := nonempty_genericTrivializingNeighbourhood_of_baseChange_chart p
    (Spec.map (CommRingCat.ofHom (algebraMap R K))) j
    (hasGenericTrivializingNeighbourhoods_specSource K (j ≫ p)) D (U.isoSpec.hom y)
  simpa only [j, ← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc] using h

/-- Choose an actual total neighbourhood and actual generic
restriction-sheaf trivialization at a point of a smooth valuation scheme. -/
def smoothGenericTrivializingNeighbourhood
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R)) [Smooth p]
    (D : LineBundle (pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (x : X) : GenericTrivializingNeighbourhood (pullback.fst _ _) D x :=
  (hasGenericTrivializingNeighbourhoods_of_smooth K p D x).some

end Langlands.AlgebraicGeometry.Picard
