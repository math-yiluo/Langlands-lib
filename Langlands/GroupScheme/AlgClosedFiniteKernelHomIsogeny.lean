import Langlands.AbelianScheme.Isogeny
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.AbelianScheme.KernelFiberTranslation
import Langlands.AbelianScheme.SmoothGeometricIntegralityProof
import Langlands.AlgebraicGeometry.FiniteGenericFlatProof
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Finite-kernel surjective homomorphisms over algebraically closed fields are isogenies

This module generalizes the Library's endomorphism results
`fieldFiniteKernelQuasiFinite` and `translationFlat` to homomorphisms `f : G ⟶ H`
between two group objects over an algebraically closed field. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace Langlands.GroupScheme.HomIsogeny

/-! ## Quasi-finiteness from a finite kernel -/

/-- Kernel finiteness survives arbitrary base change. -/
lemma finite_kernel_baseChange {S T : Scheme.{u}} (b : T ⟶ S)
    {G H : Grp (Over S)} (f : G ⟶ H) [IsFinite (kernel f).X.hom] :
    IsFinite (kernel ((Over.pullback b).mapGrp.map f)).X.hom := by
  let e := (Grp.forget (Over T)).mapIso (kernelBaseChangeIso b f)
  have h : IsFinite (((Over.pullback b).mapGrp.obj (kernel f)).X.hom) :=
    inferInstanceAs (IsFinite (pullback.snd (kernel f).X.hom b))
  have he : e.inv.left ≫ (((Over.pullback b).mapGrp.obj (kernel f)).X.hom) =
      (kernel ((Over.pullback b).mapGrp.map f)).X.hom := e.inv.w
  rw [← he]
  infer_instance

/-- Translation transports kernel finiteness to the fibre over a lifted section. -/
lemma finite_split_fiber {S : Scheme.{u}} {G H : Grp (Over S)}
    (f : G ⟶ H) (x : 𝟙_ (Over S) ⟶ G.X) [IsFinite (kernel f).X.hom] :
    IsFinite (pullback f.hom.hom (x ≫ f.hom.hom)).hom := by
  rw [← kernelFiberIso_inv_structure f x]
  infer_instance

/-- A finite scheme over a field has finitely many underlying points. -/
lemma finite_points_over_field {L : Type u} [Field L] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of L)) [IsFinite p] : Finite X := by
  have : IsLocallyArtinian X := IsLocallyArtinian.of_locallyQuasiFinite p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  exact finite_of_compact_of_discrete

/-- The naturality square for base change is Cartesian. -/
lemma baseChange_isPullback {S T : Scheme.{u}} (b : T ⟶ S)
    {X Y : Over S} (f : X ⟶ Y) :
    IsPullback (pullback.fst X.hom b) ((Over.pullback b).map f).left
      f.left (pullback.fst Y.hom b) := by
  have h : IsPullback (pullback.fst X.hom b)
      (((Over.pullback b).map f).left ≫ pullback.snd Y.hom b)
      (f.left ≫ Y.hom) b := by
    rw [show ((Over.pullback b).map f).left ≫ pullback.snd Y.hom b =
      pullback.snd X.hom b from ((Over.pullback b).map f).w, f.w]
    exact IsPullback.of_hasPullback X.hom b
  exact h.of_bot (by simp) (IsPullback.of_hasPullback Y.hom b)

/-- With a finite kernel, every fibre of `f` through a point of its image is finite. -/
lemma finite_preimage_image_point {S : Scheme.{u}} {G H : Grp (Over S)}
    (f : G ⟶ H) [IsFinite (kernel f).X.hom] (x : G.X.left) :
    (f.hom.hom.left ⁻¹' {f.hom.hom.left x}).Finite := by
  let T := Spec (G.X.left.residueField x)
  let a : T ⟶ G.X.left := G.X.left.fromSpecResidueField x
  let b : T ⟶ S := a ≫ G.X.hom
  let f' := (Over.pullback b).mapGrp.map f
  let x' : 𝟙_ (Over T) ⟶ ((Over.pullback b).mapGrp.obj G).X :=
    Over.homMk (pullback.lift a (𝟙 T) (by simp [b])) (by simp)
  let F := pullback f'.hom.hom (x' ≫ f'.hom.hom)
  have : IsFinite (kernel f').X.hom := finite_kernel_baseChange b f
  have : IsFinite F.hom := finite_split_fiber f' x'
  have : Finite F.left := finite_points_over_field F.hom
  have hsplit := (IsPullback.of_hasPullback f'.hom.hom (x' ≫ f'.hom.hom)).map
    (Over.forget T)
  rw [toUnit_unique (pullback.snd f'.hom.hom (x' ≫ f'.hom.hom)) (toUnit F)] at hsplit
  change IsPullback (pullback.fst f'.hom.hom (x' ≫ f'.hom.hom)).left
    F.hom f'.hom.hom.left (x' ≫ f'.hom.hom).left at hsplit
  have h := hsplit.paste_horiz (baseChange_isPullback b f.hom.hom)
  have htarget : (x' ≫ f'.hom.hom).left ≫ pullback.fst H.X.hom b =
      a ≫ f.hom.hom.left := by
    simp [x', f', Category.assoc]
  rw [htarget] at h
  have : Finite (pullback (C := Scheme.{u}) f.hom.hom.left (a ≫ f.hom.hom.left)) :=
    Finite.of_injective (α := (pullback (C := Scheme.{u}) f.hom.hom.left (a ≫ f.hom.hom.left)))
      (β := F.left) (fun z => h.isoPullback.inv z) (by
        exact h.isoPullback.inv.homeomorph.injective)
  have hrange : Set.range (a ≫ f.hom.hom.left) = {f.hom.hom.left x} := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    change f.hom.hom.left '' Set.range (G.X.left.fromSpecResidueField x) = _
    rw [Scheme.range_fromSpecResidueField, Set.image_singleton]
  rw [← hrange, ← Scheme.Pullback.range_fst]
  exact Set.finite_range _

/-- A homomorphism with finite kernel is locally quasi-finite. -/
theorem locallyQuasiFinite_of_finite_kernel {S : Scheme.{u}} {G H : Grp (Over S)}
    (f : G ⟶ H) [IsFinite (kernel f).X.hom] [LocallyOfFiniteType f.hom.hom.left] :
    LocallyQuasiFinite f.hom.hom.left := by
  apply LocallyQuasiFinite.of_finite_preimage_singleton
  intro y
  by_cases hy : ∃ x, f.hom.hom.left x = y
  · obtain ⟨x, rfl⟩ := hy
    exact finite_preimage_image_point f x
  · have hempty : f.hom.hom.left ⁻¹' {y} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hy ⟨x, hx⟩
    rw [hempty]
    exact Set.finite_empty

/-- A homomorphism with finite kernel from a proper group to a separated group is finite. -/
theorem isFinite_of_finite_kernel {S : Scheme.{u}} {G H : Grp (Over S)}
    (f : G ⟶ H) [IsFinite (kernel f).X.hom] [IsProper G.X.hom] [IsSeparated H.X.hom] :
    IsFinite f.hom.hom.left := by
  have : IsProper (f.hom.hom.left ≫ H.X.hom) := by rw [Over.w]; infer_instance
  have : IsProper f.hom.hom.left := IsProper.of_comp _ H.X.hom
  have : LocallyQuasiFinite f.hom.hom.left := locallyQuasiFinite_of_finite_kernel f
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-! ## Flatness by translation -/

lemma translation_naturality {S : Scheme.{u}} {G H : Grp (Over S)}
    (f : G ⟶ H) (a : 𝟙_ (Over S) ⟶ G.X) :
    (GrpObj.mulRight a).hom ≫ f.hom.hom =
      f.hom.hom ≫ (GrpObj.mulRight (a ≫ f.hom.hom)).hom := by
  change ((𝟙 G.X) * (toUnit G.X ≫ a)) ≫ f.hom.hom =
    f.hom.hom ≫ ((𝟙 H.X) * (toUnit H.X ≫ a ≫ f.hom.hom))
  rw [mul_comp, comp_mul]
  simp

/-- A surjective homomorphism over an algebraically closed field is surjective on
rational points. -/
lemma rationalPoint_surjective {K : Type u} [Field K] [IsAlgClosed K]
    {G H : Grp (Over (Spec (CommRingCat.of K)))} (f : G ⟶ H)
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
    [Surjective f.hom.hom.left] :
    Function.Surjective (fun a : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X =>
      a ≫ f.hom.hom) := by
  have : JacobsonSpace G.X.left := LocallyOfFiniteType.jacobsonSpace G.X.hom
  intro b
  let z : H.X.left := b.left (IsLocalRing.closedPoint K)
  have hzc : IsClosed ({z} : Set H.X.left) :=
    ((pointEquivClosedPoint H.X.hom) ⟨b.left, b.w⟩).property
  have hne : (f.hom.hom.left ⁻¹' ({z} : Set H.X.left)).Nonempty := by
    obtain ⟨a, ha⟩ := f.hom.hom.left.surjective z
    exact ⟨a, ha⟩
  obtain ⟨a, ha, hac⟩ := nonempty_inter_closedPoints hne
    (hzc.preimage f.hom.hom.left.continuous).isLocallyClosed
  let a' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X :=
    Over.homMk (pointOfClosedPoint G.X.hom a hac) (by simp)
  refine ⟨a', Over.OverMorphism.ext ?_⟩
  apply ext_of_apply_closedPoint_eq H.X.hom (a' ≫ f.hom.hom).w b.w
  simpa [a', z] using ha

lemma flat_restrict_translation {K : Type u} [Field K]
    {G H : Grp (Over (Spec (CommRingCat.of K)))} (f : G ⟶ H)
    (a : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X)
    (U : H.X.left.Opens) [Flat (f.hom.hom.left ∣_ U)] :
    Flat (f.hom.hom.left ∣_ (GrpObj.mulRight (a ≫ f.hom.hom)).hom.left ⁻¹ᵁ U) := by
  have hn : (GrpObj.mulRight a).hom.left ≫ f.hom.hom.left =
      f.hom.hom.left ≫ (GrpObj.mulRight (a ≫ f.hom.hom)).hom.left :=
    congrArg (fun h => h.left) (translation_naturality f a)
  have h : Flat (((GrpObj.mulRight a).hom.left ≫ f.hom.hom.left) ∣_ U) := by
    rw [morphismRestrict_comp]
    infer_instance
  rw [hn, morphismRestrict_comp,
    MorphismProperty.cancel_right_of_respectsIso @Flat] at h
  exact h

/-- Flatness on a nonempty target open propagates by group translations, for a
surjective homomorphism between two groups over an algebraically closed field. -/
theorem flat_of_flat_restrict {K : Type u} [Field K] [IsAlgClosed K]
    {G H : Grp (Over (Spec (CommRingCat.of K)))} (f : G ⟶ H)
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
    [Surjective f.hom.hom.left]
    (hU : ∃ U : H.X.left.Opens, Set.Nonempty (U : Set H.X.left) ∧
      Flat (f.hom.hom.left ∣_ U)) :
    Flat f.hom.hom.left := by
  have : JacobsonSpace H.X.left := LocallyOfFiniteType.jacobsonSpace H.X.hom
  obtain ⟨U, hUne, hUflat⟩ := hU
  have := hUflat
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hUne U.isOpen.isLocallyClosed
  let y' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ H.X :=
    Over.homMk (pointOfClosedPoint H.X.hom y hyc) (by simp)
  let V (a : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X) : H.X.left.Opens :=
    (GrpObj.mulRight (a ≫ f.hom.hom)).hom.left ⁻¹ᵁ U
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Flat) V
  · rw [← Opens.coe_eq_univ, ← not_ne_iff, ← Set.nonempty_compl]
    intro hne
    obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints hne
      (iSup V).isOpen.isClosed_compl.isLocallyClosed
    let x' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ H.X :=
      Over.homMk (pointOfClosedPoint H.X.hom x hxc) (by simp)
    obtain ⟨a, ha⟩ := rationalPoint_surjective f (x'⁻¹ * y')
    change a ≫ f.hom.hom = x'⁻¹ * y' at ha
    have hxy : x' ≫ (GrpObj.mulRight (a ≫ f.hom.hom)).hom = y' := by
      rw [ha]
      change x' ≫ ((𝟙 H.X) * (toUnit H.X ≫ (x'⁻¹ * y'))) = y'
      rw [comp_mul]
      simp
    have hxy' : (GrpObj.mulRight (a ≫ f.hom.hom)).hom.left x = y := by
      have h := congr(($hxy).left (IsLocalRing.closedPoint K))
      change (GrpObj.mulRight (a ≫ f.hom.hom)).hom.left
        (pointOfClosedPoint H.X.hom x hxc (IsLocalRing.closedPoint K)) =
        pointOfClosedPoint H.X.hom y hyc (IsLocalRing.closedPoint K) at h
      simpa only [pointOfClosedPoint_apply] using h
    apply hx
    apply Opens.mem_iSup.mpr
    refine ⟨a, ?_⟩
    change (GrpObj.mulRight (a ≫ f.hom.hom)).hom.left x ∈ U
    rwa [hxy']
  · intro a
    exact flat_restrict_translation f a U

/-! ## The isogeny criterion -/

/-- Over an algebraically closed field, a surjective homomorphism with finite kernel from a
proper group to a smooth, geometrically connected, separated group is an isogeny. -/
theorem isIsogeny_of_finite_kernel_of_surjective {K : Type u} [Field K] [IsAlgClosed K]
    {G H : Grp (Over (Spec (CommRingCat.of K)))} (f : G ⟶ H)
    (hG : IsProper G.X.hom) (hHs : Smooth H.X.hom) (hHc : GeometricallyConnected H.X.hom)
    (hHsep : IsSeparated H.X.hom) (hk : IsFinite (kernel f).X.hom)
    (hsurj : Surjective f.hom.hom.left) : IsIsogeny f := by
  let : IsProper G.X.hom := hG
  let : Smooth H.X.hom := hHs
  let : IsSeparated H.X.hom := hHsep
  let : IsFinite (kernel f).X.hom := hk
  let : Surjective f.hom.hom.left := hsurj
  have hfin : IsFinite f.hom.hom.left := isFinite_of_finite_kernel f
  have hnoeth : IsLocallyNoetherian H.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  have hint : IsIntegral H.X.left := by
    let : GeometricallyIntegral H.X.hom :=
      Langlands.AbelianScheme.smoothGeometricIntegrality K H.X.left H.X.hom hHs hHc
    exact GeometricallyIntegral.isIntegral_of_subsingleton H.X.hom
  have hopen := Langlands.AlgebraicGeometry.finiteGenericFlat
    G.X.left H.X.left f.hom.hom.left hint hnoeth hfin
  exact ⟨hfin, flat_of_flat_restrict f hopen, hsurj⟩

end Langlands.GroupScheme.HomIsogeny
