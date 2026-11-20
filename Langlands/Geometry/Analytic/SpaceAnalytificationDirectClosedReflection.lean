import Langlands.AlgebraicGeometry.FiniteOpenFactorization
import Langlands.Geometry.Analytic.AffineAnalytificationConstructibleClosedness
import Langlands.Geometry.Analytic.AffineAnalytificationImmersionProof
import Langlands.Geometry.Analytic.AnalyticClosedImmersionTopology
import Langlands.Geometry.Analytic.LocalizedCompactNeighborhoods
import Langlands.Geometry.Analytic.SchemeAnalytificationMorphismProof
import Langlands.Geometry.Analytic.SpaceAnalytificationClosedImmersionReflection
import Langlands.Geometry.Analytic.SpaceAnalytificationEtaleReduction
import Langlands.Geometry.Analytic.SpaceAnalytificationExistenceAffineModels
import Langlands.Geometry.Analytic.SpaceAnalytificationMonomorphismDetection
import Langlands.Geometry.Analytic.SpaceAnalytificationSeparatedness

/-! # Closed-immersion reflection from supplied analytifications -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set _root_.Topology
open SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.AlgebraicGeometry.QuasiFiniteFactorization
open AffineAnalytification
open ExistenceReduction (ty ty_comp ty_injective exists_algHom_of_isPullback)

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X' X : AlgebraicSpace (Spec (CommRingCat.of K))} (f : X' ⟶ X)
  {Y' Y : LocalizedCategory.{u, u, u} (K := K)} {p' : PointFamily K X' Y'}
  {p : PointFamily K X Y} (hp' : IsAnalytification K X' Y' p')
  (hp : IsAnalytification K X Y p) {F : Y' ⟶ Y}
  (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
    (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
      p' A P x ≫ F = p A P (RingPoints.map f x))

/-- An affine étale test equipped with a compact subset of its analytification. -/
structure CompactEtaleTest (X : AlgebraicSpace (Spec (CommRingCat.of K))) where
  test : EtaleAffineTest K X
  points : Set (Space K test.presentation)
  isCompact : IsCompact points

/-- The underlying map of an affine étale test in the point family. -/
abbrev CompactEtaleTest.map (i : CompactEtaleTest (K := K) X')
    (p' : PointFamily K X' Y') :=
  localizedSpaceFunctor.map (p' i.test.algebra i.test.presentation i.test.point)

include hp' in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_finite_compactEtaleTest_cover
    {T : Set (localizedSpaceFunctor.obj Y')} (hT : IsCompact T) :
    ∃ s : Finset (CompactEtaleTest (K := K) X'),
      T ⊆ ⋃ i ∈ s, i.map p' '' i.points := by
  classical
  let U (i : CompactEtaleTest (K := K) X') := i.map p' '' interior i.points
  have hU (i : CompactEtaleTest (K := K) X') : IsOpen (U i) :=
    etaleOpenMap K _ (hp'.etale_map i.test.presentation i.test.point i.test.etale_point)
      _ isOpen_interior
  have hcover : T ⊆ ⋃ i, U i := by
    intro t _
    obtain ⟨D, _, _, R, y, hy, d, hd⟩ := hp'.jointly_surjective t
    let : WeaklyLocallyCompactSpace (localizedSpaceFunctor.obj (localized K R)) :=
      weaklyLocallyCompactSpace_localized (AffineAnalytification.localized K R)
    obtain ⟨M, hM, hdM⟩ :=
      exists_compact_mem_nhds (X := localizedSpaceFunctor.obj (localized K R)) d
    let i : CompactEtaleTest (K := K) X' :=
      ⟨⟨CommAlgCat.of K D, R, y, hy⟩, M, hM⟩
    exact mem_iUnion.2 ⟨i, d, mem_interior_iff_mem_nhds.2 hdM, hd⟩
  obtain ⟨s, hs⟩ := hT.elim_finite_subcover U hU hcover
  refine ⟨s, fun t ht => ?_⟩
  obtain ⟨i, hi, d, hd, rfl⟩ := mem_iUnion₂.mp (hs ht)
  exact mem_iUnion₂.mpr ⟨i, hi, d, interior_subset hd, rfl⟩

/-- A finite family of compact parts of affine étale tests whose images cover `T`. -/
def finiteCompactEtaleTestCover {T : Set (localizedSpaceFunctor.obj Y')} (hT : IsCompact T) :
    {s : Finset (CompactEtaleTest (K := K) X') // T ⊆ ⋃ i ∈ s, i.map p' '' i.points} :=
  ⟨(exists_finite_compactEtaleTest_cover hp' hT).choose,
    (exists_finite_compactEtaleTest_cover hp' hT).choose_spec⟩

section AffineTest

variable {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
  (x : RingPoints K X A) {W : Over (Spec (CommRingCat.of K))}
  (b : (schemeYoneda _).obj W ⟶ X'.presheaf) (q : W ⟶ ringTest K A)
  (hAlg : IsPullback b ((schemeYoneda _).map q) (hom f) (pointHom K x))
  (j : W ⟶ ringTest K B) (κ : A →ₐ[K] B) (hjq : j ≫ ringTestMap K κ = q)

set_option backward.isDefEq.respectTransparency false in
private theorem exists_affine_lift_of_center_mem_range [IsOpenImmersion j.left]
    {z : Space K Q} (hz : center K Q z ∈ range j.left) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra K E)
      (R : FinitePolynomialPresentation K E) (ι : B →ₐ[K] E) (i : ringTest K E ⟶ W)
      (w : Space K R), i ≫ j = ringTestMap K ι ∧ baseMap K Q R ι w = z := by
  obtain ⟨_, ⟨a, rfl⟩, hza, ha⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      hz j.left.isOpenMap.isOpen_range
  let : Algebra.FiniteType K B := Algebra.FiniteType.of_surjective Q.map Q.surjective
  let E := Localization.Away a
  let ι : B →ₐ[K] E := IsScalarTower.toAlgHom K B E
  let R := FinitePolynomialPresentation.ofFiniteType K E
  have hrange : range (ringTestMap K ι).left ⊆ range j.left := by
    apply Set.Subset.trans _ ha
    exact (PrimeSpectrum.localization_away_comap_range E a).le
  let i₀ := IsOpenImmersion.lift j.left (ringTestMap K ι).left hrange
  have hi₀ : i₀ ≫ j.left = (ringTestMap K ι).left := IsOpenImmersion.lift_fac _ _ _
  let i : ringTest K E ⟶ W := Over.homMk i₀ (by
    rw [← Over.w j, ← Category.assoc, hi₀]
    exact Over.w (ringTestMap K ι))
  have hzi : z ∈ range (baseMap K Q R ι) := by
    rw [ImmersionComparison.range_baseMap_away K Q R a]
    exact (center_mem_basicOpen K Q z a).mp hza
  obtain ⟨w, hw⟩ := hzi
  exact ⟨E, inferInstance, inferInstance, R, ι, i, w, Over.OverMorphism.ext hi₀, hw⟩

private theorem baseMap_apply_comp {D E H : Type u}
    [CommRing D] [Algebra K D] [CommRing E] [Algebra K E] [CommRing H] [Algebra K H]
    (R : FinitePolynomialPresentation K D) (S : FinitePolynomialPresentation K E)
    (T : FinitePolynomialPresentation K H) (a : D →ₐ[K] E) (c : E →ₐ[K] H)
    (w : Space K T) :
    baseMap K R S a (baseMap K S T c w) = baseMap K R T (c.comp a) w :=
  MorphismComparison.baseMap_baseMap K R S T a c (c.comp a) (fun _ => rfl) w

include hp' hp hF hAlg hjq in
set_option backward.isDefEq.respectTransparency false in
private theorem isCompact_center_open_inter_preimage [IsOpenImmersion j.left]
    (hX' : IsSeparated X') (hX : IsSeparated X)
    (hproper : IsProperMap (localizedSpaceFunctor.map F))
    {L : Set (Space K P)} (hL : IsCompact L) :
    IsCompact (center K Q ⁻¹' range j.left ∩ baseMap K P Q κ ⁻¹' L) := by
  classical
  let J := schemeYoneda (Spec (CommRingCat.of K))
  let T := localizedSpaceFunctor.map F ⁻¹' (localizedSpaceFunctor.map (p A P x) '' L)
  have hT : IsCompact T := hproper.isCompact_preimage (hL.image
    (localizedSpaceFunctor.map (p A P x)).hom.continuous)
  obtain ⟨s, hs⟩ := finiteCompactEtaleTestCover hp' hT
  have htest (i : CompactEtaleTest (K := K) X') :
      ∃ M : Set (Space K Q), IsCompact M ∧
        M ⊆ center K Q ⁻¹' range j.left ∩ baseMap K P Q κ ⁻¹' L ∧
        ∀ {E : Type u} [CommRing E] [Algebra K E] (R : FinitePolynomialPresentation K E)
          (ι : B →ₐ[K] E) (l : ringTest K E ⟶ W) (w : Space K R)
          (y : RingPoints K X' E), l ≫ j = ringTestMap K ι →
          pointHom K y = J.map l ≫ b →
          baseMap K P Q κ (baseMap K Q R ι w) ∈ L →
          localizedSpaceFunctor.map (p' E R y) w ∈ i.map p' '' i.points →
          baseMap K Q R ι w ∈ M := by
    let D := i.test.algebra
    let S := i.test.presentation
    let y := i.test.point
    obtain ⟨C, _, _, R, α, β, hsurj, hpb⟩ :=
      hasClosedAffinePointPullbacks_of_isSeparated hX D S A P (RingPoints.map f y) x
    have hw : (ty α ≫ pointHom K y) ≫ hom f = ty β ≫ pointHom K x := by
      rw [Category.assoc, ← pointHom_map]
      exact hpb.w
    let l := J.preimage (hAlg.lift (ty α ≫ pointHom K y) (ty β) hw)
    have hl : J.map l = hAlg.lift (ty α ≫ pointHom K y) (ty β) hw := J.map_preimage _
    have hl₁ : J.map l ≫ b = ty α ≫ pointHom K y := by
      rw [hl, hAlg.lift_fst]
    have hl₂ : J.map l ≫ J.map q = ty β := by rw [hl, hAlg.lift_snd]
    let γ := affineRingPointEquiv K B C (l ≫ j)
    have hγ : ringTestMap K γ = l ≫ j := ringTestMap_affineRingPointEquiv K _
    have hγκ : γ.comp κ = β := by
      apply ty_injective
      rw [ty_comp]
      change J.map (ringTestMap K γ) ≫ J.map (ringTestMap K κ) = ty β
      rw [hγ, ← J.map_comp, Category.assoc, hjq, J.map_comp]
      exact hl₂
    let N := (fun c : Space K R => (baseMap K S R α c, baseMap K P R β c)) ⁻¹'
      (i.points ×ˢ L)
    refine ⟨baseMap K Q R γ '' N, ?_, ?_, ?_⟩
    · exact (isCompact_preimage_pair_baseMap_of_surjective S P R α β hsurj
        (i.isCompact.prod hL)).image (baseMap K Q R γ).continuous
    · rintro _ ⟨c, hc, rfl⟩
      refine ⟨?_, ?_⟩
      · change center K Q (baseMap K Q R γ c) ∈ range j.left
        rw [center_baseMap]
        change (ringTestMap K γ).left (center K R c) ∈ range j.left
        rw [hγ]
        exact ⟨l.left (center K R c), rfl⟩
      · change baseMap K P Q κ (baseMap K Q R γ c) ∈ L
        rw [baseMap_apply_comp, hγκ]
        exact hc.2
    · intro E _ _ U ι m w v hm hv hwL hwv
      obtain ⟨d, hd, hdw⟩ := hwv
      obtain ⟨H, _, _, V, a, c, _, hOverlap⟩ :=
        hasClosedAffinePointPullbacks_of_isSeparated hX' D S E U y v
      let ρ := ι.comp κ
      have hmρ : J.map m ≫ J.map q = ty ρ := by
        rw [← J.map_comp, ← hjq, ← Category.assoc, hm, ty_comp, J.map_comp]
      have hco : ty a ≫ pointHom K (RingPoints.map f y) = ty (c.comp ρ) ≫ pointHom K x := by
        calc
          ty a ≫ pointHom K (RingPoints.map f y) =
              (ty a ≫ pointHom K y) ≫ hom f := by rw [pointHom_map, Category.assoc]
          _ = (ty c ≫ J.map m ≫ b) ≫ hom f := by rw [hOverlap.w, hv]
          _ = ty c ≫ (J.map m ≫ J.map q) ≫ pointHom K x := by
                simp only [Category.assoc, hAlg.w, J]
          _ = _ := by
            rw [hmρ]
            exact (Category.assoc _ _ _).symm.trans
              (congrArg (fun g => g ≫ pointHom K x) (ty_comp ρ c).symm)
      obtain ⟨η, hη₁, hη₂⟩ := exists_algHom_of_isPullback hpb a (c.comp ρ) hco
      have hηl : ty η ≫ J.map l = ty c ≫ J.map m := by
        apply hAlg.hom_ext
        · rw [Category.assoc, hl₁, ← Category.assoc, ← ty_comp, hη₁,
            hOverlap.w, hv, Category.assoc]
        · rw [Category.assoc, hl₂, ← ty_comp, hη₂, ty_comp, Category.assoc, hmρ]
      have hηγ : η.comp γ = c.comp ι := by
        apply ty_injective
        rw [ty_comp, ty_comp]
        change ty η ≫ J.map (ringTestMap K γ) = ty c ≫ J.map (ringTestMap K ι)
        rw [hγ, ← hm, J.map_comp, J.map_comp, ← Category.assoc, ← Category.assoc, hηl]
      obtain ⟨t, ht₁, ht₂⟩ := exists_point_of_isPullback _ _ _ _
        (hp'.isPullback S U V a c y v hOverlap) d w hdw
      rw [localizedSpaceFunctor_map_localizedHom] at ht₁ ht₂
      change baseMap K S V a t = d at ht₁
      change baseMap K U V c t = w at ht₂
      refine ⟨baseMap K R V η t, ⟨?_, ?_⟩, ?_⟩
      · change baseMap K S R α (baseMap K R V η t) ∈ i.points
        rw [baseMap_apply_comp, hη₁, ht₁]
        exact hd
      · change baseMap K P R β (baseMap K R V η t) ∈ L
        rw [baseMap_apply_comp, hη₂, ← baseMap_apply_comp P U V ρ c, ht₂,
          ← baseMap_apply_comp P Q U κ ι]
        exact hwL
      · rw [baseMap_apply_comp, hηγ, ← baseMap_apply_comp Q U V ι c, ht₂]
  choose M hM hMV hcover using htest
  have heq : center K Q ⁻¹' range j.left ∩ baseMap K P Q κ ⁻¹' L =
      ⋃ i ∈ s, M i := by
    apply Set.Subset.antisymm
    · rintro z ⟨hz, hzL⟩
      obtain ⟨E, _, _, R, ι, l, w, hl, rfl⟩ :=
        exists_affine_lift_of_center_mem_range Q j hz
      let ρ := ι.comp κ
      let y : RingPoints K X' E := uliftYonedaEquiv.{u + 1} (J.map l ≫ b)
      have hy : pointHom K y = J.map l ≫ b := Equiv.symm_apply_apply _ _
      have hxy : RingPoints.map f y = RingPoints.changeRing ρ x := by
        apply uliftYonedaEquiv.{u + 1}.symm.injective
        change pointHom K (RingPoints.map f y) = pointHom K (RingPoints.changeRing ρ x)
        rw [pointHom_map, hy, Category.assoc, hAlg.w, ← Category.assoc, ← J.map_comp,
          ← hjq, ← Category.assoc, hl, ← ringTestMap_comp, pointHom_changeRing]
      have ht : localizedSpaceFunctor.map (p' E R y) w ∈ T := by
        refine ⟨baseMap K P Q κ (baseMap K Q R ι w), hzL, ?_⟩
        rw [baseMap_apply_comp, ← TopCat.comp_app, ← Functor.map_comp, hF, hxy,
          hp.naturality, Functor.map_comp, TopCat.comp_app,
          localizedSpaceFunctor_map_localizedHom]
        rfl
      obtain ⟨i, hi, hwi⟩ := mem_iUnion₂.mp (hs ht)
      exact mem_iUnion₂.mpr ⟨i, hi, hcover i R ι l w y hl hy hzL hwi⟩
    · exact iUnion₂_subset fun i _ => hMV i
  rw [heq]
  exact s.isCompact_biUnion fun i _ => hM i

include hp' hp hF P hAlg hjq in
set_option backward.isDefEq.respectTransparency false in
private theorem isClosed_center_preimage_range [IsOpenImmersion j.left]
    (hX' : IsSeparated X') (hX : IsSeparated X)
    (hproper : IsProperMap (localizedSpaceFunctor.map F)) :
    IsClosed (center K Q ⁻¹' range j.left) := by
  let G := baseMap K P Q κ
  let V := center K Q ⁻¹' range j.left
  change IsClosed V
  rw [← closure_subset_iff_isClosed]
  intro z hz
  let : WeaklyLocallyCompactSpace (Space K P) := weaklyLocallyCompactSpace_localized (localized K P)
  obtain ⟨L, hL, hzL⟩ := exists_compact_mem_nhds (X := Space K P) (G z)
  have hN : G ⁻¹' L ∈ 𝓝 z := G.continuous.continuousAt.preimage_mem_nhds hzL
  have hslice : IsCompact (V ∩ G ⁻¹' L) :=
    isCompact_center_open_inter_preimage f hp' hp hF P Q x b q hAlg j κ hjq hX' hX hproper hL
  have hz' : z ∈ closure (V ∩ G ⁻¹' L) := by
    apply mem_closure_iff_nhds.mpr
    intro U hU
    obtain ⟨w, ⟨hwU, hwL⟩, hwV⟩ :=
      mem_closure_iff_nhds.mp hz (U ∩ G ⁻¹' L) (Filter.inter_mem hU hN)
    exact ⟨w, hwU, hwV, hwL⟩
  rw [hslice.isClosed.closure_eq] at hz'
  exact hz'.1

include hp' hp hF P hAlg in
set_option backward.isDefEq.respectTransparency false in
private theorem isClosedImmersion_of_proper_affine_test [QuasiCompact q.left] [Mono q.left]
    [LocallyOfFiniteType W.hom] (hX' : IsSeparated X') (hX : IsSeparated X)
    (hproper : IsProperMap (localizedSpaceFunctor.map F)) :
    _root_.AlgebraicGeometry.IsClosedImmersion q.left := by
  let : IsAffine (ringTest K A).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  let : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective P.map P.surjective
  let : LocallyOfFiniteType (ringTest K A).hom :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  have : LocallyOfFiniteType (q.left ≫ (ringTest K A).hom) := by
    rw [Over.w q]
    infer_instance
  let : LocallyOfFiniteType q.left := locallyOfFiniteType_of_comp q.left (ringTest K A).hom
  obtain ⟨D⟩ := nonempty_finiteOpenFactorization q.left
  let B : Type u := D.ring
  let t := D.finiteMap ≫ (ringTest K A).hom
  let : Algebra K B := (Spec.preimage t).hom.toAlgebra
  have ht : Spec.algebraMap K B = t := by
    change Spec.map (CommRingCat.ofHom (Spec.preimage t).hom) = t
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let : IsOpenImmersion D.openMap := D.openImmersion
  let : IsFinite D.finiteMap := D.finite
  let j : W ⟶ ringTest K B := Over.homMk D.openMap (by
    change D.openMap ≫ Spec.algebraMap K B = W.hom
    rw [ht, ← Category.assoc, D.comp_eq, Over.w q])
  let k : ringTest K B ⟶ ringTest K A := Over.homMk D.finiteMap ht.symm
  let κ := affineRingPointEquiv K A B k
  have hjq : j ≫ ringTestMap K κ = q := by
    rw [ringTestMap_affineRingPointEquiv K k]
    exact Over.OverMorphism.ext D.comp_eq
  have hft : LocallyOfFiniteType (Spec.algebraMap K B) := by
    rw [ht]
    exact inferInstanceAs (LocallyOfFiniteType (D.finiteMap ≫ (ringTest K A).hom))
  let : Algebra.FiniteType K B := RingHom.finiteType_algebraMap.mp
    (HasRingHomProperty.Spec_iff.mp hft)
  let Q := FinitePolynomialPresentation.ofFiniteType K B
  let : IsOpenImmersion j.left := D.openImmersion
  let : CompactSpace W.left := QuasiCompact.compactSpace_of_compactSpace q.left
  have hconstructible : IsConstructible (range j.left) :=
    (isCompact_range j.left.continuous).isConstructible j.left.isOpenMap.isOpen_range
  have hclosed : IsClosed (range j.left) :=
    isClosed_of_isConstructible_of_isClosed_center_preimage K Q hconstructible
      (isClosed_center_preimage_range f hp' hp hF P Q x b q hAlg j κ hjq hX' hX hproper)
  let : _root_.AlgebraicGeometry.IsClosedImmersion D.openMap :=
    _root_.AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion _ hclosed
  have : IsFinite q.left := by
    rw [← D.comp_eq]
    infer_instance
  exact (_root_.AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono _).mpr
    ⟨inferInstance, inferInstance⟩

end AffineTest

include hp' hp hF in
set_option backward.isDefEq.respectTransparency false in
/-- A compatible analytic closed immersion reflects to an algebraic closed immersion
for a quasi-compact morphism of separated algebraic spaces locally of finite type. -/
theorem isClosedImmersion_of_closedImmersion
    (hX' : IsSeparated X') (hX'ft : LocallyOfFiniteTypeOverBase X')
    (hX : IsSeparated X) (hXft : LocallyOfFiniteTypeOverBase X)
    (hqc : IsQuasiCompactMorphism f) (hc : closedImmersion F) :
    AlgebraicSpace.IsClosedImmersion (hom f) := by
  let : Mono F := hc.mono
  let : Mono (hom f) := mono_of_mono_analytification_of_isSeparated f hp' hp hF hX' hX hX'ft
  let hr := isRepresentableMorphism_of_mono_of_finiteType_source f hX'ft hX
  apply isClosedImmersion_of_finiteType_affine_etale_tests f hr hXft
  intro A _ _ _ x hx W b q hAlg
  let S := Spec (CommRingCat.of K)
  let P := FinitePolynomialPresentation.ofFiniteType K A
  let : IsAffine (ringTest K A).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  let : QuasiCompact q.left := quasiCompact_of_represented_affine_pullback f hqc _ hAlg
  let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
    (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S))
  have hb : AlgebraicSpace.IsEtale b := MorphismProperty.of_isPullback
    (P := (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
      (schemeYoneda S)) hAlg.flip hx
  let : LocallyOfFiniteType W.hom := locallyOfFiniteType_of_isEtale hX'ft b hb
  let : Mono ((schemeYoneda S).map q) := hAlg.mono_snd_of_mono
  let : Mono q := (schemeYoneda S).mono_of_mono_map inferInstance
  let : Mono q.left := Over.mono_left_of_mono q
  exact isClosedImmersion_of_proper_affine_test f hp' hp hF P x b q hAlg hX' hX
    hc.isClosedEmbedding.isProperMap

end Langlands.Analytic.SpaceAnalytification
