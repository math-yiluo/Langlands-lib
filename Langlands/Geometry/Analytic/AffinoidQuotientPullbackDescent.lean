import Langlands.Geometry.Analytic.AffinoidTransportedCharts
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteDomainIdealDescentProof
import Langlands.Geometry.Analytic.RecognizedAffinoidNet
import Langlands.Geometry.Analytic.SpaceAnalytificationClosedTestPullbacks
import Langlands.Geometry.Analytic.SpaceAnalytificationDirectOpenPreservation

/-! # Closed quotient pullbacks on affinoid covers -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set
open PresentedAffinoidAlgebra SaturatedAtlasPresentation

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {U V : LocalizedCategory.{u, u, u} (K := K)} {F : U ⟶ V}
  {R S T : PresentedAffinoidAlgebra K} {a : localizedAffinoidSpectrum R ⟶ V}

private abbrev spectrumMap (φ : BoundedAlgHom K R S) :
    localizedAffinoidSpectrum S ⟶ localizedAffinoidSpectrum R :=
  SmallAffinoidSpectrum.localizedMapEquiv.{u, u} R S φ

private theorem spectrumMap_comp (φ : BoundedAlgHom K R S) (ψ : BoundedAlgHom K S T) :
    spectrumMap (ψ.comp φ) = spectrumMap ψ ≫ spectrumMap φ :=
  SmallAffinoidSpectrum.localizedMapEquiv_comp.{u, u} φ ψ

namespace AffinoidQuotientPullback

variable (P : AffinoidQuotientPullback R F a)

/-- The original presented affinoid quotient of the test algebra. -/
abbrev quotientAlgebra := @ClosedQuotient.algebra K _ _ R P.ideal P.isClosed

/-- The actual bounded quotient projection on algebras. -/
abbrev quotientMap : BoundedAlgHom K R P.quotientAlgebra :=
  @ClosedQuotient.map K _ _ R P.ideal P.isClosed

set_option backward.isDefEq.respectTransparency false in
/-- A bounded test map annihilates the ideal exactly when the analytic
test has a lift through the original morphism. -/
theorem exists_lift_iff (φ : BoundedAlgHom K R S) :
    (∃ b : localizedAffinoidSpectrum S ⟶ U, b ≫ F = spectrumMap φ ≫ a) ↔
      ∀ x ∈ P.ideal, φ x = 0 := by
  constructor
  · rintro ⟨b, hb⟩
    let l := P.isPullback.lift b (spectrumMap φ) hb
    obtain ⟨ψ, hψ⟩ :=
      (SmallAffinoidSpectrum.localizedMapEquiv.{u, u} P.quotientAlgebra S).surjective l
    have hcomp : ψ.comp P.quotientMap = φ := by
      apply (SmallAffinoidSpectrum.localizedMapEquiv.{u, u} R S).injective
      change spectrumMap (ψ.comp P.quotientMap) = spectrumMap φ
      rw [spectrumMap_comp, show spectrumMap ψ = l from hψ]
      exact P.isPullback.lift_snd b _ hb
    intro x hx
    have hx₀ := (@ClosedQuotient.map_eq_zero_iff K _ _ R P.ideal P.isClosed x).mpr hx
    have he := congrArg (fun p : BoundedAlgHom K R S => p x) hcomp
    change ψ (P.quotientMap x) = φ x at he
    rw [hx₀, map_zero] at he
    exact he.symm
  · intro hφ
    let ψ := @ClosedQuotient.lift K _ _ R P.ideal P.isClosed S _ _ φ hφ
    have hψ : ψ.comp P.quotientMap = φ :=
      @ClosedQuotient.lift_comp_map K _ _ R P.ideal P.isClosed S _ _ φ hφ
    refine ⟨spectrumMap ψ ≫ P.lift, ?_⟩
    have hw : P.lift ≫ F = spectrumMap P.quotientMap ≫ a := P.isPullback.w
    rw [Category.assoc, hw, ← Category.assoc, ← spectrumMap_comp, hψ]

end AffinoidQuotientPullback

omit [CompleteSpace K] in
private theorem annihilates_closedIdealMap (φ : BoundedAlgHom K R S) (I : Ideal R)
    (ψ : BoundedAlgHom K S T) :
    (∀ z ∈ φ.closedIdealMap I, ψ z = 0) ↔ ∀ z ∈ I, ψ (φ z) = 0 := by
  constructor
  · intro h z hz
    exact h _ (φ.mem_closedIdealMap hz)
  · intro h z hz
    have hc : IsClosed (RingHom.ker ψ.toAlgHom.toRingHom : Set S) :=
      isClosed_eq ψ.continuous continuous_const
    exact ((φ.closedIdealMap_le_iff I _ hc).mpr h) hz

section Cover

variable (c : Domain.FiniteCover (Domain.whole K R))
  (P : ∀ i : Fin c.size, AffinoidQuotientPullback (c.obj i).algebra F
    (spectrumMap (c.obj i).baseMap ≫ a))

set_option backward.isDefEq.respectTransparency false in
private theorem idealCompatible_of_quotientPullbacks :
    c.IdealCompatible (fun i => (P i).ideal) := by
  intro i j
  let L := ((c.obj i).interLeft (c.obj j)).restriction
  let M := ((c.obj i).interRight (c.obj j)).restriction
  let D := (c.obj i).inter (c.obj j)
  have hLM : L.comp (c.obj i).baseMap = M.comp (c.obj j).baseMap :=
    ((c.obj i).interLeft (c.obj j)).comp_baseMap.trans
      (((c.obj i).interRight (c.obj j)).comp_baseMap.symm)
  let J₁ := L.closedIdealMap (P i).ideal
  let J₂ := M.closedIdealMap (P j).ideal
  have hvanish (C : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K D.algebra C) :
      (∀ z ∈ J₁, φ z = 0) ↔ ∀ z ∈ J₂, φ z = 0 := by
    rw [annihilates_closedIdealMap L (P i).ideal φ,
      annihilates_closedIdealMap M (P j).ideal φ]
    change (∀ z ∈ (P i).ideal, (φ.comp L) z = 0) ↔
      ∀ z ∈ (P j).ideal, (φ.comp M) z = 0
    rw [← (P i).exists_lift_iff, ← (P j).exists_lift_iff]
    have hm : spectrumMap (φ.comp L) ≫ spectrumMap (c.obj i).baseMap ≫ a =
        spectrumMap (φ.comp M) ≫ spectrumMap (c.obj j).baseMap ≫ a := by
      rw [← Category.assoc, ← Category.assoc, ← spectrumMap_comp, ← spectrumMap_comp,
        BoundedAlgHom.comp_assoc, BoundedAlgHom.comp_assoc, hLM]
    simp only [hm]
  let hJ₁ := L.isClosed_closedIdealMap (P i).ideal
  let hJ₂ := M.isClosed_closedIdealMap (P j).ideal
  change J₁ = J₂
  apply le_antisymm
  · intro x hx
    let q := @ClosedQuotient.map K _ _ D.algebra J₂ hJ₂
    have hq : ∀ z ∈ J₂, q z = 0 := fun z hz =>
      (@ClosedQuotient.map_eq_zero_iff K _ _ D.algebra J₂ hJ₂ z).mpr hz
    exact (@ClosedQuotient.map_eq_zero_iff K _ _ D.algebra J₂ hJ₂ x).mp
      ((hvanish _ q).mpr hq x hx)
  · intro x hx
    let q := @ClosedQuotient.map K _ _ D.algebra J₁ hJ₁
    have hq : ∀ z ∈ J₁, q z = 0 := fun z hz =>
      (@ClosedQuotient.map_eq_zero_iff K _ _ D.algebra J₁ hJ₁ z).mpr hz
    exact (@ClosedQuotient.map_eq_zero_iff K _ _ D.algebra J₁ hJ₁ x).mp
      ((hvanish _ q).mp hq x hx)

end Cover

open IndexedAffinoidAtlas

private theorem locallyRefines_univ_of_isQuasinet {X : Type u} [TopologicalSpace X]
    {σ : Set (Set X)} (hσ : AtlasTopology.IsQuasinet σ) :
    AtlasTopology.LocallyRefines σ {univ} := by
  intro W hW x _
  obtain rfl := mem_singleton_iff.mp hW
  obtain ⟨τ, hτ, hsub, hx, hn⟩ := hσ x
  exact ⟨τ, hτ, hsub, fun S hS => ⟨subset_univ _, hx S hS⟩,
    by simpa only [nhdsWithin_univ] using hn⟩

set_option backward.isDefEq.respectTransparency false in
private theorem exists_lift_of_finite_domain_cover
    (c : Domain.FiniteCover (Domain.whole K R))
    {B C D : LocalizedCategory.{u, u, u} (K := K)} {p : D ⟶ B} {q : D ⟶ C} [Mono p]
    (b : localizedAffinoidSpectrum R ⟶ B) (d : localizedAffinoidSpectrum R ⟶ C)
    (h : ∀ i : Fin c.size, ∃ l : localizedAffinoidSpectrum (c.obj i).algebra ⟶ D,
      l ≫ p = spectrumMap (c.obj i).baseMap ≫ b ∧
      l ≫ q = spectrumMap (c.obj i).baseMap ≫ d) :
    ∃ l : localizedAffinoidSpectrum R ⟶ D, l ≫ p = b ∧ l ≫ q = d := by
  let A := SmallAffinoidSpectrum.saturated.{u, u} R
  let L (i : Fin c.size) : LocalDomain (SmallAffinoidSpectrum.presentation.{u, u} R).atlas :=
    ⟨PUnit.unit, c.obj i⟩
  let k (i : Fin c.size) : A.presentation.atlas.Index := ⟨(L i).locus, ⟨L i, rfl⟩⟩
  let eR := SmallAffinoidSpectrum.spectrumHomeomorph.{u, u} R
  have hk (i : Fin c.size) :
      range (A.presentation.atlas.chart (k i)) = eR '' (c.obj i).locus :=
    (SmallAffinoidSpectrum.presentation.{u, u} R).atlas.range_saturatedChart (k i)
  have hcov : ⋃₀ range (fun i => range (A.presentation.atlas.chart (k i))) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := c.covers (eR.symm x) (mem_univ _)
    refine ⟨_, mem_range_self i, ?_⟩
    rw [hk]
    exact ⟨eR.symm x, hi, eR.apply_symm_apply x⟩
  have hclosed (i : Fin c.size) : IsClosed (range (A.presentation.atlas.chart (k i))) := by
    rw [hk]
    exact eR.isClosedMap _ (c.obj i).represents.1
  have hq : AtlasTopology.IsQuasinet (range (fun i => range (A.presentation.atlas.chart (k i)))) :=
    AtlasTopology.isQuasinet_of_finite_closedCover _ (finite_range _) Subset.rfl
      (by rintro _ ⟨i, rfl⟩; exact hclosed i) hcov
  refine exists_lift_of_chartCover k (locallyRefines_univ_of_isQuasinet hq) p q
    (fun _ _ _ hp _ => (cancel_mono p).mp hp) b d ?_
  intro i
  let E := affinoidChartDomain (Iso.refl (localizationFunctor.obj A)) (k i)
  have hE : E.locus = (c.obj i).locus := by
    ext x
    rw [mem_affinoidChartDomain_iff, Iso.refl_inv]
    have hx : localizedSpaceFunctor.map (𝟙 (localizationFunctor.obj A)) (eR x) = eR x :=
      congrArg (fun m : localizedSpaceFunctor.obj (localizationFunctor.obj A) ⟶
          localizedSpaceFunctor.obj (localizationFunctor.obj A) => m (eR x))
        (_root_.CategoryTheory.Functor.map_id localizedSpaceFunctor (localizationFunctor.obj A))
    rw [hx, hk]
    change eR x ∈ eR '' (c.obj i).locus ↔ _
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact eR.injective hxy ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  let t := (Domain.inclusionOfSubset E (c.obj i) hE.subset).restriction
  have ht : t.comp (c.obj i).baseMap = E.baseMap :=
    (Domain.inclusionOfSubset E (c.obj i) hE.subset).comp_baseMap
  have htp : spectrumMap t ≫ spectrumMap (c.obj i).baseMap =
      localizationFunctor.map (A.smallChartSpectrumInclusion (k i)) := by
    rw [← spectrumMap_comp, ht]
    exact (affinoidChartDomain_map (Iso.refl (localizationFunctor.obj A)) (k i)).trans
      (Category.comp_id _)
  obtain ⟨l, hlp, hlq⟩ := h i
  refine ⟨spectrumMap t ≫ l, ?_, ?_⟩
  · rw [Category.assoc, hlp, ← Category.assoc]
    exact congrArg (fun f : localizedAffinoidSpectrum E.algebra ⟶
      localizedAffinoidSpectrum R => f ≫ b) htp
  · rw [Category.assoc, hlq, ← Category.assoc]
    exact congrArg (fun f : localizedAffinoidSpectrum E.algebra ⟶
      localizedAffinoidSpectrum R => f ≫ d) htp

set_option backward.isDefEq.respectTransparency false in
private theorem mono_spectrumMap_of_surjective (q : BoundedAlgHom K R S)
    (hq : Function.Surjective q) : Mono (spectrumMap q) := by
  have hpb := SmallAffinoidSpectrum.pushout_localized_isPullback.{u, u} q q
  have hmap : AffinoidPushout.leftMap q q = AffinoidPushout.rightMap q q := by
    apply BoundedAlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := hq x
    exact congrArg (fun m : BoundedAlgHom K R (AffinoidPushout.algebra q q) => m y)
      (AffinoidPushout.condition q q)
  constructor
  intro T b c he
  have hfst := hpb.lift_fst b c he
  have hsnd := hpb.lift_snd b c he
  change hpb.lift b c he ≫ spectrumMap (AffinoidPushout.leftMap q q) = b at hfst
  change hpb.lift b c he ≫ spectrumMap (AffinoidPushout.rightMap q q) = c at hsnd
  rw [hmap] at hfst
  exact hfst.symm.trans hsnd

private def pulledBackWholeCover (c : Domain.FiniteCover (Domain.whole K R))
    (φ : BoundedAlgHom K R S) : Domain.FiniteCover (Domain.whole K S) where
  size := c.size
  obj i := Domain.pullback φ (c.obj i)
  map i := ⟨(Domain.pullback φ (c.obj i)).baseMap, BoundedAlgHom.comp_id _⟩
  covers x _ := c.covers (BanachSpectrum.comap φ.toBoundedRingHom x) (mem_univ _)

private theorem wholeCover_restriction_eq_baseMap
    (c : Domain.FiniteCover (Domain.whole K R)) (i : Fin c.size) :
    (c.map i).restriction = (c.obj i).baseMap :=
  (BoundedAlgHom.comp_id (c.map i).restriction).symm.trans (c.map i).comp_baseMap

section Cover

variable (c : Domain.FiniteCover (Domain.whole K R))
  (P : ∀ i : Fin c.size, AffinoidQuotientPullback (c.obj i).algebra F
    (spectrumMap (c.obj i).baseMap ≫ a))

set_option backward.isDefEq.respectTransparency false in
private theorem annihilates_contractedIdeal_of_lift
    (φ : BoundedAlgHom K R S) (b : localizedAffinoidSpectrum S ⟶ U)
    (hb : b ≫ F = spectrumMap φ ≫ a) :
    ∀ x ∈ c.idealContraction (fun i => (P i).ideal), φ x = 0 := by
  intro x hx
  let C := pulledBackWholeCover c φ
  apply C.algebra_ext_of_restrict_eq
  intro i
  change (Domain.pullback φ (c.obj i)).baseMap (φ x) =
    (Domain.pullback φ (c.obj i)).baseMap 0
  let ψ := Domain.pullbackMap φ (c.obj i)
  let δ := (Domain.pullback φ (c.obj i)).baseMap
  have heq := Domain.pullbackMap_comp_baseMap φ (c.obj i)
  have hψ : ∀ z ∈ (P i).ideal, ψ z = 0 := (P i).exists_lift_iff ψ |>.mp (by
    refine ⟨spectrumMap δ ≫ b, ?_⟩
    rw [Category.assoc, hb, ← Category.assoc, ← Category.assoc,
      ← spectrumMap_comp, ← spectrumMap_comp, heq])
  rw [map_zero]
  have h := congrArg
    (fun m : BoundedAlgHom K R (Domain.pullback φ (c.obj i)).algebra => m x) heq
  have hx' := (c.mem_idealContraction _ x).mp hx i
  rw [wholeCover_restriction_eq_baseMap c i] at hx'
  exact h.symm.trans (hψ _ hx')

set_option backward.isDefEq.respectTransparency false in
/-- Descend the quotient models of a fixed affinoid test along a finite
full-domain cover, using effectiveness of the closed ideal family. -/
def affinoidQuotientPullbackOfDomainCover [Mono F] : AffinoidQuotientPullback R F a := by
  let J : Ideal R := c.idealContraction (fun i => (P i).ideal)
  let hJ : IsClosed (J : Set R) :=
    c.isClosed_idealContraction (fun i => (P i).ideal) (fun i => (P i).isClosed)
  let Q := @ClosedQuotient.algebra K _ _ R J hJ
  let q := @ClosedQuotient.map K _ _ R J hJ
  let s := spectrumMap q
  let : Mono s := mono_spectrumMap_of_surjective q
    (@ClosedQuotient.map_surjective K _ _ R J hJ)
  have heff (i : Fin c.size) : (c.obj i).baseMap.closedIdealMap J = (P i).ideal := by
    have he := Domain.FiniteCover.idealEffectiveness K R (Domain.whole K R) c
      (fun j => (P j).ideal) (fun j => (P j).isClosed)
      (idealCompatible_of_quotientPullbacks c P) i
    exact (congrArg (fun g : BoundedAlgHom K R (c.obj i).algebra => g.closedIdealMap J)
      (wholeCover_restriction_eq_baseMap c i).symm).trans he
  have htotal : ∃ r : localizedAffinoidSpectrum Q ⟶ U, r ≫ F = s ≫ a := by
    obtain ⟨r, hr, _⟩ := exists_lift_of_finite_domain_cover (pulledBackWholeCover c q)
      (p := F) (q := F) (s ≫ a) (s ≫ a) (fun i => by
        let ψ := Domain.pullbackMap q (c.obj i)
        let δ := (Domain.pullback q (c.obj i)).baseMap
        have he := Domain.pullbackMap_comp_baseMap q (c.obj i)
        have hψ : ∀ z ∈ (P i).ideal, ψ z = 0 := by
          rw [← heff i, annihilates_closedIdealMap]
          intro z hz
          have h := congrArg (fun m : BoundedAlgHom K R (Domain.pullback q (c.obj i)).algebra =>
            m z) he
          change ψ ((c.obj i).baseMap z) = δ (q z) at h
          rw [h, (@ClosedQuotient.map_eq_zero_iff K _ _ R J hJ z).mpr hz, map_zero]
        obtain ⟨l, hl⟩ := ((P i).exists_lift_iff ψ).mpr hψ
        have hl' : l ≫ F = spectrumMap δ ≫ s ≫ a := by
          rw [hl, ← Category.assoc, ← Category.assoc,
            ← spectrumMap_comp, ← spectrumMap_comp, he]
        exact ⟨l, hl', hl'⟩)
    exact ⟨r, hr⟩
  let r := htotal.choose
  have hr : r ≫ F = s ≫ a := htotal.choose_spec
  have hAffinoid (C : PresentedAffinoidAlgebra K) (b : localizedAffinoidSpectrum C ⟶ U)
      (d : localizedAffinoidSpectrum C ⟶ localizedAffinoidSpectrum R)
      (hd : b ≫ F = d ≫ a) :
      ∃ l : localizedAffinoidSpectrum C ⟶ localizedAffinoidSpectrum Q,
        l ≫ r = b ∧ l ≫ s = d := by
    obtain ⟨φ, rfl⟩ := (SmallAffinoidSpectrum.localizedMapEquiv.{u, u} R C).surjective d
    have hφ := annihilates_contractedIdeal_of_lift c P φ b hd
    let ψ := @ClosedQuotient.lift K _ _ R J hJ C _ _ φ hφ
    have heq : spectrumMap ψ ≫ s = spectrumMap φ := by
      rw [← spectrumMap_comp, @ClosedQuotient.lift_comp_map K _ _ R J hJ C _ _ φ hφ]
    refine ⟨spectrumMap ψ, (cancel_mono F).mp ?_, heq⟩
    rw [Category.assoc, hr, ← Category.assoc, heq]
    exact hd.symm
  have hLift (d : PullbackCone F a) : ∃ l : d.pt ⟶ localizedAffinoidSpectrum Q,
      l ≫ r = d.fst ∧ l ≫ s = d.snd := by
    obtain ⟨A, hA⟩ := localizedObjectEquiv.surjective d.pt
    let e : localizationFunctor.obj A ≅ d.pt := eqToIso hA
    obtain ⟨l, hlr, hls⟩ := exists_lift_of_chartCover
      (fun i : A.presentation.atlas.Index => i)
      (locallyRefines_univ_of_isQuasinet A.presentation.atlas.isNet_chartFamily.1) r s
      (fun _ _ _ _ h => (cancel_mono s).mp h) (e.hom ≫ d.fst) (e.hom ≫ d.snd) (fun i => by
        let j := localizationFunctor.map (A.smallChartSpectrumInclusion i) ≫ e.hom
        obtain ⟨l, hl, hm⟩ := hAffinoid _ (j ≫ d.fst) (j ≫ d.snd) (by
          rw [Category.assoc j, Category.assoc j, d.condition])
        exact ⟨l, hl.trans (Category.assoc _ _ _), hm.trans (Category.assoc _ _ _)⟩)
    refine ⟨e.inv ≫ l, ?_, ?_⟩
    · rw [Category.assoc, hlr, Iso.inv_hom_id_assoc]
    · rw [Category.assoc, hls, Iso.inv_hom_id_assoc]
  exact ⟨J, hJ, r, IsPullback.of_isLimit (PullbackCone.IsLimit.mk hr
    (fun d => (hLift d).choose) (fun d => (hLift d).choose_spec.1)
    (fun d => (hLift d).choose_spec.2)
    (fun d m _ hm => (cancel_mono s).mp (hm.trans (hLift d).choose_spec.2.symm)))⟩

end Cover

open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false in
/-- Every affinoid test of a compatible analytified closed immersion
has an affinoid quotient pullback. -/
theorem nonempty_affinoidQuotientPullback_of_isClosedImmersion
    {X' X : AlgebraicSpace (Spec (CommRingCat.of K))}
    {p' : PointFamily K X' U} {p : PointFamily K X V}
    (hp' : IsAnalytification K X' U p') (hp : IsAnalytification K X V p)
    (hs' : IsSeparated X') (ht' : LocallyOfFiniteTypeOverBase X')
    (hs : IsSeparated X) (ht : LocallyOfFiniteTypeOverBase X)
    (f : X' ⟶ X)
    (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
      p' A P x ≫ F = p A P (RingPoints.map f x))
    (hf : AlgebraicSpace.IsClosedImmersion (hom f)) :
    Nonempty (AffinoidQuotientPullback R F a) := by
  let S := Spec (CommRingCat.of K)
  have hm : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (Over.forget S)) ≤ MorphismProperty.monomorphisms (Over S) := by
    intro A B g hg
    have : _root_.AlgebraicGeometry.IsClosedImmersion g.left := hg
    exact Over.mono_of_mono_left g
  let : Mono (hom f) := SliceOpenGluing.relative_monomorphisms_le_monomorphisms _
    (MorphismProperty.relative_monotone hm _ hf)
  let : Mono F := mono_of_mono_hom f F hp' hp hs' ht' hs ht hF
  obtain ⟨B, e, I, hI, h⟩ := exists_affinoidPointHom_pair_chartCover
    hp hp hs ht hs ht (SmallAffinoidSpectrum.saturated.{u, u} R) a a
  obtain ⟨c, i, hi⟩ := exists_finite_cover_of_affinoidChartDomain e I hI
  have hlocal (k : Fin c.size) : Nonempty (AffinoidQuotientPullback (c.obj k).algebra F
      (spectrumMap (c.obj k).baseMap ≫ a)) := by
    rw [hi k]
    obtain ⟨x, _, hx, _⟩ := h (i k)
    have he : spectrumMap (affinoidChartDomain e (i k).val).baseMap ≫ a =
        affinoidPointHom hp hs ht _ x := by
      exact (congrArg (fun g : localizedAffinoidSpectrum
          (affinoidChartDomain e (i k).val).algebra ⟶ localizedAffinoidSpectrum R => g ≫ a)
        (affinoidChartDomain_map e (i k).val)).trans
        ((Category.assoc _ _ _).trans hx.symm)
    rw [he]
    exact ⟨affinoidQuotientPullbackOfIsClosedImmersion hp' hp hs' ht' hs ht hF hf _ x⟩
  exact ⟨affinoidQuotientPullbackOfDomainCover c (fun k => Classical.choice (hlocal k))⟩

end Langlands.Analytic.SpaceAnalytification
