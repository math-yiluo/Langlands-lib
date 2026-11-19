import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineFiniteTypePullbacks
import Langlands.AlgebraicGeometry.AlgebraicSpace.FibreProduct
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteTypeMorphismAtlas
import Langlands.AlgebraicGeometry.AlgebraicSpace.MonomorphismLocallyFiniteTypeSchemeProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentedAtlasEffectivityDescent
import Langlands.Geometry.Analytic.SpaceAnalytificationMonomorphismDetection
import Langlands.Geometry.Analytic.AnalyticClosedImmersionMonomorphism

/-! # Reflection of closed immersions by analytification -/

noncomputable section

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

variable {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X)

set_option backward.isDefEq.respectTransparency false in
private theorem exists_scheme_pullback_of_mono [Mono (hom f)]
    (hX' : LocallyOfFiniteTypeOverBase X') (hX : IsSeparated X)
    (T : Over S) (g : (schemeYoneda S).obj T ⟶ X.presheaf) :
    ∃ R : Over S, Nonempty ((schemeYoneda S).obj R ≅ Limits.pullback (hom f) g) := by
  let g' : (schemeToSpace S).obj T ⟶ X := homMk g
  let W := fibreProduct f g'
  let i : W.presheaf ≅ Limits.pullback (hom f) g := FibreProduct.presheafIso f g'
  let p : W.presheaf ⟶ (schemeYoneda S).obj T := hom (FibreProduct.snd f g')
  have hp : Mono p := (FibreProduct.isPullback_presheaf f g').mono_snd_of_mono
  obtain ⟨U, a, ha, hs, hU⟩ := hX'.exists_atlas
  let R := SchemePullbackChart.scheme f a g
  let b := SchemePullbackChart.atlas f a g ≫ i.inv
  let r := SchemePullbackChart.fst f a g
  let q := SchemePullbackChart.snd f a g
  have hb : IsEtale b :=
    IsEtale.comp_iso (SchemePullbackChart.atlas_isEtale f a g ha) i.symm
  have hbs : IsSurjective b :=
    IsSurjective.comp_iso (SchemePullbackChart.atlas_isSurjective f a g hs) i.symm
  have hbq : b ≫ p = (schemeYoneda S).map q := by
    have h : i.inv ≫ p = pullback.snd (hom f) g := by
      change i.inv ≫ hom (FibreProduct.snd f g') = _
      rw [← FibreProduct.presheafIso_hom_snd f g']
      exact i.inv_hom_id_assoc _
    rw [show b = SchemePullbackChart.atlas f a g ≫ i.inv from rfl, Category.assoc, h]
    simp only [SchemePullbackChart.atlas, Category.assoc, Limits.pullback.map,
      Limits.pullback.lift_snd, Category.comp_id, IsPullback.isoPullback_hom_snd, q]
  have hq : LocallyOfFiniteType q.left := by
    let : LocallyOfFiniteType U.hom := hU
    let : _root_.AlgebraicGeometry.IsClosedImmersion (prod.lift r q).left :=
      closedImmersion_pair_of_isPullback hX (a ≫ hom f) g r q (SchemePullbackChart.isPullback f a g)
    let : LocallyOfFiniteType (prod.snd : U ⨯ T ⟶ T).left := by
      rw [← Over.prodLeftIsoPullback_hom_snd U T]
      infer_instance
    have h : q.left = (prod.lift r q).left ≫ (prod.snd : U ⨯ T ⟶ T).left := by
      rw [← Over.comp_left, prod.lift_snd]
    rw [h]
    infer_instance
  obtain ⟨M, ⟨e⟩⟩ := monomorphismLocallyFiniteTypeScheme S W T p hp
    ⟨R, b, q, hb, hbs, hbq, hq⟩
  exact ⟨M, ⟨e ≪≫ i⟩⟩

/-- A monomorphism with a locally finite type source and a separated target
has an actual representing scheme on every scheme test pullback. -/
def schemePullbackModelOfMono [Mono (hom f)]
    (hX' : LocallyOfFiniteTypeOverBase X') (hX : IsSeparated X)
    (T : Over S) (g : (schemeYoneda S).obj T ⟶ X.presheaf) :
    Σ R : Over S, (schemeYoneda S).obj R ≅ Limits.pullback (hom f) g :=
  let h := exists_scheme_pullback_of_mono f hX' hX T g
  ⟨h.choose, Classical.choice h.choose_spec⟩

/-- The scheme pullback models imply representability of the monomorphism. -/
theorem isRepresentableMorphism_of_mono_of_finiteType_source [Mono (hom f)]
    (hX' : LocallyOfFiniteTypeOverBase X') (hX : IsSeparated X) :
    IsRepresentableMorphism (hom f) := by
  intro T g
  let m := schemePullbackModelOfMono f hX' hX T g
  obtain ⟨q, a, h⟩ := AtlasEffectivity.exists_isPullback_of_iso
    (IsPullback.of_hasPullback (hom f) g) m.2
  exact ⟨m.1, q, a, h⟩

set_option backward.isDefEq.respectTransparency false in
/-- The quasi-compactness of an algebraic-space map gives quasi-compactness
of a represented pullback projection to an affine test. -/
theorem quasiCompact_of_represented_affine_pullback
    (hf : IsQuasiCompactMorphism f)
    {T W : Over S} [IsAffine T.left] (g : (schemeYoneda S).obj T ⟶ X.presheaf)
    {a : (schemeYoneda S).obj W ⟶ X'.presheaf} {q : W ⟶ T}
    (h : IsPullback a ((schemeYoneda S).map q) (hom f) g) : QuasiCompact q.left := by
  obtain ⟨U, b, hU, -, hbs⟩ := hf T inferInstance g
  let e := h.isoPullback
  let c := b ≫ e.inv
  have hc : IsSurjective c := IsSurjective.comp_iso hbs e.symm
  obtain ⟨r, hr⟩ := (schemeYoneda S).map_surjective c
  rw [← hr] at hc
  have hsr : Surjective r.left :=
    MorphismProperty.of_relative_map
      (P := MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)) hc
  have hW : CompactSpace W.left :=
    Function.Surjective.compactSpace r.left.continuous hsr.surj
  exact HasAffineProperty.iff_of_isAffine.mpr hW

end Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory _root_.CategoryTheory.Limits SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [NontriviallyNormedField K]
  {X' X : AlgebraicSpace (Spec (CommRingCat.of K))} (f : X' ⟶ X)

set_option backward.isDefEq.respectTransparency false in
/-- Closed immersions of represented morphisms can be tested on the
affine opens of an étale atlas locally of finite type over the base. -/
theorem isClosedImmersion_of_finiteType_affine_etale_tests
    (hr : IsRepresentableMorphism (hom f)) (hX : LocallyOfFiniteTypeOverBase X)
    (htest : ∀ (A : Type u) [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
      (x : RingPoints K X A), AlgebraicSpace.IsEtale (pointHom K x) →
      ∀ {W : Over (Spec (CommRingCat.of K))}
        (b : (schemeYoneda _).obj W ⟶ X'.presheaf) (q : W ⟶ ringTest K A),
        IsPullback b ((schemeYoneda _).map q) (hom f) (pointHom K x) →
        _root_.AlgebraicGeometry.IsClosedImmersion q.left) :
    AlgebraicSpace.IsClosedImmersion (hom f) := by
  obtain ⟨T, a, ha, hs, hT⟩ := hX.exists_atlas
  let : LocallyOfFiniteType T.hom := hT
  let S := Spec (CommRingCat.of K)
  let p := hr.snd a
  apply relativeProperty_of_etale_atlas @_root_.AlgebraicGeometry.IsClosedImmersion hr a ha hs
  change _root_.AlgebraicGeometry.IsClosedImmersion p.left
  let C := T.left.affineCover
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @_root_.AlgebraicGeometry.IsClosedImmersion) C]
  intro i
  let U := SchemeOpenChart.obj C i
  let j := SchemeOpenChart.map C i
  let : IsAffine U.left := inferInstanceAs (IsAffine (C.X i))
  let : LocallyOfFiniteType U.hom := by
    rw [← Over.w j]
    infer_instance
  let A := AffineCoordinateRing K U
  let e := affineSchemeOverIso K U
  let x : RingPoints K X A :=
    uliftYonedaEquiv.{u + 1} ((schemeYoneda S).map (e.inv ≫ j) ≫ a)
  have hx : pointHom K x = (schemeYoneda S).map (e.inv ≫ j) ≫ a :=
    Equiv.symm_apply_apply _ _
  have he : AlgebraicSpace.IsEtale (pointHom K x) := by
    rw [hx]
    apply AlgebraicSpace.IsEtale.comp _ ha
    apply isEtale_map
    change Etale (e.inv.left ≫ j.left)
    infer_instance
  let b := (schemeYoneda S).map (pullback.fst p j) ≫ hr.fst a
  let q := pullback.snd p j
  have hpb : IsPullback ((schemeYoneda S).map (pullback.fst p j))
      ((schemeYoneda S).map q) ((schemeYoneda S).map p) ((schemeYoneda S).map j) :=
    (IsPullback.of_hasPullback p j).map (schemeYoneda S)
  have hsq : IsPullback b ((schemeYoneda S).map q) (hom f)
      ((schemeYoneda S).map j ≫ a) := hpb.paste_horiz (hr.isPullback a)
  have hsq' : IsPullback b ((schemeYoneda S).map (q ≫ e.hom)) (hom f) (pointHom K x) := by
    apply hsq.of_iso (Iso.refl _) (Iso.refl _) ((schemeYoneda S).mapIso e) (Iso.refl _)
    · simp
    · simp only [Functor.mapIso_hom, Iso.refl_hom, Category.id_comp, Functor.map_comp]
    · simp
    · simp only [Functor.mapIso_hom, Iso.refl_hom, Category.comp_id]
      rw [hx, ← Functor.map_comp_assoc, Iso.hom_inv_id_assoc]
  have hc := htest A x he b (q ≫ e.hom) hsq'
  have hq : _root_.AlgebraicGeometry.IsClosedImmersion q.left :=
    (MorphismProperty.cancel_right_of_respectsIso
      @_root_.AlgebraicGeometry.IsClosedImmersion q.left ((Over.forget S).mapIso e).hom).mp hc
  have hscheme : IsPullback (pullback.fst p j).left q.left p.left j.left :=
    (IsPullback.of_hasPullback p j).map (Over.forget S)
  change _root_.AlgebraicGeometry.IsClosedImmersion (pullback.snd p.left j.left)
  rw [← hscheme.isoPullback_inv_snd]
  exact MorphismProperty.RespectsIso.precomp @_root_.AlgebraicGeometry.IsClosedImmersion _ _ hq

variable [IsUltrametricDist K] [CompleteSpace K]

set_option backward.isDefEq.respectTransparency false in
/-- For a quasi-compact algebraic-space map, closed immersion reflection
reduces to the compatible analytic pullback of each affine étale test and
the closed immersion comparison for maps of schemes. -/
theorem isClosedImmersion_of_closedImmersion_of_scheme_reflection
    (hClosedBase : ∀ {P A B Y : LocalizedCategory.{u, u, u} (K := K)}
      {r : P ⟶ A} {s : P ⟶ B} {g : A ⟶ Y} {h : B ⟶ Y},
      IsPullback r s g h → closedImmersion g → closedImmersion s)
    (hScheme : ∀ (A : Type u) [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
      (W : Over (Spec (CommRingCat.of K))) (q : W ⟶ ringTest K A),
      LocallyOfFiniteType W.hom → _root_.AlgebraicGeometry.IsSeparated W.hom →
      QuasiCompact q.left →
      ∀ (V : LocalizedCategory.{u, u, u} (K := K))
        (v : PointFamily K ((schemeToSpace _).obj W) V),
        IsAnalytification K ((schemeToSpace _).obj W) V v →
        ∀ s : V ⟶ AffineAnalytification.localized K P,
          (∀ (B : Type u) [CommRing B] [Algebra K B] (Q : FinitePolynomialPresentation K B)
            (z : RingPoints K ((schemeToSpace _).obj W) B),
              v B Q z ≫ s = AffineAnalytification.localizedHom K P Q
                (affineRingPointEquiv K A B (schemeRingPointsEquiv K W B z ≫ q))) →
          closedImmersion s → _root_.AlgebraicGeometry.IsClosedImmersion q.left)
    (hX'sep : IsSeparated X') (hX'ft : LocallyOfFiniteTypeOverBase X')
    (hXsep : IsSeparated X) (hXft : LocallyOfFiniteTypeOverBase X)
    {Y' Y : LocalizedCategory.{u, u, u} (K := K)} {p' : PointFamily K X' Y'}
    {p : PointFamily K X Y} (hp' : IsAnalytification K X' Y' p')
    (hp : IsAnalytification K X Y p) {F : Y' ⟶ Y}
    (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
        p' A P x ≫ F = p A P (RingPoints.map f x))
    (hChart : ∀ (A : Type u) [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
      (x : RingPoints K X A), AlgebraicSpace.IsEtale (pointHom K x) →
      ∀ {W : Over (Spec (CommRingCat.of K))}
        (b : (schemeYoneda _).obj W ⟶ X'.presheaf) (q : W ⟶ ringTest K A),
        IsPullback b ((schemeYoneda _).map q) (hom f) (pointHom K x) →
        LocallyOfFiniteType W.hom → _root_.AlgebraicGeometry.IsSeparated W.hom →
        ∃ (V : LocalizedCategory.{u, u, u} (K := K))
          (v : PointFamily K ((schemeToSpace _).obj W) V)
          (r : V ⟶ Y') (s : V ⟶ AffineAnalytification.localized K P),
          IsAnalytification K ((schemeToSpace _).obj W) V v ∧
          IsPullback r s F (p A P x) ∧
          ∀ (B : Type u) [CommRing B] [Algebra K B] (Q : FinitePolynomialPresentation K B)
            (z : RingPoints K ((schemeToSpace _).obj W) B),
              v B Q z ≫ s = AffineAnalytification.localizedHom K P Q
                (affineRingPointEquiv K A B (schemeRingPointsEquiv K W B z ≫ q)))
    (hqc : IsQuasiCompactMorphism f) (hc : closedImmersion F) :
    AlgebraicSpace.IsClosedImmersion (hom f) := by
  let : Mono F := hc.mono
  let : Mono (hom f) :=
    mono_of_mono_analytification_of_isSeparated f hp' hp hF hX'sep hXsep hX'ft
  let hr := isRepresentableMorphism_of_mono_of_finiteType_source f hX'ft hXsep
  apply isClosedImmersion_of_finiteType_affine_etale_tests f hr hXft
  intro A _ _ _ x hx W b q hAlg
  let P := FinitePolynomialPresentation.ofFiniteType K A
  let : IsAffine (ringTest K A).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  have hq := quasiCompact_of_represented_affine_pullback f hqc _ hAlg
  let S := Spec (CommRingCat.of K)
  let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
    (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S))
  have hb : AlgebraicSpace.IsEtale b := MorphismProperty.of_isPullback
    (P := (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
      (schemeYoneda S)) hAlg.flip hx
  have hft : LocallyOfFiniteType W.hom := locallyOfFiniteType_of_isEtale hX'ft b hb
  let : Mono ((schemeYoneda S).map q) := hAlg.mono_snd_of_mono
  let : Mono q := (schemeYoneda S).mono_of_mono_map inferInstance
  have hs : _root_.AlgebraicGeometry.IsSeparated W.hom := by
    rw [← Over.w q]
    have : _root_.AlgebraicGeometry.IsSeparated (ringTest K A).hom := by
      change _root_.AlgebraicGeometry.IsSeparated (Spec.algebraMap K A)
      infer_instance
    infer_instance
  obtain ⟨V, v, r, s, hv, hpb, hcompat⟩ := hChart A P x hx b q hAlg hft hs
  exact hScheme A P W q hft hs hq V v hv s hcompat (hClosedBase hpb hc)

end Langlands.Analytic.SpaceAnalytification
