import Langlands.Geometry.Analytic.SpaceAnalytificationImmersionHelpers
import Langlands.Geometry.Analytic.AffineAnalytificationImmersionStatement
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedFunctorialityProof

/-! # Closed immersion analytification reduced to the affine closed embedding input -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory CategoryTheory.Limits _root_.Topology Opposite SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology
  (ringTest ringTestMap ringTestMap_comp affineRingPointEquiv AffineCoordinateRing
    affineSchemeOverIso)

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- A closed immersion to an affine test is represented by a surjection of finite-type
coordinate algebras, with the original pullback square retained. -/
theorem exists_closed_affine_test_pullback
    {X' X : AlgebraicSpace (Spec (CommRingCat.of K))} (f : X' ⟶ X)
    (hf : AlgebraicSpace.IsClosedImmersion (hom f))
    (A : Type u) [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
    (x : RingPoints K X A) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra K C)
      (_Q : FinitePolynomialPresentation K C) (z : RingPoints K X' C) (φ : A →ₐ[K] C),
      Function.Surjective φ ∧
        IsPullback (pointHom K z) ((schemeYoneda _).map (ringTestMap K φ))
          (hom f) (pointHom K x) := by
  let : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective P.map P.surjective
  let hr := hf.representable
  let V := hr.pullback (pointHom K x)
  let q : V ⟶ ringTest K A := hr.snd (pointHom K x)
  let : _root_.AlgebraicGeometry.IsClosedImmersion q.left :=
    hf.pullback_closedImmersion hr (pointHom K x)
  let : IsAffine V.left := isAffine_of_isAffineHom q.left
  have : LocallyOfFiniteType V.hom := by
    rw [← Over.w q]
    infer_instance
  let C := AffineCoordinateRing K V
  let Q := FinitePolynomialPresentation.ofFiniteType K C
  let e : V ≅ ringTest K C := affineSchemeOverIso K V
  let φ : A →ₐ[K] C := affineRingPointEquiv K A C (e.inv ≫ q)
  have hφ : ringTestMap K φ = e.inv ≫ q := by
    ext1
    exact Spec.map_preimage _
  let z : RingPoints K X' C := uliftYonedaEquiv.{u + 1}
    ((schemeYoneda _).map e.inv ≫ hr.fst (pointHom K x))
  have hz : pointHom K z = (schemeYoneda _).map e.inv ≫ hr.fst (pointHom K x) :=
    uliftYonedaEquiv.symm_apply_apply _
  have hspec : _root_.AlgebraicGeometry.IsClosedImmersion
      (Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
    change _root_.AlgebraicGeometry.IsClosedImmersion (ringTestMap K φ).left
    rw [hφ]
    let : IsIso e.inv.left := by
      change IsIso ((Over.forget _).map e.inv)
      infer_instance
    change _root_.AlgebraicGeometry.IsClosedImmersion (e.inv.left ≫ q.left)
    infer_instance
  have hsurj : Function.Surjective φ := by
    let := hspec
    have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine
      (Spec.map (CommRingCat.ofHom φ.toRingHom))).2
    intro c
    obtain ⟨t, ht⟩ := hs ((Scheme.ΓSpecIso (CommRingCat.of C)).inv c)
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom t, ?_⟩
    have hn := congrArg (fun k => k t)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ.toRingHom))
    change (Scheme.ΓSpecIso (CommRingCat.of C)).hom
      ((Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop t) =
        φ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom t) at hn
    rw [ht, Iso.inv_hom_id_apply] at hn
    exact hn.symm
  refine ⟨C, inferInstance, inferInstance, Q, z, φ, hsurj, ?_⟩
  rw [hz, hφ]
  apply (hr.isPullback (pointHom K x)).of_iso ((schemeYoneda _).mapIso e)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp
  · simp [q, ← Functor.map_comp]
  · simp
  · simp

/-- Closed subsets of an analytification can be tested on its etale affine charts. -/
theorem IsAnalytification.isClosed_of_chart_preimages
    {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    {Y : LocalizedCategory.{u, u, u} (K := K)} {p : PointFamily K X Y}
    (hp : IsAnalytification K X Y p) (s : Set (localizedSpaceFunctor.obj Y))
    (hs : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X A),
      AlgebraicSpace.IsEtale (pointHom K x) →
        IsClosed (localizedSpaceFunctor.map (p A P x) ⁻¹' s)) : IsClosed s := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_forall_mem_open.mpr
  intro y hy
  obtain ⟨A, _, _, P, x, hx, a, ha⟩ := hp.jointly_surjective y
  have hopen := etaleOpenMap K (p A P x) (hp.etale_map P x hx)
  refine ⟨localizedSpaceFunctor.map (p A P x) ''
    (localizedSpaceFunctor.map (p A P x) ⁻¹' s)ᶜ, ?_,
    hopen _ (hs A P x hx).isOpen_compl, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact hb
  · refine ⟨a, ?_, ha⟩
    change localizedSpaceFunctor.map (p A P x) a ∉ s
    rw [ha]
    exact hy

/-- Any represented affine test square has lifts of all compatible analytic point pairs. -/
theorem exists_point_of_affine_test_pullback
    {X' X : AlgebraicSpace (Spec (CommRingCat.of K))} (f : X' ⟶ X)
    (hX : IsSeparated X)
    {Y' Y : LocalizedCategory.{u, u, u} (K := K)}
    {p' : PointFamily K X' Y'} {p : PointFamily K X Y}
    (hp' : IsAnalytification K X' Y' p') (hp : IsAnalytification K X Y p)
    (F : Y' ⟶ Y)
    (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
      p' A P x ≫ F = p A P (RingPoints.map f x))
    {A C : Type u} [CommRing A] [Algebra K A] [CommRing C] [Algebra K C]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K C)
    (x : RingPoints K X A) (z : RingPoints K X' C) (φ : A →ₐ[K] C)
    (hsq : IsPullback (pointHom K z) ((schemeYoneda _).map (ringTestMap K φ))
      (hom f) (pointHom K x))
    (y' : localizedSpaceFunctor.obj Y') (a : localizedSpaceFunctor.obj
      (AffineAnalytification.localized K P))
    (hya : localizedSpaceFunctor.map F y' = localizedSpaceFunctor.map (p A P x) a) :
    ∃ c : localizedSpaceFunctor.obj (AffineAnalytification.localized K Q),
      localizedSpaceFunctor.map (p' C Q z) c = y' ∧
        localizedSpaceFunctor.map (AffineAnalytification.localizedHom K P Q φ) c = a := by
  obtain ⟨B, _, _, R, b, _, b₀, hb₀⟩ := hp'.jointly_surjective y'
  let : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective P.map P.surjective
  let : Algebra.FiniteType K B := Algebra.FiniteType.of_surjective R.map R.surjective
  obtain ⟨D, _, _, hD, α, β, hpb⟩ := hasFiniteTypeAffinePullbacks_of_separated K X hX
    B A (pointHom K (RingPoints.map f b)) (pointHom K x)
  let := hD
  let T := FinitePolynomialPresentation.ofFiniteType K D
  have hcompat : localizedSpaceFunctor.map (p B R (RingPoints.map f b)) b₀ =
      localizedSpaceFunctor.map (p A P x) a := by
    rw [← hF B R b, Functor.map_comp, TopCat.comp_app, hb₀]
    exact hya
  obtain ⟨d, hd₁, hd₂⟩ := exists_point_of_isPullback _ _ _ _
    (hp.isPullback R P T α β _ _ hpb) b₀ a hcompat
  let l := hsq.lift ((schemeYoneda _).map (ringTestMap K α) ≫ pointHom K b)
    ((schemeYoneda _).map (ringTestMap K β)) (by
      rw [Category.assoc, ← pointHom_map K]
      exact hpb.w)
  let l₀ := (schemeYoneda (Spec (CommRingCat.of K))).preimage l
  let γ : C →ₐ[K] D := affineRingPointEquiv K C D l₀
  have hγ : ringTestMap K γ = l₀ := by
    ext1
    exact Spec.map_preimage _
  have hl : (schemeYoneda _).map (ringTestMap K γ) = l := by
    rw [hγ]
    exact Functor.map_preimage _ _
  have hsource : RingPoints.changeRing γ z = RingPoints.changeRing α b := by
    apply uliftYonedaEquiv.{u + 1}.symm.injective
    simpa only [pointHom_changeRing, hl] using
      hsq.lift_fst ((schemeYoneda _).map (ringTestMap K α) ≫ pointHom K b)
        ((schemeYoneda _).map (ringTestMap K β)) _
  have hcomp : γ.comp φ = β := by
    have hmap : (schemeYoneda _).map (ringTestMap K (γ.comp φ)) =
        (schemeYoneda _).map (ringTestMap K β) := by
      rw [ringTestMap_comp, Functor.map_comp, hl]
      exact hsq.lift_snd _ _ _
    have hscheme := (schemeYoneda _).map_injective hmap
    have hspec := congrArg (fun k => k.left) hscheme
    apply AlgHom.coe_ringHom_injective
    exact congrArg (fun k => k.hom) (Spec.map_injective hspec)
  refine ⟨localizedSpaceFunctor.map (AffineAnalytification.localizedHom K Q T γ) d, ?_, ?_⟩
  · have hn : AffineAnalytification.localizedHom K Q T γ ≫ p' C Q z =
        AffineAnalytification.localizedHom K R T α ≫ p' B R b := by
      rw [← hp'.naturality, ← hp'.naturality, hsource]
    have he := congrArg (fun k => localizedSpaceFunctor.map k d) hn
    simpa only [Functor.map_comp, TopCat.comp_app, hd₁, hb₀] using he
  · have hc := (AffineAnalytification.affineAnalytificationLocalizedFunctoriality K
      A C D P P Q T φ γ).2.2.2.1
    rw [hcomp] at hc
    have he := congrArg (fun k => localizedSpaceFunctor.map k d) hc
    simpa only [Functor.map_comp, TopCat.comp_app, hd₂] using he.symm

/-- The affine closed embedding input required by the descent argument. -/
def AffineClosedEmbeddingProperty (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ (A C : Type u) [CommRing A] [Algebra K A] [CommRing C] [Algebra K C]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K C)
    (φ : A →ₐ[K] C), Function.Surjective φ →
      IsClosedEmbedding (localizedSpaceFunctor.map (AffineAnalytification.localizedHom K P Q φ))

/-- The published affine immersion target supplies precisely this affine input. -/
theorem affineClosedEmbeddingProperty_of_statement
    (h : AffineAnalytification.AffineAnalytificationImmersionStatement.{u, u, u, u}) :
    AffineClosedEmbeddingProperty K := by
  intro A C _ _ _ _ P Q φ hφ
  rw [AffineAnalytification.localizedSpaceFunctor_map_localizedHom]
  exact (h K A P).1 C Q φ hφ

/-- The analytification of a closed immersion is a closed map, given the affine input. -/
theorem isClosedMap_of_isClosedImmersion
    (hAffine : AffineClosedEmbeddingProperty K)
    {X' X : AlgebraicSpace (Spec (CommRingCat.of K))} (f : X' ⟶ X)
    (hX : IsSeparated X) (hf : AlgebraicSpace.IsClosedImmersion (hom f))
    {Y' Y : LocalizedCategory.{u, u, u} (K := K)}
    {p' : PointFamily K X' Y'} {p : PointFamily K X Y}
    (hp' : IsAnalytification K X' Y' p') (hp : IsAnalytification K X Y p)
    (F : Y' ⟶ Y)
    (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
      p' A P x ≫ F = p A P (RingPoints.map f x)) :
    IsClosedMap (localizedSpaceFunctor.map F) := by
  intro s hs
  apply hp.isClosed_of_chart_preimages
  intro A _ _ P x _
  obtain ⟨C, _, _, Q, z, φ, hsurj, hsq⟩ := exists_closed_affine_test_pullback f hf A P x
  have hxz : RingPoints.map f z = RingPoints.changeRing φ x := by
    apply uliftYonedaEquiv.{u + 1}.symm.injective
    rw [← pointHom, ← pointHom, pointHom_map K, pointHom_changeRing]
    exact hsq.w
  have hcomm : p' C Q z ≫ F =
      AffineAnalytification.localizedHom K P Q φ ≫ p A P x := by
    rw [hF, hxz, hp.naturality]
  have heq : localizedSpaceFunctor.map (p A P x) ⁻¹'
      (localizedSpaceFunctor.map F '' s) =
      localizedSpaceFunctor.map (AffineAnalytification.localizedHom K P Q φ) ''
        (localizedSpaceFunctor.map (p' C Q z) ⁻¹' s) := by
    ext a
    constructor
    · rintro ⟨y', hy', hya⟩
      obtain ⟨c, hc₁, hc₂⟩ := exists_point_of_affine_test_pullback f hX hp' hp F hF
        P Q x z φ hsq y' a hya
      refine ⟨c, ?_, hc₂⟩
      change localizedSpaceFunctor.map (p' C Q z) c ∈ s
      rw [hc₁]
      exact hy'
    · rintro ⟨c, hc, rfl⟩
      refine ⟨localizedSpaceFunctor.map (p' C Q z) c, hc, ?_⟩
      have he := congrArg (fun k => localizedSpaceFunctor.map k c) hcomm
      simpa only [Functor.map_comp, TopCat.comp_app] using he
  rw [heq]
  exact (hAffine A C P Q φ hsurj).isClosedMap _
    (hs.preimage (localizedSpaceFunctor.map (p' C Q z)).hom.continuous)

/-- The analytification of a closed immersion is a closed embedding, given the affine input. -/
theorem isClosedEmbedding_of_isClosedImmersion
    (hAffine : AffineClosedEmbeddingProperty K)
    {X' X : AlgebraicSpace (Spec (CommRingCat.of K))} (f : X' ⟶ X)
    (hX : IsSeparated X) (hf : AlgebraicSpace.IsClosedImmersion (hom f))
    {Y' Y : LocalizedCategory.{u, u, u} (K := K)}
    {p' : PointFamily K X' Y'} {p : PointFamily K X Y}
    (hp' : IsAnalytification K X' Y' p') (hp : IsAnalytification K X Y p)
    (F : Y' ⟶ Y)
    (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
      p' A P x ≫ F = p A P (RingPoints.map f x)) :
    IsClosedEmbedding (localizedSpaceFunctor.map F) := by
  let : Mono (hom f) := mono_of_isClosedImmersion hf
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap
    (localizedSpaceFunctor.map F).hom.continuous (map_injective_of_mono f hX hp' hp F hF)
    (isClosedMap_of_isClosedImmersion hAffine f hX hf hp' hp F hF)

/-- The unchanged full immersion statement reduces to affine closed embeddings alone. -/
def SpaceAnalytificationImmersionReductionStatement : Prop :=
  (∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K],
    AffineClosedEmbeddingProperty K) → SpaceAnalytificationImmersionStatement.{u}

/-- Both immersion conclusions follow from the supplied affine closed embedding input. -/
theorem spaceAnalytificationImmersionReduction :
    SpaceAnalytificationImmersionReductionStatement.{u} := by
  intro hAffine K _ _ _ X' X f _ _ hX _ Y' Y p' p hp' hp F hF
  exact ⟨fun hf => isOpenEmbedding_of_isOpenImmersion f hX hf hp' hp F hF,
    fun hf => isClosedEmbedding_of_isClosedImmersion (hAffine K) f hX hf hp' hp F hF⟩

end Langlands.Analytic.SpaceAnalytification
