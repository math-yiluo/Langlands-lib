import Langlands.AlgebraicGeometry.FiniteLocallyConstantRepresentableStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentationZariski
import Langlands.AlgebraicGeometry.Morphisms.FiniteCoproduct
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent
import Langlands.AlgebraicGeometry.Picard.EtaleRelationQuasiAffineEffectivity
import Langlands.AlgebraicGeometry.Picard.LocalRepresenterEtaleRelation
import Langlands.AlgebraicGeometry.Picard.LocalRepresenterSheafComparison
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top

/-! # Representability of finite locally constant étale sheaves -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry

open AlgebraicSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private abbrev splitProjection (U : Scheme.{u}) (A : Type u) :
    (∐ fun _ : A ↦ U) ⟶ U :=
  Sigma.desc fun _ ↦ 𝟙 U

private theorem splitProjection_finite (U : Scheme.{u}) (A : Type u) [Finite A] :
    IsFinite (splitProjection U A) := by
  have : IsProper (splitProjection U A) :=
    FiniteCoproduct.isProper_sigmaDesc (fun _ : A ↦ U) (fun _ ↦ 𝟙 U) (fun _ ↦ inferInstance)
  have : LocallyQuasiFinite (splitProjection U A) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @LocallyQuasiFinite) (fun _ : A ↦ inferInstanceAs
      (LocallyQuasiFinite (𝟙 U)))
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

private theorem splitProjection_etale (U : Scheme.{u}) (A : Type u) :
    Etale (splitProjection U A) :=
  IsZariskiLocalAtSource.sigmaDesc (P := @Etale) (fun _ : A ↦ inferInstanceAs (Etale (𝟙 U)))

section SplitRepresentation

variable {U : Scheme.{u}} {A : Type u} [TopologicalSpace A] [DiscreteTopology A]

private def splitLabel {T : Over U} (g : T ⟶ Over.mk (splitProjection U A)) : C(T.left, A) :=
  ⟨fun x ↦ ((sigmaMk (fun _ : A ↦ U)).symm (g.left x)).1,
    (continuous_sigma (fun a : A ↦ continuous_const (y := a))).comp
      ((sigmaMk (fun _ : A ↦ U)).symm.continuous.comp g.left.continuous)⟩

/-- A map to the disjoint union of copies of the base is determined by its continuous label. -/
private theorem splitLabel_bijective (T : Over U) :
    Function.Bijective (splitLabel (U := U) (A := A) (T := T)) := by
  classical
  let X : A → Scheme.{u} := fun _ ↦ U
  have classify (c : C(T.left, A)) : ∃! g : T ⟶ Over.mk (splitProjection U A),
      splitLabel g = c := by
    let V (a : A) : T.left.Opens := ⟨c ⁻¹' {a}, (isOpen_discrete _).preimage c.continuous⟩
    have hcov : (⨆ a, V a) = ⊤ := by
      apply eq_top_iff.mpr
      intro x _
      exact Opens.mem_iSup.mpr ⟨c x, rfl⟩
    have hdisj (a b : A) (h : a ≠ b) : Disjoint (V a) (V b) := by
      rw [← Opens.coe_disjoint, Set.disjoint_left]
      exact fun _ ha hb ↦ h (ha.symm.trans hb)
    let 𝒱 := T.left.openCoverOfIsOpenCover V hcov
    obtain ⟨g, hg, huniq⟩ := T.left.existsUnique_hom_sigma_of_disjoint_iSup_eq_top X V
      hdisj hcov (fun a ↦ (V a).ι ≫ T.hom)
    have hgU : g ≫ splitProjection U A = T.hom := by
      apply 𝒱.hom_ext
      intro a
      change (V a).ι ≫ g ≫ splitProjection U A = (V a).ι ≫ T.hom
      rw [← Category.assoc, hg a]
      simp [Category.assoc, splitProjection, X]
    refine ⟨Over.homMk g hgU, ?_, ?_⟩
    · ext x
      have e := congrArg (fun f : (V (c x)).toScheme ⟶ ∐ X ↦ f ⟨x, rfl⟩) (hg (c x))
      change splitLabel (Over.homMk g hgU) x = c x
      change ((sigmaMk X).symm (g x)).1 = c x
      simp only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at e
      rw [e, ← sigmaMk_mk, Homeomorph.symm_apply_apply]
    · intro k hk
      apply Over.OverMorphism.ext
      apply huniq
      intro a
      have hr : Set.range ((V a).ι ≫ k.left) ⊆ Set.range (Sigma.ι X a) := by
        rintro _ ⟨x, rfl⟩
        have hx : ((sigmaMk X).symm (k.left x.1)).1 = a := by
          change splitLabel k x.1 = a
          rw [hk]
          exact x.2
        rcases he : (sigmaMk X).symm (k.left x.1) with ⟨b, y⟩
        have hb : b = a := by simpa only [he] using hx
        subst b
        refine ⟨y, ?_⟩
        have hy := congrArg (sigmaMk X) he
        simpa only [Homeomorph.apply_symm_apply, sigmaMk_mk, Scheme.Hom.comp_apply,
          Scheme.Opens.ι_apply] using hy.symm
      let l := IsOpenImmersion.lift (Sigma.ι X a) ((V a).ι ≫ k.left) hr
      have hl : l ≫ Sigma.ι X a = (V a).ι ≫ k.left := IsOpenImmersion.lift_fac _ _ _
      have hkU : k.left ≫ splitProjection U A = T.hom := Over.w k
      have hlU : l = (V a).ι ≫ T.hom := by
        calc
          l = (l ≫ Sigma.ι X a) ≫ splitProjection U A := by
            simp [Category.assoc, splitProjection, X]
          _ = (V a).ι ≫ T.hom := by rw [hl, Category.assoc, hkU]
      rw [← hl, hlU]
  exact ⟨fun g k h ↦ ((classify (splitLabel k)).unique h rfl),
    fun c ↦ (classify c).exists⟩

/-- On all schemes over the base, the coproduct represents continuous labels. -/
private def splitRepresentation (U : Scheme.{u}) (A : Type u)
    [TopologicalSpace A] [DiscreteTopology A] :
    ((Over.forget U).op ⋙ continuousMapPresheaf.{u, u} A).RepresentableBy
      (Over.mk (splitProjection U A)) where
  homEquiv {T} := Equiv.ofBijective splitLabel (splitLabel_bijective T)
  homEquiv_comp {T T'} f g := by
    change splitLabel (f ≫ g) = (splitLabel g).comp f.left.base.hom
    ext x
    change ((sigmaMk (fun _ : A ↦ U)).symm ((f.left ≫ g.left) x)).1 =
      ((sigmaMk (fun _ : A ↦ U)).symm (g.left (f.left x))).1
    rw [Scheme.Hom.comp_apply]

end SplitRepresentation

private def restrictComp {S U T : Scheme.{u}} (F : AlgebraicSpace.Presheaf S)
    (a : U ⟶ S) (b : T ⟶ U) :
    (Over.map b).op ⋙ (Over.map a).op ⋙ F ≅ (Over.map (b ≫ a)).op ⋙ F :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (NatIso.op (Over.mapComp b a)) F

private def restrictRepresentation {S U T : Scheme.{u}} {F : AlgebraicSpace.Presheaf S}
    {a : U ⟶ S} {M : Over U} (b : T ⟶ U)
    (e : (schemeYoneda U).obj M ≅ (Over.map a).op ⋙ F) :
    (schemeYoneda T).obj ((Over.pullback b).obj M) ≅ (Over.map (b ≫ a)).op ⋙ F :=
  representedBaseChangeIso b M e ≪≫ restrictComp F a b

private theorem glueRepresentations {S : Scheme.{u}} {F : AlgebraicSpace.Presheaf S}
    (hF : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (𝒰 : S.OpenCover.{u}) (M : ∀ i, Over (𝒰.X i))
    (e : ∀ i, (schemeYoneda (𝒰.X i)).obj (M i) ≅ (Over.map (𝒰.f i)).op ⋙ F)
    (hfin : ∀ i, IsFinite (M i).hom) (het : ∀ i, Etale (M i).hom) :
    ∃ N : Over S, IsFinite N.hom ∧ Etale N.hom ∧ Nonempty ((schemeYoneda S).obj N ≅ F) := by
  have hF' : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F :=
    hF.of_le fun _ _ h ↦ Scheme.zariskiTopology_le_etaleTopology _ h
  obtain ⟨N, ⟨eN⟩⟩ := LocalRepresentation.exists_representation_zariski hF' 𝒰 M e
  exact ⟨N, LocalRepresentation.property_of_local_representations (@IsFinite) N eN 𝒰 M e hfin,
    LocalRepresentation.property_of_local_representations (@Etale) N eN 𝒰 M e het, ⟨eN⟩⟩

private theorem descendRepresentation {S U : Scheme.{u}} [IsAffine S] [IsAffine U]
    (p : U ⟶ S) [Etale p] [Surjective p] {F : AlgebraicSpace.Presheaf S}
    (hF : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F) (M : Over U)
    (eM : (schemeYoneda U).obj M ≅ (Over.map p).op ⋙ F)
    (hfin : IsFinite M.hom) (het : Etale M.hom) :
    ∃ N : Over S, IsFinite N.hom ∧ Etale N.hom ∧ Nonempty ((schemeYoneda S).obj N ≅ F) := by
  let r : ((Over.map p).op ⋙ F).RepresentableBy M :=
    (Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} _ _).symm eM
  let E := Picard.LocalRepresenter.etaleRelation p r
  have hcart : IsPullback E.t (E.s ≫ M.hom) (M.hom ≫ p) p :=
    Picard.LocalRepresenter.cartesian p r
  have : IsAffine M.left := isAffine_of_isAffineHom M.hom
  obtain ⟨N, q, hq, hi⟩ :=
    EtaleRelationQuasiAffineEffectivity.exists_effective_of_invariantQuasiAffine
      hcart (fun _ ↦ ⟨⊤, by simp, by simp, by
        have : IsAffine ((⊤ : E.U.Opens).toScheme) := isAffineOpen_top M.left
        infer_instance⟩)
  let P : MorphismProperty Scheme.{u} := @Surjective ⊓ @Flat ⊓ @QuasiCompact
  have hp : P p := by
    exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hN := Picard.LocalRepresenter.representableByDescent p r
    ((isSheaf_iff_isSheaf_of_type _ _).mp hF) N q hq hi
  exact ⟨N, MorphismProperty.of_isPullback_of_descendsAlong (P := @IsFinite) hq.flip hp hfin,
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Etale) hq.flip hp het,
    ⟨Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} _ _ hN⟩⟩

private theorem existsRepresentationAffine {S : Scheme.{u}} [IsAffine S]
    {F : AlgebraicSpace.Presheaf S} (hF : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (𝒰 : S.Cover.{u} (Scheme.precoverage @Etale)) (M : ∀ i, Over (𝒰.X i))
    (e : ∀ i, (schemeYoneda (𝒰.X i)).obj (M i) ≅ (Over.map (𝒰.f i)).op ⋙ F)
    (hfin : ∀ i, IsFinite (M i).hom) (het : ∀ i, Etale (M i).hom) :
    ∃ N : Over S, IsFinite N.hom ∧ Etale N.hom ∧ Nonempty ((schemeYoneda S).obj N ≅ F) := by
  classical
  have : QuasiCompactCover 𝒰.toPreZeroHypercover := QuasiCompactCover.of_isOpenMap fun i ↦ by
    have : Etale (𝒰.f i) := 𝒰.map_prop i
    exact (𝒰.f i).isOpenMap
  obtain ⟨𝒱, h, hfinite, _⟩ := QuasiCompactCover.exists_hom.{u} 𝒰
  let : Finite 𝒱.I₀ := hfinite
  let B (i : 𝒱.I₀) := Spec (𝒱.X i)
  let b : (∐ B) ⟶ S := Sigma.desc 𝒱.f
  let F' := (Over.map b).op ⋙ F
  have hF' : Presheaf.IsSheaf (Scheme.etaleTopology.over (∐ B)) F' :=
    ((Scheme.etaleTopology.overMapPullback (Type (u + 1)) b).obj ⟨F, hF⟩).property
  let M' (i : 𝒱.I₀) : Over (B i) := (Over.pullback (h.h₀ i)).obj (M (h.s₀ i))
  have e' (i : 𝒱.I₀) : (schemeYoneda (B i)).obj (M' i) ≅
      (Over.map (Sigma.ι B i)).op ⋙ F' :=
    restrictRepresentation (h.h₀ i) (e (h.s₀ i)) ≪≫
      Functor.isoWhiskerRight (NatIso.op (Over.mapCongr _ _
        ((Sigma.ι_comp_desc 𝒱.f i).trans (h.w₀ i).symm))) F ≪≫
      (restrictComp F b (Sigma.ι B i)).symm
  have hfin' (i : 𝒱.I₀) : IsFinite (M' i).hom :=
    MorphismProperty.pullback_snd (P := @IsFinite) _ _ (hfin (h.s₀ i))
  have het' (i : 𝒱.I₀) : Etale (M' i).hom :=
    MorphismProperty.pullback_snd (P := @Etale) _ _ (het (h.s₀ i))
  obtain ⟨N, hnfin, hnet, ⟨eN⟩⟩ := glueRepresentations hF' (sigmaOpenCover B) M' e' hfin' het'
  have : IsAffine (∐ B) := by
    dsimp [B]
    infer_instance
  have : Etale b := IsZariskiLocalAtSource.sigmaDesc 𝒱.map_prop
  have : Surjective b := Surjective.sigmaDesc_of_union_range_eq_univ 𝒱.cover.iUnion_range
  exact descendRepresentation b hF N eN hnfin hnet

private theorem existsRepresentation {S : Scheme.{u}} {F : AlgebraicSpace.Presheaf S}
    (hF : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (𝒰 : S.Cover.{u} (Scheme.precoverage @Etale)) (M : ∀ i, Over (𝒰.X i))
    (e : ∀ i, (schemeYoneda (𝒰.X i)).obj (M i) ≅ (Over.map (𝒰.f i)).op ⋙ F)
    (hfin : ∀ i, IsFinite (M i).hom) (het : ∀ i, Etale (M i).hom) :
    ∃ N : Over S, IsFinite N.hom ∧ Etale N.hom ∧ Nonempty ((schemeYoneda S).obj N ≅ F) := by
  classical
  let 𝒱 := S.affineCover
  have localModel (i : 𝒱.I₀) : ∃ N : Over (𝒱.X i), IsFinite N.hom ∧ Etale N.hom ∧
      Nonempty ((schemeYoneda (𝒱.X i)).obj N ≅ (Over.map (𝒱.f i)).op ⋙ F) := by
    let a := 𝒱.f i
    let 𝒲 := 𝒰.pullback₁ a
    let M' (j : 𝒲.I₀) := (Over.pullback (𝒰.pullbackHom a j)).obj (M j)
    have hF' : Presheaf.IsSheaf (Scheme.etaleTopology.over (𝒱.X i)) ((Over.map a).op ⋙ F) :=
      ((Scheme.etaleTopology.overMapPullback (Type (u + 1)) a).obj ⟨F, hF⟩).property
    apply existsRepresentationAffine hF' 𝒲 M'
    · intro j
      exact restrictRepresentation (𝒰.pullbackHom a j) (e j) ≪≫
        Functor.isoWhiskerRight (NatIso.op (Over.mapCongr _ _ (𝒰.pullbackHom_map a j).symm)) F ≪≫
        (restrictComp F a (𝒲.f j)).symm
    · exact fun j ↦ MorphismProperty.pullback_snd (P := @IsFinite) _ _ (hfin j)
    · exact fun j ↦ MorphismProperty.pullback_snd (P := @Etale) _ _ (het j)
  choose N hNfin hNet eN using localModel
  exact glueRepresentations hF 𝒱 N (fun i ↦ (eN i).some) hNfin hNet

/-- A finite locally constant étale sheaf of sets is represented by a finite étale scheme. -/
theorem finiteLocallyConstantRepresentable : FiniteLocallyConstantRepresentableStatement.{u} := by
  classical
  intro S F hF hlocal
  obtain ⟨𝒰, hlocal⟩ := hlocal
  choose A hA e using hlocal
  let F' : AlgebraicSpace.Presheaf S := F ⋙ uliftFunctor.{u + 1}
  have hF' : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F' :=
    (isSheaf_iff_isSheaf_of_type _ _).mpr (Presieve.isSheaf_comp_uliftFunctor _
      ((isSheaf_iff_isSheaf_of_type _ _).mp hF))
  let M (i : 𝒰.I₀) : Over (𝒰.X i) := Over.mk (splitProjection (𝒰.X i) (A i))
  have e' (i : 𝒰.I₀) : (schemeYoneda (𝒰.X i)).obj (M i) ≅ (Over.map (𝒰.f i)).op ⋙ F' := by
    letI : TopologicalSpace (A i) := ⊥
    letI : DiscreteTopology (A i) := ⟨rfl⟩
    let r := (splitRepresentation (𝒰.X i) (A i)).ofIso (e i).some.symm
    exact Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} _ _
      (Functor.representableByUliftFunctorEquiv.symm r) ≪≫ Functor.associator _ _ _
  obtain ⟨N, hnfin, hnet, ⟨eN⟩⟩ := existsRepresentation hF' 𝒰 M e'
    (fun i ↦ have := hA i; splitProjection_finite _ _) (fun i ↦ splitProjection_etale _ _)
  obtain ⟨X, q, rfl⟩ := Over.mk_surjective N
  exact ⟨X, q, hnfin, hnet, ⟨Functor.representableByUliftFunctorEquiv
    ((Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} _ _).symm eN)⟩⟩

end Langlands.AlgebraicGeometry
