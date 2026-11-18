import Langlands.Geometry.Analytic.SpaceAnalytification
import Langlands.Geometry.Analytic.AffineSchemeAnalytification
import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineIntersections
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartOpenMap
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Closed affine pullbacks of algebraic-space test points -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory CategoryTheory.Limits Topology TensorProduct
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology (ringTest ringTestMap affineRingPointEquiv)

variable {K : Type u} [NontriviallyNormedField K]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))}

/-- Finitely presented affine test points admit a finitely presented affine
pullback, closed in the product of the two affine tests. -/
def HasClosedAffinePointPullbacks : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra K A] (_P : FinitePolynomialPresentation K A)
    (B : Type u) [CommRing B] [Algebra K B] (_Q : FinitePolynomialPresentation K B)
    (x : RingPoints K X A) (y : RingPoints K X B),
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra K C)
      (_R : FinitePolynomialPresentation K C) (f : A →ₐ[K] C) (g : B →ₐ[K] C),
      Function.Surjective
        (Algebra.TensorProduct.lift f g (fun a b => mul_comm (f a) (g b)) :
          A ⊗[K] B →ₐ[K] C) ∧
        IsPullback ((schemeYoneda _).map (ringTestMap K f))
          ((schemeYoneda _).map (ringTestMap K g)) (pointHom K x) (pointHom K y)

set_option backward.isDefEq.respectTransparency false in
/-- Separatedness supplies closed affine pullbacks for all affine tests. -/
theorem hasClosedAffinePointPullbacks_of_isSeparated (hX : IsSeparated X) :
    HasClosedAffinePointPullbacks (K := K) (X := X) := by
  intro A _ _ P B _ _ Q x y
  let : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective P.map P.surjective
  let : Algebra.FiniteType K B := Algebra.FiniteType.of_surjective Q.map Q.surjective
  let U := ringTest K A
  let V := ringTest K B
  let W := pairPullback (pointHom K x) (pointHom K y)
  let a := pairPullbackFst (pointHom K x) (pointHom K y)
  let b := pairPullbackSnd (pointHom K x) (pointHom K y)
  have hpb := pairPullback_isPullback (pointHom K x) (pointHom K y)
  have hclosed := closedImmersion_pair_of_isPullback hX
    (pointHom K x) (pointHom K y) a b hpb
  have : IsAffine W.left := isAffine_of_isPullback_of_closedDiagonal hX
    (pointHom K x) (pointHom K y) a b hpb
  have hprodft : LocallyOfFiniteType (U ⨯ V).hom := by
    rw [← Over.w (prod.fst : U ⨯ V ⟶ U), ← Over.prodLeftIsoPullback_hom_fst U V]
    infer_instance
  have : LocallyOfFiniteType W.hom := by
    rw [← Over.w (prod.lift a b)]
    infer_instance
  let C := AffineSchemeAnalytification.CoordinateRing W.hom
  let R := AffineSchemeAnalytification.presentation W.hom
  let e : W ≅ ringTest K C := Over.isoMk
    (AffineSchemeAnalytification.coordinateIso W.hom)
    (AffineSchemeAnalytification.coordinateIso_hom_over W.hom)
  let f := affineRingPointEquiv K A C (e.inv ≫ a)
  let g := affineRingPointEquiv K B C (e.inv ≫ b)
  have hfa : ringTestMap K f = e.inv ≫ a := by
    apply Over.OverMorphism.ext
    exact Spec.map_preimage _
  have hgb : ringTestMap K g = e.inv ≫ b := by
    apply Over.OverMorphism.ext
    exact Spec.map_preimage _
  have hpb' : IsPullback ((schemeYoneda _).map (ringTestMap K f))
      ((schemeYoneda _).map (ringTestMap K g)) (pointHom K x) (pointHom K y) := by
    rw [hfa, hgb]
    exact hpb.of_iso ((schemeYoneda _).mapIso e) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [a]) (by simp [b]) (by simp) (by simp)
  let h : A ⊗[K] B →ₐ[K] C :=
    Algebra.TensorProduct.lift f g (fun a b => mul_comm (f a) (g b))
  let m := (prod.lift (ringTestMap K f) (ringTestMap K g)).left
  have hm : _root_.AlgebraicGeometry.IsClosedImmersion m :=
    closedImmersion_pair_of_isPullback hX (pointHom K x) (pointHom K y)
      (ringTestMap K f) (ringTestMap K g) hpb'
  have heq : Spec.map (CommRingCat.ofHom h.toRingHom) ≫ (pullbackSpecIso K A B).inv =
      m ≫ (Over.prodLeftIsoPullback U V).hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [pullbackSpecIso_inv_fst, ← Spec.map_comp]
      erw [Over.prodLeftIsoPullback_hom_fst]
      dsimp only [m]
      erw [← Over.comp_left, prod.lift_fst]
      change Spec.map (CommRingCat.ofHom ((h.comp Algebra.TensorProduct.includeLeft).toRingHom)) = _
      rw [Algebra.TensorProduct.lift_comp_includeLeft]
      rfl
    · simp only [Category.assoc]
      rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
      erw [Over.prodLeftIsoPullback_hom_snd]
      dsimp only [m]
      erw [← Over.comp_left, prod.lift_snd]
      change Spec.map (CommRingCat.ofHom ((h.comp Algebra.TensorProduct.includeRight).toRingHom)) = _
      rw [Algebra.TensorProduct.lift_comp_includeRight']
      rfl
  have hspec : _root_.AlgebraicGeometry.IsClosedImmersion
      (Spec.map (CommRingCat.ofHom h.toRingHom)) := by
    have hc : _root_.AlgebraicGeometry.IsClosedImmersion
        (Spec.map (CommRingCat.ofHom h.toRingHom) ≫ (pullbackSpecIso K A B).inv) := by
      rw [heq]
      infer_instance
    exact (MorphismProperty.cancel_right_of_respectsIso
      @_root_.AlgebraicGeometry.IsClosedImmersion _ (pullbackSpecIso K A B).inv).mp hc
  have hsurj : Function.Surjective h := by
    intro c
    let := hspec
    have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine
      (Spec.map (CommRingCat.ofHom h.toRingHom))).2
    obtain ⟨t, ht⟩ := hs ((Scheme.ΓSpecIso (CommRingCat.of C)).inv c)
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (A ⊗[K] B))).hom t, ?_⟩
    have hn := congrArg (fun k => k t)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom h.toRingHom))
    change (Scheme.ΓSpecIso (CommRingCat.of C)).hom
      ((Spec.map (CommRingCat.ofHom h.toRingHom)).appTop t) =
      h ((Scheme.ΓSpecIso (CommRingCat.of (A ⊗[K] B))).hom t) at hn
    rw [ht, Iso.inv_hom_id_apply] at hn
    exact hn.symm
  exact ⟨C, inferInstance, inferInstance, R, f, g, hsurj, hpb'⟩

variable [IsUltrametricDist K] [CompleteSpace K]

set_option backward.isDefEq.respectTransparency false in
/-- Under analytic pullback point lifting, the image of an affine presheaf
pullback is exactly the relation of having equal image in an analytification. -/
theorem IsAnalytification.affine_point_relation_eq_range
    (hlift : ∀ {T A B Z : SaturatedAtlasPresentation.LocalizedCategory.{u, u, u} (K := K)}
      (a : T ⟶ A) (b : T ⟶ B) (f : A ⟶ Z) (g : B ⟶ Z),
      IsPullback a b f g →
      ∀ (x : SaturatedAtlasPresentation.localizedSpaceFunctor.obj A)
        (y : SaturatedAtlasPresentation.localizedSpaceFunctor.obj B),
        SaturatedAtlasPresentation.localizedSpaceFunctor.map f x =
          SaturatedAtlasPresentation.localizedSpaceFunctor.map g y →
        ∃ t : SaturatedAtlasPresentation.localizedSpaceFunctor.obj T,
          SaturatedAtlasPresentation.localizedSpaceFunctor.map a t = x ∧
            SaturatedAtlasPresentation.localizedSpaceFunctor.map b t = y)
    {Y : SaturatedAtlasPresentation.LocalizedCategory.{u, u, u} (K := K)}
    {p : PointFamily K X Y} (hp : IsAnalytification K X Y p)
    {A B C : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    [CommRing C] [Algebra K C] (P : FinitePolynomialPresentation K A)
    (Q : FinitePolynomialPresentation K B) (R : FinitePolynomialPresentation K C)
    (f : A →ₐ[K] C) (g : B →ₐ[K] C) (x : RingPoints K X A) (y : RingPoints K X B)
    (hpb : IsPullback ((schemeYoneda _).map (ringTestMap K f))
      ((schemeYoneda _).map (ringTestMap K g)) (pointHom K x) (pointHom K y)) :
    {w : AffineAnalytification.Space K P × AffineAnalytification.Space K Q |
      SaturatedAtlasPresentation.localizedSpaceFunctor.map (p A P x) w.1 =
        SaturatedAtlasPresentation.localizedSpaceFunctor.map (p B Q y) w.2} =
      Set.range (fun z : AffineAnalytification.Space K R =>
        (AffineAnalytification.baseMap K P R f z, AffineAnalytification.baseMap K Q R g z)) := by
  have hAn := hp.isPullback P Q R f g x y hpb
  ext w
  constructor
  · intro hw
    obtain ⟨z, hz₁, hz₂⟩ := hlift _ _ _ _ hAn w.1 w.2 hw
    refine ⟨z, Prod.ext ?_ ?_⟩
    · rw [AffineAnalytification.localizedSpaceFunctor_map_localizedHom] at hz₁
      exact hz₁
    · rw [AffineAnalytification.localizedSpaceFunctor_map_localizedHom] at hz₂
      exact hz₂
  · rintro ⟨z, rfl⟩
    have hw := congrArg (fun k : AffineAnalytification.localized K R ⟶ Y =>
      SaturatedAtlasPresentation.localizedSpaceFunctor.map k z) hAn.w
    simp only [Functor.map_comp, TopCat.comp_app,
      AffineAnalytification.localizedSpaceFunctor_map_localizedHom] at hw
    exact hw

end Langlands.Analytic.SpaceAnalytification
