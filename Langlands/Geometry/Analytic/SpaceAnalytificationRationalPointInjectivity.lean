import Langlands.Geometry.Analytic.SpaceAnalytification
import Langlands.Geometry.Analytic.AffineSchemeAnalytification
import Langlands.Geometry.Analytic.AffineAnalytificationSeminorm
import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineIntersections
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartOpenMap

/-! # Algebraic pullbacks for rational-point injectivity -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology
  (ringTest ringTestMap ringTestMap_comp ringTestMap_id)

variable {K : Type u} [NontriviallyNormedField K]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))}

set_option backward.isDefEq.respectTransparency false in
/-- The pullback of two ground-field points of a separated algebraic space is
an affine closed subscheme of the ground-field spectrum. -/
theorem exists_closed_affine_rationalPoint_pullback (hX : IsSeparated X)
    (x y : RingPoints K X K) :
    ∃ (W : Over (Spec (CommRingCat.of K)))
      (a b : W ⟶ ringTest K K), IsAffine W.left ∧
      _root_.AlgebraicGeometry.IsClosedImmersion W.hom ∧
      IsPullback ((schemeYoneda _).map a) ((schemeYoneda _).map b)
        (pointHom K x) (pointHom K y) := by
  let U := ringTest K K
  let W := pairPullback (pointHom K x) (pointHom K y)
  let a := pairPullbackFst (pointHom K x) (pointHom K y)
  let b := pairPullbackSnd (pointHom K x) (pointHom K y)
  have hpb := pairPullback_isPullback (pointHom K x) (pointHom K y)
  have hclosed := closedImmersion_pair_of_isPullback hX
    (pointHom K x) (pointHom K y) a b hpb
  have hU : U.hom = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _
    rw [Algebra.algebraMap_self]
    change Spec.map (𝟙 (CommRingCat.of K)) = 𝟙 _
    exact Spec.map_id _
  have : IsIso U.hom := by
    rw [hU]
    change IsIso (𝟙 (Spec (CommRingCat.of K)))
    infer_instance
  have : IsIso (prod.fst : U ⨯ U ⟶ U).left := by
    rw [← Over.prodLeftIsoPullback_hom_fst U U]
    infer_instance
  have hw : W.hom = (prod.lift a b).left ≫ (prod.fst : U ⨯ U ⟶ U).left ≫ U.hom := by
    rw [← Category.assoc, ← Over.comp_left, prod.lift_fst]
    exact (Over.w a).symm
  have : _root_.AlgebraicGeometry.IsClosedImmersion W.hom := by
    rw [hw]
    infer_instance
  exact ⟨W, a, b, isAffine_of_isAffineHom W.hom, inferInstance, hpb⟩

/-- Every pair of rational points admits an affine pullback whose coordinate
algebra is a quotient of the ground field. -/
def HasScalarQuotientRationalPointPullbacks : Prop :=
  ∀ x y : RingPoints K X K,
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra K C)
      (_R : FinitePolynomialPresentation K C),
      Function.Surjective (algebraMap K C) ∧
        IsPullback ((schemeYoneda _).map (ringTestMap K (Algebra.ofId K C)))
          ((schemeYoneda _).map (ringTestMap K (Algebra.ofId K C)))
          (pointHom K x) (pointHom K y)

set_option backward.isDefEq.respectTransparency false in
/-- Closedness of the diagonal supplies the scalar-quotient pullbacks. -/
theorem hasScalarQuotientRationalPointPullbacks_of_isSeparated (hX : IsSeparated X) :
    HasScalarQuotientRationalPointPullbacks (K := K) (X := X) := by
  intro x y
  obtain ⟨W, a, b, hWa, hWc, hpb⟩ := exists_closed_affine_rationalPoint_pullback hX x y
  let := hWa
  let := hWc
  let C := AffineSchemeAnalytification.CoordinateRing W.hom
  let R := AffineSchemeAnalytification.presentation W.hom
  let e : W ≅ ringTest K C := Over.isoMk
    (AffineSchemeAnalytification.coordinateIso W.hom)
    (AffineSchemeAnalytification.coordinateIso_hom_over W.hom)
  have hsurj : Function.Surjective (algebraMap K C) := by
    intro c
    obtain ⟨k, hk⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine W.hom).2 c
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom k, ?_⟩
    change W.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv
      ((Scheme.ΓSpecIso (CommRingCat.of K)).hom k)) = c
    simpa only [Iso.hom_inv_id_apply] using hk
  have hU : (ringTest K K).hom = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _
    rw [Algebra.algebraMap_self]
    change Spec.map (𝟙 (CommRingCat.of K)) = 𝟙 _
    exact Spec.map_id _
  have hterminal (d : ringTest K C ⟶ ringTest K K) :
      d = ringTestMap K (Algebra.ofId K C) := by
    apply Over.OverMorphism.ext
    have hd := Over.w d
    have hf := Over.w (ringTestMap K (Algebra.ofId K C))
    rw [hU, Category.comp_id] at hd hf
    exact hd.trans hf.symm
  have hpb' : IsPullback ((schemeYoneda _).map (e.inv ≫ a))
      ((schemeYoneda _).map (e.inv ≫ b)) (pointHom K x) (pointHom K y) :=
    hpb.of_iso ((schemeYoneda _).mapIso e) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  rw [hterminal (e.inv ≫ a), hterminal (e.inv ≫ b)] at hpb'
  exact ⟨C, inferInstance, inferInstance, R, hsurj, hpb'⟩

variable [IsUltrametricDist K] [CompleteSpace K]

set_option backward.isDefEq.respectTransparency false in
/-- Point lifting for analytic categorical pullbacks implies injectivity of the
rational-point map for every analytification of a separated algebraic space. -/
theorem rationalPoint_injective_of_pointLifting
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
    (hX : IsSeparated X)
    {Y : SaturatedAtlasPresentation.LocalizedCategory.{u, u, u} (K := K)}
    {p : PointFamily K X Y} (hp : IsAnalytification K X Y p)
    (P₀ : FinitePolynomialPresentation K K) :
    Function.Injective (rationalPoint p P₀) := by
  intro x y hxy
  obtain ⟨C, _, _, R, hsurj, hpb⟩ :=
    hasScalarQuotientRationalPointPullbacks_of_isSeparated hX x y
  let f := Algebra.ofId K C
  have hpa := hp.isPullback P₀ P₀ R f f x y hpb
  let a₀ := AffineAnalytification.analyticPoint K P₀
    (Langlands.AlgebraicGeometry.PointTopology.AlgPoint.ofAlgHom (AlgHom.id K K))
  obtain ⟨z, -, -⟩ := hlift _ _ _ _ hpa a₀ a₀ hxy
  let ν := AffineAnalytification.pointSeminorm K R z
  have h01 : (0 : C) ≠ 1 := by
    intro he
    have hn : (0 : ℝ) = 1 := by
      simpa only [map_zero, map_one] using congrArg ν he
    exact zero_ne_one hn
  let : Nontrivial C := ⟨⟨0, 1, h01⟩⟩
  let e : K ≃ₐ[K] C := AlgEquiv.ofBijective f ⟨RingHom.injective f.toRingHom, hsurj⟩
  let s := ringTestMap K e.symm.toAlgHom
  have hs : s ≫ ringTestMap K f = 𝟙 (ringTest K K) := by
    rw [← ringTestMap_comp]
    have he : e.symm.toAlgHom.comp f = AlgHom.id K K := by
      change e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id K K
      exact e.symm_comp
    rw [he, ringTestMap_id]
  dsimp only [f] at hs
  have h : pointHom K x = pointHom K y := by
    have hw := congrArg (fun k => (schemeYoneda _).map s ≫ k) hpb.w
    simp only [← Category.assoc, ← Functor.map_comp, hs] at hw
    simpa using hw
  exact uliftYonedaEquiv.symm.injective h

end Langlands.Analytic.SpaceAnalytification
