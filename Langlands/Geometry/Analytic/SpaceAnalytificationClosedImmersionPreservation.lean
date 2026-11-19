import Langlands.Geometry.Analytic.AnalyticClosedImmersionMonomorphism
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedFunctorialityProof
import Langlands.Geometry.Analytic.SpaceAnalytificationAffinePullback
import Langlands.Geometry.Analytic.SpaceAnalytificationEtaleReduction
import Langlands.Geometry.Analytic.EtaleGeometricPointPullbacks
import Langlands.Geometry.Analytic.LocalizedPullbackPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProductPointsLocalLift
import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestrictionRepresentability

/-! # Preservation of closed immersions by analytification -/

noncomputable section

universe u w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {Q X Y Z : LocalizedCategory.{u, u, u} (K := K)}
  {p : Q ⟶ X} {q : Q ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

set_option backward.isDefEq.respectTransparency false in
/-- Construct the limiting cone when its second leg is monic and its
pullback property is available on an étale cover of `X`. -/
def monicPullbackLimitOfEtaleSourceCover
    (hBase : LocalizedEtalePullbackStatement.{u, u} K)
    (hHom : ∀ (S T : LocalizedCategory.{u, u, u} (K := K)),
      Presieve.IsSheaf (etaleTopology S)
        ((MorphismProperty.Over.forget _ _ S ⋙ Over.forget S).op ⋙ yoneda.obj T))
    [Mono q] (hw : p ≫ f = q ≫ g)
    {ι : Type w} {U : ι → LocalizedCategory.{u, u, u} (K := K)}
    (a : ∀ i, U i ⟶ X) (ha : ∀ i, etale (a i))
    (hcover : ∀ x : localizedSpaceFunctor.obj X,
      ∃ (i : ι) (z : localizedSpaceFunctor.obj (U i)), localizedSpaceFunctor.map (a i) z = x)
    (hlocal : ∀ i, ∃ (V : LocalizedCategory.{u, u, u} (K := K))
      (r : V ⟶ U i) (s : V ⟶ Q),
      r ≫ a i = s ≫ p ∧ IsPullback r (s ≫ q) (a i ≫ f) g) :
    IsLimit (PullbackCone.mk p q hw) := by
  classical
  choose V r s hfac houter using hlocal
  have hLift (c : PullbackCone f g) : ∃ l : c.pt ⟶ Q, l ≫ p = c.fst ∧ l ≫ q = c.snd := by
    choose W b d hpb hd using fun i => hBase (a i) c.fst (ha i)
    have hcompat (i : ι) : b i ≫ a i ≫ f = (d i ≫ c.snd) ≫ g := by
      rw [← Category.assoc, (hpb i).w, Category.assoc, c.condition, ← Category.assoc]
    let l (i : ι) := (houter i).lift (b i) (d i ≫ c.snd) (hcompat i)
    let k (i : ι) := l i ≫ s i
    have hkp (i : ι) : k i ≫ p = d i ≫ c.fst := by
      dsimp only [k, l]
      rw [Category.assoc, ← hfac i, ← Category.assoc, (houter i).lift_fst, (hpb i).w]
    have hkq (i : ι) : k i ≫ q = d i ≫ c.snd := by
      dsimp only [k, l]
      rw [Category.assoc, (houter i).lift_snd]
    have hdcover (x : localizedSpaceFunctor.obj c.pt) :
        ∃ (i : ι) (z : localizedSpaceFunctor.obj (W i)),
          localizedSpaceFunctor.map (d i) z = x := by
      obtain ⟨i, y, hy⟩ := hcover (localizedSpaceFunctor.map c.fst x)
      obtain ⟨z, -, hz⟩ := exists_point_of_isPullback _ _ _ _ (hpb i) y x hy
      exact ⟨i, z, hz⟩
    let E : EtaleSite c.pt := MorphismProperty.Over.mk ⊤ (𝟙 _) (etale_of_isIso _)
    let B (i : ι) : EtaleSite c.pt := MorphismProperty.Over.mk ⊤ (d i) (hd i)
    let π (i : ι) : B i ⟶ E := MorphismProperty.Over.homMk (d i) (Category.comp_id _)
    have hπ : Presieve.ofArrows B π ∈ etalePrecoverage c.pt E :=
      ofArrows_mem_etalePrecoverage_iff.mpr hdcover
    let H (R : LocalizedCategory.{u, u, u} (K := K)) :=
      (MorphismProperty.Over.forget etale ⊤ c.pt ⋙ Over.forget c.pt).op ⋙ yoneda.obj R
    have hc : Presieve.Arrows.Compatible (H Q) π k := by
      intro i j T m n h
      change m.left ≫ k i = n.left ≫ k j
      apply (cancel_mono q).mp
      have he : m.left ≫ d i = n.left ≫ d j := congrArg (fun z => z.left) h
      simpa only [Category.assoc, hkq] using congrArg (· ≫ c.snd) he
    obtain ⟨m, hm, -⟩ := (Presieve.isSheafFor_arrows_iff (π := π) (P := H Q)).mp
      ((hHom c.pt Q).isSheafFor_of_mem_precoverage hπ) k hc
    have hm' (i : ι) : d i ≫ m = k i := hm i
    have hEq {R : LocalizedCategory.{u, u, u} (K := K)} {m n : c.pt ⟶ R}
        (h : ∀ i, d i ≫ m = d i ≫ n) : m = n := by
      apply ((hHom c.pt R).isSheafFor_of_mem_precoverage hπ).isSeparatedFor.ext
      rintro _ _ ⟨i⟩
      exact h i
    exact ⟨m,
      hEq fun i => (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ p) (hm' i)).trans (hkp i)),
      hEq fun i => (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ q) (hm' i)).trans (hkq i))⟩
  exact PullbackCone.IsLimit.mk hw (fun c => (hLift c).choose)
    (fun c => (hLift c).choose_spec.1) (fun c => (hLift c).choose_spec.2)
    (fun c m _ hm => (cancel_mono q).mp (hm.trans (hLift c).choose_spec.2.symm))

end Langlands.Analytic.SaturatedAtlasPresentation

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory _root_.CategoryTheory.Limits SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [NontriviallyNormedField K]
  {X' X : AlgebraicSpace (Spec (CommRingCat.of K))} {f : X' ⟶ X}

set_option backward.isDefEq.respectTransparency false in
/-- Pulling a representable closed immersion back to an affine test gives
the spectrum of an actual quotient of the test algebra. -/
theorem exists_affine_quotient_pullback_of_isClosedImmersion
    (hf : AlgebraicSpace.IsClosedImmersion (hom f))
    {A : Type u} [CommRing A] [Algebra K A] (x : RingPoints K X A) :
    ∃ (I : Ideal A) (z : RingPoints K X' (A ⧸ I)),
      IsPullback (pointHom K z) ((schemeYoneda _).map (ringTestMap K (Ideal.Quotient.mkₐ K I)))
        (hom f) (pointHom K x) := by
  let g := pointHom K x
  let V := hf.representable.pullback g
  let a := hf.representable.fst g
  let b := hf.representable.snd g
  have hpb : IsPullback a ((schemeYoneda _).map b) (hom f) g := hf.representable.isPullback g
  have hb : _root_.AlgebraicGeometry.IsClosedImmersion b.left := hf.projection g a b hpb
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.mp hb
  let h := Ideal.Quotient.mkₐ K I
  have he' : b.left = e.hom ≫ (ringTestMap K h).left := he
  let eV : V ≅ ringTest K (A ⧸ I) := Over.isoMk e (by
    change e.hom ≫ (ringTest K (A ⧸ I)).hom = V.hom
    rw [← Over.w (ringTestMap K h), ← Category.assoc, ← he', Over.w b])
  let z : RingPoints K X' (A ⧸ I) := uliftYonedaEquiv.{u + 1}
    ((schemeYoneda _).map eV.inv ≫ a)
  have hbe : eV.inv ≫ b = ringTestMap K h := by
    have h₁ : eV.hom ≫ ringTestMap K h = b := Over.OverMorphism.ext he'.symm
    rw [← h₁, Iso.inv_hom_id_assoc]
  refine ⟨I, z, ?_⟩
  apply hpb.of_iso' ((schemeYoneda _).mapIso eV.symm) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Functor.mapIso_hom, Iso.symm_hom, Iso.refl_hom, Category.comp_id, pointHom,
      z, Equiv.symm_apply_apply]
  · simp only [Functor.mapIso_hom, Iso.symm_hom, Iso.refl_hom, Category.comp_id,
      ← Functor.map_comp, hbe, h]
  · simp
  · simp [g]

variable [IsUltrametricDist K] [CompleteSpace K]
  {Y' Y : LocalizedCategory.{u, u, u} (K := K)} {p' : PointFamily K X' Y'}
  {p : PointFamily K X Y} (hp' : IsAnalytification K X' Y' p')
  (hp : IsAnalytification K X Y p) (F : Y' ⟶ Y)
  (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
    (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
      p' A P x ≫ F = p A P (RingPoints.map f x))
  (hBase : LocalizedEtalePullbackStatement.{u, u} K)
  (hHom : ∀ (S T : LocalizedCategory.{u, u, u} (K := K)),
    Presieve.IsSheaf (etaleTopology S)
      ((MorphismProperty.Over.forget _ _ S ⋙ Over.forget S).op ⋙ yoneda.obj T))

include hp' hp hF hBase hHom in
set_option backward.isDefEq.respectTransparency false in
/-- A represented affine pullback analytifies to a pullback if the
analytified projection to the affine base is monic and Hom descent holds. -/
theorem isPullback_of_affine_represented_of_mono
    (hX : IsSeparated X)
    {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (x : RingPoints K X A) (z : RingPoints K X' B) (g : A →ₐ[K] B)
    (hAlg : IsPullback (pointHom K z) ((schemeYoneda _).map (ringTestMap K g))
      (hom f) (pointHom K x))
    [Mono (AffineAnalytification.localizedHom K P Q g)] :
    IsPullback (p' B Q z) (AffineAnalytification.localizedHom K P Q g) F (p A P x) := by
  have hw : p' B Q z ≫ F = AffineAnalytification.localizedHom K P Q g ≫ p A P x := by
    have he : RingPoints.map f z = RingPoints.changeRing g x := by
      apply uliftYonedaEquiv.{u + 1}.symm.injective
      exact (pointHom_map K f z).trans
        (hAlg.w.trans (ProductPointsLocalLift.uliftYonedaEquiv_symm_changeRing g x).symm)
    rw [hF B Q z, he, hp.naturality P Q g x]
  let U (i : EtaleAffineTest K X') := AffineAnalytification.localized K i.presentation
  let a (i : EtaleAffineTest K X') : U i ⟶ Y' := p' i.algebra i.presentation i.point
  have ha (i : EtaleAffineTest K X') : etale (a i) :=
    hp'.etale_map i.presentation i.point i.etale_point
  have hcover (y : localizedSpaceFunctor.obj Y') :
      ∃ (i : EtaleAffineTest K X') (v : localizedSpaceFunctor.obj (U i)),
        localizedSpaceFunctor.map (a i) v = y := by
    obtain ⟨C, _, _, R, t, ht, hv⟩ := hp'.jointly_surjective y
    exact ⟨⟨CommAlgCat.of K C, R, t, ht⟩, hv⟩
  refine IsPullback.of_isLimit
    (monicPullbackLimitOfEtaleSourceCover hBase hHom hw a ha hcover ?_)
  intro i
  obtain ⟨C, _, _, R, b, c, -, hC⟩ :=
    hasClosedAffinePointPullbacks_of_isSeparated hX i.algebra i.presentation A P
      (RingPoints.map f i.point) x
  have hcone : ((schemeYoneda _).map (ringTestMap K b) ≫ pointHom K i.point) ≫ hom f =
      (schemeYoneda _).map (ringTestMap K c) ≫ pointHom K x := by
    simpa only [Category.assoc, ← pointHom_map] using hC.w
  let t := hAlg.lift ((schemeYoneda _).map (ringTestMap K b) ≫ pointHom K i.point)
    ((schemeYoneda _).map (ringTestMap K c)) hcone
  let t' : RingPoint K (ringTest K B) C := (schemeYoneda _).preimage t
  let d := affineRingPointEquiv K B C t'
  have hd : (schemeYoneda _).map (ringTestMap K d) = t :=
    (congrArg ((schemeYoneda _).map) (ringTestMap_affineRingPointEquiv K t')).trans
      (Functor.map_preimage _ _)
  have hdg : (schemeYoneda _).map (ringTestMap K (d.comp g)) =
      (schemeYoneda _).map (ringTestMap K c) := by
    rw [ringTestMap_comp, Functor.map_comp, hd]
    exact hAlg.lift_snd _ _ _
  have hpoint : RingPoints.changeRing b i.point = RingPoints.changeRing d z := by
    apply uliftYonedaEquiv.{u + 1}.symm.injective
    rw [ProductPointsLocalLift.uliftYonedaEquiv_symm_changeRing,
      ProductPointsLocalLift.uliftYonedaEquiv_symm_changeRing, hd]
    exact (hAlg.lift_fst _ _ _).symm
  have hC' : IsPullback ((schemeYoneda _).map (ringTestMap K b))
      ((schemeYoneda _).map (ringTestMap K (d.comp g)))
      (pointHom K (RingPoints.map f i.point)) (pointHom K x) :=
    hdg.symm ▸ hC
  have hAn := hp.isPullback i.presentation P R b (d.comp g) (RingPoints.map f i.point) x hC'
  have hcomp := (AffineAnalytification.affineAnalytificationLocalizedFunctoriality
    K A B C P P Q R g d).2.2.2.1
  rw [← hF i.algebra i.presentation i.point, hcomp] at hAn
  refine ⟨AffineAnalytification.localized K R, AffineAnalytification.localizedHom K i.presentation R b,
    AffineAnalytification.localizedHom K Q R d, ?_, hAn⟩
  change AffineAnalytification.localizedHom K i.presentation R b ≫
      p' i.algebra i.presentation i.point =
    AffineAnalytification.localizedHom K Q R d ≫ p' B Q z
  rw [← hp'.naturality i.presentation R b i.point, ← hp'.naturality Q R d z, hpoint]

include hp' hp hF hBase hHom in
/-- Preservation of closed immersions follows from the affine closed
comparison and analytic étale target descent, together with Hom descent. -/
theorem closedImmersion_of_isClosedImmersion_of_descent
    (hAffine : ∀ (A B : Type u) [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
      (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
      (g : A →ₐ[K] B), Function.Surjective g →
        closedImmersion (AffineAnalytification.localizedHom K P Q g))
    (hDescent : ∀ {ι : Type (u + 1)} {A B : LocalizedCategory.{u, u, u} (K := K)}
      (h : A ⟶ B) {U : ι → LocalizedCategory.{u, u, u} (K := K)}
      (a : ∀ i, U i ⟶ B), (∀ i, etale (a i)) →
      (∀ b : localizedSpaceFunctor.obj B, ∃ (i : ι) (u : localizedSpaceFunctor.obj (U i)),
        localizedSpaceFunctor.map (a i) u = b) →
      ∀ {V : ι → LocalizedCategory.{u, u, u} (K := K)} (r : ∀ i, V i ⟶ A)
        (s : ∀ i, V i ⟶ U i), (∀ i, IsPullback (r i) (s i) h (a i)) →
        (∀ i, closedImmersion (s i)) → closedImmersion h)
    (hX : IsSeparated X) (hf : AlgebraicSpace.IsClosedImmersion (hom f)) :
    closedImmersion F := by
  classical
  let U (i : EtaleAffineTest K X) := AffineAnalytification.localized K i.presentation
  let a (i : EtaleAffineTest K X) : U i ⟶ Y := p i.algebra i.presentation i.point
  have ha (i : EtaleAffineTest K X) : etale (a i) :=
    hp.etale_map i.presentation i.point i.etale_point
  have hcover (y : localizedSpaceFunctor.obj Y) :
      ∃ (i : EtaleAffineTest K X) (v : localizedSpaceFunctor.obj (U i)),
        localizedSpaceFunctor.map (a i) v = y := by
    obtain ⟨A, _, _, P, x, hx, hv⟩ := hp.jointly_surjective y
    exact ⟨⟨CommAlgCat.of K A, P, x, hx⟩, hv⟩
  have hlocal (i : EtaleAffineTest K X) :
      ∃ (V : LocalizedCategory.{u, u, u} (K := K)) (r : V ⟶ Y') (s : V ⟶ U i),
        IsPullback r s F (a i) ∧ closedImmersion s := by
    obtain ⟨I, z, hI⟩ := exists_affine_quotient_pullback_of_isClosedImmersion hf i.point
    let φ := Ideal.Quotient.mkₐ K I
    let : Algebra.FiniteType K i.algebra :=
      Algebra.FiniteType.of_surjective i.presentation.map i.presentation.surjective
    let : Algebra.FiniteType K (i.algebra ⧸ I) :=
      Algebra.FiniteType.of_surjective φ (Ideal.Quotient.mkₐ_surjective K I)
    let Q := FinitePolynomialPresentation.ofFiniteType K (i.algebra ⧸ I)
    let s := AffineAnalytification.localizedHom K i.presentation Q φ
    have hs : closedImmersion s := hAffine _ _ i.presentation Q φ
      (Ideal.Quotient.mkₐ_surjective K I)
    let : Mono s := hs.mono
    exact ⟨_, p' _ Q z, s, isPullback_of_affine_represented_of_mono hp' hp F hF hBase hHom hX
      i.presentation Q i.point z φ hI, hs⟩
  choose V r s hpb hs using hlocal
  exact hDescent F a ha hcover r s hpb hs

end Langlands.Analytic.SpaceAnalytification
