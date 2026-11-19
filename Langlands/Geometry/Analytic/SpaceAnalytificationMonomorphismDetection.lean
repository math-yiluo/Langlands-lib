import Langlands.Geometry.Analytic.AffineAnalytificationFaithfulness
import Langlands.Geometry.Analytic.SpaceAnalytificationMonomorphismReflection
import Langlands.AlgebraicGeometry.AlgebraicSpace.ThickeningAssembly
import Langlands.AlgebraicGeometry.AlgebraicSpace.KernelPairDiagonal

/-! # Analytification detects monomorphisms of separated algebraic spaces -/

noncomputable section

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem mono_of_locallySurjective_family
    {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X)
    {I : Type u} {U : I → Over S} (a : ∀ i, (schemeYoneda S).obj (U i) ⟶ X'.presheaf)
    (ha : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) (Sigma.desc a))
    (h : ∀ i j {W : Over S} (r : W ⟶ U i) (s : W ⟶ U j),
      (schemeYoneda S).map r ≫ a i ≫ hom f = (schemeYoneda S).map s ≫ a j ≫ hom f →
      (schemeYoneda S).map r ≫ a i = (schemeYoneda S).map s ≫ a j) :
    Mono (hom f) := by
  let F := ∐ fun i => (schemeYoneda S).obj (U i)
  let π : F ⟶ X'.presheaf := Sigma.desc a
  let fS : X'.toSheaf ⟶ X.toSheaf := ObjectProperty.homMk (hom f)
  have hLift {W : Over S} (x : F.obj (op W)) :
      ∃ (i : I) (r : W ⟶ U i), π.app (op W) x = (a i).app (op W) (ULift.up r) := by
    obtain ⟨⟨i⟩, ⟨r⟩, rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves ((evaluation _ _).obj (op W))
        (coproductIsCoproduct (fun i ↦ (schemeYoneda S).obj (U i)))) x
    exact ⟨i, r, congrArg (fun k => k.app (op W) (ULift.up r)) (Sigma.ι_comp_desc a i)⟩
  have hl : Sheaf.IsLocallyInjective fS := by
    refine ⟨fun {T} x y hxy => ?_⟩
    apply (fppfTopology S).superset_covering _
      ((fppfTopology S).intersection_covering (ha.imageSieve_mem x) (ha.imageSieve_mem y))
    rintro W k ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩
    obtain ⟨i, r, hr⟩ := hLift x'
    obtain ⟨j, s, hs⟩ := hLift y'
    have hxy' : (a i ≫ hom f).app (op W) (ULift.up r) =
        (a j ≫ hom f).app (op W) (ULift.up s) := by
      change (hom f).app _ ((a i).app _ (ULift.up r)) =
        (hom f).app _ ((a j).app _ (ULift.up s))
      rw [← hr, ← hs, hx', hy', NatTrans.naturality_apply, NatTrans.naturality_apply]
      exact congrArg (X.presheaf.map k.op) hxy
    have hcomp := h i j r s (KernelPair.map_comp_eq_map_comp_of_app_eq _ _ hxy')
    change X'.presheaf.map k.op x = X'.presheaf.map k.op y
    rw [← hx', ← hy', hr, hs]
    exact congrArg uliftYonedaEquiv hcomp
  rw [NatTrans.mono_iff_mono_app]
  intro W
  exact (CategoryTheory.mono_iff_injective _).mpr
    ((Sheaf.isLocallyInjective_iff_injective fS).mp hl W)

end Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X' X : AlgebraicSpace (Spec (CommRingCat.of K))} (f : X' ⟶ X)
  {Y' Y : LocalizedCategory.{u, u, u} (K := K)} {p' : PointFamily K X' Y'}
  {p : PointFamily K X Y} (hp' : IsAnalytification K X' Y' p')
  (hp : IsAnalytification K X Y p) {F : Y' ⟶ Y}
  (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
    (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
      p' A P x ≫ F = p A P (RingPoints.map f x))

section Overlaps

variable {A B C D : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [CommRing C] [Algebra K C] [CommRing D] [Algebra K D]
  {x : RingPoints K X' A} {y : RingPoints K X' B}
  {a : A →ₐ[K] C} {b : B →ₐ[K] C} {c : A →ₐ[K] D} {d : B →ₐ[K] D}

variable (hC : IsPullback ((schemeYoneda _).map (ringTestMap K a))
    ((schemeYoneda _).map (ringTestMap K b)) (pointHom K x) (pointHom K y))
  (hD : IsPullback ((schemeYoneda _).map (ringTestMap K c))
    ((schemeYoneda _).map (ringTestMap K d))
    (pointHom K (RingPoints.map f x)) (pointHom K (RingPoints.map f y)))
  (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
  (R : FinitePolynomialPresentation K C) (S : FinitePolynomialPresentation K D)

/-- Under an analytic monomorphism, the comparison between the two
closed affine overlaps is an algebra equivalence. -/
def affineOverlapAlgEquivOfMono [Mono F]
    (hsurj : Function.Surjective (Algebra.TensorProduct.productMap a b)) :
    D ≃ₐ[K] C := by
  have : IsIso (AffineAnalytification.localizedHom K S R (affineOverlapComparison f hC hD)) :=
    isIso_localizedHom_affineOverlapComparison f hC hD hp' hp hF P Q R S
  exact AlgEquiv.ofBijective (affineOverlapComparison f hC hD)
    ⟨AffineAnalytification.injective_of_epi_localizedHom K S R _,
      affineOverlapComparison_surjective f hC hD hsurj⟩

end Overlaps

include hp' hp hF in
set_option backward.isDefEq.respectTransparency false in
private theorem cancel_on_presented_affine_points [Mono F] (hX' : IsSeparated X')
    (hX : IsSeparated X) {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (x : RingPoints K X' A) (y : RingPoints K X' B)
    {W : Over (Spec (CommRingCat.of K))} (r : W ⟶ ringTest K A) (s : W ⟶ ringTest K B)
    (h : (schemeYoneda _).map r ≫ pointHom K x ≫ hom f =
      (schemeYoneda _).map s ≫ pointHom K y ≫ hom f) :
    (schemeYoneda _).map r ≫ pointHom K x = (schemeYoneda _).map s ≫ pointHom K y := by
  obtain ⟨C, _, _, R, a, b, hs, hC⟩ :=
    hasClosedAffinePointPullbacks_of_isSeparated hX' A P B Q x y
  obtain ⟨D, _, _, S, c, d, _, hD⟩ :=
    hasClosedAffinePointPullbacks_of_isSeparated hX A P B Q
      (RingPoints.map f x) (RingPoints.map f y)
  let e := affineOverlapAlgEquivOfMono f hp' hp hF hC hD P Q R S hs
  have hinv : e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id K C := by
    ext z
    exact e.apply_symm_apply z
  let i : ringTest K C ≅ ringTest K D :=
    ⟨ringTestMap K e.toAlgHom, ringTestMap K e.symm.toAlgHom,
      by rw [← ringTestMap_comp, hinv, ringTestMap_id],
      by rw [← ringTestMap_comp, e.symm_comp, ringTestMap_id]⟩
  have hpull : IsPullback ((schemeYoneda _).map (ringTestMap K a))
      ((schemeYoneda _).map (ringTestMap K b))
      (pointHom K (RingPoints.map f x)) (pointHom K (RingPoints.map f y)) := by
    apply hD.of_iso' ((schemeYoneda _).mapIso i) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · rw [Functor.mapIso_hom, ← Functor.map_comp, ← ringTestMap_comp, Iso.refl_hom,
        Category.comp_id]
      exact congrArg (fun k => (schemeYoneda _).map (ringTestMap K k))
        (affineOverlapComparison_comp_left f hC hD)
    · rw [Functor.mapIso_hom, ← Functor.map_comp, ← ringTestMap_comp, Iso.refl_hom,
        Category.comp_id]
      exact congrArg (fun k => (schemeYoneda _).map (ringTestMap K k))
        (affineOverlapComparison_comp_right f hC hD)
    · simp
    · simp
  let t := hpull.lift ((schemeYoneda _).map r) ((schemeYoneda _).map s)
    (by simpa only [pointHom_map] using h)
  have ht₁ : t ≫ (schemeYoneda _).map (ringTestMap K a) = (schemeYoneda _).map r :=
    hpull.lift_fst _ _ _
  have ht₂ : t ≫ (schemeYoneda _).map (ringTestMap K b) = (schemeYoneda _).map s :=
    hpull.lift_snd _ _ _
  simpa only [← Category.assoc, ht₁, ht₂] using
    congrArg (t ≫ ·) hC.w

include hp' hp hF in
set_option backward.isDefEq.respectTransparency false in
/-- A compatible analytic monomorphism of supplied analytifications of
separated algebraic spaces reflects to a monomorphism of presheaves. The
source algebraic space is required to be locally of finite type. -/
theorem mono_of_mono_analytification_of_isSeparated [Mono F] (hX' : IsSeparated X')
    (hX : IsSeparated X) (hLFT : LocallyOfFiniteTypeOverBase X') :
    Mono (hom f) := by
  obtain ⟨U, a, ha, hs, hU⟩ := hLFT.exists_atlas
  let base := Spec (CommRingCat.of K)
  let : LocallyOfFiniteType U.hom := hU
  let V := ThickeningAssembly.affineCharts U
  let j := ThickeningAssembly.affineChartMap U
  let b (i : U.left.affineCover.I₀) := (schemeYoneda base).map (j i) ≫ a
  let : ∀ i, LocallyOfFiniteType (V i).hom := fun i => by
    rw [← Over.w (j i)]
    exact inferInstanceAs (LocallyOfFiniteType (U.left.affineCover.f i ≫ U.hom))
  let R (i : U.left.affineCover.I₀) := AffineCoordinateRing K (V i)
  let e (i : U.left.affineCover.I₀) := affineSchemeOverIso K (V i)
  let z (i : U.left.affineCover.I₀) : RingPoints K X' (R i) :=
    uliftYonedaEquiv.{u + 1} ((schemeYoneda base).map (e i).inv ≫ b i)
  have hz (i : U.left.affineCover.I₀) :
      pointHom K (z i) = (schemeYoneda base).map (e i).inv ≫ b i :=
    Equiv.symm_apply_apply _ _
  let := isLocallySurjective_of_isEtale_isSurjective a ha hs
  let := ThickeningAssembly.affineChartMap_cover U
  let : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology base) (Sigma.desc b) := by
    have hb : Sigma.desc b = Sigma.desc (fun i => (schemeYoneda base).map (j i)) ≫ a := by
      apply Sigma.hom_ext
      intro i
      simp [b]
    rw [hb]
    infer_instance
  refine mono_of_locallySurjective_family f (fun i => pointHom K (z i)) ?_ ?_
  · simp only [hz]
    exact ThickeningAssembly.coproduct_cover_of_isos b
      (fun i => (schemeYoneda base).mapIso (e i).symm)
  · intro i k W r s hrs
    exact cancel_on_presented_affine_points f hp' hp hF hX' hX
      (FinitePolynomialPresentation.ofFiniteType K (R i))
      (FinitePolynomialPresentation.ofFiniteType K (R k)) (z i) (z k) r s hrs

end Langlands.Analytic.SpaceAnalytification
