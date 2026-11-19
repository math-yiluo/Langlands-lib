import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedFunctorialityProof
import Langlands.Geometry.Analytic.AffineAnalytificationMaximalCenters
import Langlands.Geometry.Analytic.SpaceAnalytificationAffinePullback
import Langlands.Geometry.Analytic.SpaceAnalytificationEtaleReflection
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleAffineTests
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtalePresentationComparison

/-! # Reflection of monomorphisms by affine overlaps -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology
open SaturatedAtlasPresentation

variable {K : Type u} [NontriviallyNormedField K]
  {X' X : AlgebraicSpace (Spec (CommRingCat.of K))} (f : X' ⟶ X)
  {A B C D : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [CommRing C] [Algebra K C] [CommRing D] [Algebra K D]
  {x : RingPoints K X' A} {y : RingPoints K X' B}
  {a : A →ₐ[K] C} {b : B →ₐ[K] C} {c : A →ₐ[K] D} {d : B →ₐ[K] D}

variable (hC : IsPullback ((schemeYoneda _).map (ringTestMap K a))
    ((schemeYoneda _).map (ringTestMap K b)) (pointHom K x) (pointHom K y))
  (hD : IsPullback ((schemeYoneda _).map (ringTestMap K c))
    ((schemeYoneda _).map (ringTestMap K d))
    (pointHom K (RingPoints.map f x)) (pointHom K (RingPoints.map f y)))

include hC in
private theorem comparison_comm :
    (schemeYoneda _).map (ringTestMap K a) ≫ pointHom K (RingPoints.map f x) =
      (schemeYoneda _).map (ringTestMap K b) ≫ pointHom K (RingPoints.map f y) := by
  simpa only [pointHom_map, ← Category.assoc] using congrArg (· ≫ hom f) hC.w

/-- The algebra map from the overlap over the target to the overlap over the source. -/
def affineOverlapComparison : D →ₐ[K] C :=
  affineRingPointEquiv K D C ((schemeYoneda _).preimage
    (hD.lift _ _ (comparison_comm f hC)))

private theorem ringTestMap_affineOverlapComparison :
    (schemeYoneda _).map (ringTestMap K (affineOverlapComparison f hC hD)) =
      hD.lift _ _ (comparison_comm f hC) := by
  let r : RingPoint K (ringTest K D) C := (schemeYoneda _).preimage
    (hD.lift _ _ (comparison_comm f hC))
  change (schemeYoneda _).map (ringTestMap K (affineRingPointEquiv K D C r)) = _
  exact (congrArg ((schemeYoneda _).map) (ringTestMap_affineRingPointEquiv K r)).trans
    (Functor.map_preimage _ _)

private theorem algHom_eq_of_schemeYoneda_ringTestMap_eq {U V : Type u}
    [CommRing U] [Algebra K U] [CommRing V] [Algebra K V] {r s : U →ₐ[K] V}
    (h : (schemeYoneda _).map (ringTestMap K r) =
      (schemeYoneda _).map (ringTestMap K s)) : r = s := by
  have he := (schemeYoneda _).map_injective h
  have hs := Spec.map_injective (congrArg Over.Hom.left he)
  ext t
  exact ConcreteCategory.congr_hom hs t

theorem affineOverlapComparison_comp_left : (affineOverlapComparison f hC hD).comp c = a := by
  apply algHom_eq_of_schemeYoneda_ringTestMap_eq
  rw [ringTestMap_comp, Functor.map_comp, ringTestMap_affineOverlapComparison]
  exact hD.lift_fst _ _ _

theorem affineOverlapComparison_comp_right : (affineOverlapComparison f hC hD).comp d = b := by
  apply algHom_eq_of_schemeYoneda_ringTestMap_eq
  rw [ringTestMap_comp, Functor.map_comp, ringTestMap_affineOverlapComparison]
  exact hD.lift_snd _ _ _

/-- If the source overlap is closed in the affine product, its comparison
algebra map is surjective. -/
theorem affineOverlapComparison_surjective
    (h : Function.Surjective (Algebra.TensorProduct.productMap a b)) :
    Function.Surjective (affineOverlapComparison f hC hD) := by
  have he : (affineOverlapComparison f hC hD).comp
      (Algebra.TensorProduct.productMap c d) = Algebra.TensorProduct.productMap a b := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.productMap_apply_tmul, map_mul]
    exact congrArg₂ (· * ·)
      (AlgHom.congr_fun (affineOverlapComparison_comp_left f hC hD) x)
      (AlgHom.congr_fun (affineOverlapComparison_comp_right f hC hD) y)
  intro z
  obtain ⟨t, rfl⟩ := h z
  exact ⟨Algebra.TensorProduct.productMap c d t, AlgHom.congr_fun he t⟩

variable [IsUltrametricDist K] [CompleteSpace K]
  {Y' Y : LocalizedCategory.{u, u, u} (K := K)} {p' : PointFamily K X' Y'}
  {p : PointFamily K X Y} (hp' : IsAnalytification K X' Y' p')
  (hp : IsAnalytification K X Y p) {F : Y' ⟶ Y}
  (hF : ∀ (U : Type u) [CommRing U] [Algebra K U]
    (P : FinitePolynomialPresentation K U) (z : RingPoints K X' U),
      p' U P z ≫ F = p U P (RingPoints.map f z))
  (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
  (R : FinitePolynomialPresentation K C) (S : FinitePolynomialPresentation K D)

include hp' hp hF P Q in
set_option backward.isDefEq.respectTransparency false in
/-- A monomorphism of analytifications makes the analytified affine overlap
comparison an isomorphism. -/
theorem isIso_localizedHom_affineOverlapComparison [Mono F] :
    IsIso (AffineAnalytification.localizedHom K S R (affineOverlapComparison f hC hD)) := by
  have hAnC := hp'.isPullback P Q R a b x y hC
  have hAnD := hp.isPullback P Q S c d (RingPoints.map f x) (RingPoints.map f y) hD
  rw [← hF A P x, ← hF B Q y] at hAnD
  have hAnC' : IsPullback
      (AffineAnalytification.localizedHom K P R a)
      (AffineAnalytification.localizedHom K Q R b) (p' A P x ≫ F) (p' B Q y ≫ F) := by
    refine IsPullback.mk' ?_ (fun {_ _ _} h₁ h₂ => hAnC.hom_ext h₁ h₂) ?_
    · rw [← Category.assoc, hAnC.w, Category.assoc]
    · intro T r s hrs
      have he : r ≫ p' A P x = s ≫ p' B Q y :=
        (cancel_mono F).mp (by simpa only [Category.assoc] using hrs)
      exact ⟨hAnC.lift r s he, hAnC.lift_fst _ _ _, hAnC.lift_snd _ _ _⟩
  let e := hAnC'.isoIsPullback _ _ hAnD
  let g := affineOverlapComparison f hC hD
  have he : AffineAnalytification.localizedHom K S R g = e.hom := by
    apply hAnD.hom_ext
    · rw [IsPullback.isoIsPullback_hom_fst, ←
        (AffineAnalytification.affineAnalytificationLocalizedFunctoriality
          K A D C P P S R c g).2.2.2.1, affineOverlapComparison_comp_left]
    · rw [IsPullback.isoIsPullback_hom_snd, ←
        (AffineAnalytification.affineAnalytificationLocalizedFunctoriality
          K B D C Q Q S R d g).2.2.2.1, affineOverlapComparison_comp_right]
  rw [he]
  infer_instance

variable (hAffineReflect : ∀ (U V : Type u) [CommRing U] [Algebra K U]
    [CommRing V] [Algebra K V]
    (P : FinitePolynomialPresentation K U) (Q : FinitePolynomialPresentation K V)
    (g : U →ₐ[K] V), etale (AffineAnalytification.localizedHom K P Q g) →
      g.toRingHom.Etale)

include hp' hp hF P Q R S hAffineReflect in
private theorem affineOverlapComparison_bijective_of_mono [Mono F]
    (h : Function.Surjective (Algebra.TensorProduct.productMap a b)) :
    Function.Bijective (affineOverlapComparison f hC hD) := by
  let g := affineOverlapComparison f hC hD
  let G := AffineAnalytification.localizedHom K S R g
  let : IsIso G := isIso_localizedHom_affineOverlapComparison f hC hD hp' hp hF P Q R S
  have hFlat : g.toRingHom.Flat :=
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp
      (hAffineReflect D C S R g (etale_of_isIso G))).1
  have hSurj : Function.Surjective (AffineAnalytification.baseMap K S R g) := by
    have hMap := (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso (asIso G))).surjective
    change Function.Surjective
      (localizedSpaceFunctor.map (AffineAnalytification.localizedHom K S R g)) at hMap
    rw [AffineAnalytification.localizedSpaceFunctor_map_localizedHom] at hMap
    exact hMap
  exact AffineAnalytification.bijective_of_surjective_of_flat_of_baseMap_surjective K S R g
    (affineOverlapComparison_surjective f hC hD h) hFlat hSurj

variable (hX' : IsSeparated X') (hX : IsSeparated X)

include hp' hp hF hAffineReflect hX' hX in
set_option backward.isDefEq.respectTransparency false in
private theorem cancel_on_finite_affine_tests [Mono F]
    (x : RingPoints K X' A) (y : RingPoints K X' B)
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    {T : Over (Spec (CommRingCat.of K))} (r : T ⟶ ringTest K A) (s : T ⟶ ringTest K B)
    (h : (schemeYoneda _).map r ≫ pointHom K (RingPoints.map f x) =
      (schemeYoneda _).map s ≫ pointHom K (RingPoints.map f y)) :
    (schemeYoneda _).map r ≫ pointHom K x = (schemeYoneda _).map s ≫ pointHom K y := by
  obtain ⟨C, _, _, R, a, b, hprod, hC⟩ :=
    hasClosedAffinePointPullbacks_of_isSeparated hX' A P B Q x y
  obtain ⟨D, _, _, S, c, d, _, hD⟩ :=
    hasClosedAffinePointPullbacks_of_isSeparated hX A P B Q
      (RingPoints.map f x) (RingPoints.map f y)
  let g := affineOverlapComparison f hC hD
  have hg : Function.Bijective g :=
    affineOverlapComparison_bijective_of_mono f hC hD hp' hp hF P Q R S hAffineReflect hprod
  let e := AlgEquiv.ofBijective g hg
  let t := hD.lift ((schemeYoneda _).map r) ((schemeYoneda _).map s) h
  let t' := t ≫ (schemeYoneda _).map (ringTestMap K e.symm.toAlgHom)
  have hl : e.symm.toAlgHom.comp a = c := by
    rw [← affineOverlapComparison_comp_left f hC hD, ← AlgHom.comp_assoc]
    change (e.symm.toAlgHom.comp e.toAlgHom).comp c = c
    rw [e.symm_comp, AlgHom.id_comp]
  have hr : e.symm.toAlgHom.comp b = d := by
    rw [← affineOverlapComparison_comp_right f hC hD, ← AlgHom.comp_assoc]
    change (e.symm.toAlgHom.comp e.toAlgHom).comp d = d
    rw [e.symm_comp, AlgHom.id_comp]
  have h₁ : t' ≫ (schemeYoneda _).map (ringTestMap K a) = (schemeYoneda _).map r := by
    rw [show t' = t ≫ (schemeYoneda _).map (ringTestMap K e.symm.toAlgHom) from rfl,
      Category.assoc, ← Functor.map_comp, ← ringTestMap_comp, hl]
    exact hD.lift_fst _ _ _
  have h₂ : t' ≫ (schemeYoneda _).map (ringTestMap K b) = (schemeYoneda _).map s := by
    rw [show t' = t ≫ (schemeYoneda _).map (ringTestMap K e.symm.toAlgHom) from rfl,
      Category.assoc, ← Functor.map_comp, ← ringTestMap_comp, hr]
    exact hD.lift_snd _ _ _
  simpa only [← Category.assoc, h₁, h₂] using congrArg (t' ≫ ·) hC.w

include hp' hp hF hAffineReflect hX' hX in
set_option backward.isDefEq.respectTransparency false in
/-- For separated spaces with a locally finite type source, affine étale
reflection suffices to reflect monicity of compatible analytified maps. -/
theorem mono_of_mono_analytification [Mono F] (hLFT : LocallyOfFiniteTypeOverBase X') :
    Mono (hom f) := by
  obtain ⟨U, a, ha, hsurj, hU⟩ := hLFT.exists_atlas
  let : LocallyOfFiniteType U.hom := hU
  let base := Spec (CommRingCat.of K)
  let J := Scheme.etaleTopology.over base
  have hlocal : CategoryTheory.Presheaf.IsLocallySurjective J a :=
    isLocallySurjective_etale_of_isEtale_isSurjective a ha hsurj
  have hsheaf := (isSheaf_iff_isSheaf_of_type _ _).mp
    (X'.toSheaf.property.of_le (Sites.etaleTopologyOver_le_fppfTopologyOver base))
  let 𝒰 := U.left.affineCover
  let V := SchemeOpenChart.obj 𝒰
  let j := SchemeOpenChart.map 𝒰
  let : ∀ i, IsAffine (V i).left := fun i => inferInstanceAs (IsAffine (𝒰.X i))
  let : ∀ i, LocallyOfFiniteType (V i).hom := fun i => by
    rw [← Over.w (j i)]
    infer_instance
  let R (i : 𝒰.I₀) := AffineCoordinateRing K (V i)
  let P (i : 𝒰.I₀) := FinitePolynomialPresentation.ofFiniteType K (R i)
  let e (i : 𝒰.I₀) := affineSchemeOverIso K (V i)
  let z (i : 𝒰.I₀) : RingPoints K X' (R i) :=
    uliftYonedaEquiv.{u + 1} ((schemeYoneda base).map ((e i).inv ≫ j i) ≫ a)
  have hz (i : 𝒰.I₀) : pointHom K (z i) =
      (schemeYoneda base).map ((e i).inv ≫ j i) ≫ a :=
    Equiv.symm_apply_apply _ _
  have hcover : Sieve.ofArrows V j ∈ J U := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact Scheme.zariskiTopology_le_etaleTopology _ 𝒰.mem_grothendieckTopology
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨T⟩
  rw [CategoryTheory.mono_iff_injective]
  intro x y hxy
  let liftSieve (x : X'.sections T) : Sieve T :=
    { arrows := fun W r => ∃ (i : 𝒰.I₀) (s : W ⟶ ringTest K (R i)),
        (schemeYoneda base).map s ≫ pointHom K (z i) =
          (schemeYoneda base).map r ≫ uliftYonedaEquiv.{u + 1}.symm x
      downward_closed := by
        rintro W W' r ⟨i, s, hs⟩ k
        exact ⟨i, k ≫ s, by simp only [Functor.map_comp, Category.assoc, hs]⟩ }
  have hLift (x : X'.sections T) : liftSieve x ∈ J T := by
    apply J.transitive (hlocal.imageSieve_mem x) (liftSieve x)
    intro W r hr
    obtain ⟨v, hv⟩ := hr
    have hv' : (schemeYoneda base).map v.down ≫ a =
        (schemeYoneda base).map r ≫ uliftYonedaEquiv.{u + 1}.symm x := by
      apply uliftYonedaEquiv.{u + 1}.injective
      simp only [uliftYonedaEquiv_comp, schemeYoneda, uliftYonedaEquiv_uliftYoneda_map,
        uliftYonedaEquiv_symm_apply_app]
      exact hv
    apply J.superset_covering _ (J.pullback_stable v.down hcover)
    intro W' k hk
    obtain ⟨i, s, hs⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hk
    refine ⟨i, s ≫ (e i).hom, ?_⟩
    have hi : (s ≫ (e i).hom) ≫ ((e i).inv ≫ j i) = k ≫ v.down := by
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hs.symm
    rw [hz, ← Functor.map_comp_assoc, hi, Functor.map_comp, Category.assoc, hv',
      ← Functor.map_comp_assoc]
  have hsep := (hsheaf _ (J.intersection_covering (hLift x) (hLift y))).isSeparatedFor
  apply hsep.ext
  intro W r hr
  obtain ⟨⟨i, s, hs⟩, ⟨j, t, ht⟩⟩ := hr
  apply uliftYonedaEquiv.{u + 1}.symm.injective
  have hrestrict (q : X'.sections T) :
      uliftYonedaEquiv.{u + 1}.symm (X'.pullback r q) =
        (schemeYoneda base).map r ≫ uliftYonedaEquiv.{u + 1}.symm q :=
    uliftYonedaEquiv_symm_map (F := X'.presheaf) r.op q
  change uliftYonedaEquiv.{u + 1}.symm (X'.pullback r x) =
    uliftYonedaEquiv.{u + 1}.symm (X'.pullback r y)
  rw [hrestrict x, hrestrict y, ← hs, ← ht]
  apply cancel_on_finite_affine_tests f hp' hp hF hAffineReflect hX' hX
    (z i) (z j) (P i) (P j)
  have he : uliftYonedaEquiv.{u + 1}.symm x ≫ hom f =
      uliftYonedaEquiv.{u + 1}.symm y ≫ hom f := by
    rw [uliftYonedaEquiv_symm_comp, uliftYonedaEquiv_symm_comp, hxy]
  simp only [pointHom_map, ← Category.assoc, hs, ht]
  rw [Category.assoc, Category.assoc, he]

end Langlands.Analytic.SpaceAnalytification
