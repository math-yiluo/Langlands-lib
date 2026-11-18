import Langlands.Geometry.Analytic.SpaceAnalytificationLocalLifts
import Langlands.Geometry.Analytic.EtaleHomGluing
import Langlands.Geometry.Analytic.PullbackIntersections
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedFunctorialityStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.FibreProduct

/-! # Conditional joint monicity of analytified projections -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Analytic.SpaceAnalytification

open SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The affine pullback preservation property in the actual spectrum-map form. -/
def AffineTestPullbackPreservation : Prop :=
  ∀ {A B C D : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    [CommRing C] [Algebra K C] [CommRing D] [Algebra K D]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (R : FinitePolynomialPresentation K C) (U : FinitePolynomialPresentation K D)
    (f : C →ₐ[K] A) (g : C →ₐ[K] B) (a : A →ₐ[K] D) (b : B →ₐ[K] D),
    IsPullback ((schemeYoneda _).map (ringTestMap K a))
      ((schemeYoneda _).map (ringTestMap K b))
      ((schemeYoneda _).map (ringTestMap K f))
      ((schemeYoneda _).map (ringTestMap K g)) →
    IsPullback (AffineAnalytification.localizedHom K P U a)
      (AffineAnalytification.localizedHom K Q U b)
      (AffineAnalytification.localizedHom K R P f)
      (AffineAnalytification.localizedHom K R Q g)

variable {K}

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Any map between representable affine tests is induced by an algebra map. -/
theorem exists_algHom_of_affine_test_map
    {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (f : (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K B) ⟶
      (schemeYoneda _).obj (ringTest K A)) :
    ∃ g : A →ₐ[K] B, (schemeYoneda _).map (ringTestMap K g) = f := by
  obtain ⟨s, rfl⟩ := (schemeYoneda _).map_surjective f
  refine ⟨affineRingPointEquiv K A B s, ?_⟩
  exact congrArg ((schemeYoneda _).map) ((affineRingPointEquiv K A B).symm_apply_apply s)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Equality of composites of affine spectrum maps reflects to the algebras. -/
theorem algHom_comp_eq_of_affine_test_comp
    {A B C : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    [CommRing C] [Algebra K C]
    (f : A →ₐ[K] B) (g : B →ₐ[K] C) (k : A →ₐ[K] C)
    (h : (schemeYoneda (Spec (CommRingCat.of K))).map (ringTestMap K g) ≫
      (schemeYoneda _).map (ringTestMap K f) =
      (schemeYoneda _).map (ringTestMap K k)) :
    g.comp f = k := by
  apply (affineRingPointEquiv K A C).symm.injective
  change ringTestMap K (g.comp f) = ringTestMap K k
  apply (schemeYoneda _).map_injective
  rw [ringTestMap_comp, Functor.map_comp]
  exact h

/-- Once two maps factor through affine tests of the top space, equality
of both projections implies equality, assuming affine preservation. -/
theorem eq_of_affine_factorizations
    (haff : AffineTestPullbackPreservation K)
    (hfun : AffineAnalytification.AffineAnalytificationLocalizedFunctorialityStatement.{u,u,u,u})
    {W X₁ X₂ Z : AlgebraicSpace (Spec (CommRingCat.of K))}
    {π₁ : W ⟶ X₁} {π₂ : W ⟶ X₂} {f₁ : X₁ ⟶ Z} {f₂ : X₂ ⟶ Z}
    (hw : IsPullback π₁ π₂ f₁ f₂)
    (hX₁ : IsSeparated X₁) (hX₂ : IsSeparated X₂) (hZ : IsSeparated Z)
    {V Y₁ Y₂ T S : LocalizedCategory.{u,u,u} (K := K)}
    {q : PointFamily K W V} {p₁ : PointFamily K X₁ Y₁}
    {p₂ : PointFamily K X₂ Y₂} {r : PointFamily K Z T}
    (hq : IsAnalytification K W V q)
    (hp₁ : IsAnalytification K X₁ Y₁ p₁) (hp₂ : IsAnalytification K X₂ Y₂ p₂)
    (hr : IsAnalytification K Z T r)
    (Φ₁ : V ⟶ Y₁) (Φ₂ : V ⟶ Y₂)
    (hπ₁ : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K W A),
      q A P x ≫ Φ₁ = p₁ A P (RingPoints.map π₁ x))
    (hπ₂ : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K W A),
      q A P x ≫ Φ₂ = p₂ A P (RingPoints.map π₂ x))
    {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (x : RingPoints K W A) (y : RingPoints K W B)
    (l m : S ⟶ V) (hl₁ : l ≫ Φ₁ = m ≫ Φ₁) (hl₂ : l ≫ Φ₂ = m ≫ Φ₂)
    (a : S ⟶ AffineAnalytification.localized K P)
    (b : S ⟶ AffineAnalytification.localized K Q)
    (ha : a ≫ q A P x = l) (hb : b ≫ q B Q y = m) : l = m := by
  have hcomp {A B C : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
      [CommRing C] [Algebra K C]
      (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
      (R : FinitePolynomialPresentation K C) (f : A →ₐ[K] B) (g : B →ₐ[K] C) :
      AffineAnalytification.localizedHom K P R (g.comp f) =
        AffineAnalytification.localizedHom K Q R g ≫
          AffineAnalytification.localizedHom K P Q f :=
    (hfun K A B C P P Q R f g).2.2.2.1
  obtain ⟨C₁, _, _, R₁, a₁, b₁, h₁⟩ := exists_affine_test_intersection hX₁ P Q
    (RingPoints.map π₁ x) (RingPoints.map π₁ y)
  obtain ⟨C₂, _, _, R₂, a₂, b₂, h₂⟩ := exists_affine_test_intersection hX₂ P Q
    (RingPoints.map π₂ x) (RingPoints.map π₂ y)
  obtain ⟨C₀, _, _, R₀, a₀, b₀, h₀⟩ := exists_affine_test_intersection hZ P Q
    (RingPoints.map f₁ (RingPoints.map π₁ x)) (RingPoints.map f₁ (RingPoints.map π₁ y))
  have hwp : IsPullback (hom π₁) (hom π₂) (hom f₁) (hom f₂) :=
    hw.map (forgetToPresheaf _)
  have h₁' := h₁
  have h₂' := h₂
  have h₀' := h₀
  simp only [pointHom_map, Category.assoc] at h₁' h₂' h₀'
  have hc₁ : (schemeYoneda _).map (ringTestMap K a₁) ≫
        (pointHom K x ≫ hom π₁ ≫ hom f₁) =
      (schemeYoneda _).map (ringTestMap K b₁) ≫
        (pointHom K y ≫ hom π₁ ≫ hom f₁) := by
    simpa only [Category.assoc] using congrArg (fun k => k ≫ hom f₁) h₁'.w
  have hc₂ : (schemeYoneda _).map (ringTestMap K a₂) ≫
        (pointHom K x ≫ hom π₁ ≫ hom f₁) =
      (schemeYoneda _).map (ringTestMap K b₂) ≫
        (pointHom K y ≫ hom π₁ ≫ hom f₁) := by
    rw [hwp.w]
    simpa only [Category.assoc] using congrArg (fun k => k ≫ hom f₂) h₂'.w
  obtain ⟨u₁, hu₁⟩ := exists_algHom_of_affine_test_map
    (h₀'.lift _ _ hc₁)
  obtain ⟨u₂, hu₂⟩ := exists_algHom_of_affine_test_map
    (h₀'.lift _ _ hc₂)
  have hu₁a : (schemeYoneda _).map (ringTestMap K u₁) ≫
      (schemeYoneda _).map (ringTestMap K a₀) =
      (schemeYoneda _).map (ringTestMap K a₁) := by rw [hu₁]; exact h₀'.lift_fst _ _ hc₁
  have hu₁b : (schemeYoneda _).map (ringTestMap K u₁) ≫
      (schemeYoneda _).map (ringTestMap K b₀) =
      (schemeYoneda _).map (ringTestMap K b₁) := by rw [hu₁]; exact h₀'.lift_snd _ _ hc₁
  have hu₂a : (schemeYoneda _).map (ringTestMap K u₂) ≫
      (schemeYoneda _).map (ringTestMap K a₀) =
      (schemeYoneda _).map (ringTestMap K a₂) := by rw [hu₂]; exact h₀'.lift_fst _ _ hc₂
  have hu₂b : (schemeYoneda _).map (ringTestMap K u₂) ≫
      (schemeYoneda _).map (ringTestMap K b₀) =
      (schemeYoneda _).map (ringTestMap K b₂) := by rw [hu₂]; exact h₀'.lift_snd _ _ hc₂
  have hll₁ : a ≫ p₁ A P (RingPoints.map π₁ x) =
      b ≫ p₁ B Q (RingPoints.map π₁ y) := by
    rw [← hπ₁ A P x, ← hπ₁ B Q y, ← Category.assoc, ← Category.assoc, ha, hb]
    exact hl₁
  have hll₂ : a ≫ p₂ A P (RingPoints.map π₂ x) =
      b ≫ p₂ B Q (RingPoints.map π₂ y) := by
    rw [← hπ₂ A P x, ← hπ₂ B Q y, ← Category.assoc, ← Category.assoc, ha, hb]
    exact hl₂
  obtain ⟨l₁, hl₁a, hl₁b⟩ :=
    (hp₁.isPullback P Q R₁ a₁ b₁ _ _ h₁).exists_lift a b hll₁
  obtain ⟨l₂, hl₂a, hl₂b⟩ :=
    (hp₂.isPullback P Q R₂ a₂ b₂ _ _ h₂).exists_lift a b hll₂
  have hul : l₁ ≫ AffineAnalytification.localizedHom K R₀ R₁ u₁ =
      l₂ ≫ AffineAnalytification.localizedHom K R₀ R₂ u₂ := by
    apply (hr.isPullback P Q R₀ a₀ b₀ _ _ h₀).hom_ext
    · rw [Category.assoc, Category.assoc,
        ← hcomp P R₀ R₁ a₀ u₁, ← hcomp P R₀ R₂ a₀ u₂,
        algHom_comp_eq_of_affine_test_comp a₀ u₁ a₁ hu₁a,
        algHom_comp_eq_of_affine_test_comp a₀ u₂ a₂ hu₂a, hl₁a, hl₂a]
    · rw [Category.assoc, Category.assoc,
        ← hcomp Q R₀ R₁ b₀ u₁, ← hcomp Q R₀ R₂ b₀ u₂,
        algHom_comp_eq_of_affine_test_comp b₀ u₁ b₁ hu₁b,
        algHom_comp_eq_of_affine_test_comp b₀ u₂ b₂ hu₂b, hl₁b, hl₂b]
  obtain ⟨D, _, _, U, d₁, d₂, hd⟩ := exists_affine_test_pullback R₁ R₂ u₁ u₂
  obtain ⟨c, hc, -⟩ := (haff R₁ R₂ R₀ U u₁ u₂ d₁ d₂ hd).exists_lift l₁ l₂ hul
  have hD := isPullback_intersection_of_isPullback hwp (pointHom K x) (pointHom K y)
    h₀' h₁' h₂' _ _ hu₁a hu₁b hu₂a hu₂b hd
  have hxy : RingPoints.changeRing (d₁.comp a₁) x =
      RingPoints.changeRing (d₁.comp b₁) y := by
    apply uliftYonedaEquiv.{u + 1}.symm.injective
    change pointHom K (RingPoints.changeRing (d₁.comp a₁) x) =
      pointHom K (RingPoints.changeRing (d₁.comp b₁) y)
    rw [pointHom_changeRing, pointHom_changeRing,
      ringTestMap_comp, ringTestMap_comp, Functor.map_comp, Functor.map_comp]
    exact hD.w
  calc
    l = c ≫ q D U (RingPoints.changeRing (d₁.comp a₁) x) := by
      rw [hq.naturality P U, hcomp P R₁ U a₁ d₁,
        ← Category.assoc, ← Category.assoc, hc, hl₁a, ha]
    _ = c ≫ q D U (RingPoints.changeRing (d₁.comp b₁) y) := by rw [hxy]
    _ = m := by
      rw [hq.naturality Q U, hcomp Q R₁ U b₁ d₁,
        ← Category.assoc, ← Category.assoc, hc, hl₁b, hb]

/-- The analytic projections of this algebraic pullback are jointly monic,
assuming affine preservation and the specified étale descent inputs. -/
theorem joint_monic_of_affine_and_etale_inputs
    (haff : AffineTestPullbackPreservation K)
    (hfun : AffineAnalytification.AffineAnalytificationLocalizedFunctorialityStatement.{u,u,u,u})
    (hbase : LocalizedEtalePullbackStatement.{u,u} K)
    (hpoints : ∀ {P A B C : LocalizedCategory.{u,u,u} (K := K)}
      (p : P ⟶ A) (q : P ⟶ B) (f : A ⟶ C) (g : B ⟶ C),
      IsPullback p q f g →
      ∀ (x : localizedSpaceFunctor.obj A) (y : localizedSpaceFunctor.obj B),
        localizedSpaceFunctor.map f x = localizedSpaceFunctor.map g y →
        ∃ z : localizedSpaceFunctor.obj P,
          localizedSpaceFunctor.map p z = x ∧ localizedSpaceFunctor.map q z = y)
    {W X₁ X₂ Z : AlgebraicSpace (Spec (CommRingCat.of K))}
    {π₁ : W ⟶ X₁} {π₂ : W ⟶ X₂} {f₁ : X₁ ⟶ Z} {f₂ : X₂ ⟶ Z}
    (hw : IsPullback π₁ π₂ f₁ f₂)
    (hX₁ : IsSeparated X₁) (hX₂ : IsSeparated X₂) (hZ : IsSeparated Z)
    {V Y₁ Y₂ T S : LocalizedCategory.{u,u,u} (K := K)}
    {q : PointFamily K W V} {p₁ : PointFamily K X₁ Y₁}
    {p₂ : PointFamily K X₂ Y₂} {r : PointFamily K Z T}
    (hq : IsAnalytification K W V q)
    (hp₁ : IsAnalytification K X₁ Y₁ p₁) (hp₂ : IsAnalytification K X₂ Y₂ p₂)
    (hr : IsAnalytification K Z T r)
    (hSheaf : Presieve.IsSheaf (etaleTopology S)
      ((MorphismProperty.Over.forget _ _ S ⋙ Over.forget S).op ⋙ yoneda.obj V))
    (Φ₁ : V ⟶ Y₁) (Φ₂ : V ⟶ Y₂)
    (hπ₁ : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K W A),
      q A P x ≫ Φ₁ = p₁ A P (RingPoints.map π₁ x))
    (hπ₂ : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K W A),
      q A P x ≫ Φ₂ = p₂ A P (RingPoints.map π₂ x))
    (l m : S ⟶ V) (hl₁ : l ≫ Φ₁ = m ≫ Φ₁) (hl₂ : l ≫ Φ₂ = m ≫ Φ₂) : l = m := by
  apply hom_ext_of_etale_local_eq hSheaf l m
  intro s
  obtain ⟨U, e, he, hs, A, _, _, B, _, _, P, Q, x, y, a, b, ha, hb⟩ :=
    exists_simultaneous_etale_local_factorization hbase hpoints hq hq l m s
  refine ⟨U, e, he, hs, ?_⟩
  exact eq_of_affine_factorizations haff hfun hw hX₁ hX₂ hZ hq hp₁ hp₂ hr
    Φ₁ Φ₂ hπ₁ hπ₂ P Q x y (e ≫ l) (e ≫ m)
    (by simpa only [Category.assoc] using congrArg (fun k => e ≫ k) hl₁)
    (by simpa only [Category.assoc] using congrArg (fun k => e ≫ k) hl₂)
    a b ha hb

end Langlands.Analytic.SpaceAnalytification
