import Langlands.Geometry.Analytic.SpaceAnalytificationAffineIntersections
import Langlands.Geometry.Analytic.SpaceAnalytificationEtaleReduction
import Langlands.Geometry.Analytic.LocalizedEtaleComposition
import Langlands.Geometry.Analytic.EtaleGeometricPointPullbacks

/-! # Conditional local lifts for analytification fibre products -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Analytic.SpaceAnalytification

open SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The algebraic pullback lifts compatible points over any test algebra. -/
theorem exists_ringPoint_of_isPullback
    {W X₁ X₂ Z : AlgebraicSpace (Spec (CommRingCat.of K))}
    {π₁ : W ⟶ X₁} {π₂ : W ⟶ X₂} {f₁ : X₁ ⟶ Z} {f₂ : X₂ ⟶ Z}
    (hw : IsPullback π₁ π₂ f₁ f₂)
    {A : Type u} [CommRing A] [Algebra K A]
    (x : RingPoints K X₁ A) (y : RingPoints K X₂ A)
    (hxy : RingPoints.map f₁ x = RingPoints.map f₂ y) :
    ∃ w : RingPoints K W A, RingPoints.map π₁ w = x ∧ RingPoints.map π₂ w = y := by
  let a : (schemeToSpace _).obj (ringTest K A) ⟶ X₁ := homMk (pointHom K x)
  let b : (schemeToSpace _).obj (ringTest K A) ⟶ X₂ := homMk (pointHom K y)
  have hab : a ≫ f₁ = b ≫ f₂ := by
    apply (homEquiv _ _).injective
    change pointHom K x ≫ hom f₁ = pointHom K y ≫ hom f₂
    rw [← pointHom_map K f₁ x, ← pointHom_map K f₂ y, hxy]
  obtain ⟨l, hl₁, hl₂⟩ := hw.exists_lift a b hab
  refine ⟨uliftYonedaEquiv.{u + 1} (hom l), ?_, ?_⟩
  · change uliftYonedaEquiv.{u + 1} (hom (l ≫ π₁)) = x
    rw [hl₁]
    exact uliftYonedaEquiv.{u + 1}.apply_symm_apply x
  · change uliftYonedaEquiv.{u + 1} (hom (l ≫ π₂)) = y
    rw [hl₂]
    exact uliftYonedaEquiv.{u + 1}.apply_symm_apply y

/-- Étale base change and point lifting produce a local factorization
through one of the étale affine test maps of an analytification. -/
theorem IsAnalytification.exists_etale_local_factorization
    (hbase : LocalizedEtalePullbackStatement.{u, u} K)
    (hpoints : ∀ {P A B C : LocalizedCategory.{u, u, u} (K := K)}
      (p : P ⟶ A) (q : P ⟶ B) (f : A ⟶ C) (g : B ⟶ C),
      IsPullback p q f g →
      ∀ (x : localizedSpaceFunctor.obj A) (y : localizedSpaceFunctor.obj B),
        localizedSpaceFunctor.map f x = localizedSpaceFunctor.map g y →
        ∃ z : localizedSpaceFunctor.obj P,
          localizedSpaceFunctor.map p z = x ∧ localizedSpaceFunctor.map q z = y)
    {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    {Y S : LocalizedCategory.{u, u, u} (K := K)}
    {p : PointFamily K X Y} (hp : IsAnalytification K X Y p)
    (a : S ⟶ Y) (s : localizedSpaceFunctor.obj S) :
    ∃ (U : LocalizedCategory.{u, u, u} (K := K)) (e : U ⟶ S),
      etale e ∧ s ∈ Set.range (localizedSpaceFunctor.map e) ∧
      ∃ (A : Type u) (_ : CommRing A) (_ : Algebra K A)
        (P : FinitePolynomialPresentation K A) (x : RingPoints K X A)
        (l : U ⟶ AffineAnalytification.localized K P),
        AlgebraicSpace.IsEtale (pointHom K x) ∧ l ≫ p A P x = e ≫ a := by
  obtain ⟨A, _, _, P, x, hx, α, hα⟩ := hp.jointly_surjective
    (localizedSpaceFunctor.map a s)
  obtain ⟨U, l, e, hU, he⟩ := hbase (p A P x) a (hp.etale_map P x hx)
  obtain ⟨z, -, hz⟩ := hpoints l e (p A P x) a hU α s hα
  exact ⟨U, e, he, ⟨z, hz⟩, A, inferInstance, inferInstance, P, x, l, hx, hU.w⟩

/-- Two maps into analytifications factor simultaneously through affine
test maps after one étale source refinement containing a prescribed point. -/
theorem exists_simultaneous_etale_local_factorization
    (hbase : LocalizedEtalePullbackStatement.{u, u} K)
    (hpoints : ∀ {P A B C : LocalizedCategory.{u, u, u} (K := K)}
      (p : P ⟶ A) (q : P ⟶ B) (f : A ⟶ C) (g : B ⟶ C),
      IsPullback p q f g →
      ∀ (x : localizedSpaceFunctor.obj A) (y : localizedSpaceFunctor.obj B),
        localizedSpaceFunctor.map f x = localizedSpaceFunctor.map g y →
        ∃ z : localizedSpaceFunctor.obj P,
          localizedSpaceFunctor.map p z = x ∧ localizedSpaceFunctor.map q z = y)
    {X₁ X₂ : AlgebraicSpace (Spec (CommRingCat.of K))}
    {Y₁ Y₂ S : LocalizedCategory.{u, u, u} (K := K)}
    {p₁ : PointFamily K X₁ Y₁} {p₂ : PointFamily K X₂ Y₂}
    (hp₁ : IsAnalytification K X₁ Y₁ p₁) (hp₂ : IsAnalytification K X₂ Y₂ p₂)
    (a : S ⟶ Y₁) (b : S ⟶ Y₂) (s : localizedSpaceFunctor.obj S) :
    ∃ (U : LocalizedCategory.{u, u, u} (K := K)) (e : U ⟶ S),
      etale e ∧ s ∈ Set.range (localizedSpaceFunctor.map e) ∧
      ∃ (A : Type u) (_ : CommRing A) (_ : Algebra K A)
        (B : Type u) (_ : CommRing B) (_ : Algebra K B)
        (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
        (x : RingPoints K X₁ A) (y : RingPoints K X₂ B)
        (l₁ : U ⟶ AffineAnalytification.localized K P)
        (l₂ : U ⟶ AffineAnalytification.localized K Q),
        l₁ ≫ p₁ A P x = e ≫ a ∧ l₂ ≫ p₂ B Q y = e ≫ b := by
  obtain ⟨U₁, e₁, he₁, ⟨s₁, hs₁⟩, A, _, _, P, x, l₁, -, hl₁⟩ :=
    hp₁.exists_etale_local_factorization hbase hpoints a s
  obtain ⟨U₂, e₂, he₂, ⟨s₂, hs₂⟩, B, _, _, Q, y, l₂, -, hl₂⟩ :=
    hp₂.exists_etale_local_factorization hbase hpoints (e₁ ≫ b) s₁
  refine ⟨U₂, e₂ ≫ e₁, etale_comp he₂ he₁, ⟨s₂, ?_⟩,
    A, inferInstance, inferInstance, B, inferInstance, inferInstance,
    P, Q, x, y, e₂ ≫ l₁, l₂, ?_, ?_⟩
  · rw [Functor.map_comp, TopCat.comp_app, hs₂, hs₁]
  · rw [Category.assoc, hl₁, Category.assoc]
  · exact hl₂.trans (Category.assoc e₂ e₁ b).symm

/-- Once a compatible analytic cone factors through two affine test maps,
the analytification of the base supplies a lift into the top vertex. -/
theorem exists_lift_of_affine_factorizations
    {W X₁ X₂ Z : AlgebraicSpace (Spec (CommRingCat.of K))}
    {π₁ : W ⟶ X₁} {π₂ : W ⟶ X₂} {f₁ : X₁ ⟶ Z} {f₂ : X₂ ⟶ Z}
    (hw : IsPullback π₁ π₂ f₁ f₂) (hZ : IsSeparated Z)
    {V Y₁ Y₂ T S : LocalizedCategory.{u, u, u} (K := K)}
    {q : PointFamily K W V} {p₁ : PointFamily K X₁ Y₁}
    {p₂ : PointFamily K X₂ Y₂} {r : PointFamily K Z T}
    (hp₁ : IsAnalytification K X₁ Y₁ p₁) (hp₂ : IsAnalytification K X₂ Y₂ p₂)
    (hr : IsAnalytification K Z T r)
    (Φ₁ : V ⟶ Y₁) (Φ₂ : V ⟶ Y₂) (F₁ : Y₁ ⟶ T) (F₂ : Y₂ ⟶ T)
    (hπ₁ : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K W A),
      q A P x ≫ Φ₁ = p₁ A P (RingPoints.map π₁ x))
    (hπ₂ : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K W A),
      q A P x ≫ Φ₂ = p₂ A P (RingPoints.map π₂ x))
    (hf₁ : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X₁ A),
      p₁ A P x ≫ F₁ = r A P (RingPoints.map f₁ x))
    (hf₂ : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X₂ A),
      p₂ A P x ≫ F₂ = r A P (RingPoints.map f₂ x))
    {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (x : RingPoints K X₁ A) (y : RingPoints K X₂ B)
    (a : S ⟶ Y₁) (b : S ⟶ Y₂) (hab : a ≫ F₁ = b ≫ F₂)
    (l₁ : S ⟶ AffineAnalytification.localized K P)
    (l₂ : S ⟶ AffineAnalytification.localized K Q)
    (hl₁ : l₁ ≫ p₁ A P x = a) (hl₂ : l₂ ≫ p₂ B Q y = b) :
    ∃ l : S ⟶ V, l ≫ Φ₁ = a ∧ l ≫ Φ₂ = b := by
  obtain ⟨C, _, _, R, f, g, hC⟩ := exists_affine_test_intersection hZ P Q
    (RingPoints.map f₁ x) (RingPoints.map f₂ y)
  have hxy : RingPoints.map f₁ (RingPoints.changeRing f x) =
      RingPoints.map f₂ (RingPoints.changeRing g y) := by
    apply uliftYonedaEquiv.{u + 1}.symm.injective
    change pointHom K (RingPoints.map f₁ (RingPoints.changeRing f x)) =
      pointHom K (RingPoints.map f₂ (RingPoints.changeRing g y))
    rw [← RingPoints.changeRing_map, ← RingPoints.changeRing_map,
      pointHom_changeRing, pointHom_changeRing]
    exact hC.w
  obtain ⟨w, hw₁, hw₂⟩ := exists_ringPoint_of_isPullback hw
    (RingPoints.changeRing f x) (RingPoints.changeRing g y) hxy
  have hll : l₁ ≫ r A P (RingPoints.map f₁ x) =
      l₂ ≫ r B Q (RingPoints.map f₂ y) := by
    rw [← hf₁ A P x, ← hf₂ B Q y, ← Category.assoc, ← Category.assoc,
      hl₁, hl₂]
    exact hab
  obtain ⟨c, hc₁, hc₂⟩ :=
    (hr.isPullback P Q R f g (RingPoints.map f₁ x) (RingPoints.map f₂ y) hC).exists_lift
      l₁ l₂ hll
  refine ⟨c ≫ q C R w, ?_, ?_⟩
  · rw [Category.assoc, hπ₁ C R w, hw₁, hp₁.naturality P R f x,
      ← Category.assoc, hc₁, hl₁]
  · rw [Category.assoc, hπ₂ C R w, hw₂, hp₂.naturality Q R g y,
      ← Category.assoc, hc₂, hl₂]

/-- Every compatible cone lifts étale-locally at each source point,
assuming localized étale base change and lifting of matching points. -/
theorem exists_etale_local_lift
    (hbase : LocalizedEtalePullbackStatement.{u, u} K)
    (hpoints : ∀ {P A B C : LocalizedCategory.{u, u, u} (K := K)}
      (p : P ⟶ A) (q : P ⟶ B) (f : A ⟶ C) (g : B ⟶ C),
      IsPullback p q f g →
      ∀ (x : localizedSpaceFunctor.obj A) (y : localizedSpaceFunctor.obj B),
        localizedSpaceFunctor.map f x = localizedSpaceFunctor.map g y →
        ∃ z : localizedSpaceFunctor.obj P,
          localizedSpaceFunctor.map p z = x ∧ localizedSpaceFunctor.map q z = y)
    {W X₁ X₂ Z : AlgebraicSpace (Spec (CommRingCat.of K))}
    {π₁ : W ⟶ X₁} {π₂ : W ⟶ X₂} {f₁ : X₁ ⟶ Z} {f₂ : X₂ ⟶ Z}
    (hw : IsPullback π₁ π₂ f₁ f₂) (hZ : IsSeparated Z)
    {V Y₁ Y₂ T S : LocalizedCategory.{u, u, u} (K := K)}
    {q : PointFamily K W V} {p₁ : PointFamily K X₁ Y₁}
    {p₂ : PointFamily K X₂ Y₂} {r : PointFamily K Z T}
    (hp₁ : IsAnalytification K X₁ Y₁ p₁) (hp₂ : IsAnalytification K X₂ Y₂ p₂)
    (hr : IsAnalytification K Z T r)
    (Φ₁ : V ⟶ Y₁) (Φ₂ : V ⟶ Y₂) (F₁ : Y₁ ⟶ T) (F₂ : Y₂ ⟶ T)
    (hπ₁ : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K W A),
      q A P x ≫ Φ₁ = p₁ A P (RingPoints.map π₁ x))
    (hπ₂ : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K W A),
      q A P x ≫ Φ₂ = p₂ A P (RingPoints.map π₂ x))
    (hf₁ : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X₁ A),
      p₁ A P x ≫ F₁ = r A P (RingPoints.map f₁ x))
    (hf₂ : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X₂ A),
      p₂ A P x ≫ F₂ = r A P (RingPoints.map f₂ x))
    (a : S ⟶ Y₁) (b : S ⟶ Y₂) (hab : a ≫ F₁ = b ≫ F₂)
    (s : localizedSpaceFunctor.obj S) :
    ∃ (U : LocalizedCategory.{u, u, u} (K := K)) (e : U ⟶ S),
      etale e ∧ s ∈ Set.range (localizedSpaceFunctor.map e) ∧
        ∃ l : U ⟶ V, l ≫ Φ₁ = e ≫ a ∧ l ≫ Φ₂ = e ≫ b := by
  obtain ⟨U, e, he, hs, A, _, _, B, _, _, P, Q, x, y, l₁, l₂, hl₁, hl₂⟩ :=
    exists_simultaneous_etale_local_factorization hbase hpoints hp₁ hp₂ a b s
  have hcomm : (e ≫ a) ≫ F₁ = (e ≫ b) ≫ F₂ := by
    rw [Category.assoc, Category.assoc, hab]
  obtain ⟨l, hl₁', hl₂'⟩ := exists_lift_of_affine_factorizations hw hZ hp₁ hp₂ hr
    Φ₁ Φ₂ F₁ F₂ hπ₁ hπ₂ hf₁ hf₂ P Q x y (e ≫ a) (e ≫ b) hcomm l₁ l₂ hl₁ hl₂
  exact ⟨U, e, he, hs, l, hl₁', hl₂'⟩

end Langlands.Analytic.SpaceAnalytification
