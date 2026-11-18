import Langlands.Geometry.Analytic.EtaleHomGluing
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedFunctorialityProof
import Langlands.Geometry.Analytic.LocalizedPullbackPoints
import Langlands.Geometry.Analytic.SpaceAnalytificationAffinePullbacks
import Langlands.Geometry.Analytic.SpaceAnalytificationFibreProductStatement
import Langlands.Geometry.Analytic.SpaceAnalytificationLocalLifts

/-! # Conditional reductions for analytification fibre products -/

noncomputable section

universe u v

open CategoryTheory

namespace Langlands.Analytic.SpaceAnalytification

open SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The étale affine test maps of an analytification detect equality,
assuming the actual analytic Hom-sheaf property at this source and target. -/
theorem IsAnalytification.hom_ext
    {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    {Y T : LocalizedCategory.{u, u, u} (K := K)}
    {p : PointFamily K X Y} (hp : IsAnalytification K X Y p)
    (hSheaf : Presieve.IsSheaf (etaleTopology Y) ((MorphismProperty.Over.forget _ _ Y ⋙ Over.forget Y).op ⋙ yoneda.obj T))
    (f g : Y ⟶ T)
    (h : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X A),
      p A P x ≫ f = p A P x ≫ g) :
    f = g := by
  apply hom_ext_of_etale_local_eq hSheaf f g
  intro y
  obtain ⟨A, _, _, P, x, hx, hy⟩ := hp.jointly_surjective y
  exact ⟨AffineAnalytification.localized K P, p A P x, hp.etale_map P x hx,
    hy, h A P x⟩

/-- Compatibility with the algebraic square implies commutativity of the
analytic square, assuming Hom-sheaf uniqueness for its source and target. -/
theorem compatible_square_commutes
    {W X₁ X₂ Z : AlgebraicSpace (Spec (CommRingCat.of K))}
    {π₁ : W ⟶ X₁} {π₂ : W ⟶ X₂} {f₁ : X₁ ⟶ Z} {f₂ : X₂ ⟶ Z}
    (hw : π₁ ≫ f₁ = π₂ ≫ f₂)
    {V Y₁ Y₂ T : LocalizedCategory.{u, u, u} (K := K)}
    {q : PointFamily K W V} {p₁ : PointFamily K X₁ Y₁}
    {p₂ : PointFamily K X₂ Y₂} {r : PointFamily K Z T}
    (hq : IsAnalytification K W V q)
    (hSheaf : Presieve.IsSheaf (etaleTopology V) ((MorphismProperty.Over.forget _ _ V ⋙ Over.forget V).op ⋙ yoneda.obj T))
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
      p₂ A P x ≫ F₂ = r A P (RingPoints.map f₂ x)) :
    Φ₁ ≫ F₁ = Φ₂ ≫ F₂ := by
  apply hq.hom_ext hSheaf
  intro A _ _ P x
  rw [← Category.assoc, hπ₁ A P x, hf₁ A P (RingPoints.map π₁ x),
    ← RingPoints.map_comp, hw, RingPoints.map_comp,
    ← hf₂ A P (RingPoints.map π₂ x), ← hπ₂ A P x, Category.assoc]

/-- Hom descent and the local existence construction reduce preservation
of this algebraic pullback to joint monicity of its analytic projections. -/
theorem isPullback_of_joint_monic
    (hSheaf : ∀ (S T : LocalizedCategory.{u, u, u} (K := K)),
      Presieve.IsSheaf (etaleTopology S)
        ((MorphismProperty.Over.forget _ _ S ⋙ Over.forget S).op ⋙ yoneda.obj T))
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
    {V Y₁ Y₂ T : LocalizedCategory.{u, u, u} (K := K)}
    {q : PointFamily K W V} {p₁ : PointFamily K X₁ Y₁}
    {p₂ : PointFamily K X₂ Y₂} {r : PointFamily K Z T}
    (hq : IsAnalytification K W V q)
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
    (hmono : ∀ (S : LocalizedCategory.{u, u, u} (K := K)) (l m : S ⟶ V),
      l ≫ Φ₁ = m ≫ Φ₁ → l ≫ Φ₂ = m ≫ Φ₂ → l = m) :
    IsPullback Φ₁ Φ₂ F₁ F₂ := by
  apply isPullback_of_etale_local_lifts Φ₁ Φ₂ F₁ F₂
    (compatible_square_commutes hw.w hq (hSheaf V T)
      Φ₁ Φ₂ F₁ F₂ hπ₁ hπ₂ hf₁ hf₂) hSheaf hmono
  intro S a b hab s
  exact exists_etale_local_lift hbase hpoints hw hZ hp₁ hp₂ hr
    Φ₁ Φ₂ F₁ F₂ hπ₁ hπ₂ hf₁ hf₂ a b hab s

/-- The full published fibre-product proposition follows from the
specified affine preservation, functoriality, and étale descent inputs. -/
theorem fibreProductStatement_of_affine_and_etale_inputs
    (hSheaf : ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
      [CompleteSpace K] (S T : LocalizedCategory.{u,u,u} (K := K)),
      Presieve.IsSheaf (etaleTopology S)
        ((MorphismProperty.Over.forget _ _ S ⋙ Over.forget S).op ⋙ yoneda.obj T))
    (haff : AffineAnalytification.AffineAnalytificationFibreProductStatement.{u,u,u,u})
    (hfun : AffineAnalytification.AffineAnalytificationLocalizedFunctorialityStatement.{u,u,u,u})
    (hbase : ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
      [CompleteSpace K], LocalizedEtalePullbackStatement.{u,u} K)
    (hpoints : ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
      [CompleteSpace K] {P A B C : LocalizedCategory.{u,u,u} (K := K)}
      (p : P ⟶ A) (q : P ⟶ B) (f : A ⟶ C) (g : B ⟶ C),
      IsPullback p q f g →
      ∀ (x : localizedSpaceFunctor.obj A) (y : localizedSpaceFunctor.obj B),
        localizedSpaceFunctor.map f x = localizedSpaceFunctor.map g y →
        ∃ z : localizedSpaceFunctor.obj P,
          localizedSpaceFunctor.map p z = x ∧ localizedSpaceFunctor.map q z = y) :
    SpaceAnalytificationFibreProductStatement.{u} := by
  intro K _ _ _ W X₁ X₂ Z π₁ π₂ f₁ f₂ hw hX₁ _ hX₂ _ hZ _
    V Y₁ Y₂ T q p₁ p₂ r hq hp₁ hp₂ hr Φ₁ Φ₂ F₁ F₂ hπ₁ hπ₂ hf₁ hf₂
  apply isPullback_of_joint_monic (hSheaf K) (hbase K) (hpoints K) hw hZ
    hq hp₁ hp₂ hr Φ₁ Φ₂ F₁ F₂ hπ₁ hπ₂ hf₁ hf₂
  intro S l m hl₁ hl₂
  exact joint_monic_of_affine_and_etale_inputs
    (affineTestPullbackPreservation_of_tensor haff hfun) hfun (hbase K) (hpoints K)
    hw hX₁ hX₂ hZ hq hp₁ hp₂ hr (hSheaf K S V) Φ₁ Φ₂ hπ₁ hπ₂ l m hl₁ hl₂

/-- Published localized affine functoriality leaves only affine preservation
and the three analytic descent inputs as premises. -/
theorem fibreProductStatement_of_affine_and_descent_inputs
    (hSheaf : ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
      [CompleteSpace K] (S T : LocalizedCategory.{u,u,u} (K := K)),
      Presieve.IsSheaf (etaleTopology S)
        ((MorphismProperty.Over.forget _ _ S ⋙ Over.forget S).op ⋙ yoneda.obj T))
    (haff : AffineAnalytification.AffineAnalytificationFibreProductStatement.{u,u,u,u})
    (hbase : ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
      [CompleteSpace K], LocalizedEtalePullbackStatement.{u,u} K)
    (hpoints : ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
      [CompleteSpace K] {P A B C : LocalizedCategory.{u,u,u} (K := K)}
      (p : P ⟶ A) (q : P ⟶ B) (f : A ⟶ C) (g : B ⟶ C),
      IsPullback p q f g →
      ∀ (x : localizedSpaceFunctor.obj A) (y : localizedSpaceFunctor.obj B),
        localizedSpaceFunctor.map f x = localizedSpaceFunctor.map g y →
        ∃ z : localizedSpaceFunctor.obj P,
          localizedSpaceFunctor.map p z = x ∧ localizedSpaceFunctor.map q z = y) :
    SpaceAnalytificationFibreProductStatement.{u} :=
  fibreProductStatement_of_affine_and_etale_inputs hSheaf haff
    AffineAnalytification.affineAnalytificationLocalizedFunctoriality hbase hpoints

/-- The remaining three inputs imply the unchanged fibre-product
proposition. This is a conditional reduction, not any of its premises. -/
def FibreProductReductionStatement : Prop :=
  (∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (S T : LocalizedCategory.{u,u,u} (K := K)),
    Presieve.IsSheaf (etaleTopology S)
      ((MorphismProperty.Over.forget _ _ S ⋙ Over.forget S).op ⋙ yoneda.obj T)) →
  AffineAnalytification.AffineAnalytificationFibreProductStatement.{u,u,u,u} →
  (∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K], LocalizedEtalePullbackStatement.{u,u} K) →
  SpaceAnalytificationFibreProductStatement.{u}

/-- Published localized functoriality and underlying point lifting
discharge two inputs of the full conditional reduction. -/
theorem fibreProductReduction : FibreProductReductionStatement.{u} := by
  intro hSheaf haff hbase
  apply fibreProductStatement_of_affine_and_descent_inputs hSheaf haff hbase
  intro K _ _ _ P A B C p q f g h x y hxy
  exact exists_point_of_isPullback p q f g h x y hxy

end Langlands.Analytic.SpaceAnalytification
