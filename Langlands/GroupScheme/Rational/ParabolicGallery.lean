import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Rational.SplitTorus
import Mathlib.Logic.Relation

/-! # Rank-one galleries between parabolics with one fixed embedded Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G L : GroupScheme (Spec (CommRingCat.of k))}

/-- An actual rational parabolic image with the specified embedded rational Levi. -/
def IsRationalParabolicWithLevi (j : L ⟶ G) (F : SubgroupFunctor G) : Prop :=
  ∃ (R : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ G) (l : L ⟶ R),
    IsParabolicSubgroup r ∧ IsRationalLeviSubgroup l ∧
      l ≫ r = j ∧ SubgroupFunctor.range r = F

/-- Actual geometric data for a rank-one wall between two parabolic images.
The inner parabolics are the exact intersections with the outer Levi, are
opposite with common Levi `L`, and are maximal proper parabolics there. -/
structure RationalRankOneWallData (j : L ⟶ G) (F F' : SubgroupFunctor G) where
  P : GroupScheme (Spec (CommRingCat.of k))
  M : GroupScheme (Spec (CommRingCat.of k))
  Q : GroupScheme (Spec (CommRingCat.of k))
  Q' : GroupScheme (Spec (CommRingCat.of k))
  p : P ⟶ G
  m : M ⟶ P
  q : Q ⟶ M
  q' : Q' ⟶ M
  l : L ⟶ Q
  l' : L ⟶ Q'
  parabolic : IsParabolicSubgroup p
  levi : IsRationalLeviSubgroup m
  innerParabolic : IsParabolicSubgroup q
  innerParabolic' : IsParabolicSubgroup q'
  innerLevi : IsRationalLeviSubgroup l
  innerLevi' : IsRationalLeviSubgroup l'
  commonLevi : l' ≫ q' = l ≫ q
  levi_comp : (l ≫ q) ≫ m ≫ p = j
  contained : F ≤ SubgroupFunctor.range p
  contained' : F' ≤ SubgroupFunctor.range p
  intersection : SubgroupFunctor.range q = F.comap (m ≫ p)
  intersection' : SubgroupFunctor.range q' = F'.comap (m ≫ p)
  opposite : SubgroupFunctor.range q ⊓ SubgroupFunctor.range q' =
    SubgroupFunctor.range (l ≫ q)
  proper : ¬ IsIso q
  maximal : ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ M) (f : Q ⟶ H),
    IsParabolicSubgroup h → f ≫ h = q → IsIso f ∨ IsIso h

/-- The two vertices of a rank-one wall retain their actual rational Levi. -/
def IsRationalRankOneWall (j : L ⟶ G) (F F' : SubgroupFunctor G) : Prop :=
  IsRationalParabolicWithLevi j F ∧ IsRationalParabolicWithLevi j F' ∧
    Nonempty (RationalRankOneWallData j F F')

/-- A finite rank-one gallery, encoded as the reflexive transitive closure. -/
def HasRationalParabolicGallery (j : L ⟶ G) (F F' : SubgroupFunctor G) : Prop :=
  IsRationalParabolicWithLevi j F ∧ IsRationalParabolicWithLevi j F' ∧
    Relation.ReflTransGen (IsRationalRankOneWall j) F F'

variable {B : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A rank-one wall at which the specified central torus of `L` becomes
noncentral in the intermediate Levi. -/
def IsRationalRankOneWallAvoiding (b : B.toGrp ⟶ L) (j : L ⟶ G)
    (F F' : SubgroupFunctor G) : Prop :=
  IsRationalParabolicWithLevi j F ∧ IsRationalParabolicWithLevi j F' ∧
    ∃ d : RationalRankOneWallData j F F', ¬ IsCentral (b ≫ d.l ≫ d.q)

/-- A finite gallery every wall of which is nonzero on the specified torus. -/
def HasRationalParabolicGalleryAvoiding (b : B.toGrp ⟶ L) (j : L ⟶ G)
    (F F' : SubgroupFunctor G) : Prop :=
  IsRationalParabolicWithLevi j F ∧ IsRationalParabolicWithLevi j F' ∧
    Relation.ReflTransGen (IsRationalRankOneWallAvoiding b j) F F'

/-- Reflexive galleries include the case when the two parabolics coincide. -/
theorem HasRationalParabolicGallery.refl {j : L ⟶ G} {F : SubgroupFunctor G}
    (h : IsRationalParabolicWithLevi j F) : HasRationalParabolicGallery j F F :=
  ⟨h, h, Relation.ReflTransGen.refl⟩

/-- Finite galleries concatenate without changing the embedded Levi. -/
theorem HasRationalParabolicGallery.trans {j : L ⟶ G} {F F' F'' : SubgroupFunctor G}
    (h : HasRationalParabolicGallery j F F') (h' : HasRationalParabolicGallery j F' F'') :
    HasRationalParabolicGallery j F F'' :=
  ⟨h.1, h'.2.1, h.2.2.trans h'.2.2⟩

/-- A single wall is a gallery. -/
theorem IsRationalRankOneWall.gallery {j : L ⟶ G} {F F' : SubgroupFunctor G}
    (h : IsRationalRankOneWall j F F') : HasRationalParabolicGallery j F F' :=
  ⟨h.1, h.2.1, Relation.ReflTransGen.single h⟩

/-- Reflexive galleries satisfy every wall restriction vacuously. -/
theorem HasRationalParabolicGalleryAvoiding.refl {b : B.toGrp ⟶ L} {j : L ⟶ G}
    {F : SubgroupFunctor G} (h : IsRationalParabolicWithLevi j F) :
    HasRationalParabolicGalleryAvoiding b j F F :=
  ⟨h, h, Relation.ReflTransGen.refl⟩

/-- Restricted galleries concatenate. -/
theorem HasRationalParabolicGalleryAvoiding.trans {b : B.toGrp ⟶ L} {j : L ⟶ G}
    {F F' F'' : SubgroupFunctor G}
    (h : HasRationalParabolicGalleryAvoiding b j F F')
    (h' : HasRationalParabolicGalleryAvoiding b j F' F'') :
    HasRationalParabolicGalleryAvoiding b j F F'' :=
  ⟨h.1, h'.2.1, h.2.2.trans h'.2.2⟩

/-- Forgetting the wall restriction gives an ordinary gallery. -/
theorem HasRationalParabolicGalleryAvoiding.gallery {b : B.toGrp ⟶ L} {j : L ⟶ G}
    {F F' : SubgroupFunctor G} (h : HasRationalParabolicGalleryAvoiding b j F F') :
    HasRationalParabolicGallery j F F' := by
  refine ⟨h.1, h.2.1, Relation.ReflTransGen.mono ?_ _ _ h.2.2⟩
  rintro F₀ F₁ ⟨h₀, h₁, d, -⟩
  exact ⟨h₀, h₁, ⟨d⟩⟩

end Langlands.GroupScheme
