import Langlands.GroupScheme.AffineWeilRestriction

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj TensorProduct

namespace Langlands.GroupScheme.AffineWeil

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  {G H K : GroupScheme (Spec (CommRingCat.of B))}

/-- The original target homomorphism on the actual tensor-valued point functors. -/
def pointTransformation (f : G ⟶ H) : pointFunctor A B G ⟶ pointFunctor A B H where
  app T := GrpCat.ofHom (G.affinePointsTarget f ((tensorFunctor A B).obj T))
  naturality := by
    intro T T' a
    apply GrpCat.hom_ext
    exact (G.affinePointsTarget_naturality f ((tensorFunctor A B).map a)).symm

variable [Module.Finite A B] [Module.Projective A B]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  [IsAffine K.X.left] [LocallyOfFiniteType K.X.hom]

/-- Restriction of a homomorphism is an actual group-scheme homomorphism. -/
def map (f : G ⟶ H) : groupScheme A B G ⟶ groupScheme A B H :=
  Corepresented.groupSchemeMap (corepresentableBy A B G) (corepresentableBy A B H)
    (pointTransformation A B f)

/-- On every affine test, restriction recovers the original target homomorphism. -/
theorem map_affinePoints (f : G ⟶ H) (T : Type u) [CommRing T] [Algebra A T]
    (p : (groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) T)) :
    pointsEquiv A B H T
        ((groupScheme A B G).affinePointsTarget (map A B f)
          (CommAlgCat.of (CommRingCat.of A) T) p) =
      G.affinePointsTarget f (CommAlgCat.of (CommRingCat.of B) (B ⊗[A] T))
        (pointsEquiv A B G T p) :=
  Corepresented.groupSchemeMap_affinePoints (corepresentableBy A B G)
    (corepresentableBy A B H) (pointTransformation A B f) p

/-- Affine tests detect homomorphisms out of the restricted affine group. -/
theorem hom_ext (f g : groupScheme A B G ⟶ groupScheme A B H)
    (h : ∀ (T : CommAlgCat.{u} (CommRingCat.of A))
      (p : (groupScheme A B G).affinePoints T),
      (groupScheme A B G).affinePointsTarget f T p =
        (groupScheme A B G).affinePointsTarget g T p) : f = g := by
  apply Grp.hom_ext
  have h' := h (coordinateAlgebra A B G) (𝟙 (groupScheme A B G).X)
  change 𝟙 (groupScheme A B G).X ≫ f.hom.hom =
    𝟙 (groupScheme A B G).X ≫ g.hom.hom at h'
  simpa only [Category.id_comp] using h'

/-- Restriction preserves the identity homomorphism. -/
@[simp] theorem map_id : map A B (𝟙 G) = 𝟙 (groupScheme A B G) := by
  apply hom_ext A B
  intro T p
  apply (pointsEquiv A B G T).injective
  have h := map_affinePoints A B (𝟙 G) T p
  change pointsEquiv A B G T (p ≫ (map A B (𝟙 G)).hom.hom) =
    pointsEquiv A B G T p ≫ 𝟙 G.X at h
  change pointsEquiv A B G T (p ≫ (map A B (𝟙 G)).hom.hom) =
    pointsEquiv A B G T (p ≫ 𝟙 (groupScheme A B G).X)
  simpa only [Category.comp_id] using h

/-- Restriction preserves composition of homomorphisms. -/
@[simp] theorem map_comp (f : G ⟶ H) (g : H ⟶ K) :
    map A B (f ≫ g) = map A B f ≫ map A B g := by
  apply hom_ext A B
  intro T p
  apply (pointsEquiv A B K T).injective
  have h := map_affinePoints A B (f ≫ g) T p
  have hf := map_affinePoints A B f T p
  have hg := map_affinePoints A B g T (p ≫ (map A B f).hom.hom)
  change pointsEquiv A B K T (p ≫ (map A B (f ≫ g)).hom.hom) =
    pointsEquiv A B G T p ≫ f.hom.hom ≫ g.hom.hom at h
  change pointsEquiv A B H T (p ≫ (map A B f).hom.hom) =
    pointsEquiv A B G T p ≫ f.hom.hom at hf
  change pointsEquiv A B K T ((p ≫ (map A B f).hom.hom) ≫ (map A B g).hom.hom) =
    pointsEquiv A B H T (p ≫ (map A B f).hom.hom) ≫ g.hom.hom at hg
  change pointsEquiv A B K T (p ≫ (map A B (f ≫ g)).hom.hom) =
    pointsEquiv A B K T (p ≫ ((map A B f).hom.hom ≫ (map A B g).hom.hom))
  rw [Category.assoc] at hg
  exact h.trans (by simpa only [hf, Category.assoc] using hg.symm)

section Commutative

variable (G) [hcomm : IsCommMonObj G.X]

/-- Commutativity follows from the original point groups on relative global sections. -/
instance groupScheme_isCommMonObj : IsCommMonObj (groupScheme A B G).X := by
  rw [isCommMonObj_iff_isMulCommutative]
  intro T
  refine ⟨⟨fun p q => ?_⟩⟩
  let e := Corepresented.pointsEquiv (pointFunctor A B G) (corepresentableBy A B G) T
  apply e.injective
  have hc : e p * e q = e q * e p := by
    exact @mul_comm
      (G.affinePoints ((tensorFunctor A B).obj ((algΓ (CommRingCat.of A)).obj T).unop))
      inferInstance (e p) (e q)
  exact (e.map_mul p q).trans (hc.trans (e.map_mul q p).symm)

/-- The commutative variant retains precisely the same underlying group scheme. -/
def commGroupScheme : CommGroupScheme (Spec (CommRingCat.of A)) :=
  { groupScheme A B G with comm := groupScheme_isCommMonObj A B G }

include hcomm in
/-- Forgetting commutativity leaves the original restriction and its point comparison. -/
@[simp] theorem commGroupScheme_toGrp :
    (commGroupScheme A B G).toGrp = groupScheme A B G := rfl

end Commutative

end Langlands.GroupScheme.AffineWeil
