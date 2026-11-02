import Langlands.Global.AdelicGroupPointTopology
import Langlands.GroupScheme.AffinePointProducts

/-! # Infinite and finite factors of the actual adelic point group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped CategoryTheory.MonObj

namespace Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

namespace AdelicGroupPoints

/-- The actual full adelic point group is the product of its infinite and finite factors. -/
def split : AdelicGroupPoints F G ≃ₜ*
    (InfiniteAdelicGroupPoints F G × FiniteAdelicGroupPoints F G) :=
  G.affinePointsProdHomeomorph (CommAlgCat.of F (InfiniteAdeleRing F))
    (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F))

/-- The infinite coefficient projection on actual group-scheme points. -/
def infinite : AdelicGroupPoints F G →ₜ* InfiniteAdelicGroupPoints F G where
  toMonoidHom := G.affinePointsFst (CommAlgCat.of F (InfiniteAdeleRing F))
    (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F))
  continuous_toFun := continuous_fst.comp (split F G).continuous

/-- The finite coefficient projection on actual group-scheme points. -/
def finite : AdelicGroupPoints F G →ₜ* FiniteAdelicGroupPoints F G where
  toMonoidHom := G.affinePointsSnd (CommAlgCat.of F (InfiniteAdeleRing F))
    (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F))
  continuous_toFun := continuous_snd.comp (split F G).continuous

/-- Pair actual infinite and finite points via the coordinate-product equivalence. -/
def pair (a : InfiniteAdelicGroupPoints F G) (b : FiniteAdelicGroupPoints F G) :
    AdelicGroupPoints F G := (split F G).symm (a, b)

@[simp] theorem split_apply (g : AdelicGroupPoints F G) :
    split F G g = (infinite F G g, finite F G g) := rfl

@[simp] theorem infinite_pair (a : InfiniteAdelicGroupPoints F G)
    (b : FiniteAdelicGroupPoints F G) : infinite F G (pair F G a b) = a :=
  congrArg Prod.fst ((split F G).apply_symm_apply (a, b))

@[simp] theorem finite_pair (a : InfiniteAdelicGroupPoints F G)
    (b : FiniteAdelicGroupPoints F G) : finite F G (pair F G a b) = b :=
  congrArg Prod.snd ((split F G).apply_symm_apply (a, b))

@[simp] theorem pair_projections (g : AdelicGroupPoints F G) :
    pair F G (infinite F G g) (finite F G g) = g :=
  (split F G).symm_apply_apply g

theorem continuous_pair : Continuous (fun p : InfiniteAdelicGroupPoints F G ×
    FiniteAdelicGroupPoints F G => pair F G p.1 p.2) :=
  (split F G).symm.continuous

theorem pair_mul (a c : InfiniteAdelicGroupPoints F G)
    (b d : FiniteAdelicGroupPoints F G) :
    pair F G a b * pair F G c d = pair F G (a * c) (b * d) :=
  ((split F G).symm.map_mul (a, b) (c, d)).symm

theorem pair_mul_right (a : InfiniteAdelicGroupPoints F G)
    (b : FiniteAdelicGroupPoints F G) (g : AdelicGroupPoints F G) :
    pair F G a b * g = pair F G (a * infinite F G g) (b * finite F G g) := by
  conv_lhs => rw [← pair_projections F G g]
  exact pair_mul F G _ _ _ _

/-- Include the infinite point group with the finite point equal to the group identity. -/
def ofInfinite : InfiniteAdelicGroupPoints F G →ₜ* AdelicGroupPoints F G :=
  (ContinuousMonoidHom.toContinuousMonoidHom (split F G).symm).comp
    (ContinuousMonoidHom.id _ |>.prod
      (1 : InfiniteAdelicGroupPoints F G →ₜ* FiniteAdelicGroupPoints F G))

/-- Include the finite point group with the infinite point equal to the group identity. -/
def ofFinite : FiniteAdelicGroupPoints F G →ₜ* AdelicGroupPoints F G :=
  (ContinuousMonoidHom.toContinuousMonoidHom (split F G).symm).comp
    ((1 : FiniteAdelicGroupPoints F G →ₜ* InfiniteAdelicGroupPoints F G).prod
      (ContinuousMonoidHom.id _))

@[simp] theorem ofInfinite_eq_pair (a : InfiniteAdelicGroupPoints F G) :
    ofInfinite F G a = pair F G a 1 := rfl

@[simp] theorem ofFinite_eq_pair (b : FiniteAdelicGroupPoints F G) :
    ofFinite F G b = pair F G 1 b := rfl

@[simp] theorem infinite_ofInfinite (a : InfiniteAdelicGroupPoints F G) :
    infinite F G (ofInfinite F G a) = a := infinite_pair F G a 1

@[simp] theorem finite_ofInfinite (a : InfiniteAdelicGroupPoints F G) :
    finite F G (ofInfinite F G a) = 1 := finite_pair F G a 1

@[simp] theorem infinite_ofFinite (b : FiniteAdelicGroupPoints F G) :
    infinite F G (ofFinite F G b) = 1 := infinite_pair F G 1 b

@[simp] theorem finite_ofFinite (b : FiniteAdelicGroupPoints F G) :
    finite F G (ofFinite F G b) = b := finite_pair F G 1 b

/-- Conjugation by a full adelic point acts on the included finite factor by its finite part. -/
theorem finite_conjugation (g : AdelicGroupPoints F G) (b : FiniteAdelicGroupPoints F G) :
    g⁻¹ * ofFinite F G b * g =
      ofFinite F G ((finite F G g)⁻¹ * b * finite F G g) := by
  apply (split F G).injective
  change (infinite F G _, finite F G _) = (infinite F G _, finite F G _)
  simp only [map_mul, map_inv, infinite_ofFinite, finite_ofFinite, mul_one, inv_mul_cancel,
    inv_one]

/-- The two included factor subgroups commute. -/
theorem factors_commute (a : InfiniteAdelicGroupPoints F G)
    (b : FiniteAdelicGroupPoints F G) : Commute (ofInfinite F G a) (ofFinite F G b) := by
  change ofInfinite F G a * ofFinite F G b = ofFinite F G b * ofInfinite F G a
  simp only [ofInfinite_eq_pair, ofFinite_eq_pair, pair_mul, mul_one, one_mul]

end AdelicGroupPoints

namespace GeneralLinearGroupPoints

variable (n : ℕ)

local instance generalLinearIsAffine :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

/-- The general infinite projection is the existing matrix projection. -/
theorem infiniteHomeomorph_infinite
    (g : AdelicGroupPoints F (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))) :
    infiniteHomeomorph F n (AdelicGroupPoints.infinite F _ g) =
      AdelicGL.infinite F n (adelicHomeomorph F n g) :=
  GroupScheme.GeneralLinear.affinePointsEquiv_naturality (n := Fin n)
    (R := CommRingCat.of F)
    (S := CommAlgCat.of F (AdeleRing (𝓞 F) F))
    (T := CommAlgCat.of F (InfiniteAdeleRing F))
    (CommAlgCat.ofHom (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) g

/-- The general finite projection is the existing matrix projection. -/
theorem finiteHomeomorph_finite
    (g : AdelicGroupPoints F (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))) :
    finiteHomeomorph F n (AdelicGroupPoints.finite F _ g) =
      AdelicGL.finite F n (adelicHomeomorph F n g) :=
  GroupScheme.GeneralLinear.affinePointsEquiv_naturality (n := Fin n)
    (R := CommRingCat.of F)
    (S := CommAlgCat.of F (AdeleRing (𝓞 F) F))
    (T := CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F))
    (CommAlgCat.ofHom (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) g

/-- The actual point-product decomposition commutes with the existing matrix decomposition. -/
theorem split_adelicHomeomorph
    (g : AdelicGroupPoints F (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))) :
    AdelicGL.split F n (adelicHomeomorph F n g) =
      (infiniteHomeomorph F n (AdelicGroupPoints.infinite F _ g),
        finiteHomeomorph F n (AdelicGroupPoints.finite F _ g)) :=
  Prod.ext (infiniteHomeomorph_infinite F n g).symm (finiteHomeomorph_finite F n g).symm

/-- Pairing points corresponds to the original entrywise pairing of invertible matrices. -/
theorem adelicHomeomorph_pair
    (a : InfiniteAdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)))
    (b : FiniteAdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))) :
    adelicHomeomorph F n (AdelicGroupPoints.pair F _ a b) =
      AdelicGL.pair F n (infiniteHomeomorph F n a) (finiteHomeomorph F n b) := by
  apply (AdelicGL.split F n).injective
  rw [split_adelicHomeomorph]
  change _ = (AdelicGL.infinite F n _, AdelicGL.finite F n _)
  rw [AdelicGroupPoints.infinite_pair, AdelicGroupPoints.finite_pair,
    AdelicGL.infinite_pair, AdelicGL.finite_pair]

/-- Finite-factor inclusion agrees with the existing matrix-factor inclusion. -/
theorem adelicHomeomorph_ofFinite
    (b : FiniteAdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))) :
    adelicHomeomorph F n (AdelicGroupPoints.ofFinite F _ b) =
      AdelicGL.ofFinite F n (finiteHomeomorph F n b) := by
  change adelicHomeomorph F n (AdelicGroupPoints.pair F _ 1 b) =
    AdelicGL.pair F n 1 (finiteHomeomorph F n b)
  rw [adelicHomeomorph_pair, map_one]

/-- Infinite-factor inclusion agrees with the existing matrix-factor inclusion. -/
theorem adelicHomeomorph_ofInfinite
    (a : InfiniteAdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))) :
    adelicHomeomorph F n (AdelicGroupPoints.ofInfinite F _ a) =
      AdelicGL.ofInfinite F n (infiniteHomeomorph F n a) := by
  change adelicHomeomorph F n (AdelicGroupPoints.pair F _ a 1) =
    AdelicGL.pair F n (infiniteHomeomorph F n a) 1
  rw [adelicHomeomorph_pair, map_one]

end GeneralLinearGroupPoints

end Langlands.Global
