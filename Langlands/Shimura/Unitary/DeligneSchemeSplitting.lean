import Langlands.GroupScheme.CorepresentedPoints
import Langlands.GroupScheme.Multiplicative
import Langlands.Shimura.Unitary.DeligneGroupScheme
import Langlands.Shimura.Unitary.DeligneSplitting

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.Shimura.DeligneTorus

/-- The complex point of the real base induced by the usual scalar inclusion. -/
def complexBaseMap : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of ℝ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))

/-- The actual pullback of the real Deligne group scheme to the complex base. -/
abbrev complexGroupScheme := (Over.pullback complexBaseMap).mapGrp.obj groupScheme

/-- Quadratic units describe every point of the actual complex pullback. -/
def complexPointsEquiv (T : Over (Spec (CommRingCat.of ℂ))) :
    (T ⟶ complexGroupScheme.X) ≃* Points Γ(T.left, ⊤) :=
  (GroupScheme.baseChangePointsEquiv complexBaseMap groupScheme T).trans
    (GroupScheme.Corepresented.pointsEquiv (R := CommRingCat.of ℝ) functor corepresentableBy
      ((Over.map complexBaseMap).obj T))

/-- Restriction of pullback points is coefficient change on quadratic units. -/
theorem complexPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of ℂ))}
    (a : T' ⟶ T) (x : T ⟶ complexGroupScheme.X) :
    complexPointsEquiv T' (a ≫ x) =
      Units.map (map a.left.appTop.hom).toMonoidHom (complexPointsEquiv T x) := by
  change GroupScheme.Corepresented.pointsEquiv (R := CommRingCat.of ℝ) functor
    corepresentableBy _ (GroupScheme.baseChangePointsEquiv _ groupScheme _ (a ≫ x)) = _
  rw [GroupScheme.baseChangePointsEquiv_naturality,
    GroupScheme.Corepresented.pointsEquiv_naturality]
  rfl

local instance complexGlobalAlgebra (T : Over (Spec (CommRingCat.of ℂ))) :
    Algebra ℂ Γ(T.left, ⊤) := ((algΓ (CommRingCat.of ℂ)).obj T).unop.algebra

/-- Split quadratic units on every complex test scheme. -/
def complexSplitPointsEquiv (T : Over (Spec (CommRingCat.of ℂ))) :
    (T ⟶ complexGroupScheme.X) ≃* (Γ(T.left, ⊤))ˣ × (Γ(T.left, ⊤))ˣ :=
  (complexPointsEquiv T).trans (splitPointsEquiv Γ(T.left, ⊤))

/-- The complex splitting commutes with restriction along every test-scheme map. -/
theorem complexSplitPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of ℂ))}
    (a : T' ⟶ T) (x : T ⟶ complexGroupScheme.X) :
    complexSplitPointsEquiv T' (a ≫ x) =
      Prod.map (Units.map a.left.appTop.hom.toMonoidHom)
        (Units.map a.left.appTop.hom.toMonoidHom) (complexSplitPointsEquiv T x) := by
  simp only [complexSplitPointsEquiv, MulEquiv.trans_apply, complexPointsEquiv_naturality]
  exact splitPointsEquiv_natural ((algΓ (CommRingCat.of ℂ)).map a).unop.hom
    (complexPointsEquiv T x)

/-- The product of two copies of the existing multiplicative group scheme. -/
abbrev splitGroupScheme :=
  (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⊗
    (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp

/-- Points of a product group scheme are pairs, with componentwise multiplication. -/
def productPointsEquiv {S : Scheme} (G H : GroupScheme S) (T : Over S) :
    (T ⟶ (G ⊗ H).X) ≃* (T ⟶ G.X) × (T ⟶ H.X) :=
  { homEquivToProd with
    map_mul' := fun x y => by
      apply Prod.ext <;> simp only [homEquivToProd, Prod.mul_def]
      · exact MonObj.mul_comp x y (fst G.X H.X)
      · exact MonObj.mul_comp x y (snd G.X H.X) }

/-- Points of the split group scheme are two global units. -/
def splitSchemePointsEquiv (T : Over (Spec (CommRingCat.of ℂ))) :
    (T ⟶ splitGroupScheme.X) ≃* (Γ(T.left, ⊤))ˣ × (Γ(T.left, ⊤))ˣ :=
  (productPointsEquiv _ _ T).trans
    ((GroupScheme.Gm.pointsEquiv _ T).prodCongr (GroupScheme.Gm.pointsEquiv _ T))

/-- The two global units restrict componentwise. -/
theorem splitSchemePointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of ℂ))}
    (a : T' ⟶ T) (x : T ⟶ splitGroupScheme.X) :
    splitSchemePointsEquiv T' (a ≫ x) =
      Prod.map (Units.map a.left.appTop.hom.toMonoidHom)
        (Units.map a.left.appTop.hom.toMonoidHom) (splitSchemePointsEquiv T x) := by
  apply Prod.ext
  · change GroupScheme.Gm.pointsEquiv _ T' ((a ≫ x) ≫ fst _ _) =
      Units.map a.left.appTop.hom.toMonoidHom
        (GroupScheme.Gm.pointsEquiv _ T (x ≫ fst _ _))
    rw [Category.assoc, GroupScheme.Gm.pointsEquiv_naturality]
  · change GroupScheme.Gm.pointsEquiv _ T' ((a ≫ x) ≫ snd _ _) =
      Units.map a.left.appTop.hom.toMonoidHom
        (GroupScheme.Gm.pointsEquiv _ T (x ≫ snd _ _))
    rw [Category.assoc, GroupScheme.Gm.pointsEquiv_naturality]

/-- The point comparison needed by group-valued Yoneda is natural. -/
theorem complexSplitting_naturality {T T' : Over (Spec (CommRingCat.of ℂ))}
    (a : T' ⟶ T) (x : T ⟶ complexGroupScheme.X) :
    (splitSchemePointsEquiv T').symm (complexSplitPointsEquiv T' (a ≫ x)) =
      a ≫ (splitSchemePointsEquiv T).symm (complexSplitPointsEquiv T x) := by
  apply (splitSchemePointsEquiv T').injective
  rw [MulEquiv.apply_symm_apply, splitSchemePointsEquiv_naturality,
    MulEquiv.apply_symm_apply, complexSplitPointsEquiv_naturality]

/-- The complex pullback of the real Deligne group scheme is the product of two copies of Gm. -/
def complexSplitting : complexGroupScheme ≅ splitGroupScheme :=
  GroupScheme.isoOfPoints (fun T =>
    (complexSplitPointsEquiv T).trans (splitSchemePointsEquiv T).symm)
    complexSplitting_naturality

/-- The forward scheme isomorphism induces the explicit quadratic splitting on all points. -/
theorem complexSplitting_hom_points (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ complexGroupScheme.X) :
    splitSchemePointsEquiv T (x ≫ complexSplitting.hom.hom.hom) =
      complexSplitPointsEquiv T x := by
  have key : x ≫ complexSplitting.hom.hom.hom = _ :=
    GroupScheme.comp_isoOfPoints_hom _ complexSplitting_naturality T x
  rw [key]
  exact (splitSchemePointsEquiv T).apply_symm_apply _

/-- The inverse scheme isomorphism induces the inverse quadratic splitting on all points. -/
theorem complexSplitting_inv_points (T : Over (Spec (CommRingCat.of ℂ)))
    (y : T ⟶ splitGroupScheme.X) :
    complexSplitPointsEquiv T (y ≫ complexSplitting.inv.hom.hom) =
      splitSchemePointsEquiv T y := by
  have key : y ≫ complexSplitting.inv.hom.hom = _ :=
    GroupScheme.comp_isoOfPoints_inv _ complexSplitting_naturality T y
  rw [key]
  exact (complexSplitPointsEquiv T).apply_symm_apply _

/-- The first geometric coordinate is evaluation at the image of i. -/
theorem complexSplitting_hom_fst (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ complexGroupScheme.X) :
    ((splitSchemePointsEquiv T (x ≫ complexSplitting.hom.hom.hom)).1 : Γ(T.left, ⊤)) =
      (complexPointsEquiv T x : Complexification Γ(T.left, ⊤)).re +
        (complexPointsEquiv T x : Complexification Γ(T.left, ⊤)).im *
          algebraMap ℂ Γ(T.left, ⊤) Complex.I := by
  rw [complexSplitting_hom_points]
  exact splitPointsEquiv_fst _ _

/-- The second geometric coordinate is evaluation at the image of -i. -/
theorem complexSplitting_hom_snd (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ complexGroupScheme.X) :
    ((splitSchemePointsEquiv T (x ≫ complexSplitting.hom.hom.hom)).2 : Γ(T.left, ⊤)) =
      (complexPointsEquiv T x : Complexification Γ(T.left, ⊤)).re -
        (complexPointsEquiv T x : Complexification Γ(T.left, ⊤)).im *
          algebraMap ℂ Γ(T.left, ⊤) Complex.I := by
  rw [complexSplitting_hom_points]
  exact splitPointsEquiv_snd _ _

/-- On all test-scheme points, the quadratic norm is the product of geometric coordinates. -/
theorem complexSplitting_hom_norm (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ complexGroupScheme.X) :
    norm Γ(T.left, ⊤) (complexPointsEquiv T x) =
      (splitSchemePointsEquiv T (x ≫ complexSplitting.hom.hom.hom)).1 *
        (splitSchemePointsEquiv T (x ≫ complexSplitting.hom.hom.hom)).2 := by
  rw [complexSplitting_hom_points]
  exact splitPointsEquiv_norm _ _

end Langlands.Shimura.DeligneTorus
