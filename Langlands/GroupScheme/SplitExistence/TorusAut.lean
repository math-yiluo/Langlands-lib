import Langlands.GroupScheme.SplitExistence.Characters
import Langlands.GroupScheme.SplitExistence.Weyl

/-! # Automorphisms of `D(X)` from automorphisms of `X`

An additive automorphism `e` of `X` induces the automorphism `χ ↦ χ ∘ e` of the points of
`D(X)`, hence an automorphism `torusAut e` of `D(X)`. Precomposition with its inverse sends the
character `charOf x` to `charOf (e⁻¹ x)`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {X : Type u} [AddCommGroup X] (k : Type u) [Field k]

/-- Precomposition of characters with an additive endomorphism of `X`. -/
def precompChar (w : X →+ X) (R : Type u) [CommRing R] :
    (Multiplicative X →* Rˣ) →* (Multiplicative X →* Rˣ) where
  toFun χ := χ.comp (AddMonoidHom.toMultiplicative w)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The endomorphism of `D(X)` attached to `w : X →+ X`, on points. -/
def torusEndPoints (w : X →+ X) (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (Tk (X := X) k).toGrp.X) →* (T ⟶ (Tk (X := X) k).toGrp.X) :=
  (torusPointsEquiv k T).symm.toMonoidHom.comp
    ((precompChar w Γ(T.left, ⊤)).comp (torusPointsEquiv k T).toMonoidHom)

theorem torusPointsEquiv_torusEndPoints (w : X →+ X) (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (Tk (X := X) k).toGrp.X) :
    torusPointsEquiv k T (torusEndPoints k w T x) =
      (torusPointsEquiv k T x).comp (AddMonoidHom.toMultiplicative w) :=
  MulEquiv.apply_symm_apply _ _

theorem torusEndPoints_naturality (w : X →+ X) {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T) (x : T ⟶ (Tk (X := X) k).toGrp.X) :
    torusEndPoints k w T' (a ≫ x) = a ≫ torusEndPoints k w T x := by
  apply (torusPointsEquiv k T').injective
  rw [torusPointsEquiv_torusEndPoints]
  rw [show torusPointsEquiv k T' (a ≫ x) = (Units.map a.left.appTop.hom.toMonoidHom).comp
      (torusPointsEquiv k T x) from rfl,
    show torusPointsEquiv k T' (a ≫ torusEndPoints k w T x) =
      (Units.map a.left.appTop.hom.toMonoidHom).comp
        (torusPointsEquiv k T (torusEndPoints k w T x)) from rfl,
    torusPointsEquiv_torusEndPoints]
  rfl

/-- The endomorphism of `D(X)` attached to `w : X →+ X`. -/
def torusEnd (w : X →+ X) : (Tk (X := X) k).toGrp ⟶ (Tk (X := X) k).toGrp :=
  homOfPoints (torusEndPoints k w) fun a x => torusEndPoints_naturality k w a x

theorem torusPointsEquiv_torusEnd (w : X →+ X) (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (Tk (X := X) k).toGrp.X) :
    torusPointsEquiv k T (x ≫ (torusEnd k w).hom.hom) =
      (torusPointsEquiv k T x).comp (AddMonoidHom.toMultiplicative w) := by
  rw [torusEnd, comp_homOfPoints, torusPointsEquiv_torusEndPoints]

theorem torusEnd_comp (w w' : X →+ X) :
    torusEnd k w' ≫ torusEnd k w = torusEnd k (w'.comp w) := by
  refine hom_ext_points fun T x => ?_
  apply (torusPointsEquiv k T).injective
  rw [Grp.comp_hom_hom, ← Category.assoc, torusPointsEquiv_torusEnd, torusPointsEquiv_torusEnd,
    torusPointsEquiv_torusEnd]
  rfl

theorem torusEnd_id : torusEnd k (AddMonoidHom.id X) = 𝟙 _ := by
  refine hom_ext_points fun T x => ?_
  apply (torusPointsEquiv k T).injective
  rw [torusPointsEquiv_torusEnd]
  rfl

/-- The automorphism of `D(X)` attached to an additive automorphism of `X`. -/
def torusAut (e : X ≃+ X) : Tk (X := X) k ≅ Tk (X := X) k where
  hom := Additive.ofMul (torusEnd k e.toAddMonoidHom)
  inv := Additive.ofMul (torusEnd k e.symm.toAddMonoidHom)
  hom_inv_id := by
    change Additive.ofMul (torusEnd k e.toAddMonoidHom ≫ torusEnd k e.symm.toAddMonoidHom) =
      Additive.ofMul (𝟙 _)
    rw [torusEnd_comp]
    congr 1
    convert torusEnd_id k
    ext x
    simp
  inv_hom_id := by
    change Additive.ofMul (torusEnd k e.symm.toAddMonoidHom ≫ torusEnd k e.toAddMonoidHom) =
      Additive.ofMul (𝟙 _)
    rw [torusEnd_comp]
    congr 1
    convert torusEnd_id k
    ext x
    simp

theorem groupHom_torusAut_hom (e : X ≃+ X) :
    CommGroupScheme.groupHom (torusAut k e).hom = torusEnd k e.toAddMonoidHom :=
  rfl

/-- Precomposing `charOf x` with `torusAut e`⁻¹ gives `charOf (e⁻¹ x)`. -/
theorem torusAut_inv_comp_charOf (e : X ≃+ X) (x : X) :
    (torusAut k e).inv ≫ charOf k x = charOf k (e.symm x) := by
  apply CommGroupScheme.hom_ext_points
  intro T y
  apply (Gm.pointsEquiv _ T).injective
  change Gm.pointsEquiv _ T ((y ≫ (torusEnd k e.symm.toAddMonoidHom).hom.hom) ≫
    (CommGroupScheme.groupHom (charOf k x)).hom.hom) = _
  rw [gmPoints_charOf, gmPoints_charOf, torusPointsEquiv_torusEnd]
  rfl

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
