import Langlands.GroupScheme.RelativeUnipotent.RootWeightIntrinsicCutoff
import Langlands.GroupScheme.RelativeUnipotent.RootWeightQuotient

/-! # Homogeneous polynomial coordinates on the actual positive terms -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.RootWeightData

open LocalSplitCell Corepresented

variable {R : Type u} [CommRing R]
  {I J : Type u} [Fintype I] [DecidableEq I]
  {U G : GroupScheme (Spec (CommRingCat.of R))}
  {t : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {ch : J → I → ℤ} {fam : J → (Ga R ⟶ G)}
  {C : RootHeightChart U} (W : RootWeightData C)
  (j : U ⟶ G) [Mono j.hom.hom]
  {index : Fin C.dimension → J}
  (hroot : ∀ k, C.roots (ULift.up k) ≫ j = fam (index k))
  (hu : TorusEquivariant t ch fam)

/-- The literal affine-space scheme of a represented term is a polynomial chart
for its actual induced group law. -/
def termChart (d : ℕ) :
    (VectorGroup.groupScheme (CommRingCat.of R) (Nat.card (W.support d))).X ≅
      (W.groupScheme d).X := Iso.refl _

/-- The original term polynomial ring corepresents the actual group law. -/
abbrev termPolynomialCorepresentation (d : ℕ) :
    ((W.groupScheme d).affinePointFunctor ⋙ forget GrpCat).CorepresentableBy
      (VectorGroup.coordinateAlgebra (CommRingCat.of R) (Nat.card (W.support d))) :=
  AffineLinearEmbedding.corepresentableBy (W.groupScheme d) (W.termChart d)

/-- Algebra coordinates and the term's own affine-space coordinates agree after
the affine section comparison. -/
theorem termPolynomialCoordinate_sections (d : ℕ)
    {A : CommAlgCat.{u} (CommRingCat.of R)} (x : (W.groupScheme d).affinePoints A)
    (k : Fin (Nat.card (W.support d))) :
    (affineSectionsIso A).inv.hom
      (coord (W.termPolynomialCorepresentation d) x (X k)) =
      (VectorGroup.coordinates (CommRingCat.of R) _
        ((algSpec (CommRingCat.of R)).obj (op A)) x).toAdd k := by
  have h := congrArg (fun y => y.toAdd k)
    (pointsEquiv_eq_affinePointsEquiv
      (VectorGroup.functor (CommRingCat.of R) (Nat.card (W.support d)))
      (VectorGroup.corepresentableBy (CommRingCat.of R) (Nat.card (W.support d))) A x)
  exact h.symm

/-- The actual action is diagonal in the term's own affine-space coordinates,
with the root characters of its retained indices. -/
theorem term_coordinates_torusAction (d : ℕ)
    (T : Over (Spec (CommRingCat.of R)))
    (s : T ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X)
    (x : T ⟶ (W.groupScheme d).X) (k : Fin (Nat.card (W.support d))) :
    (VectorGroup.coordinates (CommRingCat.of R) _ T
      ((W.torusAction j hroot hu d).act s x)).toAdd k =
        torusChar (ch (index (W.enumeration d k).val)) T s *
          (VectorGroup.coordinates (CommRingCat.of R) _ T x).toAdd k := by
  have h := congrFun (W.coordinates_torusAction_inclusion j hroot hu d s x)
    (W.enumeration d k).val
  dsimp only at h
  rw [W.coordinates_inclusion, W.coordinates_inclusion] at h
  simpa only [dite_eq_left (W.enumeration d k).property,
    Subtype.coe_eta, Equiv.symm_apply_apply] using h

/-- The actual term action on its affine-point group. -/
abbrev termPolynomialTorusAction (d : ℕ) :
    TorusAction (W.groupScheme d).affinePointFunctor I :=
  (W.torusAction j hroot hu d).affineTorusAction

/-- Each retained polynomial coordinate is homogeneous of its exact root
character for the actual term group, not an auxiliary additive group law. -/
theorem isHomogeneous_termPolynomialVariable (d : ℕ)
    (k : Fin (Nat.card (W.support d))) :
    IsHomogeneous (W.termPolynomialCorepresentation d)
      (W.termPolynomialTorusAction j hroot hu d)
        (ch (index (W.enumeration d k).val)) (X k) := by
  apply (isHomogeneous_iff_coord_act _ _ _ _).2
  intro A s x
  apply (ConcreteCategory.bijective_of_isIso (affineSectionsIso A).inv).1
  rw [map_mul, W.termPolynomialCoordinate_sections, W.termPolynomialCoordinate_sections]
  change (VectorGroup.coordinates (CommRingCat.of R) _ _
    ((W.torusAction j hroot hu d).act (torusPt I A s) x)).toAdd k = _
  rw [W.term_coordinates_torusAction j hroot hu]
  rw [mul_comm]
  congr 1
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1
  have hchar := charValue_torusPt (R := CommRingCat.of R) (A := A)
    (ch (index (W.enumeration d k).val)) s
  exact hchar.trans
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id _).symm

/-- The actual group identity has zero coordinates in the term's affine space. -/
theorem term_coordinates_one (d : ℕ) (T : Over (Spec (CommRingCat.of R)))
    (k : Fin (Nat.card (W.support d))) :
    (VectorGroup.coordinates (CommRingCat.of R) _ T
      (1 : T ⟶ (W.groupScheme d).X)).toAdd k = 0 := by
  have h := W.coordinates_inclusion d T (1 : T ⟶ (W.groupScheme d).X)
    (W.enumeration d k).val
  rw [MonObj.one_comp] at h
  have hz : C.coordinates T (1 : T ⟶ U.X) = 0 := by
    rw [← orderedProduct_zero C.roots ULift.up T, C.coordinates_orderedProduct]
  rw [hz] at h
  simpa only [dite_eq_left (W.enumeration d k).property,
    Subtype.coe_eta, Equiv.symm_apply_apply, Pi.zero_apply] using h.symm

/-- The actual term augmentation sends every polynomial variable to zero. -/
theorem termPolynomialVariable_counit (d : ℕ)
    (k : Fin (Nat.card (W.support d))) :
    AffineLinearEmbedding.counit (W.termPolynomialCorepresentation d) (X k) = 0 := by
  let A : CommAlgCat.{u} (CommRingCat.of R) := CommAlgCat.of (CommRingCat.of R) R
  have hz : coord (W.termPolynomialCorepresentation d)
      (1 : (W.groupScheme d).affinePoints A) (X k) = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (affineSectionsIso A).inv).1
    rw [W.termPolynomialCoordinate_sections, map_zero]
    exact W.term_coordinates_one d _ k
  rw [coord_one] at hz
  exact hz

/-- Polynomial cyclic-coordinate data on the actual positive term, for a
cocharacter realizing a positive multiple q of the secondary weights. -/
def positiveTermCyclicCoordinates (v : I → ℤ) (q : ℕ)
    (hw : ∀ k, coPairing (ch (index k)) v = q * W.weight k) :
    NonnegativeCyclicCoordinates (W.termPolynomialCorepresentation 0)
      ((W.termPolynomialTorusAction j hroot hu 0).alongCocharacter v)
        (fun _ : PUnit => (1 : ℤ)) where
  dimension := Nat.card (W.support 0)
  weight k := q * W.weight (W.enumeration 0 k).val
  generator := X
  homogeneous k := by
    have h := isHomogeneous_alongCocharacter (W.termPolynomialCorepresentation 0)
      (W.termPolynomialTorusAction j hroot hu 0) v
        (W.isHomogeneous_termPolynomialVariable j hroot hu 0 k)
    have he : ((q * W.weight (W.enumeration 0 k).val) • (fun _ : PUnit => (1 : ℤ))) =
        (fun _ : PUnit => coPairing (ch (index (W.enumeration 0 k).val)) v) := by
      funext z
      simp only [Pi.smul_apply, nsmul_eq_mul, mul_one, hw, Nat.cast_mul]
    rw [he]
    exact h
  augmented := W.termPolynomialVariable_counit 0
  surjective := fun p => ⟨p, aeval_X_left_apply p⟩

/-- All the retained weights are strictly positive when q is positive. -/
theorem positiveTermCyclicCoordinates_positive (v : I → ℤ) (q : ℕ) (hq : 0 < q)
    (hw : ∀ k, coPairing (ch (index k)) v = q * W.weight k)
    (k : Fin (Nat.card (W.support 0))) :
    0 < (W.positiveTermCyclicCoordinates j hroot hu v q hw).weight k :=
  Nat.mul_pos hq (W.enumeration 0 k).property

end Langlands.GroupScheme.RelativeUnipotent.RootWeightData
