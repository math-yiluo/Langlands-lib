import Langlands.GroupScheme.Torus.CharacterActionGrading
import Langlands.GroupScheme.AffineCorepresented
import Langlands.GroupScheme.AutomorphicAction

/-! # Actual diagonalizable actions in affine coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace AffineCoordinates

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffine G.X.left]

/-- The underlying affine-scheme comparison of the coordinate cogroup. -/
def coordinateSchemeIso : (algSpec R).obj (op (algebra G)) ≅ G.X :=
  (Grp.forget _).mapIso (coordinateCogroupIso G)

/-- Coordinate algebra maps are actual affine scheme points of the given group. -/
def pointEquiv (C : CommAlgCat.{u} R) :
    (algebra G ⟶ C) ≃ ((algSpec R).obj (op C) ⟶ G.X) where
  toFun x := (algSpec R).map x.op ≫ (coordinateSchemeIso G).hom
  invFun x := (algSpec.fullyFaithful.preimage
    (x ≫ (coordinateSchemeIso G).inv)).unop
  left_inv x := by
    apply Quiver.Hom.op_inj
    apply (algSpec R).map_injective
    rw [Quiver.Hom.op_unop, algSpec.fullyFaithful.map_preimage]
    simp
  right_inv x := by
    change (algSpec R).map
      ((algSpec.fullyFaithful.preimage (x ≫ (coordinateSchemeIso G).inv)).unop).op ≫
        (coordinateSchemeIso G).hom = x
    rw [Quiver.Hom.op_unop, algSpec.fullyFaithful.map_preimage]
    simp

/-- Refining an affine coordinate point is precomposition by its spectrum map. -/
theorem pointEquiv_comp {C D : CommAlgCat.{u} R} (x : algebra G ⟶ C) (f : C ⟶ D) :
    pointEquiv G D (x ≫ f) = (algSpec R).map f.op ≫ pointEquiv G C x := by
  change (algSpec R).map (f.op ≫ x.op) ≫ _ = _
  rw [Functor.map_comp, Category.assoc]
  rfl

end AffineCoordinates

namespace CharacterAction

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]

/-- The actual diagonalizable-group point specified by a character over an algebra. -/
abbrev characterPoint {C : CommAlgCat.{u} R} (t : Multiplicative M →* Cˣ) :
    (algSpec R).obj (op C) ⟶ (Diagonalizable.groupScheme R M).X :=
  (Corepresented.affinePointsEquiv (Diagonalizable.functor R M)
    (Diagonalizable.grpCorepresentation R M) C).symm t

@[simp] theorem characterPoint_one (C : CommAlgCat.{u} R) :
    characterPoint (1 : Multiplicative M →* Cˣ) = 1 :=
  map_one _

@[simp] theorem characterPoint_mul {C : CommAlgCat.{u} R}
    (t s : Multiplicative M →* Cˣ) :
    characterPoint (t * s) = characterPoint t * characterPoint s :=
  map_mul _ _ _

/-- Character restriction is the actual pullback of its scheme point. -/
theorem characterPoint_mapCharacter {C D : CommAlgCat.{u} R} (f : C ⟶ D)
    (t : Multiplicative M →* Cˣ) :
    characterPoint (mapCharacter f t) = (algSpec R).map f.op ≫ characterPoint t := by
  apply (Corepresented.affinePointsEquiv (Diagonalizable.functor R M)
    (Diagonalizable.grpCorepresentation R M) D).injective
  unfold characterPoint
  rw [MulEquiv.apply_symm_apply, Corepresented.affinePointsEquiv_naturality,
    MulEquiv.apply_symm_apply]
  rfl

variable {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  (a : AutomorphicAction (Diagonalizable.groupScheme R M).toGrp G)

/-- The coordinate action induced by an actual diagonalizable group-scheme action. -/
def ofAutomorphicAction : Action (M := M) (AffineCoordinates.algebra G) where
  act {C} t x := (AffineCoordinates.pointEquiv G C).symm
    (a.act (characterPoint t) (AffineCoordinates.pointEquiv G C x))
  one {C} x := by
    apply (AffineCoordinates.pointEquiv G C).injective
    simp only [Equiv.apply_symm_apply, characterPoint_one, a.act_one_left]
  mul {C} t s x := by
    apply (AffineCoordinates.pointEquiv G C).injective
    simp only [Equiv.apply_symm_apply, characterPoint_mul, a.act_mul_left]
  naturality {C D} f t x := by
    apply (AffineCoordinates.pointEquiv G D).injective
    simp only [Equiv.apply_symm_apply, AffineCoordinates.pointEquiv_comp,
      characterPoint_mapCharacter, ← a.naturality]

/-- The coordinate action recovers the actual action on affine scheme points. -/
theorem pointEquiv_act {C : CommAlgCat.{u} R} (t : Multiplicative M →* Cˣ)
    (x : AffineCoordinates.algebra G ⟶ C) :
    AffineCoordinates.pointEquiv G C ((ofAutomorphicAction a).act t x) =
      a.act (characterPoint t) (AffineCoordinates.pointEquiv G C x) :=
  Equiv.apply_symm_apply _ _

end CharacterAction

namespace AutomorphicAction

variable {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)}
  [IsAffine H.X.left] (a : AutomorphicAction H G)

/-- On an affine test scheme, all-test fixedness can be checked using every affine
algebra refinement. The universal acting test is affine. -/
theorem isFixed_iff_affineRefinements {C : CommAlgCat.{u} R}
    (g : (algSpec R).obj (op C) ⟶ G.X) :
    a.IsFixed g ↔
      ∀ (D : CommAlgCat.{u} R) (f : C ⟶ D)
        (h : (algSpec R).obj (op D) ⟶ H.X),
        a.act h ((algSpec R).map f.op ≫ g) = (algSpec R).map f.op ≫ g := by
  constructor
  · intro hg D f h
    exact hg _ ((algSpec R).map f.op) h
  · intro hg
    rw [a.isFixed_iff_universal]
    let T := (algSpec R).obj (op C)
    let : IsAffine T.left := by
      change IsAffine (Spec (CommRingCat.of C))
      infer_instance
    have : IsAffine (T ⊗ H.X).left := by
      change IsAffine (CategoryTheory.Limits.pullback T.hom H.X.hom)
      infer_instance
    have hW : (algSpec R).essImage (T ⊗ H.X) := essImage_algSpec.mpr (by infer_instance)
    let D := hW.witness.unop
    let e : (algSpec R).obj (op D) ≅ T ⊗ H.X := hW.getIso
    let f : C ⟶ D := (algSpec.fullyFaithful.preimage
      (e.hom ≫ fst T H.X)).unop
    have he : (algSpec R).map f.op = e.hom ≫ fst T H.X :=
      algSpec.fullyFaithful.map_preimage _
    have h := hg D f (e.hom ≫ snd T H.X)
    rw [he, Category.assoc] at h
    apply (cancel_epi e.hom).1
    rw [a.naturality, ← Category.assoc]
    exact h

end AutomorphicAction

namespace CharacterAction

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  (a : AutomorphicAction (Diagonalizable.groupScheme R M).toGrp G)

/-- The coordinate fixed condition retains fixedness on every scheme refinement. -/
theorem isFixed_iff_scheme {C : CommAlgCat.{u} R}
    (x : AffineCoordinates.algebra G ⟶ C) :
    IsFixed (ofAutomorphicAction a) x ↔
      a.IsFixed (AffineCoordinates.pointEquiv G C x) := by
  let : IsAffine (Diagonalizable.groupScheme R M).X.left := by
    change IsAffine (Spec (CommRingCat.of (AddMonoidAlgebra R M)))
    infer_instance
  rw [a.isFixed_iff_affineRefinements]
  constructor
  · intro hx D f h
    let t := Corepresented.affinePointsEquiv (Diagonalizable.functor R M)
      (Diagonalizable.grpCorepresentation R M) D h
    have ht : characterPoint t = h := MulEquiv.symm_apply_apply _ h
    have e := congrArg (AffineCoordinates.pointEquiv G D) (hx D f t)
    rw [pointEquiv_act, AffineCoordinates.pointEquiv_comp, ht] at e
    exact e
  · intro hx D f t
    apply (AffineCoordinates.pointEquiv G D).injective
    rw [pointEquiv_act, AffineCoordinates.pointEquiv_comp]
    exact hx D f (characterPoint t)

/-- The coordinate ideal imposing the actual all-test fixed subgroup. -/
abbrev schemeFixedIdeal : Ideal (AffineCoordinates.algebra G) :=
  Langlands.CommutativeAlgebra.GradedFixedQuotient.fixedIdeal
    (coaction (ofAutomorphicAction a)).hom.toRingHom

/-- The fixed ideal cuts out the existing fixed subgroup on every affine test. -/
theorem schemeFixedIdeal_le_ker_iff {C : CommAlgCat.{u} R}
    (x : AffineCoordinates.algebra G ⟶ C) :
    schemeFixedIdeal a ≤ RingHom.ker x.hom.toRingHom ↔
      AffineCoordinates.pointEquiv G C x ∈
        a.fixedSubgroup.carrier ((algSpec R).obj (op C)) := by
  rw [AutomorphicAction.mem_fixedSubgroup, ← isFixed_iff_scheme,
    ← fixedIdeal_le_ker_iff_isFixed]

/-- The actual fixed-locus coordinate quotient is formally smooth. -/
theorem formallySmooth_schemeFixedQuotient
    [Algebra.FormallySmooth R (AffineCoordinates.algebra G)] :
    Algebra.FormallySmooth R (AffineCoordinates.algebra G ⧸ schemeFixedIdeal a) :=
  formallySmooth_fixedQuotient (ofAutomorphicAction a)

/-- Conjugation gives the coordinate ideal of the published torus centralizer. -/
abbrev centralizerIdeal (i : (Diagonalizable.groupScheme R M).toGrp ⟶ G) :
    Ideal (AffineCoordinates.algebra G) :=
  schemeFixedIdeal (AutomorphicAction.conjugation i)

/-- These equations characterize the published centralizer, including all
scheme refinements of the affine test. -/
theorem centralizerIdeal_le_ker_iff
    (i : (Diagonalizable.groupScheme R M).toGrp ⟶ G)
    {C : CommAlgCat.{u} R} (x : AffineCoordinates.algebra G ⟶ C) :
    centralizerIdeal i ≤ RingHom.ker x.hom.toRingHom ↔
      AffineCoordinates.pointEquiv G C x ∈
        (torusCentralizer i).carrier ((algSpec R).obj (op C)) := by
  rw [← AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer]
  exact schemeFixedIdeal_le_ker_iff _ x

/-- Formal smoothness of the coordinate algebra passes to the centralizer
coordinate quotient. -/
theorem formallySmooth_centralizerQuotient
    (i : (Diagonalizable.groupScheme R M).toGrp ⟶ G)
    [Algebra.FormallySmooth R (AffineCoordinates.algebra G)] :
    Algebra.FormallySmooth R (AffineCoordinates.algebra G ⧸ centralizerIdeal i) :=
  formallySmooth_schemeFixedQuotient (AutomorphicAction.conjugation i)

end CharacterAction

end Langlands.GroupScheme
