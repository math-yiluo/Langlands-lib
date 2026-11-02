import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Rational.PointTopology

/-! # Rational points of a represented standard Levi

The representation witness identifies the same all-test subgroup functor used
by `standardLeviPoints`. Its rational-point equivalence is algebraic; compatibility
with the canonical and inherited topologies is a separate proposition.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (J : Set (characterLattice T))
  {M : GroupScheme (Spec (CommRingCat.of F))} (j : M ⟶ G)
  (hj : (standardLevi i ν J).IsRepresentedBy j)

/-- The actual inclusion on rational points, with codomain restricted using the
all-test equality in `hj`. -/
def standardLeviRationalPointsMap : rationalPoints M →* standardLeviPoints i ν J where
  toFun x := ⟨rationalPoints.map j x, by
    change rationalPoints.map j x ∈ (standardLevi i ν J).carrier _
    rw [← hj.2]
    exact ⟨x, rfl⟩⟩
  map_one' := Subtype.ext (map_one (rationalPoints.map j))
  map_mul' x y := Subtype.ext (map_mul (rationalPoints.map j) x y)

@[simp] theorem standardLeviRationalPointsMap_val (x : rationalPoints M) :
    (standardLeviRationalPointsMap i ν J j hj x : rationalPoints G) =
      rationalPoints.map j x := rfl

/-- A representation is mono and has the specified image on every test scheme;
on the identity test these give injectivity and surjectivity, respectively. -/
theorem standardLeviRationalPointsMap_bijective :
    Function.Bijective (standardLeviRationalPointsMap i ν J j hj) := by
  have : Mono j.hom.hom := hj.1
  constructor
  · intro x y h
    apply (cancel_mono j.hom.hom).1
    exact congrArg Subtype.val h
  · rintro ⟨g, hg⟩
    change g ∈ (standardLevi i ν J).carrier _ at hg
    rw [← hj.2] at hg
    obtain ⟨x, hx⟩ := hg
    exact ⟨x, Subtype.ext hx⟩

/-- The rational points of the represented group scheme are the actual standard
Levi subgroup of `G(F)`. The forward function is postcomposition with `j`. -/
def standardLeviRationalPointsEquiv :
    rationalPoints M ≃* standardLeviPoints i ν J :=
  MulEquiv.ofBijective (standardLeviRationalPointsMap i ν J j hj)
    (standardLeviRationalPointsMap_bijective i ν J j hj)

@[simp] theorem standardLeviRationalPointsEquiv_val (x : rationalPoints M) :
    (standardLeviRationalPointsEquiv i ν J j hj x : rationalPoints G) =
      rationalPoints.map j x := rfl

variable [TopologicalSpace F] [IsAffine G.X.left]

/-- The topology inherited by the actual standard Levi subgroup of `G(F)` from
the canonical rational-point topology of `G`. No global instance is installed. -/
@[instance_reducible]
def standardLeviPointTopology : TopologicalSpace (standardLeviPoints i ν J) :=
  TopologicalSpace.induced
    (fun x : standardLeviPoints i ν J => (x : rationalPoints G))
    (rationalPointTopology F G.X)

variable [IsAffine M.X.left]

/-- The explicit rational-point equivalence is a homeomorphism from the
canonical point topology of the represented scheme to the inherited topology
on `standardLeviPoints`. This is a target, not an assumed property of `hj`. -/
def StandardLeviPointTopologyComparison : Prop :=
  letI : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
  letI : TopologicalSpace (standardLeviPoints i ν J) := standardLeviPointTopology i ν J
  IsHomeomorph (standardLeviRationalPointsEquiv i ν J j hj)

/-- Canonical versus inherited topology for every closed representation of a
standard Levi of an actual connected reductive group over a topological field. -/
def StandardLeviPointTopologyComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [TopologicalSpace F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (_hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    IsGenericCocharacter i ν →
    ∀ (J : Set (characterLattice T)), J ⊆ simpleRelativeRoots i ν →
    ∀ (M : GroupScheme (Spec (CommRingCat.of F))) (hM : IsConnectedReductive M)
      (j : M ⟶ G), IsClosedSubgroup j →
    ∀ hj : (standardLevi i ν J).IsRepresentedBy j,
      haveI := hM.isAffineHom
      haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
      StandardLeviPointTopologyComparison i ν J j hj

end Langlands.GroupScheme
