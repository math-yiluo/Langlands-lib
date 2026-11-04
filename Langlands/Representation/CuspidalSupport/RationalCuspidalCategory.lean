import Langlands.Representation.CuspidalSupport.RationalInertiaDecompositionStatement

/-!
# The whole cuspidal factors of Renard VI.3.5

The all/no cuspidal factors quantify over arbitrary actual subquotients.
Inertia factors quantify over irreducible actual subquotients. The index of
cuspidal inertia factors is a subtype of the existing actual inertia quotient,
with an existential cuspidal representative. No representative is chosen and
no category decomposition is proved.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

variable [LocallyCompactSpace (GroupScheme.rationalPoints G)]
  [NonarchimedeanGroup (GroupScheme.rationalPoints G)]
variable {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]
  (h : ∀ I, IsSemidirectDecomposition
    (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (GroupScheme.rationalPoints G)))

/-- All actual subquotients are cuspidal for the proper actual standard family.
There is no irreducibility or finite-length restriction on the subquotient. -/
def rationalAllCuspidalSubquotientProperty :
    ObjectProperty (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :=
  fun A => ∀ D : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G),
    SmoothRep.IsSubquotient D A →
      IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU D

/-- No nonzero actual subquotient is cuspidal. Nontriviality excludes the zero
subquotient, whose Jacquet modules vanish. -/
def rationalNoCuspidalSubquotientProperty :
    ObjectProperty (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :=
  fun A => ∀ D : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G),
    Nontrivial D → SmoothRep.IsSubquotient D A →
      ¬ IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU D

/-- The full category denoted `M(G)_sc` in VI.3.5. -/
abbrev RationalWholeCuspidalCategory :=
  (rationalAllCuspidalSubquotientProperty.{uF, uV} G i ν h hU).FullSubcategory

/-- The full category denoted `M(G)_ind` in VI.3.5. -/
abbrev RationalNoncuspidalCategory :=
  (rationalNoCuspidalSubquotientProperty.{uF, uV} G i ν h hU).FullSubcategory

/-- The two whole-category factors, with the cuspidal factor indexed by `true`. -/
def rationalWholeCuspidalDecompositionProperties :
    Bool → ObjectProperty (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
  | true => rationalAllCuspidalSubquotientProperty G i ν h hU
  | false => rationalNoCuspidalSubquotientProperty G i ν h hU

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
@[simp]
theorem rationalWholeCuspidalDecompositionProperties_true :
    rationalWholeCuspidalDecompositionProperties.{uF, uV} G i ν h hU true =
      rationalAllCuspidalSubquotientProperty G i ν h hU := rfl

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
@[simp]
theorem rationalWholeCuspidalDecompositionProperties_false :
    rationalWholeCuspidalDecompositionProperties.{uF, uV} G i ν h hU false =
      rationalNoCuspidalSubquotientProperty G i ν h hU := rfl

/-- The first category-decomposition assertion of VI.3.5, without a proof. -/
def IsRationalWholeCuspidalCategoryDecomposition : Prop :=
  Renard.IsCategoryDecomposition
    (rationalWholeCuspidalDecompositionProperties.{uF, uV} G i ν h hU)

/-- The cuspidal part of the existing inertia quotient. Membership asks for an
actual irreducible cuspidal representative and does not select one. -/
def RationalCuspidalInertiaClass :=
  {c : RationalIrreducibleInertiaClass.{uF, uV} G //
    ∃ (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
      (hπ : π.IsIrreducible),
      IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU π ∧
        rationalIrreducibleInertiaClass G π hπ = c}

/-- An irreducible actual cuspidal object determines a cuspidal inertia class. -/
def rationalCuspidalInertiaClass
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (hπ : π.IsIrreducible)
    (hc : IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU π) :
    RationalCuspidalInertiaClass.{uF, uV} G i ν h hU :=
  ⟨rationalIrreducibleInertiaClass G π hπ, π, hπ, hc, rfl⟩

@[simp]
theorem rationalCuspidalInertiaClass_val
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (hπ : π.IsIrreducible)
    (hc : IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU π) :
    (rationalCuspidalInertiaClass G i ν h hU π hπ hc).val =
      rationalIrreducibleInertiaClass G π hπ := rfl

/-- Every irreducible actual subquotient has the specified inertia class. -/
def rationalCuspidalInertiaClassBlockProperty
    (c : RationalCuspidalInertiaClass.{uF, uV} G i ν h hU) :
    ObjectProperty (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :=
  fun A => ∀ (D : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (hD : D.IsIrreducible), SmoothRep.IsSubquotient D A →
      rationalIrreducibleInertiaClass G D hD = c.val

/-- The inertia factors and the remaining noncuspidal factor of VI.3.5.
`none` denotes the noncuspidal factor; `some c` denotes the inertia factor `c`. -/
def rationalCuspidalInertiaProductProperties :
    Option (RationalCuspidalInertiaClass.{uF, uV} G i ν h hU) →
      ObjectProperty (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
  | none => rationalNoCuspidalSubquotientProperty G i ν h hU
  | some c => rationalCuspidalInertiaClassBlockProperty G i ν h hU c

@[simp]
theorem rationalCuspidalInertiaProductProperties_none :
    rationalCuspidalInertiaProductProperties.{uF, uV} G i ν h hU none =
      rationalNoCuspidalSubquotientProperty G i ν h hU := rfl

@[simp]
theorem rationalCuspidalInertiaProductProperties_some
    (c : RationalCuspidalInertiaClass.{uF, uV} G i ν h hU) :
    rationalCuspidalInertiaProductProperties G i ν h hU (some c) =
      rationalCuspidalInertiaClassBlockProperty G i ν h hU c := rfl

/-- The refined whole-category decomposition of VI.3.5, without a proof. -/
def IsRationalCuspidalInertiaProductDecomposition : Prop :=
  Renard.IsCategoryDecomposition
    (rationalCuspidalInertiaProductProperties.{uF, uV} G i ν h hU)

variable {G i ν h hU}
  {A B : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)}

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The all-cuspidal property is closed under actual subquotients. -/
theorem rationalAllCuspidalSubquotientProperty_of_isSubquotient
    (hA : rationalAllCuspidalSubquotientProperty G i ν h hU A)
    (hBA : SmoothRep.IsSubquotient B A) :
    rationalAllCuspidalSubquotientProperty G i ν h hU B :=
  fun D hDB => hA D (smoothSubquotientTransitivity ℂ _ A B D hDB hBA)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The no-cuspidal property is closed under actual subquotients. -/
theorem rationalNoCuspidalSubquotientProperty_of_isSubquotient
    (hA : rationalNoCuspidalSubquotientProperty G i ν h hU A)
    (hBA : SmoothRep.IsSubquotient B A) :
    rationalNoCuspidalSubquotientProperty G i ν h hU B :=
  fun D hD hDB => hA D hD (smoothSubquotientTransitivity ℂ _ A B D hDB hBA)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The all-cuspidal property is invariant under ambient isomorphism. -/
theorem rationalAllCuspidalSubquotientProperty_of_iso
    (hA : rationalAllCuspidalSubquotientProperty G i ν h hU A) (e : B ≅ A) :
    rationalAllCuspidalSubquotientProperty G i ν h hU B :=
  fun D hDB => hA D (hDB.of_iso_right e)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The no-cuspidal property is invariant under ambient isomorphism. -/
theorem rationalNoCuspidalSubquotientProperty_of_iso
    (hA : rationalNoCuspidalSubquotientProperty G i ν h hU A) (e : B ≅ A) :
    rationalNoCuspidalSubquotientProperty G i ν h hU B :=
  fun D hD hDB => hA D hD (hDB.of_iso_right e)

/-- A represented class gives exactly the already published inertia-block
property. This is a quotient-equality comparison, without a cuspidal theorem. -/
theorem rationalCuspidalInertiaClassBlockProperty_iff
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (hπ : π.IsIrreducible)
    (hc : IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU π) :
    rationalCuspidalInertiaClassBlockProperty G i ν h hU
        (rationalCuspidalInertiaClass G i ν h hU π hπ hc) A ↔
      rationalInertiaBlockProperty G π A := by
  constructor
  · intro hA D hD hDA
    exact (rationalIrreducibleInertiaClass_eq_iff G π D hπ hD).mp
      (hA D hD hDA).symm
  · intro hA D hD hDA
    exact ((rationalIrreducibleInertiaClass_eq_iff G π D hπ hD).mpr
      (hA D hD hDA)).symm

end Langlands.CuspidalSupport
