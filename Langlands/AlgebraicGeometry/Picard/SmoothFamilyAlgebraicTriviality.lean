import Langlands.AlgebraicGeometry.Picard.RelativePicardZero
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Algebraic triviality via actual smooth families -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- The map `a ↦ (c, a)` into the parameter-first product `C ×_S A`.
Its construction needs no smoothness hypothesis on the parameter. -/
def smoothFamilyPointMap (C : Over S) (c : Over.mk (𝟙 S) ⟶ C) :
    A.X.left ⟶ (relativeSpace A.X.hom).obj C :=
  pullback.lift (A.X.hom ≫ c.left) (𝟙 A.X.left) (by simp [Category.assoc, c.w])

@[simp] lemma smoothFamilyPointMap_fst (C : Over S) (c : Over.mk (𝟙 S) ⟶ C) :
    smoothFamilyPointMap A C c ≫ pullback.fst C.hom A.X.hom = A.X.hom ≫ c.left :=
  pullback.lift_fst _ _ _

@[simp] lemma smoothFamilyPointMap_snd (C : Over S) (c : Over.mk (𝟙 S) ⟶ C) :
    smoothFamilyPointMap A C c ≫ pullback.snd C.hom A.X.hom = 𝟙 A.X.left :=
  pullback.lift_snd _ _ _

/-- A smooth-family definition over an algebraically closed field: a line bundle
on an actual smooth separated finite-type geometrically integral parameter times
`A` restricts to the structure line bundle and to `L` at two rational points.
Comparisons with divisor algebraic equivalence and Picard components are separate. -/
def IsAlgebraicallyTrivialViaSmoothFamily
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (L : LineBundle A.X.left) : Prop :=
  ∃ C : Over (Spec (CommRingCat.of K)),
    Smooth C.hom ∧ IsSeparated C.hom ∧
    LocallyOfFiniteType C.hom ∧ QuasiCompact C.hom ∧ GeometricallyIntegral C.hom ∧
    ∃ (c0 c1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ C)
      (N : LineBundle ((relativeSpace A.X.hom).obj C)),
      Nonempty ((LineBundle.pullback (smoothFamilyPointMap A C c0)).obj N ≅
        LineBundle.trivial A.X.left) ∧
      Nonempty ((LineBundle.pullback (smoothFamilyPointMap A C c1)).obj N ≅ L)

/-- Transport the second restriction isomorphism, retaining the same actual family. -/
lemma isAlgebraicallyTrivialViaSmoothFamily_of_iso
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) {L M : LineBundle A.X.left}
    (e : L ≅ M) (hL : IsAlgebraicallyTrivialViaSmoothFamily A L) :
    IsAlgebraicallyTrivialViaSmoothFamily A M := by
  obtain ⟨C, hSm, hSep, hFt, hQc, hInt, c0, c1, N, h0, ⟨h1⟩⟩ := hL
  exact ⟨C, hSm, hSep, hFt, hQc, hInt, c0, c1, N, h0, ⟨h1 ≪≫ e⟩⟩

lemma isAlgebraicallyTrivialViaSmoothFamily_iff_of_iso
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) {L M : LineBundle A.X.left}
    (e : L ≅ M) :
    IsAlgebraicallyTrivialViaSmoothFamily A L ↔
      IsAlgebraicallyTrivialViaSmoothFamily A M :=
  ⟨isAlgebraicallyTrivialViaSmoothFamily_of_iso A e,
    isAlgebraicallyTrivialViaSmoothFamily_of_iso A e.symm⟩

/-- Every actual geometric-fibre restriction admits a smooth-family witness. -/
def IsFibrewiseAlgebraicallyTrivialViaSmoothFamily (L : LineBundle A.X.left) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S),
    IsAlgebraicallyTrivialViaSmoothFamily ((baseChange s).obj A) (fibreLineBundle A L s)

/-- Pull an actual bundle isomorphism back to each geometric fibre. -/
lemma isFibrewiseAlgebraicallyTrivialViaSmoothFamily_of_iso
    {L M : LineBundle A.X.left} (e : L ≅ M)
    (hL : IsFibrewiseAlgebraicallyTrivialViaSmoothFamily A L) :
    IsFibrewiseAlgebraicallyTrivialViaSmoothFamily A M := by
  intro K _ _ s
  exact isAlgebraicallyTrivialViaSmoothFamily_of_iso _
    ((LineBundle.pullback (pullback.fst A.X.hom s)).mapIso e) (hL K s)

lemma isFibrewiseAlgebraicallyTrivialViaSmoothFamily_iff_of_iso
    {L M : LineBundle A.X.left} (e : L ≅ M) :
    IsFibrewiseAlgebraicallyTrivialViaSmoothFamily A L ↔
      IsFibrewiseAlgebraicallyTrivialViaSmoothFamily A M :=
  ⟨isFibrewiseAlgebraicallyTrivialViaSmoothFamily_of_iso A e,
    isFibrewiseAlgebraicallyTrivialViaSmoothFamily_of_iso A e.symm⟩

/-- Apply the geometric-fibre smooth-family predicate to the existing underlying
bundle, transported from `T ×_S A` to `A ×_S T` by `familyLineBundle`. -/
def IsAlgebraicallyTrivialFamilyViaSmoothFamily {T : Over S}
    (L : RigidifiedFamily A T) : Prop :=
  IsFibrewiseAlgebraicallyTrivialViaSmoothFamily
    ((baseChange T.hom).obj A) (familyLineBundle A L)

/-- Forget a rigidified isomorphism and pull it across the existing product symmetry. -/
lemma isAlgebraicallyTrivialFamilyViaSmoothFamily_iff_of_iso
    {T : Over S} {L M : RigidifiedFamily A T} (e : L ≅ M) :
    IsAlgebraicallyTrivialFamilyViaSmoothFamily A L ↔
      IsAlgebraicallyTrivialFamilyViaSmoothFamily A M :=
  isFibrewiseAlgebraicallyTrivialViaSmoothFamily_iff_of_iso _
    ((LineBundle.pullback (relativeSpaceSymmetry A.X.hom T).inv).mapIso
      ((RigidifiedLineBundle.forget _).mapIso e))

/-- Descend the geometric-fibre smooth-family condition through actual rigidified
isomorphism to the existing quotient of rigidified families. -/
def IsAlgebraicallyTrivialClassViaSmoothFamily {T : Over S}
    (q : RigidifiedClasses A T) : Prop :=
  Quotient.lift (s := isIsomorphicSetoid (RigidifiedFamily A T))
    (IsAlgebraicallyTrivialFamilyViaSmoothFamily A)
    (fun _ _ ⟨e⟩ ↦ propext (isAlgebraicallyTrivialFamilyViaSmoothFamily_iff_of_iso A e)) q

/-- The descended predicate agrees with the condition on each actual representative. -/
@[simp] lemma isAlgebraicallyTrivialClassViaSmoothFamily_classOf
    {T : Over S} (L : RigidifiedFamily A T) :
    IsAlgebraicallyTrivialClassViaSmoothFamily A
      (RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) L) ↔
        IsAlgebraicallyTrivialFamilyViaSmoothFamily A L :=
  Iff.rfl

/-- Rigidified classes whose geometric fibres admit actual smooth-family witnesses. -/
abbrev AlgebraicallyTrivialClassesViaSmoothFamily (T : Over S) :=
  {q : RigidifiedClasses A T // IsAlgebraicallyTrivialClassViaSmoothFamily A q}

end Langlands.AbelianScheme
