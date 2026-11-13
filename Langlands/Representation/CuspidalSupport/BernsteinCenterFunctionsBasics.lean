import Langlands.Representation.Classification.SegmentHeadSupportGeneric
import Langlands.Representation.CuspidalSupport.BernsteinCenterFunctionsStatements
import Langlands.Representation.CuspidalSupport.BernsteinJacquetInertiaExclusion
import Langlands.Representation.Aubert.General.RationalStandardInductionNonzero
import Langlands.Representation.Category.IrreducibleSubquotientExistence
import Langlands.Representation.Classification.SupercuspidalSupport

/-! # Unconditional facts used for Renard VI.10.4

* A central element of a category over smooth representations that acts by a scalar on an
  object acts by the same scalar on its images and on its subobjects; for a full subcategory
  closed under subquotients it acts by that scalar on every subquotient. Two scalars by which a
  central element acts on a nonzero object agree.
* For a cuspidal datum `a = (M, ρ)` and `ω ∈ X(M)`, the twisted datum `(M, ρ ⊗ ω)` is an
  inertially equivalent cuspidal datum whose induction is literally `i_P^G(ρ ⊗ ω)`; hence
  `i_P^G(ρ ⊗ ω)` lies in the saturated Bernstein block of `a` and is nonzero.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.SmoothRep

universe uG uV w w'

section CenterScalar

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {C : Type w} [Category.{w'} C] (Φ : C ⥤ SmoothRep.{0, uG, uV} ℂ G) (z : CatCenter C)

/-- A central element acting by `c` on the source of a morphism whose underlying map is
surjective acts by `c` on its target. -/
theorem centerScalar_of_surjective {A B : C} (f : A ⟶ B)
    (hf : Function.Surjective (hom (Φ.map f))) {c : ℂ}
    (hA : ∀ x, hom (Φ.map (z.app A)) x = c • x) :
    ∀ y, hom (Φ.map (z.app B)) y = c • y := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  have h := congrArg (fun g => hom (Φ.map g) x) (z.naturality f)
  simp only [Functor.map_comp] at h
  change hom (Φ.map (z.app B)) (hom (Φ.map f) x) =
    hom (Φ.map f) (hom (Φ.map (z.app A)) x) at h
  rw [h, hA, map_smul]

/-- A central element acting by `c` on the target of a morphism whose underlying map is
injective acts by `c` on its source. -/
theorem centerScalar_of_injective {A B : C} (f : A ⟶ B)
    (hf : Function.Injective (hom (Φ.map f))) {c : ℂ}
    (hB : ∀ y, hom (Φ.map (z.app B)) y = c • y) :
    ∀ x, hom (Φ.map (z.app A)) x = c • x := by
  intro x
  apply hf
  have h := congrArg (fun g => hom (Φ.map g) x) (z.naturality f)
  simp only [Functor.map_comp] at h
  change hom (Φ.map (z.app B)) (hom (Φ.map f) x) =
    hom (Φ.map f) (hom (Φ.map (z.app A)) x) at h
  rw [← h, hB, map_smul]

/-- Two scalars by which the same endomorphism acts on a nonzero object agree. -/
theorem scalar_unique {A : SmoothRep.{0, uG, uV} ℂ G} [Nontrivial A] (g : A ⟶ A) {c d : ℂ}
    (hc : ∀ x, hom g x = c • x) (hd : ∀ x, hom g x = d • x) : c = d := by
  obtain ⟨x, hx⟩ := exists_ne (0 : A)
  have h : c • x = d • x := (hc x).symm.trans (hd x)
  by_contra hcd
  apply hx
  have h' : (c - d) • x = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hcd)

end CenterScalar

section CenterScalarSubquotient

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A central element of the category of smooth representations acting by `c` on `V` acts by
`c` on every subquotient of `V`. -/
theorem centerScalar_of_isSubquotient (z : CatCenter (SmoothRep.{0, uG, uV} ℂ G))
    {V W : SmoothRep.{0, uG, uV} ℂ G} (hWV : IsSubquotient W V) {c : ℂ}
    (hV : ∀ x, hom (z.app V) x = c • x) : ∀ y, hom (z.app W) y = c • y := by
  obtain ⟨D, j, q, hj, hq⟩ := isSubquotient_iff_exists.mp hWV
  exact centerScalar_of_surjective (𝟭 (SmoothRep.{0, uG, uV} ℂ G)) z q hq
    (centerScalar_of_injective (𝟭 (SmoothRep.{0, uG, uV} ℂ G)) z j hj hV)

/-- For a full subcategory closed under subquotients, a central element acting by `c` on an
object `V` acts by `c` on every subquotient of `V`. -/
theorem fullSubcategory_centerScalar_of_isSubquotient
    {P : ObjectProperty (SmoothRep.{0, uG, uV} ℂ G)}
    (hP : ∀ {V W : SmoothRep.{0, uG, uV} ℂ G}, P V → IsSubquotient W V → P W)
    (z : CatCenter P.FullSubcategory)
    {V W : SmoothRep.{0, uG, uV} ℂ G} (hV : P V) (hW : P W) (hWV : IsSubquotient W V) {c : ℂ}
    (hzV : ∀ x, hom (z.app ⟨V, hV⟩).hom x = c • x) :
    ∀ y, hom (z.app ⟨W, hW⟩).hom y = c • y := by
  obtain ⟨D, j, q, hj, hq⟩ := isSubquotient_iff_exists.mp hWV
  have hD : P D := hP hV (IsSubrepresentation.isSubquotient ⟨j, hj⟩)
  have hDsc := centerScalar_of_injective P.ι z
    (A := ⟨D, hD⟩) (B := ⟨V, hV⟩) (ObjectProperty.homMk j) hj hzV
  exact centerScalar_of_surjective P.ι z
    (A := ⟨D, hD⟩) (B := ⟨W, hW⟩) (ObjectProperty.homMk q) hq hDsc

end CenterScalarSubquotient

end Langlands.SmoothRep

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance instBernsteinCenterFunctionsBasicsAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance instBernsteinCenterFunctionsBasicsTopology :
    TopologicalSpace (rationalPoints G) := pointTopology
local instance instBernsteinCenterFunctionsBasicsLeviClosedImmersion
    (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance instBernsteinCenterFunctionsBasicsLeviAffine (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance instBernsteinCenterFunctionsBasicsLeviFiniteType
    (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance instBernsteinCenterFunctionsBasicsLeviTopology (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- The unramified twist `(M, ρ ⊗ ω)` of a cuspidal datum `(M, ρ)` by `ω ∈ X(M)`: the same
standard Levi with the twisted representation, which is again irreducible and cuspidal. -/
def BernsteinCuspidalDatum.unramifiedTwist (a : BernsteinCuspidalDatum.{uF, uV} i ν family)
    (ω : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)) :
    BernsteinCuspidalDatum.{uF, uV} i ν family :=
  a.replaceInertia i ν family
    (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation)
    ((isIrreducible_rationalUnramifiedTwist_iff _ ω a.representation).mpr a.irreducible)
    ⟨ω, ⟨Iso.refl _⟩⟩

@[simp] theorem BernsteinCuspidalDatum.unramifiedTwist_roots
    (a : BernsteinCuspidalDatum.{uF, uV} i ν family)
    (ω : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)) :
    (a.unramifiedTwist i ν family ω).roots = a.roots := rfl

/-- A twist of a cuspidal datum is inertially equivalent to it. -/
theorem BernsteinCuspidalDatum.inertia_unramifiedTwist
    (a : BernsteinCuspidalDatum.{uF, uV} i ν family)
    (ω : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)) :
    IsBernsteinInertiaRelated i ν family a (a.unramifiedTwist i ν family ω) :=
  a.inertia_replaceInertia i ν family _ _ _

/-- A twist of a cuspidal datum has the same inertial class. -/
theorem bernsteinInertialClass_unramifiedTwist
    (a : BernsteinCuspidalDatum.{uF, uV} i ν family)
    (ω : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)) :
    bernsteinInertialClass i ν family (a.unramifiedTwist i ν family ω) =
      bernsteinInertialClass i ν family a :=
  ((bernsteinInertialClass_eq_iff i ν family a _).mpr
    (a.inertia_unramifiedTwist i ν family ω)).symm

/-- Replacing the representation of a cuspidal datum by an inertially equivalent one changes its
induction to the induction of the new representation. -/
theorem bernsteinInduction_replaceInertia (b : BernsteinCuspidalDatum.{uF, uV} i ν family)
    (D : SmoothRep.{0, uF, uV} ℂ (rationalPoints (bernsteinLeviScheme i ν b.roots)))
    (hD : D.IsIrreducible)
    (hbD : IsRationalInertiaRelated (bernsteinLeviScheme i ν b.roots) b.representation D) :
    bernsteinInduction i ν family (b.replaceInertia i ν family D hD hbD) =
      (normalizedInductionFunctor (family.decomposition b.roots)
        (family.closedUnipotent b.roots)).obj (bernsteinLiteralLeviRep i ν b.roots D) := by
  dsimp only [bernsteinInduction, BernsteinCuspidalDatum.replaceInertia]

/-- The induction of the twisted datum is literally `i_P^G(ρ ⊗ ω)`. -/
theorem bernsteinInduction_unramifiedTwist
    (a : BernsteinCuspidalDatum.{uF, uV} i ν family)
    (ω : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)) :
    bernsteinInduction i ν family (a.unramifiedTwist i ν family ω) =
      (normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj
          (bernsteinLiteralLeviRep i ν a.roots
            (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation)) :=
  bernsteinInduction_replaceInertia i ν family a _ _ _

/-- Every `i_P^G(ρ ⊗ ω)`, `ω ∈ X(M)`, lies in the saturated Bernstein block of the inertial
class of `(M, ρ)` (used for Renard VI.10.4, Remarks 1–2). -/
theorem twistInduction_mem_saturatedBlock
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ω : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)) :
    bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
      ((normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj
          (bernsteinLiteralLeviRep i ν a.roots
            (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation))) := by
  have h := bernsteinInduction_mem_saturatedBlock i ν family (a.unramifiedTwist i ν family ω)
  rw [bernsteinInertialClass_unramifiedTwist, bernsteinInduction_unramifiedTwist] at h
  exact h

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The normalized induction of an actual cuspidal datum is nonzero. -/
theorem nontrivial_bernsteinInduction (a : BernsteinCuspidalDatum.{uF, uV} i ν family) :
    Nontrivial (bernsteinInduction i ν family a) := by
  have hproj := continuous_standard_projection i ν standardCocharacter
    family.connectedReductive family.maximalSplitTorus family.genericCocharacter a.roots
  have : Nontrivial a.representation := Langlands.Classification.SegmentHeadSupport.nontrivial_of_isIrreducible a.irreducible
  have : Nontrivial (bernsteinLiteralLeviRep i ν a.roots a.representation) := this
  exact nontrivial_normalizedInduction (family.decomposition a.roots)
    (family.closedUnipotent a.roots) hproj _

end Langlands.CuspidalSupport
