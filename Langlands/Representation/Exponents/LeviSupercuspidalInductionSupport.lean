import Langlands.Representation.Exponents.LeviFrobeniusReciprocityProof
import Langlands.Representation.Exponents.LeviInductionNoSupercuspidalSubquotientStatement
import Langlands.Representation.Classification.SupercuspidalSupport
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Cuspidal splittings and proper represented induction

The first-adjointness consequence is unconditional. Exclusion of subquotients
additionally consumes a cuspidal/remainder splitting, whose existence is not
proved in this module.
-/

noncomputable section

universe u v w

open CategoryTheory Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance supercuspidalAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Supercuspidality tested on every proper actual rational parabolic, using
exactly the normalized Jacquet functors of the represented interface. -/
def IsSupercuspidal (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)) : Prop :=
  ∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)),
    ¬ IsIso p → Subsingleton ((jacquetFunctor p l r hp hr hl hmul).obj A)

/-- A local consequence of the two-factor decomposition of Renard VI.3.5:
a binary coproduct with a supercuspidal component and a component having no
nonzero supercuspidal actual subquotient. Existence is not asserted here. -/
def HasCuspidalRemainderSplitting
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)) : Prop :=
  ∃ (Y : Bool → SmoothRep.{0, u, v} ℂ (rationalPoints G)) (j : ∀ b, Y b ⟶ A),
    IsSupercuspidal (Y true) ∧
      (∀ D : SmoothRep.{0, u, v} ℂ (rationalPoints G),
        Nontrivial D → SmoothRep.IsSubquotient D (Y false) → ¬ IsSupercuspidal D) ∧
      Nonempty (IsColimit (Cofan.mk A j))

/-- Vanishing of maps from all supercuspidal objects, together with the supplied
actual splitting, excludes every nonzero supercuspidal actual subquotient. -/
theorem no_supercuspidal_subquotient_of_splitting
    {A : SmoothRep.{0, u, v} ℂ (rationalPoints G)}
    (hsplit : HasCuspidalRemainderSplitting A)
    (hHom : ∀ (C : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      IsSupercuspidal C → ∀ f : C ⟶ A, f = 0)
    (D : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (hD : Nontrivial D)
    (hDA : SmoothRep.IsSubquotient D A) : ¬ IsSupercuspidal D := by
  obtain ⟨Y, j, hC, hR, ⟨hc⟩⟩ := hsplit
  have hj : j true = 0 := hHom (Y true) hC (j true)
  let f : ∀ b, Y b ⟶ Y false := fun b => match b with
    | false => 𝟙 (Y false)
    | true => 0
  let p : A ⟶ Y false := Cofan.IsColimit.desc hc f
  have hjp : j false ≫ p = 𝟙 (Y false) := by
    exact Cofan.IsColimit.fac hc f false
  have hpj : p ≫ j false = 𝟙 A := by
    apply Cofan.IsColimit.hom_ext hc
    intro b
    change j b ≫ (p ≫ j false) = j b ≫ 𝟙 A
    rw [← Category.assoc]
    change ((Cofan.mk A j).inj b ≫ Cofan.IsColimit.desc hc f) ≫ j false = _
    rw [Cofan.IsColimit.fac]
    cases b <;> simp [f, hj]
  let e : A ≅ Y false := ⟨p, j false, hpj, hjp⟩
  exact hR D hD (hDA.of_iso_right e)

section LocalField

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]
  (hG : IsConnectedReductive G)
  {P M U : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))

include hG

/-- The exact represented Frobenius reciprocity theorem annihilates every map
into induction when the corresponding normalized Jacquet module is zero.
The ambient and inducing carrier universes are independent. -/
theorem hom_induction_eq_zero_of_jacquet_subsingleton
    (A : SmoothRep.{0, u, w} ℂ (rationalPoints G))
    (hA : Subsingleton ((jacquetFunctor p l r hp hr hl hmul).obj A)) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    ∀ (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (f : A.representation.IntertwiningMap
        ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).representation), f = 0 := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  intro ρ f
  obtain ⟨e, _⟩ := leviFrobeniusReciprocity k G hG P M U p l r hp hl hr hmul A ρ
  have : Subsingleton ((leviJacquetFunctor p l r hp hr hl hmul).obj A) := hA
  have hz : e f = 0 := by
    ext x
    rw [Subsingleton.elim x 0, map_zero, map_zero]
  apply e.injective
  simpa only [map_zero] using hz

/-- No map from a supercuspidal object to a proper actual parabolic induction
is nonzero. No splitting, admissibility or finite-length input is needed. -/
theorem hom_induction_eq_zero_of_supercuspidal
    (hproper : ¬ IsIso p) (A : SmoothRep.{0, u, w} ℂ (rationalPoints G))
    (hA : IsSupercuspidal A) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    ∀ (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (f : A.representation.IntertwiningMap
        ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).representation), f = 0 :=
  hom_induction_eq_zero_of_jacquet_subsingleton hG p l r hp hl hr hmul A
    (hA P M U p l r hp hl hr hmul hproper)

/-- The remaining splitting input in VI.5.2 is local to the induced object.
The tested subquotient need only be nonzero, rather than irreducible. -/
theorem no_supercuspidal_subquotient_of_induction_splitting
    (hproper : ¬ IsIso p) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    ∀ (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)),
      HasCuspidalRemainderSplitting ((leviInductionFunctor p l r hp hr hl hmul).obj ρ) →
      ∀ D : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
        Nontrivial D →
        SmoothRep.IsSubquotient D ((leviInductionFunctor p l r hp hr hl hmul).obj ρ) →
        ¬ IsSupercuspidal D := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  intro ρ hsplit D hD hDA
  apply no_supercuspidal_subquotient_of_splitting hsplit ?_ D hD hDA
  intro C hC f
  have hf := hom_induction_eq_zero_of_supercuspidal
    hG p l r hp hl hr hmul hproper C hC ρ (SmoothRep.hom f)
  ext x
  exact congrArg (fun F => F x) hf

end LocalField

end Langlands.Aubert.General.RepresentedParabolic
