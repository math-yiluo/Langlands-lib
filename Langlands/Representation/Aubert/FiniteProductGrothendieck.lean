import Langlands.Representation.Aubert.FiniteLengthCutComplex
import Mathlib.Data.Fintype.Option

/-! Exact Grothendieck classes of finite products of actual smooth representations. -/

noncomputable section

namespace Langlands.Aubert.FiniteProduct

open CategoryTheory SmoothRep
open scoped BigOperators

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {J : Type} [Fintype J]

/-- A genuine finite-length smooth product, with its original coordinate actions. -/
def object (A : J → FiniteLengthObject.{0,uG,uV} ℂ G) :
    FiniteLengthObject.{0,uG,uV} ℂ G :=
  ⟨SmoothRep.of (representation (fun j => (A j).val.representation))
    (isSmooth _ fun j => (A j).val.isSmooth),
    finiteLength.{0,uG,uV} _ fun j => (A j).property⟩

/-- A subsingleton representation has zero class in the exact Grothendieck group. -/
theorem class_eq_zero (A : FiniteLengthObject.{0,uG,uV} ℂ G) [Subsingleton A.val] :
    FiniteLengthGrothendieckGroup.ofObject A = 0 := by
  have h : IsShortExact
      (0 : A.val.representation.IntertwiningMap A.val.representation)
      (0 : A.val.representation.IntertwiningMap A.val.representation) := by
    refine ⟨fun _ _ _ => Subsingleton.elim _ _, fun v => ⟨0, Subsingleton.elim _ _⟩, ?_⟩
    exact Subsingleton.elim _ _
  exact add_eq_left.mp (FiniteLengthGrothendieckGroup.ofObject_shortExact h).symm

/-- Reindexing all coordinates is an actual equivariant linear equivalence. -/
def reindex {K : Type} [Fintype K] (e : J ≃ K)
    (A : K → FiniteLengthObject.{0,uG,uV} ℂ G) :
    (object A).val.representation.Equiv (object (fun j => A (e j))).val.representation :=
  Representation.Equiv.mk
    (LinearEquiv.piCongrLeft ℂ (fun k => (A k).val) e).symm
    (fun _ => rfl)

/-- Insert the distinguished coordinate into an option-indexed product. -/
def optionIn (A : Option J → FiniteLengthObject.{0,uG,uV} ℂ G) :
    (A none).val.representation.IntertwiningMap (object A).val.representation where
  toLinearMap :=
    { toFun v o := match o with | none => v | some _ => 0
      map_add' x y := by
        funext o
        cases o
        · rfl
        · change 0 = (0 : (A _).val) + 0
          simp
      map_smul' a x := by
        funext o
        cases o
        · rfl
        · change 0 = a • (0 : (A _).val)
          simp }
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    funext o
    cases o
    · rfl
    · exact ((A _).val.representation g).map_zero.symm

/-- Forget the distinguished coordinate of an option-indexed product. -/
def optionOut (A : Option J → FiniteLengthObject.{0,uG,uV} ℂ G) :
    (object A).val.representation.IntertwiningMap
      (object (fun j => A (some j))).val.representation where
  toLinearMap :=
    { toFun x j := x (some j)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := rfl

theorem option_shortExact (A : Option J → FiniteLengthObject.{0,uG,uV} ℂ G) :
    IsShortExact (optionIn A) (optionOut A) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    exact congrFun h none
  · intro x
    exact ⟨fun o => match o with | none => 0 | some j => x j, rfl⟩
  · apply le_antisymm
    · rintro x ⟨v, rfl⟩
      exact LinearMap.mem_ker.mpr rfl
    · intro x hx
      refine ⟨x none, ?_⟩
      have hzero := LinearMap.mem_ker.mp hx
      funext o
      cases o with
      | none => rfl
      | some j => exact (congrFun hzero j).symm

/-- Exact additivity for separating one coordinate of a finite product. -/
theorem option_class (A : Option J → FiniteLengthObject.{0,uG,uV} ℂ G) :
    FiniteLengthGrothendieckGroup.ofObject (object A) =
      FiniteLengthGrothendieckGroup.ofObject (A none) +
        FiniteLengthGrothendieckGroup.ofObject (object (fun j => A (some j))) :=
  FiniteLengthGrothendieckGroup.ofObject_shortExact (option_shortExact A)

/-- The exact Grothendieck class of a finite product is the sum of its coordinates. -/
theorem class_eq_sum (A : J → FiniteLengthObject.{0,uG,uV} ℂ G) :
    FiniteLengthGrothendieckGroup.ofObject (object A) =
      ∑ j, FiniteLengthGrothendieckGroup.ofObject (A j) := by
  classical
  have h : ∀ (I : Type) [Fintype I]
      (B : I → FiniteLengthObject.{0,uG,uV} ℂ G),
      FiniteLengthGrothendieckGroup.ofObject (object B) =
        ∑ i, FiniteLengthGrothendieckGroup.ofObject (B i) := by
    intro I _
    refine Fintype.induction_empty_option
      (P := fun I _ => ∀ (B : I → FiniteLengthObject.{0,uG,uV} ℂ G),
        FiniteLengthGrothendieckGroup.ofObject (object B) =
          ∑ i, FiniteLengthGrothendieckGroup.ofObject (B i)) ?_ ?_ ?_ I
    · intro I K _ e ih B
      let : Fintype I := Fintype.ofEquiv K e.symm
      rw [FiniteLengthGrothendieckGroup.ofObject_eq_of_iso (SmoothRep.mkIso (reindex e B))]
      rw [ih]
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)
    · intro B
      have : Subsingleton (object B).val :=
        ⟨fun x y => funext fun i => PEmpty.elim i⟩
      rw [class_eq_zero]
      simp
    · intro I _ ih B
      rw [option_class, ih, Fintype.sum_option]
  exact h J A

end Langlands.Aubert.FiniteProduct

namespace Langlands.Aubert.ActualCutComplex

open GeneralLinear SmoothRep
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ}

/-- A single actual term as a finite-length smooth object. -/
def finiteTerm (B : BlockShape n) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)),
      A.HasFiniteLength → FiniteLengthObject.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  fun A hA =>
    ⟨SmoothRep.of (Transition.term T B A.representation) (Induction.smoothInduced_smooth _ _),
      term_hasFiniteLength.{uF,uV} F T B A hA⟩

/-- Exact-K0 decomposition of one degree into its actual cut-indexed terms. -/
theorem degree_class (k : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)) (hA : A.HasFiniteLength),
      FiniteLengthGrothendieckGroup.ofObject (finiteDegree.{uF,uV} F T A hA k) =
        ∑ s : {s : Finset (Fin (n - 1)) // s.card = k},
          FiniteLengthGrothendieckGroup.ofObject
            (finiteTerm.{uF,uV} F T (shape (n := n) s.1) A hA) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro A hA
  let family := fun s : {s : Finset (Fin (n - 1)) // s.card = k} =>
    finiteTerm.{uF,uV} F T (shape (n := n) s.1) A hA
  have e : (finiteDegree.{uF,uV} F T A hA k).val.representation.Equiv
      (FiniteProduct.object family).val.representation :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ _) (fun _ => rfl)
  rw [FiniteLengthGrothendieckGroup.ofObject_eq_of_iso (SmoothRep.mkIso e)]
  exact FiniteProduct.class_eq_sum family

end Langlands.Aubert.ActualCutComplex
