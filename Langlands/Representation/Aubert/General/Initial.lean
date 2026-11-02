import Langlands.Representation.Aubert.General.Naturality

/-! Canonical orbit-function maps and the initial term of the normalized complex. -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General.Complex

open CategoryTheory

universe uI uG uV

variable {ι : Type uI} [LinearOrder ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
variable (h : ∀ s, IsSemidirectDecomposition (P s) (M s) (U s))
variable (hclosed : ∀ s, IsClosed (U s : Set G))
variable (hδ : ∀ s, IsUnimodularModulus (U s) (hclosed s))
variable (hP : Antitone P) (hU : Monotone U)
variable {A B : SmoothRep.{0, uG, max uG uV} ℂ G}

/-- The actual normalized orbit-function map into any coordinate. -/
def augmentation (A : SmoothRep.{0, uG, max uG uV} ℂ G) (s : Finset ι) :
    A.representation.IntertwiningMap (termRepresentation P M U h hclosed A s) :=
  (termEquiv P M U h hclosed hδ A s).symm.toIntertwiningMap.comp
    (SubgroupTransition.augmentation (P s) (U s) (h s).le_normalizer
      A.representation A.isSmooth)

omit [LinearOrder ι] in
theorem termEquiv_augmentation (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (s : Finset ι) (v : A) :
    termEquiv P M U h hclosed hδ A s (augmentation P M U h hclosed hδ A s v) =
      SubgroupTransition.augmentation (P s) (U s) (h s).le_normalizer
        A.representation A.isSmooth v :=
  (termEquiv P M U h hclosed hδ A s).toLinearEquiv.apply_symm_apply _

omit [LinearOrder ι] in
/-- Evaluation gives the canonical class of the translated input vector. -/
theorem augmentation_eval (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (s : Finset ι) (v : A) (g : G) :
    Induction.eval (P s) (coefficientRepresentation P M U h hclosed A s)
        (augmentation P M U h hclosed hδ A s v) g =
      Jacquet.Localization.mk A.representation (U s) 1 (A.representation g v) := rfl

omit [LinearOrder ι] in
/-- All canonical quotient transitions carry orbit functions to orbit functions. -/
theorem transition_augmentation (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    {s t : Finset ι} (hst : s ⊆ t) :
    (transition P M U h hclosed hδ hP hU A hst).comp
        (augmentation P M U h hclosed hδ A s) =
      augmentation P M U h hclosed hδ A t := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  apply (termEquiv P M U h hclosed hδ A t).injective
  change termEquiv P M U h hclosed hδ A t
    (transition P M U h hclosed hδ hP hU A hst
      (augmentation P M U h hclosed hδ A s v)) =
    termEquiv P M U h hclosed hδ A t (augmentation P M U h hclosed hδ A t v)
  rw [termEquiv_transition, termEquiv_augmentation, termEquiv_augmentation]
  exact LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap
    (SubgroupTransition.map_augmentation (P s) (U s) (P t) (U t)
      (h s).le_normalizer (h t).le_normalizer (hP hst) (hU hst)
      A.representation A.isSmooth)) v

omit [LinearOrder ι] in
/-- The canonical input map is natural in the ambient smooth representation. -/
theorem augmentation_natural (φ : A ⟶ B) (s : Finset ι) :
    (termMap P M U h hclosed φ s).comp (augmentation P M U h hclosed hδ A s) =
      (augmentation P M U h hclosed hδ B s).comp (SmoothRep.hom φ) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  apply (termEquiv P M U h hclosed hδ B s).injective
  change termEquiv P M U h hclosed hδ B s
    (termMap P M U h hclosed φ s (augmentation P M U h hclosed hδ A s v)) =
    termEquiv P M U h hclosed hδ B s
      (augmentation P M U h hclosed hδ B s (SmoothRep.hom φ v))
  rw [termEquiv_map, termEquiv_augmentation, termEquiv_augmentation]
  exact LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap
    (SubgroupTransition.augmentation_natural (P s) (U s) (h s).le_normalizer
      A.isSmooth B.isSmooth (SmoothRep.hom φ))) v

/-- In degree zero there is exactly the empty removed-root coordinate. -/
def degreeZeroEvaluation (A : SmoothRep.{0, uG, max uG uV} ℂ G) :
    (degreeRepresentation P M U h hclosed A 0).IntertwiningMap
      (termRepresentation P M U h hclosed A ∅) where
  toLinearMap :=
    { toFun := fun x => x ⟨∅, Finset.card_empty⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := rfl

omit [LinearOrder ι] in
/-- The empty coordinate identifies degree zero with its actual term. -/
theorem degreeZeroEvaluation_bijective (A : SmoothRep.{0, uG, max uG uV} ℂ G) :
    Function.Bijective (degreeZeroEvaluation P M U h hclosed A) := by
  constructor
  · intro x y hxy
    funext s
    rcases s with ⟨s, hs⟩
    have hs0 := Finset.card_eq_zero.mp hs
    subst s
    exact hxy
  · intro f
    refine ⟨fun s => ?_, ?_⟩
    · rcases s with ⟨s, hs⟩
      have hs0 := Finset.card_eq_zero.mp hs
      subst s
      exact f
    · rfl

/-- The canonical map from the original object to degree zero. -/
def initialMap (A : SmoothRep.{0, uG, max uG uV} ℂ G) :
    A.representation.IntertwiningMap (degreeRepresentation P M U h hclosed A 0) where
  toLinearMap :=
    { toFun := fun v s => augmentation P M U h hclosed hδ A s.1 v
      map_add' _ _ := by funext s; exact map_add _ _ _
      map_smul' _ _ := by funext s; exact map_smul _ _ _ }
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    funext s
    exact LinearMap.congr_fun ((augmentation P M U h hclosed hδ A s.1).isIntertwining' g) v

omit [LinearOrder ι] in
/-- Full parabolic and trivial radical make the initial coordinate canonical and bijective. -/
theorem augmentation_empty_bijective (hP0 : P ∅ = ⊤) (hU0 : U ∅ = ⊥)
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) :
    Function.Bijective (augmentation P M U h hclosed hδ A ∅) := by
  have aux (P0 U0 : Subgroup G) (hnorm : P0 ≤ Subgroup.normalizer U0)
      (hp : P0 = ⊤) (hu : U0 = ⊥) :
      Function.Bijective
        (SubgroupTransition.augmentation P0 U0 hnorm A.representation A.isSmooth) := by
    subst P0
    subst U0
    exact ⟨SubgroupTransition.initial_augmentation_injective A.representation A.isSmooth,
      SubgroupTransition.initial_augmentation_surjective A.representation A.isSmooth⟩
  have hbij : Function.Bijective
      (SubgroupTransition.augmentation (P ∅) (U ∅) (h ∅).le_normalizer
        A.representation A.isSmooth) := by
    exact aux (P ∅) (U ∅) (h ∅).le_normalizer hP0 hU0
  exact (termEquiv P M U h hclosed hδ A ∅).symm.toLinearEquiv.bijective.comp hbij

/-- The actual initial map is an equivalence, without an exactness or length premise. -/
def initialEquiv (hP0 : P ∅ = ⊤) (hU0 : U ∅ = ⊥)
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) :
    A.representation.Equiv (degreeRepresentation P M U h hclosed A 0) :=
  (initialMap P M U h hclosed hδ A).ofBijective (by
    have heval := degreeZeroEvaluation_bijective P M U h hclosed A
    have haug := augmentation_empty_bijective P M U h hclosed hδ hP0 hU0 A
    constructor
    · intro v w hvw
      exact haug.injective (congrArg (degreeZeroEvaluation P M U h hclosed A) hvw)
    · intro x
      obtain ⟨v, hv⟩ := haug.surjective (degreeZeroEvaluation P M U h hclosed A x)
      exact ⟨v, heval.injective hv⟩)

/-- The input-to-degree-zero comparison is natural. -/
theorem initialMap_natural (φ : A ⟶ B) :
    (degreeMap P M U h hclosed hδ hP hU φ 0).comp (initialMap P M U h hclosed hδ A) =
      (initialMap P M U h hclosed hδ B).comp (SmoothRep.hom φ) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  funext s
  exact LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap
    (augmentation_natural P M U h hclosed hδ φ s.1)) v

variable [Fintype ι]

/-- The first arrow from `E`, after the canonical degree-zero identification. -/
def initialDifferential (A : SmoothRep.{0, uG, max uG uV} ℂ G) :
    A.representation.IntertwiningMap (degreeRepresentation P M U h hclosed A 1) :=
  (differential P M U h hclosed hδ hP hU A 0).comp (initialMap P M U h hclosed hδ A)

/-- The next differential kills the actual initial arrow. -/
theorem initialDifferential_square (A : SmoothRep.{0, uG, max uG uV} ℂ G) :
    (differential P M U h hclosed hδ hP hU A 1).comp
      (initialDifferential P M U h hclosed hδ hP hU A) = 0 := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  exact LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap
    (differential_square P M U h hclosed hδ hP hU A 0))
    (initialMap P M U h hclosed hδ A v)

end Langlands.Aubert.General.Complex
