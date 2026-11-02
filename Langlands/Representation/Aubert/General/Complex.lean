import Langlands.Representation.Aubert.General.Parabolic
import Langlands.Representation.Aubert.SubgroupComplexNaturality
import Langlands.Representation.Aubert.SubgroupInitialTerm
import Langlands.Representation.Aubert.CutDiagramEquivalence

/-! The signed diagram on actual normalized induction--Jacquet objects. -/

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

/-- The actual normalized action inflated from the Levi to the parabolic. -/
def coefficientRepresentation (A : SmoothRep.{0, uG, max uG uV} ℂ G) (s : Finset ι) :
    Representation ℂ (P s) (Jacquet.Localization.Coinvariants A.representation (U s) 1) :=
  Langlands.twist (HaarModulus.closedHalfCharacter (U s) (hclosed s) (P s) (h s).le_normalizer)
    ((Langlands.twist
      (HaarModulus.closedInverseHalfCharacter (U s) (hclosed s) (M s) (h s).levi_le_normalizer)
      (Jacquet.Localization.action A.representation (U s) 1 (M s) (h s).levi_le_normalizer
        (Jacquet.Localization.isInvariant_one (U s) (M s) (h s).levi_le_normalizer))).comp
      (h s).projection)

/-- The actual normalized smooth induced-function carrier. -/
abbrev Term (A : SmoothRep.{0, uG, max uG uV} ℂ G) (s : Finset ι) :=
  Induction.SmoothFunctions (P s) (coefficientRepresentation P M U h hclosed A s)

/-- The actual right-translation action on the normalized composite. -/
def termRepresentation (A : SmoothRep.{0, uG, max uG uV} ℂ G) (s : Finset ι) :
    Representation ℂ G (Term P M U h hclosed A s) :=
  Induction.smoothInduced (P s) (coefficientRepresentation P M U h hclosed A s)

/-- The genuine normalized composite `i_s (r_s A)` in the full smooth category. -/
abbrev termObject (A : SmoothRep.{0, uG, max uG uV} ℂ G) (s : Finset ι) :=
  SmoothRep.of (termRepresentation P M U h hclosed A s)
    (Induction.smoothInduced_smooth _ _)

omit [LinearOrder ι] in
/-- The explicit model is definitionally the actual normalized functor object. -/
theorem termObject_eq (A : SmoothRep.{0, uG, max uG uV} ℂ G) (s : Finset ι) :
    termObject P M U h hclosed A s =
      (inductionJacquetFunctor.{uG, uV} (h s) (hclosed s)).obj A := rfl

/-- The finite homogeneous carrier, with its pointwise module structure. -/
abbrev Degree (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :=
  ∀ s : {s : Finset ι // s.card = k}, Term P M U h hclosed A s.1

/-- The normalization comparison, with the identity map on induced functions. -/
def termEquiv (A : SmoothRep.{0, uG, max uG uV} ℂ G) (s : Finset ι) :
    (termRepresentation P M U h hclosed A s).Equiv
      (SubgroupTransition.term (P s) (U s) (h s).le_normalizer A.representation) :=
  SmoothRep.equivOfIso (inductionJacquetTermIso.{uG, uV} (h s) (hclosed s) (hδ s) A)

/-- Transport the actual pointwise coinvariant quotient map to the normalized objects. -/
def transition (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    {s t : Finset ι} (hst : s ⊆ t) :
    (termRepresentation P M U h hclosed A s).IntertwiningMap
      (termRepresentation P M U h hclosed A t) :=
  (termEquiv P M U h hclosed hδ A t).symm.toIntertwiningMap.comp
    ((SubgroupComplex.transition P U (fun s => (h s).le_normalizer) hP hU
      A.representation hst).comp
      (termEquiv P M U h hclosed hδ A s).toIntertwiningMap)

omit [LinearOrder ι] in
/-- Normalization preserves the canonical quotient transition, not only the objects. -/
theorem termEquiv_transition (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    {s t : Finset ι} (hst : s ⊆ t) (f : termObject P M U h hclosed A s) :
    termEquiv P M U h hclosed hδ A t
        (transition P M U h hclosed hδ hP hU A hst f) =
      SubgroupComplex.transition P U (fun s => (h s).le_normalizer) hP hU
        A.representation hst (termEquiv P M U h hclosed hδ A s f) := by
  exact (termEquiv P M U h hclosed hδ A t).toLinearEquiv.apply_symm_apply _

omit [LinearOrder ι] in
/-- At every group point the transition sends `[v]_U(s)` to `[v]_U(t)`. -/
theorem transition_eval (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    {s t : Finset ι} (hst : s ⊆ t) (f : termObject P M U h hclosed A s) (g : G) :
    Induction.eval (P t)
        (inducingRepresentation (h t) (hclosed t) ((jacquetFunctor (h t) (hclosed t)).obj A))
        (transition P M U h hclosed hδ hP hU A hst f) g =
      Jacquet.Localization.transitionLinear (U s) (U t) (hU hst) 1 1 (fun _ => rfl)
        A.representation
        (Induction.eval (P s)
          (inducingRepresentation (h s) (hclosed s) ((jacquetFunctor (h s) (hclosed s)).obj A))
          f g) := rfl

/-- The actual normalized terms and their canonical maps form a commuting diagram. -/
def diagram (A : SmoothRep.{0, uG, max uG uV} ℂ G) : CutComplex.Diagram ι where
  Obj := Term P M U h hclosed A
  add _ := inferInstance
  module _ := inferInstance
  map hst := (transition P M U h hclosed hδ hP hU A hst).toLinearMap
  map_refl s := by
    apply LinearMap.ext
    intro f
    apply (termEquiv P M U h hclosed hδ A s).injective
    change termEquiv P M U h hclosed hδ A s
      (transition P M U h hclosed hδ hP hU A Finset.Subset.rfl f) =
      termEquiv P M U h hclosed hδ A s f
    rw [termEquiv_transition]
    change (SubgroupComplex.diagram P U (fun s => (h s).le_normalizer) hP hU
      A.representation).map Finset.Subset.rfl _ = _
    rw [(SubgroupComplex.diagram P U (fun s => (h s).le_normalizer) hP hU
      A.representation).map_refl]
    rfl
  map_comp hst htu := by
    apply LinearMap.ext
    intro f
    apply (termEquiv P M U h hclosed hδ A _).injective
    change termEquiv P M U h hclosed hδ A _
      (transition P M U h hclosed hδ hP hU A htu
        (transition P M U h hclosed hδ hP hU A hst f)) =
      termEquiv P M U h hclosed hδ A _
        (transition P M U h hclosed hδ hP hU A (Finset.Subset.trans hst htu) f)
    rw [termEquiv_transition, termEquiv_transition, termEquiv_transition]
    exact (SubgroupComplex.diagram P U (fun s => (h s).le_normalizer) hP hU
      A.representation).map_map hst htu _

/-- Coordinate normalization compares the actual maps of the two diagrams. -/
def diagramEquivalence (A : SmoothRep.{0, uG, max uG uV} ℂ G) :
    CutComplex.Diagram.Equivalence (diagram P M U h hclosed hδ hP hU A)
      (SubgroupComplex.diagram P U (fun s => (h s).le_normalizer) hP hU A.representation) where
  obj s := (termEquiv P M U h hclosed hδ A s).toLinearEquiv
  natural hst f := termEquiv_transition P M U h hclosed hδ hP hU A hst f

variable [Fintype ι]

/-- The homogeneous action is the finite product of the genuine normalized actions. -/
def degreeRepresentation (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :
    Representation ℂ G (Degree P M U h hclosed A k) :=
  FiniteProduct.representation (fun s =>
    (termRepresentation P M U h hclosed A s.1))

/-- The signed differential with its actual equivariant structure. -/
def differential (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :
    (degreeRepresentation P M U h hclosed A k).IntertwiningMap
      (degreeRepresentation P M U h hclosed A (k + 1)) where
  toLinearMap := (diagram P M U h hclosed hδ hP hU A).degreeDifferential k
  isIntertwining' g := LinearMap.ext fun x =>
    EquivariantDiagram.degreeDifferential_intertwining
      (diagram P M U h hclosed hδ hP hU A)
      (fun s => (termRepresentation P M U h hclosed A s))
      (fun hst g v => LinearMap.congr_fun
        ((transition P M U h hclosed hδ hP hU A hst).isIntertwining' g) v) k g x

/-- Exterior signs and the proved composition law give square zero. -/
theorem differential_square (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :
    (differential P M U h hclosed hδ hP hU A (k + 1)).comp
      (differential P M U h hclosed hδ hP hU A k) = 0 := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  exact (diagram P M U h hclosed hδ hP hU A).degreeDifferential_square k

omit [LinearOrder ι] in
/-- All homogeneous objects are smooth, with no finite-length assumption on `A`. -/
theorem degree_isSmooth (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :
    IsSmooth (degreeRepresentation P M U h hclosed A k) :=
  FiniteProduct.isSmooth
    (fun s : {s : Finset ι // s.card = k} =>
      (termRepresentation P M U h hclosed A s.1))
    (fun _ => Induction.smoothInduced_smooth _ _)

/-- The homogeneous object in the full smooth category. -/
def degreeObject (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :
    SmoothRep.{0, uG, max uI uG uV} ℂ G :=
  SmoothRep.of (degreeRepresentation P M U h hclosed A k)
    (degree_isSmooth P M U h hclosed A k)

/-- The signed differential as a morphism in the full smooth category. -/
def degreeMorphism (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :
    degreeObject P M U h hclosed A k ⟶ degreeObject P M U h hclosed A (k + 1) :=
  SmoothRep.ofHom (differential P M U h hclosed hδ hP hU A k)

/-- Coordinate normalization is an actual equivariant degree equivalence. -/
def degreeEquiv (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ) :
    (degreeRepresentation P M U h hclosed A k).Equiv
      (SubgroupComplex.degreeRepresentation P U (fun s => (h s).le_normalizer)
        hP hU A.representation k) :=
  Representation.Equiv.mk
    ((diagramEquivalence P M U h hclosed hδ hP hU A).degreeEquiv k) (fun g => by
      apply LinearMap.ext
      intro x
      funext s
      exact LinearMap.congr_fun
        ((termEquiv P M U h hclosed hδ A s.1).isIntertwining' g) (x s))

/-- The unchanged signed differentials commute with the normalization comparison. -/
theorem degreeEquiv_differential (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (k : ℕ) (x : (diagram P M U h hclosed hδ hP hU A).Degree k) :
    (diagramEquivalence P M U h hclosed hδ hP hU A).degreeEquiv (k + 1)
        (differential P M U h hclosed hδ hP hU A k x) =
      SubgroupComplex.differential P U (fun s => (h s).le_normalizer) hP hU A.representation k
        ((diagramEquivalence P M U h hclosed hδ hP hU A).degreeEquiv k x) :=
  (diagramEquivalence P M U h hclosed hδ hP hU A).degreeEquiv_differential k x

end Langlands.Aubert.General.Complex
