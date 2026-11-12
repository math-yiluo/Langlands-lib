import Langlands.AlgebraicGeometry.LangWeil.SpaceFamily.FieldPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineIntersections
import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteActionChartDescent
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleFieldPoints
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleBound
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleDegreeScheme
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleThresholdInvariance

/-!
# Symmetric tuple charts of a separated algebraic space

A separated algebraic space `X` over `Spec (ULift ℤ)` with an affine étale surjective chart
`a : U → X` gives the étale equivalence relation `R = U ×_X U ⇉ U`, whose relation scheme is
affine and whose joint endpoint map is a closed immersion. For each `n` the symmetric group
acts freely on the affine scheme `W_n` of distinct related `(n + 1)`-tuples; its quotient
`V_n` is affine, and the first coordinate descends to an étale map `e_n : V_n → X`
(Stacks Project, Lemma 68.8.3, Tag 0BBN). The construction of `e_n` is copied from Worker 80's
draft proof of `UniformFieldPointChartsStatement` (Task 5417).
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.LangWeil.SpaceFamily

open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry (EtaleEquivalenceRelation)

-- The relation `ofKernelPair` is a plain definition, so its fields `U`, `R`, `t`, `s` are
-- `U.left`, `R.left`, `t.left`, `s.left` only up to unfolding it.
set_option backward.isDefEq.respectTransparency false

/-- A separated algebraic space over `Spec (ULift ℤ)` with an affine étale surjective chart and
the kernel pair of that chart. -/
structure SepChart where
  /-- The separated algebraic space. -/
  X : AlgebraicSpace S0.{u}
  /-- Its diagonal is a representable closed immersion. -/
  sep : AlgebraicSpace.IsSeparated X
  /-- The affine chart. -/
  U : Over S0.{u}
  affine_U : IsAffine U.left
  /-- The chart map. -/
  a : (schemeYoneda S0).obj U ⟶ X.presheaf
  etale_a : IsEtale a
  surj_a : IsSurjective a
  /-- The kernel pair of the chart. -/
  R : Over S0.{u}
  t : R ⟶ U
  s : R ⟶ U
  pb : IsPullback ((schemeYoneda S0).map t) ((schemeYoneda S0).map s) a a
  etale_t : Etale t.left
  etale_s : Etale s.left

namespace SepChart

/-- Every separated algebraic space with an affine étale surjective chart gives a `SepChart`. -/
theorem exists_of_chart (X : AlgebraicSpace S0.{u}) (hX : AlgebraicSpace.IsSeparated X)
    (U : Over S0.{u}) [IsAffine U.left] (a : (schemeYoneda S0).obj U ⟶ X.presheaf)
    (ha : IsEtale a) (has : IsSurjective a) :
    ∃ c : SepChart.{u}, c.X = X ∧ c.U = U := by
  obtain ⟨R, t, s, hpb, ht, hs⟩ := exists_kernelPair ha
  exact ⟨⟨X, hX, U, inferInstance, a, ha, has, R, t, s, hpb, ht, hs⟩, rfl, rfl⟩

variable (c : SepChart.{u})

instance : IsAffine c.U.left := c.affine_U

instance : IsAffine c.R.left :=
  isAffine_of_isPullback_of_closedDiagonal c.sep c.a c.a c.t c.s c.pb

/-- The joint endpoint map of the kernel pair is a closed immersion of absolute schemes. -/
theorem isClosedImmersion_lift :
    _root_.AlgebraicGeometry.IsClosedImmersion (prod.lift c.t.left c.s.left) := by
  have h := closedImmersion_pair_of_isPullback c.sep c.a c.a c.t c.s c.pb
  have : (Over.forget S0.{u}).IsEquivalence :=
    (Over.equivalenceOfIsTerminal specULiftZIsTerminal.{u}).isEquivalence_functor
  have hiso : IsIso (prodComparison (Over.forget S0.{u}) c.U c.U) := inferInstance
  have heq : prod.lift c.t.left c.s.left =
      (prod.lift c.t c.s).left ≫ prodComparison (Over.forget S0.{u}) c.U c.U := by
    apply prod.hom_ext
    · rw [prod.lift_fst, Category.assoc]
      erw [prodComparison_fst]
      rw [Over.forget_map, ← Over.comp_left, prod.lift_fst]
    · rw [prod.lift_snd, Category.assoc]
      erw [prodComparison_snd]
      rw [Over.forget_map, ← Over.comp_left, prod.lift_snd]
  rw [heq]
  infer_instance

/-- The étale equivalence relation `U ×_X U ⇉ U`. -/
abbrev E : EtaleEquivalenceRelation.{u} :=
  EtaleEquivalenceRelation.ofKernelPair c.t c.s c.a c.pb c.etale_t c.etale_s

instance : IsAffine c.E.U := c.affine_U

instance : IsAffine c.E.R := inferInstanceAs (IsAffine c.R.left)

instance : _root_.AlgebraicGeometry.IsSeparated c.E.s := by
  change _root_.AlgebraicGeometry.IsSeparated c.s.left
  infer_instance

instance : _root_.AlgebraicGeometry.IsClosedImmersion (prod.lift c.E.t c.E.s) :=
  c.isClosedImmersion_lift

/-- Every coordinate of a related tuple has the same image in the base. -/
theorem tupleProjection_hom (n : ℕ) (i : Fin (n + 1)) :
    c.E.tupleProjection n i ≫ c.U.hom = c.E.tupleProjection n 0 ≫ c.U.hom :=
  specULiftZIsTerminal.hom_ext _ _

/-- The distinct related tuples, over the base through their first coordinate. -/
abbrev tupleOver (n : ℕ) : Over S0.{u} :=
  Over.mk (c.E.tupleDistinctProjection n 0 ≫ c.U.hom)

/-- A coordinate of the distinct related tuples, as a morphism over the base. -/
def projOver (n : ℕ) (i : Fin (n + 1)) : c.tupleOver n ⟶ c.U :=
  Over.homMk (c.E.tupleDistinctProjection n i) (specULiftZIsTerminal.hom_ext _ _)

@[simp] theorem projOver_left (n : ℕ) (i : Fin (n + 1)) :
    (c.projOver n i).left = c.E.tupleDistinctProjection n i := rfl

/-- All coordinates of the distinct related tuples have the same image in `X`. -/
theorem map_projOver (n : ℕ) (i j : Fin (n + 1)) :
    (schemeYoneda _).map (c.projOver n i) ≫ c.a =
      (schemeYoneda _).map (c.projOver n j) ≫ c.a := by
  obtain ⟨r, hrt, hrs⟩ := c.E.tupleProjection_related n i j
  let r' : c.tupleOver n ⟶ c.R :=
    Over.homMk ((c.E.tupleDistinctOpen n).ι ≫ r) (specULiftZIsTerminal.hom_ext _ _)
  have h1 : c.projOver n i = r' ≫ c.t := Over.OverMorphism.ext (by
    change _ ≫ _ = (_ ≫ r) ≫ c.t.left
    rw [Category.assoc]
    exact congrArg (_ ≫ ·) hrt.symm)
  have h2 : c.projOver n j = r' ≫ c.s := Over.OverMorphism.ext (by
    change _ ≫ _ = (_ ≫ r) ≫ c.s.left
    rw [Category.assoc]
    exact congrArg (_ ≫ ·) hrs.symm)
  rw [h1, h2, Functor.map_comp_assoc, Functor.map_comp_assoc, c.pb.w]

/-- The permutation action on distinct tuples is an action over the base. -/
theorem act_hom (n : ℕ) (g : EtaleEquivalenceRelation.TuplePermutationGroup.{u} n) :
    ((c.E.tuplePermutationAction n).act g).hom ≫ (c.tupleOver n).hom =
      (c.tupleOver n).hom :=
  specULiftZIsTerminal.hom_ext _ _

theorem actOver_projOver (n : ℕ) (g : EtaleEquivalenceRelation.TuplePermutationGroup.{u} n)
    (i : Fin (n + 1)) :
    FiniteActionChart.actOver (A := c.tupleOver n) _ (c.act_hom n) g ≫ c.projOver n i =
      c.projOver n (g.down i) :=
  Over.OverMorphism.ext (c.E.tuplePermutationAction_projection n g i)

/-- The affine quotient `V_n` of the distinct tuples by the symmetric group, over the base. -/
abbrev quot (n : ℕ) : Over S0.{u} :=
  FiniteActionChart.quotientOver (A := c.tupleOver n) _ (c.act_hom n)
    (c.E.tupleSymmetricQuotient n)

/-- The quotient map from the distinct tuples to `V_n`, over the base. -/
abbrev quotMap (n : ℕ) : c.tupleOver n ⟶ c.quot n :=
  FiniteActionChart.quotientMapOver (A := c.tupleOver n) _ (c.act_hom n)
    (c.E.tupleSymmetricQuotient n)

theorem quot_left (n : ℕ) : (c.quot n).left = c.E.tupleSymmetricScheme n := rfl

theorem quotMap_left (n : ℕ) : (c.quotMap n).left = c.E.tupleSymmetricMap n := rfl

theorem actOver_quotMap (n : ℕ) (g : EtaleEquivalenceRelation.TuplePermutationGroup.{u} n) :
    FiniteActionChart.actOver (A := c.tupleOver n) _ (c.act_hom n) g ≫ c.quotMap n =
      c.quotMap n :=
  Over.OverMorphism.ext ((c.E.tupleSymmetricQuotient n).invariant g)

/-- The first coordinate descends to an étale map `V_n → X`. -/
theorem exists_chart (n : ℕ) :
    ∃ tM : (schemeYoneda _).obj (c.quot n) ⟶ c.X.presheaf, IsEtale tM ∧
      (schemeYoneda _).map (c.quotMap n) ≫ tM =
        (schemeYoneda _).map (c.projOver n 0) ≫ c.a := by
  obtain ⟨tM, htM⟩ := FiniteActionChart.exists_desc (A := c.tupleOver n) _
    (c.act_hom n) (c.E.tupleSymmetricQuotient n) c.X.toSheaf
    ((schemeYoneda _).map (c.projOver n 0) ≫ c.a)
    (fun g => by rw [← Functor.map_comp_assoc, actOver_projOver, map_projOver])
  refine ⟨tM, ?_, htM⟩
  apply isEtale_of_finiteEtale_comp c.X.hasRepresentableDiagonal (c.quotMap n)
  rw [htM]
  exact IsEtale.comp (isEtale_map _
    (inferInstanceAs (Etale (c.E.tupleDistinctProjection n 0)))) c.etale_a

/-- The étale map `e_n : V_n → X`. -/
def e (n : ℕ) : (schemeYoneda _).obj (c.quot n) ⟶ c.X.presheaf :=
  (c.exists_chart n).choose

theorem e_isEtale (n : ℕ) : IsEtale (c.e n) := (c.exists_chart n).choose_spec.1

@[reassoc]
theorem quotMap_e (n : ℕ) :
    (schemeYoneda _).map (c.quotMap n) ≫ c.e n =
      (schemeYoneda _).map (c.projOver n 0) ≫ c.a :=
  (c.exists_chart n).choose_spec.2

/-- The uniform bound on the lengths of distinct related tuples. -/
abbrev N : ℕ := c.E.tupleLengthBound

end SepChart

end Langlands.AlgebraicGeometry.LangWeil.SpaceFamily
