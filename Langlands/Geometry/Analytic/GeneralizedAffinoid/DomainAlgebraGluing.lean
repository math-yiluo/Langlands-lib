import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainRelativeRationalRefinement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalGluingProof

/-! # Descent in the actual stored algebra of a full affinoid domain -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K} {U : Domain K A}

private theorem rational_ext {B : PresentedAffinoidAlgebra K}
    {I : Type v} [Finite I] (D : I → RationalChart K B)
    (hcover : ∀ x : BanachSpectrum B, ∃ i, x ∈ (D i).locus)
    {a b : B} (hab : ∀ i, (D i).baseMap a = (D i).baseMap b) : a = b := by
  have hcompat : ∀ i j,
      (RationalChart.interLeft (D i) (D j)).restriction ((D i).baseMap a) =
      (RationalChart.interRight (D i) (D j)).restriction ((D j).baseMap a) := by
    intro i j
    exact congrArg (fun f : BoundedAlgHom K B ((D i).inter (D j)).algebra => f a)
      ((RationalChart.interLeft (D i) (D j)).comp_baseMap.trans
        (RationalChart.interRight (D i) (D j)).comp_baseMap.symm)
  obtain ⟨z, _, hz⟩ := RationalChart.wholeSpectrumRationalGluing
    K B I D hcover (fun i => (D i).baseMap a) hcompat
  exact (hz a (fun _ => rfl)).trans (hz b (fun i => (hab i).symm)).symm

/-- Actual restrictions along any finite full-domain cover detect equality
of elements in the stored target algebra. -/
theorem algebra_ext_of_restrict_eq (c : FiniteCover U) {a b : U.algebra}
    (hab : ∀ i, (c.map i).restriction a = (c.map i).restriction b) : a = b := by
  let r := c.relativeRationalRefinement
  apply rational_ext r.chart r.covers
  intro i
  rw [← r.restriction_comp i]
  exact congrArg (r.map i).restriction (hab (r.index i))

/-- Local algebra elements agree after every actual represented-domain test
mapping to two members of the cover. -/
def AlgebraCompatible (c : FiniteCover U)
    (s : ∀ i : Fin c.size, (c.obj i).algebra) : Prop :=
  ∀ (i j : Fin c.size) (W : Domain K A) (f : W ⟶ c.obj i) (g : W ⟶ c.obj j),
    f.restriction (s i) = g.restriction (s j)

/-- Restrict an element using the original stored bounded maps. -/
def algebraRestrict (c : FiniteCover U) (a : U.algebra) :
    ∀ i : Fin c.size, (c.obj i).algebra :=
  fun i => (c.map i).restriction a

theorem algebraCompatible_restrict (c : FiniteCover U) (a : U.algebra) :
    c.AlgebraCompatible (c.algebraRestrict a) := by
  intro i j W f g
  exact congrArg (fun h : Inclusion W U => h.restriction a)
    (@Subsingleton.elim (Inclusion W U) inferInstance
      (f ≫ c.map i) (g ≫ c.map j))

namespace RelativeRationalRefinement

variable {c : FiniteCover U} (r : RelativeRationalRefinement c)

/-- Restrict a compatible family through the chosen actual refinement maps. -/
def algebraFamily (s : ∀ i : Fin c.size, (c.obj i).algebra) :
    ∀ i : Fin r.size, (r.chart i).algebra :=
  fun i => (r.map i).restriction (s (r.index i))

/-- Full test compatibility implies the actual rational intersection equations. -/
theorem algebraFamily_compatible (s : ∀ i : Fin c.size, (c.obj i).algebra)
    (hs : c.AlgebraCompatible s) :
    ∀ i j,
      (RationalChart.interLeft (r.chart i) (r.chart j)).restriction
          (r.algebraFamily s i) =
        (RationalChart.interRight (r.chart i) (r.chart j)).restriction
          (r.algebraFamily s j) := by
  intro i j
  exact hs (r.index i) (r.index j)
    (U.extend ((r.chart i).inter (r.chart j)).toDomain)
    (U.extendFunctor.map ((RationalChart.toDomainFunctor K U.algebra).map
      (RationalChart.interLeft (r.chart i) (r.chart j))) ≫ r.map i)
    (U.extendFunctor.map ((RationalChart.toDomainFunctor K U.algebra).map
      (RationalChart.interRight (r.chart i) (r.chart j))) ≫ r.map j)

/-- Agreement with the refined rational family implies agreement with every
original component, by testing on pulled rational intersections. -/
theorem restrict_eq_of_refined_eq
    (s : ∀ i : Fin c.size, (c.obj i).algebra) (hs : c.AlgebraCompatible s)
    (a : U.algebra) (ha : ∀ j, (r.chart j).baseMap a = r.algebraFamily s j) :
    c.algebraRestrict a = s := by
  funext i
  let V := U.relative (c.obj i) (c.map i)
  apply rational_ext (fun j => RationalChart.pullback V.baseMap (r.chart j))
    (by
      intro x
      obtain ⟨j, hj⟩ := r.covers ((c.map i).spectrumMap x)
      refine ⟨j, ?_⟩
      rw [RationalChart.pullback_locus]
      exact hj)
  intro j
  let W := V.rationalInter (r.chart j)
  let f : U.extend W ⟶ c.obj i :=
    U.extendFunctor.map (V.rationalInterLeft (r.chart j)) ≫
      (U.extendRelativeOfInjectiveIso U.spectrumMap_injective (c.obj i) (c.map i)).hom
  let g : U.extend W ⟶ U.extend (r.chart j).toDomain :=
    U.extendFunctor.map (V.rationalInterRight (r.chart j))
  change (V.rationalInterLeft (r.chart j)).restriction
      ((c.map i).restriction a) =
    (V.rationalInterLeft (r.chart j)).restriction (s i)
  calc
    (V.rationalInterLeft (r.chart j)).restriction ((c.map i).restriction a) =
        (V.rationalInterRight (r.chart j)).restriction ((r.chart j).baseMap a) :=
      congrArg (fun q : BoundedAlgHom K U.algebra W.algebra => q a)
        ((V.rationalInterLeft (r.chart j)).comp_baseMap.trans
          (V.rationalInterRight (r.chart j)).comp_baseMap.symm)
    _ = (V.rationalInterRight (r.chart j)).restriction (r.algebraFamily s j) :=
      congrArg (V.rationalInterRight (r.chart j)).restriction (ha j)
    _ = (V.rationalInterLeft (r.chart j)).restriction (s i) :=
      (hs i (r.index j) (U.extend W) f (g ≫ r.map j)).symm

end RelativeRationalRefinement

/-- Compatible actual algebra sections on any finite full-domain cover
uniquely glue in the stored algebra of the target. -/
theorem algebra_existsUnique (c : FiniteCover U)
    (s : ∀ i : Fin c.size, (c.obj i).algebra) (hs : c.AlgebraCompatible s) :
    ∃! a : U.algebra, c.algebraRestrict a = s := by
  let r := c.relativeRationalRefinement
  obtain ⟨a, ha, _⟩ := RationalChart.wholeSpectrumRationalGluing
    K U.algebra (Fin r.size) r.chart r.covers
    (r.algebraFamily s) (r.algebraFamily_compatible s hs)
  refine ⟨a, r.restrict_eq_of_refined_eq s hs a ha, ?_⟩
  intro b hb
  apply c.algebra_ext_of_restrict_eq
  intro i
  exact congrFun (hb.trans (r.restrict_eq_of_refined_eq s hs a ha).symm) i

/-- The actual element obtained by finite rational descent. -/
def algebraGlue (c : FiniteCover U)
    (s : ∀ i : Fin c.size, (c.obj i).algebra) (hs : c.AlgebraCompatible s) :
    U.algebra :=
  (c.algebra_existsUnique s hs).choose

@[simp]
theorem algebraRestrict_glue (c : FiniteCover U)
    (s : ∀ i : Fin c.size, (c.obj i).algebra) (hs : c.AlgebraCompatible s) :
    c.algebraRestrict (c.algebraGlue s hs) = s :=
  (c.algebra_existsUnique s hs).choose_spec.1

@[simp]
theorem algebraGlue_restrict (c : FiniteCover U) (a : U.algebra) :
    c.algebraGlue (c.algebraRestrict a) (c.algebraCompatible_restrict a) = a := by
  apply c.algebra_ext_of_restrict_eq
  intro i
  exact congrFun (c.algebraRestrict_glue _ _) i

/-- Stored elements are exactly the full-test-compatible local algebra families. -/
def algebraGluingEquiv (c : FiniteCover U) :
    U.algebra ≃ {s : ∀ i : Fin c.size, (c.obj i).algebra // c.AlgebraCompatible s} where
  toFun a := ⟨c.algebraRestrict a, c.algebraCompatible_restrict a⟩
  invFun s := c.algebraGlue s.val s.property
  left_inv := c.algebraGlue_restrict
  right_inv s := Subtype.ext (c.algebraRestrict_glue s.val s.property)

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover
