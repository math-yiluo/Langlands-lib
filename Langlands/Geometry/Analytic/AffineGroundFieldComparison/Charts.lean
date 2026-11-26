import Langlands.Geometry.Analytic.AffineAnalytificationChartBaseChangeStatement
import Langlands.Geometry.Analytic.AffineAnalytificationGroundFieldComparisonStatement

/-! # Mixed-radius bounded pullbacks for the affine ground field comparison -/

noncomputable section

universe u u' v

namespace Langlands.Analytic.AffineAnalytification.GroundFieldComparison

open Set Topology PresentedAffinoidAlgebra
open PresentedAffinoidAlgebra.GroundFieldExtension
open scoped TensorProduct

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)

/-- The presentation of `L ⊗[K] A` by the scalar-extended generators. -/
abbrev Q := baseChangePresentation K L P
/-- The chart system of the ground field extension of the affine atlas of `P`. -/
abbrev S := IndexedAffinoidAtlas.GroundFieldExtension.chartSystem K L (atlas K P)
/-- The polyradius of the selected original chart `i`. -/
abbrev rK (i : ChartIndex K P) := AnalyticAffineSpace.polyradius K P.arity i.val
/-- The polyradius of the raw `L`-chart `n` of `Q`. -/
abbrev rL (n : ℕ) := AnalyticAffineSpace.polyradius L (Q K L P).arity n
/-- The scalar extension to `L` of the original chart algebra at `i`. -/
abbrev E (i : ChartIndex K P) := (S K L P).algebra i
/-- The chart algebra of `Q` at the radius of the original chart `i`. -/
abbrev C (i : ChartIndex K P) := PolynomialLocus.chart (Q K L P) (rK K P i)

variable (hfixed : AffineAnalytificationChartBaseChangeStatement.{u, u', v})

/-- Fixed-radius comparison, in the direction from the extended original algebra. -/
def eAt (i : ChartIndex K P) : BoundedAlgEquiv L (E K L P i) (C K L P i) :=
  Classical.choose (hfixed K L A P (rK K P i))

theorem eAt_algebraMap (i : ChartIndex K P) (a : A) :
    eAt K L P hfixed i (iota K L (algebra K P i.val) (PolynomialLocus.algebraMap P (rK K P i) a)) =
      PolynomialLocus.algebraMap (Q K L P) (rK K P i) ((1 : L) ⊗ₜ[K] a) :=
  Classical.choose_spec (hfixed K L A P (rK K P i)) a

/-- Pull back a raw `L`-chart to the extended selected `K`-chart, whenever
its radius bounds the original radius numerically. -/
def rawPull (i : ChartIndex K P) (n : ℕ)
    (hn : AnalyticAffineSpace.radius K i.val ≤ AnalyticAffineSpace.radius L n) :
    BoundedAlgHom L (algebra L (Q K L P) n) (E K L P i) :=
  (eAt K L P hfixed i).symm.toBoundedAlgHom.comp
    (PolynomialLocus.restriction (Q K L P) (rL K L P n) (rK K P i) (fun _ => hn))

theorem rawPull_algebraMap (i : ChartIndex K P) (n : ℕ)
    (hn : AnalyticAffineSpace.radius K i.val ≤ AnalyticAffineSpace.radius L n) (a : A) :
    rawPull K L P hfixed i n hn
      (PolynomialLocus.algebraMap (Q K L P) (rL K L P n) ((1 : L) ⊗ₜ[K] a)) =
        iota K L (algebra K P i.val) (PolynomialLocus.algebraMap P (rK K P i) a) := by
  have h₁ := PolynomialLocus.restriction_algebraMap (Q K L P) (rL K L P n)
    (rK K P i) (fun _ => hn) ((1 : L) ⊗ₜ[K] a)
  refine (congrArg (fun x : C K L P i => (eAt K L P hfixed i).symm x) h₁).trans ?_
  exact (congrArg (fun x : C K L P i => (eAt K L P hfixed i).symm x)
    (eAt_algebraMap K L P hfixed i a).symm).trans ((eAt K L P hfixed i).symm_apply_apply _)

theorem rawPull_coordinate (i : ChartIndex K P) (n : ℕ)
    (hn : AnalyticAffineSpace.radius K i.val ≤ AnalyticAffineSpace.radius L n)
    (t : Fin P.arity) :
    rawPull K L P hfixed i n hn (coordinate L (algebra L (Q K L P) n) t) =
      coordinate L (E K L P i) t := by
  have hL : PolynomialLocus.algebraMap (Q K L P) (rL K L P n)
      ((1 : L) ⊗ₜ[K] P.map (MvPolynomial.X t)) = coordinate L (algebra L (Q K L P) n) t :=
    (congrArg (fun a : L ⊗[K] A => PolynomialLocus.algebraMap (Q K L P) (rL K L P n) a)
      (baseChangePresentation_map_X K L P t).symm).trans
      ((PolynomialLocus.algebraMap_map (Q K L P) (rL K L P n) (MvPolynomial.X t)).trans
        (PolynomialLocus.polynomialMap_X (Q K L P) (rL K L P n) t))
  have hK : PolynomialLocus.algebraMap P (rK K P i) (P.map (MvPolynomial.X t)) =
      coordinate K (algebra K P i.val) t :=
    (PolynomialLocus.algebraMap_map P (rK K P i) (MvPolynomial.X t)).trans
      (PolynomialLocus.polynomialMap_X P (rK K P i) t)
  exact (congrArg (fun a : algebra L (Q K L P) n => rawPull K L P hfixed i n hn a) hL).symm.trans
    ((rawPull_algebraMap K L P hfixed i n hn _).trans
      ((congrArg (fun a : algebra K P i.val => iota K L (algebra K P i.val) a) hK).trans
        (iota_coordinate K L (algebra K P i.val) t)))

theorem rawPull_comp (i : ChartIndex K P) {m n : ℕ} (h : m ≤ n)
    (hm : AnalyticAffineSpace.radius K i.val ≤ AnalyticAffineSpace.radius L m)
    (hn : AnalyticAffineSpace.radius K i.val ≤ AnalyticAffineSpace.radius L n) :
    (rawPull K L P hfixed i m hm).comp (restriction L (Q K L P) h) =
      rawPull K L P hfixed i n hn := by
  unfold rawPull AffineAnalytification.restriction
  rw [BoundedAlgHom.comp_assoc]
  exact congrArg ((eAt K L P hfixed i).symm.toBoundedAlgHom.comp)
    (PolynomialLocus.restriction_trans (Q K L P) (rL K L P n) (rL K L P m)
      (AnalyticAffineSpace.polyradius_le L (Q K L P).arity h) (rK K P i) (fun _ => hm)).symm

open IndexedAffinoidAtlas.GroundFieldExtension in
theorem rawPull_sub (i j : ChartIndex K P) (h : (S K L P).Sub i j) (n : ℕ)
    (hi : AnalyticAffineSpace.radius K i.val ≤ AnalyticAffineSpace.radius L n)
    (hj : AnalyticAffineSpace.radius K j.val ≤ AnalyticAffineSpace.radius L n) :
    ((S K L P).restriction i j h).comp (rawPull K L P hfixed j n hj) =
      rawPull K L P hfixed i n hi := by
  apply hom_ext_coordinate L (E K L P i) (algebra L (Q K L P) n)
  intro t
  have hrad := (selected_range_subset_iff K P i j).1 h
  let φ : BoundedAlgHom K (algebra K P j.val) (algebra K P i.val) :=
    AffineAnalytification.restriction K P hrad
  have hφ : φ (coordinate K (algebra K P j.val) t) = coordinate K (algebra K P i.val) t :=
    PolynomialLocus.restriction_coordinate P _ _ (AnalyticAffineSpace.polyradius_le K P.arity hrad) t
  change map K L φ (rawPull K L P hfixed j n hj (coordinate L (algebra L (Q K L P) n) t)) = _
  exact (congrArg (fun x : E K L P j => map K L φ x)
    (rawPull_coordinate K L P hfixed j n hj t)).trans
      ((map_coordinate (L := L) φ t).trans
        ((congrArg (fun x : algebra K P i.val => iota K L (algebra K P i.val) x) hφ).trans
          ((iota_coordinate K L (algebra K P i.val) t).trans
            (rawPull_coordinate K L P hfixed i n hi t).symm)))

theorem rawPull_represents (i : ChartIndex K P) (n : ℕ)
    (hn : AnalyticAffineSpace.radius K i.val ≤ AnalyticAffineSpace.radius L n) :
    Represents L (rawPull K L P hfixed i n hn)
      {x | ∀ t, x (coordinate L (algebra L (Q K L P) n) t) ≤ AnalyticAffineSpace.radius K i.val} :=
  (PolynomialLocus.represents_restriction (Q K L P) (rL K L P n) (rK K P i)
    (fun _ => hn)).postcomp_equiv (eAt K L P hfixed i).symm

end Langlands.Analytic.AffineAnalytification.GroundFieldComparison
