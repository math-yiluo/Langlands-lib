import Langlands.GroupScheme.AffinePointCoordinateJet
import Langlands.GroupScheme.ProductCoordinateSmooth
import Langlands.GroupScheme.MatrixRepresentationProductDifferentialConjugation
import Langlands.GroupScheme.GeneralLinearPointTopology

/-! # First jets on actual finite products of general linear schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped Classical CategoryTheory.MonObj Topology TensorProduct

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}} {B : Type u}
  [NormedCommRing B] [NormedAlgebra ℝ B] [Algebra R B]

namespace GeneralLinear

variable (n : Type) [Fintype n] [DecidableEq n]

/-- A matrix curve has the prescribed dual-number first jet on its entries
and inverse entries. -/
def ValuesJet (g : ℝ → GL n B) (q : GL n (DualNumber B)) (t : ℝ) : Prop :=
  ∀ i, (values q i).fst = values (g t) i ∧
    HasDerivAt (fun s => values (g s) i) (values q i).snd t

private theorem jet_classify (g : ℝ → GL n B) (q : GL n (DualNumber B)) (t : ℝ)
    (h : ∀ i, (values q i).fst = values (g t) i ∧
      HasDerivAt (fun s => values (g s) i) (values q i).snd t)
    (a : CoordinateRing n R) :
    (classify (R := R) q a).fst = classify (R := R) (g t) a ∧
      HasDerivAt (fun s => classify (R := R) (g s) a) (classify (R := R) q a).snd t := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  change (classify (R := R) q (quotient n R p)).fst =
      classify (R := R) (g t) (quotient n R p) ∧
    HasDerivAt (fun s => classify (R := R) (g s) (quotient n R p))
      (classify (R := R) q (quotient n R p)).snd t
  simp_rw [classify_quotient]
  induction p using MvPolynomial.induction_on with
  | C r =>
      simp only [aeval_C]
      exact ⟨rfl, hasDerivAt_const t _⟩
  | add p q hp hq =>
      simp only [map_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add]
      exact ⟨congrArg₂ (· + ·) hp.1 hq.1, hp.2.add hq.2⟩
  | mul_X p i hp =>
      simp only [map_mul, aeval_X, TrivSqZeroExt.fst_mul]
      refine ⟨by rw [hp.1, (h i).1], ?_⟩
      convert! (hp.2.mul (h i).2) using 1
      simp only [TrivSqZeroExt.snd_mul, smul_eq_mul, op_smul_eq_smul,
        hp.1, (h i).1, mul_comm, add_comm]

/-- Entry and inverse-entry jets determine the jet of every actual regular
function on the general linear scheme. -/
theorem coordinateJet_of_values (g : ℝ → GL n B) (q : GL n (DualNumber B)) (t : ℝ)
    (h : ValuesJet n g q t) :
    (groupScheme n R).CoordinateJet
      (fun s => (affinePointsEquiv n R (CommAlgCat.of R B)).symm (g s))
      ((affinePointsEquiv n R (CommAlgCat.of R (DualNumber B))).symm q) t := by
  intro a
  change ((groupScheme n R).affinePointEvaluation (CommAlgCat.of R (DualNumber B))
      ((affinePointsEquiv n R (CommAlgCat.of R (DualNumber B))).symm q) a).fst =
      (groupScheme n R).affinePointEvaluation (CommAlgCat.of R B)
        ((affinePointsEquiv n R (CommAlgCat.of R B)).symm (g t)) a ∧
    HasDerivAt (fun s => (groupScheme n R).affinePointEvaluation (CommAlgCat.of R B)
      ((affinePointsEquiv n R (CommAlgCat.of R B)).symm (g s)) a)
      ((groupScheme n R).affinePointEvaluation (CommAlgCat.of R (DualNumber B))
        ((affinePointsEquiv n R (CommAlgCat.of R (DualNumber B))).symm q) a).snd t
  have he (A : CommAlgCat.{u} R) (g' : GL n A) :
      (groupScheme n R).affinePointEvaluation A
        ((affinePointsEquiv n R A).symm g') a =
      classify g' ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing n R))).hom a) := by
    rw [affinePointsEquiv_symm_apply (n := n) (R := R) A g']
    exact affinePointEvaluation_map_classify n R A g' a
  simp_rw [he]
  exact jet_classify n g q t h _

end GeneralLinear

section Products

variable {J : Type u} [Finite J]
  (G : J → GroupScheme (Spec R)) [∀ j, IsAffine (G j).X.left]

private theorem coordinateJet_list_prod (l : List J)
    (p : J → ℝ → (pi G).affinePoints (CommAlgCat.of R B))
    (q : J → (pi G).affinePoints (CommAlgCat.of R (DualNumber B))) (t : ℝ)
    (h : ∀ j, (pi G).CoordinateJet (p j) (q j) t) :
    (pi G).CoordinateJet (fun s => (l.map (fun j => p j s)).prod)
      (l.map q).prod t := by
  let : IsAffine (pi G).X.left := isAffine_pi G
  induction l with
  | nil =>
      have hc := coordinateJet_const (pi G)
        (1 : (pi G).affinePoints (CommAlgCat.of R B)) t
      simpa only [map_one, List.map_nil, List.prod_nil] using hc
  | cons j l ih =>
      simpa only [List.map_cons, List.prod_cons] using (h j).mul (G := pi G) ih

/-- First jets assemble along the actual finite product point equivalence. -/
theorem coordinateJet_piPointsEquiv_symm
    (p : ∀ j, ℝ → (G j).affinePoints (CommAlgCat.of R B))
    (q : ∀ j, (G j).affinePoints (CommAlgCat.of R (DualNumber B))) (t : ℝ)
    (h : ∀ j, (G j).CoordinateJet (p j) (q j) t) :
    (pi G).CoordinateJet
      (fun s => (piPointsEquiv G ((algSpec R).obj (op (CommAlgCat.of R B)))).symm
        (fun j => p j s))
      ((piPointsEquiv G ((algSpec R).obj (op (CommAlgCat.of R (DualNumber B))))).symm q)
      t := by
  let := Fintype.ofFinite J
  have hh := coordinateJet_list_prod G Finset.univ.toList
    (fun j s => p j s ≫ piFactorInclusion G j)
    (fun j => q j ≫ piFactorInclusion G j) t
    (fun j => (h j).postcomp (piFactorInclusion G j))
  have hp (s : ℝ) :=
    piPointsEquiv_symm_eq_list_prod G ((algSpec R).obj (op (CommAlgCat.of R B)))
      (fun j => p j s) Finset.univ.toList (Finset.nodup_toList _) (by simp)
  have hq :=
    piPointsEquiv_symm_eq_list_prod G ((algSpec R).obj (op (CommAlgCat.of R (DualNumber B))))
      q Finset.univ.toList (Finset.nodup_toList _) (by simp)
  simpa only [← hp, ← hq] using hh

end Products

namespace GeneralLinearProductDualNumber

variable {J : Type u} [Finite J]
  {n : J → Type} [∀ j, Fintype (n j)] [∀ j, DecidableEq (n j)]

local instance factorAffine (j : J) :
    IsAffine (GeneralLinear.groupScheme (n j) R).X.left :=
  GeneralLinear.isAffine_groupScheme (n j) R

/-- The original matrix point equivalence preserves jets detected on every
factor's entries and inverse entries. -/
theorem coordinateJet_affineMatrixEquiv_symm
    (g : ℝ → ∀ j, GL (n j) B) (q : ∀ j, GL (n j) (DualNumber B)) (t : ℝ)
    (h : ∀ j i, (GeneralLinear.values (q j) i).fst = GeneralLinear.values (g t j) i ∧
      HasDerivAt (fun s => GeneralLinear.values (g s j) i)
        (GeneralLinear.values (q j) i).snd t) :
    (groupScheme n R).CoordinateJet
      (fun s => (affineMatrixEquiv (n := n) (R := R) B).symm (g s))
      ((affineMatrixEquiv (n := n) (R := R) (DualNumber B)).symm q) t :=
  coordinateJet_piPointsEquiv_symm (fun j => GeneralLinear.groupScheme (n j) R)
    _ _ t (fun j => GeneralLinear.coordinateJet_of_values (n j) _ _ t (h j))

end GeneralLinearProductDualNumber

end Langlands.GroupScheme
