/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Module.DegreeZeroFractions
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineProjChartIsomorphism
import WeilConjectures.AlgebraicGeometry.ProjectiveLinePolynomialProjectionChartIso
import WeilConjectures.AlgebraicGeometry.ProjTwistGluedComparison
import WeilConjectures.AlgebraicGeometry.ProjFiniteTwistCoproductFractions
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineTwist

/-!
# Shifted free graded modules and the glued twists on the projective line

Source: blueprint `theorem-riemann-roch-coherent-serre-duality`, final clause; Stacks Project,
Constructions, Definitions 01M6, 01MN and Lemma 01M7.
(blueprint: lem-sc-p1-proj-shifted-free-twist)

`Proj.twist` is the recorded sheaf of `S(d)`. Its comparison target is the glued
`ProjectiveLine.TwistData`, transported along a chart-compatible scheme isomorphism.
For a finite family, the coproduct is specified as the associated sheaf by injective
section maps onto degree-zero fractions, respecting scalars and canonical restrictions.
The finite direct sum is represented by `Fin r → S`. Its degree-`n` part consists of
vectors whose `i`th component has polynomial degree `a i + n`, with negative parts zero.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite LocalizedModule

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The sheaf of `S(d)` agrees with the twist glued using `g₀ = t⁻ᵈ g₁`, and the
sheaf of a finite direct sum of shifts is the coproduct of their twists.
Source: Stacks Project, Constructions, Definitions 01M6 (3), 01MN (1), Lemma 01M7 (2),(3).
(blueprint: lem-sc-p1-proj-shifted-free-twist)

Proof:
1. On `Uᵢ = D₊(xᵢ)`, def-weil-pbc-proj-twisting-sheaf gives the degree-`d`
   fractions. Multiplication by `xᵢ⁻ᵈ` identifies these with `k[x_{1-i}/xᵢ]`,
   making `xᵢᵈ` a generator on every subopen. The standard charts of
   def-sc-p1-standard identify polynomial Proj with the glued projective line.
2. On the overlap, `x₀ᵈ = (x₀/x₁)ᵈ x₁ᵈ = t⁻ᵈ x₁ᵈ`. Hence these trivializations
   give precisely TwistData. By theorem-riemann-roch-coherent-serre-duality the chart
   identifications glue to the isomorphism with the transported glued twist.
3. Localization and taking the degree-zero part commute with finite direct sums.
   The associated-sheaf description of def-weil-pbc-proj-twisting-sheaf therefore
   identifies the sheaf of the sum with the coproduct of the individual sheaves.
   Componentwise fraction maps give the displayed scalar and restriction formulas,
   including the empty family. Apply the isomorphism of step 2 to each summand.
-/
theorem proj_shifted_free_is_twist (k : Type v) [Field k] (d : ℤ) :
    ∃ C : ProjectiveLine.ProjChartIsomorphism k,
      (∃ (L : (ProjectiveLine (Spec (.of k))).Modules),
        Nonempty (ProjectiveLine.TwistData (Spec (.of k)) d L) ∧
        Nonempty (twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) d ≅
          (Scheme.Modules.tensorPullback C.iso.hom).obj L)) ∧
      (∀ (r : ℕ) (a : Fin r → ℤ),
        ∃ alpha : ∀ (f : MvPolynomial (Fin 2) k) (b : ℕ),
          0 < b → f ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k b →
          (∐ (fun i : Fin r ↦ twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
            (a i))).val.obj (op (basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) f))
            →+ LocalizedModule.Away f (Fin r → MvPolynomial (Fin 2) k),
        (∀ (f : MvPolynomial (Fin 2) k) (b : ℕ) (hb : 0 < b)
          (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k b),
          Function.Injective (alpha f b hb hf) ∧
          Set.range (alpha f b hb hf) = degreeZeroFractions
            (fun n : ℕ ↦ (MvPolynomial.homogeneousSubmodule (Fin 2) k n : Set _))
            (fun n : ℕ ↦ {y : Fin r → MvPolynomial (Fin 2) k | ∀ i,
              if 0 ≤ a i + n then
                y i ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k (a i + n).toNat
              else y i = 0}) (Submonoid.powers f)) ∧
        (∀ (f : MvPolynomial (Fin 2) k) (b : ℕ) (hb : 0 < b)
          (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k b)
          (q : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 2) k) f)
          (s : (∐ (fun i : Fin r ↦ twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
            (a i))).val.obj (op (basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) f))),
          alpha f b hb hf (awayToSection (MvPolynomial.homogeneousSubmodule (Fin 2) k) f q
            • s) = algebraMap
              (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 2) k) f)
              (Localization.Away f) q • alpha f b hb hf s) ∧
        (∀ (f g : MvPolynomial (Fin 2) k) (b c : ℕ) (hb : 0 < b) (hc : 0 < c)
          (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k b)
          (hg : g ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k c)
          (inc : basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) g ≤
            basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) f)
          (e t : ℕ) (h : MvPolynomial (Fin 2) k),
          0 < e → h ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k t → g ^ e = h * f →
          ∀ (m : ℕ) (y : Fin r → MvPolynomial (Fin 2) k)
            (s : (∐ (fun i : Fin r ↦ twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
              (a i))).val.obj
                (op (basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) f))),
            alpha f b hb hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
            alpha g c hc hg ((∐ (fun i : Fin r ↦
              twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (a i))).val.map
                (homOfLE inc).op s) =
              mk (h ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g))) := by
  classical
  have hcov : (⨆ i : ULift.{v} (Fin 2),
      basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X i.down)) =
        ⊤ := by
    have h := iSup_basicOpen_eq_top' (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      MvPolynomial.X (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X k i⟩)
      (MvPolynomial.adjoin_range_X_eq_top (Fin 2) k)
    refine top_le_iff.mp fun x hx ↦ ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (h.ge hx)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  let p := linearProjection (MvPolynomial.homogeneousSubmodule (Fin 2) k)
    (fun j : ULift.{v} (Fin 2) ↦ MvPolynomial.X j.down)
    (fun j ↦ MvPolynomial.X_mem_homogeneousSubmodule_one k j.down) hcov
  have hp : IsIso p := by
    apply (IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := MorphismProperty.isomorphisms Scheme) (f := p) _
      (ProjectiveSpace.iSup_standardOpen (ULift.{v} (Fin 2)) (Spec (.of k)))).mpr
    intro i
    exact isIso_polynomial_linearProjection_restrict k hcov i
  let C : ProjectiveLine.ProjChartIsomorphism k :=
    { iso := asIso p
      chart_eq := fun i ↦ awayι_linearProjection _ _ _ hcov i }
  let L := ProjectiveSpace.twist (ULift.{v} (Fin 2)) (Spec (.of k)) d
  let T := ProjectiveLine.twistData (Spec (.of k)) d
  refine ⟨C, ⟨L, ⟨T⟩, ?_⟩, ?_⟩
  · exact nonempty_twist_iso_tensorPullback_of_twistData k d C L T
  · intro r a
    exact finite_twist_coproduct_fractions (MvPolynomial.homogeneousSubmodule (Fin 2) k) r a

end AlgebraicGeometry.Proj
