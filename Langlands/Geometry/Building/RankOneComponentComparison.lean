import Langlands.Geometry.Building.ChamberProductInjective
import Langlands.GroupScheme.Rational.RootSubgroupPositive
import Langlands.GroupScheme.Rational.WeightVectorUniqueness

/-! # Comparison of opposite-root components and depth sums -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The translations of opposite root functions cancel in their sum, including
when either value is infinite. -/
theorem RootFunctionFamily.opposite_value_sum_vadd
    (φ : RootFunctionFamily S G) (w : V S) (a : characterLattice S)
    (g h : rationalPoints G) :
    (w +ᵥ φ) a g + (w +ᵥ φ) (-a) h = φ a g + φ (-a) h := by
  simp only [RootFunctionFamily.vadd_apply, eval_neg_char]
  calc
    φ a g + (eval S a w : WithTop ℝ) +
        (φ (-a) h + (-eval S a w : ℝ)) =
      (φ a g + φ (-a) h) +
        (((eval S a w + -eval S a w : ℝ)) : WithTop ℝ) := by
      rw [WithTop.coe_add]
      ac_rfl
    _ = φ a g + φ (-a) h := by simp

/-- The opposite-root value sum is invariant under equipollence. -/
theorem Equipollent.opposite_value_sum_eq
    {φ ψ : RootFunctionFamily S G} (hφψ : Equipollent φ ψ)
    (a : characterLattice S) (g h : rationalPoints G) :
    ψ a g + ψ (-a) h = φ a g + φ (-a) h := by
  obtain ⟨w, rfl⟩ := hφψ
  exact φ.opposite_value_sum_vadd w a g h

variable (i : S.toGrp ⟶ G) [IsAffineHom G.X.hom]

/-- Opposite root subgroups and an injectively mapped central factor give an
injective product over any field, for every nonzero split-torus character. -/
theorem oppositeRootTripleProduct_injective_of_isSplitTorus
    (hS : IsSplitTorus S.toGrp) {a : characterLattice S} (ha : a ≠ 0)
    {Z : Type u} (j : Z → rationalPoints G) (hj : Function.Injective j)
    (hcentral : ∀ z, j z ∈ centralizerPoints i) :
    Function.Injective (fun p : rootGroupPoints i (-a) × Z × rootGroupPoints i a =>
      (p.1 : rationalPoints G) * j p.2.1 * (p.2.2 : rationalPoints G)) := by
  obtain ⟨N, hN, ν, hν⟩ := hS.exists_pairing_eq_pos ha
  have hpos : 0 < latticePairing S a ν := by
    rw [hν]
    exact_mod_cast hN
  apply unipotentTripleProduct_injective i ν
    (rootGroupPoints i (-a)) (rootGroupPoints i a) j hj
  · exact RelativeRoot.subgroup_le_dynamicUnipotent i (-ν)
      (by simpa using hpos) (Over.mk (𝟙 _))
  · exact RelativeRoot.subgroup_le_dynamicUnipotent i ν hpos (Over.mk (𝟙 _))
  · exact hcentral

/-- The opposite-root product with its original value in the ambient group. -/
def oppositeRootTripleProductEmbedding
    (hS : IsSplitTorus S.toGrp) {a : characterLattice S} (ha : a ≠ 0)
    {Z : Type u} (j : Z → rationalPoints G) (hj : Function.Injective j)
    (hcentral : ∀ z, j z ∈ centralizerPoints i) :
    (rootGroupPoints i (-a) × Z × rootGroupPoints i a) ↪ rationalPoints G where
  toFun p := (p.1 : rationalPoints G) * j p.2.1 * (p.2.2 : rationalPoints G)
  inj' := oppositeRootTripleProduct_injective_of_isSplitTorus i hS ha j hj hcentral

/-- Two opposite-root factorizations have the same actual centralizer point. -/
theorem centralizerComponent_eq_of_root_factorizations
    (hS : IsSplitTorus S.toGrp) (C : CentralizerDatum i)
    {a : characterLattice S} (ha : a ≠ 0)
    {v' v w' w : rationalPoints G} {z t : rationalPoints C.Z}
    (hv' : v' ∈ rootGroupPoints i (-a)) (hv : v ∈ rootGroupPoints i a)
    (hw' : w' ∈ rootGroupPoints i (-a)) (hw : w ∈ rootGroupPoints i a)
    (heq : v' * rationalPoints.map C.j z * v =
      w' * rationalPoints.map C.j t * w) : z = t := by
  have hj : Function.Injective (rationalPoints.map C.j) := by
    have : Mono C.j.hom.hom := C.isRepresentedBy.1
    intro z t h
    exact (cancel_mono C.j.hom.hom).mp h
  have h :=
    oppositeRootTripleProduct_injective_of_isSplitTorus i hS ha
      (rationalPoints.map C.j) hj
      (map_mem_centralizerPoints C.isRepresentedBy)
      (a₁ := (⟨v', hv'⟩, z, ⟨v, hv⟩))
      (a₂ := (⟨w', hw'⟩, t, ⟨w, hw⟩)) heq
  exact congrArg (fun p : rootGroupPoints i (-a) × rationalPoints C.Z ×
    rootGroupPoints i a => p.2.1) h

namespace KPApartmentData

variable [Mono i.hom.hom.left] {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- The sum of opposite root values is independent of the apartment point. -/
theorem opposite_value_sum_eq (x y : D.Apartment) (a : characterLattice S)
    (g h : rationalPoints G) :
    x.val a g + x.val (-a) h = y.val a g + y.val (-a) h :=
  (D.equipollent_of_mem y.mem x.mem).opposite_value_sum_eq a g h

end KPApartmentData

end Langlands.Geometry.Building
