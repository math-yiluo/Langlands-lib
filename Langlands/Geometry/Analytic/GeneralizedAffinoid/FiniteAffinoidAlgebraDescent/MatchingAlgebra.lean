import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.LocalData
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Topology.MetricSpace.Ultra.Pi

/-! # The complete bounded matching algebra of finite local algebras -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K}
  {c : Domain.FiniteCover (Domain.whole K R)} {F : LocalAlgebras c}

theorem restriction_baseMap {E D : Domain K R} (h : E.locus ⊆ D.locus) :
    (restriction h).comp D.baseMap = E.baseMap :=
  (Domain.inclusionOfSubset E D h).comp_baseMap

namespace LocalAlgebras

/-- The original bounded structural map on the component. -/
def structuralMap (F : LocalAlgebras c) (i : Fin c.size) :
    BoundedAlgHom K R (F.algebra i) :=
  (F.map i).comp (c.map i).restriction

theorem structuralMap_eq (F : LocalAlgebras c) (i : Fin c.size) :
    F.structuralMap i = (F.map i).comp (c.obj i).baseMap := by
  have h : (c.map i).restriction = (c.obj i).baseMap := (c.map i).comp_baseMap
  rw [structuralMap, h]

end LocalAlgebras

namespace PairTransitions

variable (t : PairTransitions F)

/-- The first local algebra is transported to the second intersection model. -/
def leftRestriction (i j : Fin c.size) :
    BoundedAlgHom K (F.algebra i)
      (F.baseChange j (F.overlap i j) (F.overlapRight i j)) :=
  (t.equiv i j).toBoundedAlgHom.comp
    (F.localMap i (F.overlap i j) (F.overlapLeft i j))

/-- The second local algebra maps by the original first pushout leg. -/
def rightRestriction (_t : PairTransitions F) (i j : Fin c.size) :
    BoundedAlgHom K (F.algebra j)
      (F.baseChange j (F.overlap i j) (F.overlapRight i j)) :=
  F.localMap j (F.overlap i j) (F.overlapRight i j)

/-- The finite product carries its actual maximum norm. -/
abbrev Product (_t : PairTransitions F) := ∀ i : Fin c.size, F.algebra i

/-- The matching equations are equations in the actual intersection quotients. -/
def matchingSubalgebra : Subalgebra K t.Product where
  carrier := {s | ∀ i j, t.leftRestriction i j (s i) = t.rightRestriction i j (s j)}
  zero_mem' := by intro i j; simp only [Pi.zero_apply, map_zero]
  one_mem' := by intro i j; simp only [Pi.one_apply, map_one]
  add_mem' := by
    intro s a hs ha i j
    change t.leftRestriction i j (s i + a i) = t.rightRestriction i j (s j + a j)
    rw [map_add, map_add, hs i j, ha i j]
  mul_mem' := by
    intro s a hs ha i j
    change t.leftRestriction i j (s i * a i) = t.rightRestriction i j (s j * a j)
    rw [map_mul, map_mul, hs i j, ha i j]
  algebraMap_mem' := by
    intro a i j
    exact ((t.leftRestriction i j).toAlgHom.commutes a).trans
      ((t.rightRestriction i j).toAlgHom.commutes a).symm

theorem isClosed_matchingSubalgebra :
    IsClosed (t.matchingSubalgebra : Set t.Product) := by
  change IsClosed {s : t.Product | ∀ i j,
    t.leftRestriction i j (s i) = t.rightRestriction i j (s j)}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq ((t.leftRestriction i j).continuous.comp (continuous_apply i))
      ((t.rightRestriction i j).continuous.comp (continuous_apply j))

/-- The matching Banach algebra is constructed before any affinoid realization. -/
abbrev MatchingAlgebra := t.matchingSubalgebra

instance : CompleteSpace t.MatchingAlgebra := t.isClosed_matchingSubalgebra.completeSpace_coe

instance : IsUltrametricDist t.MatchingAlgebra := inferInstanceAs
  (IsUltrametricDist {s : t.Product // s ∈ t.matchingSubalgebra})

def projection (i : Fin c.size) :
    BoundedAlgHom K t.MatchingAlgebra (F.algebra i) where
  toAlgHom := (Pi.evalAlgHom K (fun i => F.algebra i) i).comp t.matchingSubalgebra.val
  bounded := ⟨1, zero_lt_one, fun s => by
    change ‖s.val i‖ ≤ 1 * ‖s.val‖
    simpa only [one_mul] using norm_le_pi_norm s.val i⟩

@[simp] theorem projection_apply (i : Fin c.size) (s : t.MatchingAlgebra) :
    t.projection i s = s.val i := rfl

theorem projection_overlap (i j : Fin c.size) :
    (t.leftRestriction i j).comp (t.projection i) =
      (t.rightRestriction i j).comp (t.projection j) :=
  BoundedAlgHom.ext fun s => s.property i j

@[ext] theorem matching_ext {s a : t.MatchingAlgebra}
    (h : ∀ i, t.projection i s = t.projection i a) : s = a :=
  Subtype.ext (funext h)

variable {A : Type v} [NormedCommRing A] [Algebra K A]

/-- Compatibility of entire bounded maps, including nonreduced test algebras. -/
def MapCompatible (f : ∀ i : Fin c.size, BoundedAlgHom K A (F.algebra i)) : Prop :=
  ∀ i j, (t.leftRestriction i j).comp (f i) =
    (t.rightRestriction i j).comp (f j)

variable (f : ∀ i : Fin c.size, BoundedAlgHom K A (F.algebra i))
  (hf : t.MapCompatible f)

/-- Construct the bounded map into the matching algebra using a uniform finite
bound; no open mapping theorem or nontrivial valuation is involved. -/
def lift : BoundedAlgHom K A t.MatchingAlgebra where
  toAlgHom := (AlgHom.pi fun i => (f i).toAlgHom).codRestrict t.matchingSubalgebra
    (fun a i j => congrArg (fun q : BoundedAlgHom K A
      (F.baseChange j (F.overlap i j) (F.overlapRight i j)) => q a) (hf i j))
  bounded := by
    choose M hMpos hM using fun i => (f i).bounded
    have hsum : 0 ≤ ∑ i, M i := Finset.sum_nonneg fun i _ => (hMpos i).le
    refine ⟨(∑ i, M i) + 1, by linarith, fun a => ?_⟩
    change ‖fun i => f i a‖ ≤ ((∑ i, M i) + 1) * ‖a‖
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by linarith) (norm_nonneg a))).2
    intro i
    have hMi : M i ≤ (∑ j, M j) + 1 := by
      have := Finset.single_le_sum (fun j _ => (hMpos j).le) (Finset.mem_univ i)
      linarith
    exact (hM i a).trans (mul_le_mul_of_nonneg_right hMi (norm_nonneg a))

@[simp] theorem projection_comp_lift (i : Fin c.size) :
    (t.projection i).comp (t.lift f hf) = f i := rfl

theorem hom_ext {g h : BoundedAlgHom K A t.MatchingAlgebra}
    (hgh : ∀ i, (t.projection i).comp g = (t.projection i).comp h) : g = h := by
  apply BoundedAlgHom.ext
  intro a
  apply t.matching_ext
  intro i
  exact congrArg (fun q : BoundedAlgHom K A (F.algebra i) => q a) (hgh i)

/-- The constructed complete matching algebra has the full bounded equalizer
universal property for arbitrary normed commutative test algebras. -/
def boundedHomEquiv : BoundedAlgHom K A t.MatchingAlgebra ≃
    {f : ∀ i : Fin c.size, BoundedAlgHom K A (F.algebra i) // t.MapCompatible f} where
  toFun g := ⟨fun i => (t.projection i).comp g, fun i j =>
    congrArg (fun q : BoundedAlgHom K t.MatchingAlgebra
      (F.baseChange j (F.overlap i j) (F.overlapRight i j)) => q.comp g)
        (t.projection_overlap i j)⟩
  invFun f := t.lift f.val f.property
  left_inv _g := t.hom_ext fun _ => rfl
  right_inv _f := Subtype.ext (funext fun _ => rfl)

theorem structuralMap_compatible : t.MapCompatible F.structuralMap := by
  intro i j
  rw [F.structuralMap_eq, F.structuralMap_eq]
  change ((t.equiv i j).toBoundedAlgHom.comp
    (F.localMap i (F.overlap i j) _)).comp
      ((F.map i).comp (c.obj i).baseMap) =
        (F.localMap j (F.overlap i j) _).comp
          ((F.map j).comp (c.obj j).baseMap)
  rw [BoundedAlgHom.comp_assoc (t.equiv i j).toBoundedAlgHom,
    ← BoundedAlgHom.comp_assoc (F.localMap i (F.overlap i j) _),
    F.condition, BoundedAlgHom.comp_assoc,
    restriction_baseMap, ← BoundedAlgHom.comp_assoc, t.over_base,
    ← BoundedAlgHom.comp_assoc (F.localMap j (F.overlap i j) _),
    F.condition, BoundedAlgHom.comp_assoc, restriction_baseMap]

/-- The original structural map from R is constructed in the complete matching
algebra, before any claim of affinoidness or finiteness. -/
def structuralMap : BoundedAlgHom K R t.MatchingAlgebra :=
  t.lift F.structuralMap t.structuralMap_compatible

@[simp] theorem projection_structuralMap (i : Fin c.size) :
    (t.projection i).comp t.structuralMap = F.structuralMap i := rfl

end PairTransitions
end Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent
