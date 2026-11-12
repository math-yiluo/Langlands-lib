import Langlands.Representation.CuspidalSupport.CenterActionSpan
import Langlands.Representation.Category.Subquotients

/-! # Finite support of categorical central projectors

Elementary support control for the last implication of Renard VI.10.8.
This file does not construct the Bernstein projectors.
-/

noncomputable section

open CategoryTheory

namespace Langlands.SmoothRep

universe uR uG uV uI

variable {R : Type uR} [Field R] {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI}

/-- The indices of central transformations acting nontrivially on `A`. -/
def centralOperatorSupport (A : SmoothRep.{uR, uG, uV} R G)
    (e : I → CatCenter (SmoothRep.{uR, uG, uV} R G)) : Set I :=
  {i | (hom ((e i).app A)).toLinearMap ≠ 0}

/-- Nonzero pairwise orthogonal projections are linearly independent. -/
theorem linearIndependent_orthogonal_projections
    {V : Type uV} [AddCommGroup V] [Module R V]
    (p : I → Module.End R V) (hne : ∀ i, p i ≠ 0)
    (hself : ∀ i, (p i).comp (p i) = p i)
    (horth : ∀ i j, i ≠ j → (p i).comp (p j) = 0) :
    LinearIndependent R p := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hc i hi
  have hcomp : (p i).comp (∑ j ∈ s, c j • p j) = c i • p i := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum,
      LinearMap.smul_apply, map_smul]
    rw [Finset.sum_eq_single i]
    · change c i • ((p i).comp (p i)) x = c i • p i x
      rw [hself]
    · intro j hj hji
      change c j • ((p i).comp (p j)) x = 0
      rw [horth i j hji.symm]
      simp
    · intro h
      exact (h hi).elim
  rw [hc, LinearMap.comp_zero] at hcomp
  exact (smul_eq_zero.mp hcomp.symm).resolve_right (hne i)

/-- Only finitely many mutually orthogonal central projections can act
nontrivially through a finite-dimensional centre operator span. -/
theorem finite_centralOperatorSupport (A : SmoothRep.{uR, uG, uV} R G)
    (e : I → CatCenter (SmoothRep.{uR, uG, uV} R G))
    (hcenter : FiniteDimensional R (centerOperatorSpan A))
    (hself : ∀ i, ((hom ((e i).app A)).toLinearMap).comp
      (hom ((e i).app A)).toLinearMap = (hom ((e i).app A)).toLinearMap)
    (horth : ∀ i j, i ≠ j → ((hom ((e i).app A)).toLinearMap).comp
      (hom ((e j).app A)).toLinearMap = 0) :
    (centralOperatorSupport A e).Finite := by
  let := hcenter
  let p : centralOperatorSupport A e → centerOperatorSpan A :=
    fun i => ⟨(hom ((e i.val).app A)).toLinearMap, Submodule.subset_span ⟨e i.val, rfl⟩⟩
  have hlin : LinearIndependent R (fun i : centralOperatorSupport A e =>
      (hom ((e i.val).app A)).toLinearMap) :=
    linearIndependent_orthogonal_projections _ (fun i => i.property)
      (fun i => hself i.val) (fun i j hij => horth i.val j.val
        (fun h => hij (Subtype.ext h)))
  have hlin' : LinearIndependent R p :=
    LinearIndependent.of_comp (centerOperatorSpan A).subtype hlin
  have : Finite (centralOperatorSupport A e) := hlin'.finite
  exact Set.toFinite _

/-- Naturality transfers vanishing of a central operator to an actual
subrepresentation. -/
theorem centerOperator_zero_of_injective
    {A B : SmoothRep.{uR, uG, uV} R G}
    (z : CatCenter (SmoothRep.{uR, uG, uV} R G)) (f : B ⟶ A)
    (hf : Function.Injective (hom f))
    (hz : (hom (z.app A)).toLinearMap = 0) : (hom (z.app B)).toLinearMap = 0 := by
  ext x
  apply hf
  have h := congrArg (fun g : B ⟶ A => hom g x) (z.naturality f)
  change hom (z.app A) (hom f x) = hom f (hom (z.app B) x) at h
  rw [show hom (z.app A) (hom f x) = 0 from congrArg (fun t => t (hom f x)) hz] at h
  simpa using h.symm

/-- Naturality transfers vanishing of a central operator to an actual quotient. -/
theorem centerOperator_zero_of_surjective
    {A B : SmoothRep.{uR, uG, uV} R G}
    (z : CatCenter (SmoothRep.{uR, uG, uV} R G)) (f : A ⟶ B)
    (hf : Function.Surjective (hom f))
    (hz : (hom (z.app A)).toLinearMap = 0) : (hom (z.app B)).toLinearMap = 0 := by
  ext x
  obtain ⟨y, rfl⟩ := hf x
  have h := congrArg (fun g : A ⟶ B => hom g y) (z.naturality f)
  change hom (z.app B) (hom f y) = hom f (hom (z.app A) y) at h
  rw [show hom (z.app A) y = 0 from congrArg (fun t => t y) hz] at h
  simpa using h

/-- Vanishing of a categorical-centre operator passes to every actual smooth
subquotient, including the final isomorphism in the subquotient relation. -/
theorem centerOperator_zero_of_subquotient
    {A B : SmoothRep.{uR, uG, uV} R G}
    (z : CatCenter (SmoothRep.{uR, uG, uV} R G)) (hBA : IsSubquotient B A)
    (hz : (hom (z.app A)).toLinearMap = 0) : (hom (z.app B)).toLinearMap = 0 := by
  obtain ⟨S, T, ⟨f⟩⟩ := hBA
  have hS := centerOperator_zero_of_injective z (subtype A S) (subtype_injective A S) hz
  have hQ := centerOperator_zero_of_surjective z (mkQ (subrepresentation A S) T)
    (mkQ_surjective (subrepresentation A S) T) hS
  exact centerOperator_zero_of_injective z f.hom (equivOfIso f).injective hQ

/-- A central operator acting identically on a nonzero subquotient must act
nontrivially on the original representation. -/
theorem mem_centralOperatorSupport_of_subquotient
    {A B : SmoothRep.{uR, uG, uV} R G} [Nontrivial B]
    (e : I → CatCenter (SmoothRep.{uR, uG, uV} R G)) (i : I)
    (hBA : IsSubquotient B A) (he : (e i).app B = 𝟙 B) :
    i ∈ centralOperatorSupport A e := by
  intro hz
  have hzero := centerOperator_zero_of_subquotient (e i) hBA hz
  obtain ⟨x, hx⟩ := exists_ne (0 : B)
  apply hx
  have h := congrArg (fun t => t x) hzero
  simpa [he] using h

end Langlands.SmoothRep
