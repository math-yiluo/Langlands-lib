import Langlands.Representation.Smooth.IrreducibleCompositionFactors
import Langlands.Representation.Filtration.CentralEigenspaceSplitting
import Langlands.Representation.Filtration.SimpleMapMultiplicityDetectionProof
import Mathlib.Data.Fintype.EquivFin

/-! Simple quotients detected by centrally separated exact classes. -/

noncomputable section

open scoped BigOperators
open Polynomial Langlands.VirtualRepresentation

universe uK uG uV uW

namespace Langlands.CentralEigenspaceSplitting

variable {k : Type uK} [Field k] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module k V]

private def intertwiningToEnd (ρ : Representation k G V) :
    ρ.IntertwiningMap ρ →ₐ[k] Module.End k V where
  toFun f := f.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private def centralAction (ρ : Representation k G V) (z : G)
    (hz : ∀ g, z * g = g * z) : ρ.IntertwiningMap ρ where
  toLinearMap := ρ z
  isIntertwining' g := by
    ext v
    change ρ z (ρ g v) = ρ g (ρ z v)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hz]

private def centralPolynomial (ρ : Representation k G V) (z : G)
    (hz : ∀ g, z * g = g * z) (p : k[X]) : ρ.IntertwiningMap ρ :=
  aeval (centralAction ρ z hz) p

private theorem centralPolynomial_toLinearMap (ρ : Representation k G V) (z : G)
    (hz : ∀ g, z * g = g * z) (p : k[X]) :
    (centralPolynomial ρ z hz p).toLinearMap = aeval (ρ z) p :=
  (aeval_algHom_apply (intertwiningToEnd ρ) (centralAction ρ z hz) p).symm

variable {A : Rep.{uV} k G} {n : ℕ}

/-- The Lagrange projector onto a central eigenspace of a representation
with a filtration having distinct scalar actions. -/
def centralEigenProjection (s : ObjectRepFiltration A n) (z : G)
    (hz : ∀ g, z * g = g * z) (c : Fin n → k)
    (hgr : ∀ i v, (s.gradedRepresentation i).ρ z v = c i • v) (i : Fin n) :
    A.ρ.IntertwiningMap (eigenSubrep A.ρ z hz (c i)).toRepresentation where
  toLinearMap := (centralPolynomial A.ρ z hz (Lagrange.basis Finset.univ c i)).toLinearMap.codRestrict
    (eigenSubrep A.ρ z hz (c i)).toSubmodule (by
      intro v
      rw [centralPolynomial_toLinearMap]
      exact aeval_basis_mem_eigenspace (A.ρ z) c (aeval_nodal_eq_zero s z c hgr) i v)
  isIntertwining' g := by
    ext v
    exact Representation.IntertwiningMap.isIntertwining _ _
      (centralPolynomial A.ρ z hz (Lagrange.basis Finset.univ c i)) g v

/-- Each central eigenspace projector is surjective when the scalars are
pairwise distinct. -/
theorem centralEigenProjection_surjective (s : ObjectRepFiltration A n) (z : G)
    (hz : ∀ g, z * g = g * z) (c : Fin n → k) (hc : Function.Injective c)
    (hgr : ∀ i v, (s.gradedRepresentation i).ρ z v = c i • v) (i : Fin n) :
    Function.Surjective (centralEigenProjection s z hz c hgr i) := by
  intro v
  refine ⟨v.val, Subtype.ext ?_⟩
  change (centralPolynomial A.ρ z hz (Lagrange.basis Finset.univ c i)).toLinearMap v.val = v.val
  rw [centralPolynomial_toLinearMap,
    Module.End.aeval_apply_of_mem_apply_eq_smul (mem_eigenSubrep.mp v.property),
    Lagrange.eval_basis_self hc.injOn (Finset.mem_univ i), one_smul]

/-- An actual quotient map onto each graded piece of a filtration separated
by the action of one central element. -/
def centralGradedProjection (s : ObjectRepFiltration A n) (z : G)
    (hz : ∀ g, z * g = g * z) (c : Fin n → k) (hc : Function.Injective c)
    (hgr : ∀ i v, (s.gradedRepresentation i).ρ z v = c i • v) (i : Fin n) :
    A.ρ.IntertwiningMap (s.gradedRepresentation i).ρ :=
  (eigenEquivGraded s z hz c hc hgr i).toIntertwiningMap.comp
    (centralEigenProjection s z hz c hgr i)

theorem centralGradedProjection_surjective (s : ObjectRepFiltration A n) (z : G)
    (hz : ∀ g, z * g = g * z) (c : Fin n → k) (hc : Function.Injective c)
    (hgr : ∀ i v, (s.gradedRepresentation i).ρ z v = c i • v) (i : Fin n) :
    Function.Surjective (centralGradedProjection s z hz c hc hgr i) :=
  (eigenEquivGraded s z hz c hc hgr i).surjective.comp
    (centralEigenProjection_surjective s z hz c hc hgr i)

end Langlands.CentralEigenspaceSplitting

namespace Langlands.VirtualRepresentation

private theorem mem_range_of_generator_sum_eq
    {ι α β : Type*} [Fintype α] [Fintype β] (f : α → ι) (g : β → ι)
    (h : ∑ i, generator (f i) = ∑ j, generator (g j)) (j : β) :
    ∃ i, f i = g j := by
  classical
  by_contra hn
  push Not at hn
  have hz : (∑ i, generator (f i)) (g j) = 0 := by
    simp [Finsupp.finsetSum_apply, generator, hn]
  rw [h] at hz
  have hp : 0 < ∑ l : β, (generator (g l)) (g j) := by
    apply Finset.sum_pos'
    · intro l _
      simp only [generator, Finsupp.single_apply]
      split_ifs <;> norm_num
    · exact ⟨j, Finset.mem_univ j, by simp [generator]⟩
  exact (ne_of_gt hp) (by simpa only [Finsupp.finsetSum_apply] using hz)

/-- Equality of two finite sums of generators matches their indices when
the labels of one sum are distinct. -/
theorem exists_equiv_of_generator_sum_eq
    {ι α β : Type*} [Fintype α] [Fintype β] (f : α → ι) (g : β → ι)
    (hf : Function.Injective f)
    (h : ∑ i, generator (f i) = ∑ j, generator (g j)) :
    ∃ e : β ≃ α, ∀ j, f (e j) = g j := by
  classical
  have hcard : Fintype.card α = Fintype.card β := by
    have hc := congrArg (extend (fun _ : ι => (1 : ℤ))) h
    have hc' : (Fintype.card α : ℤ) = (Fintype.card β : ℤ) := by
      simpa [extend, generator] using hc
    exact_mod_cast hc'
  choose t ht using mem_range_of_generator_sum_eq f g h
  have hsurj : Function.Surjective t := by
    intro i
    obtain ⟨j, hj⟩ := mem_range_of_generator_sum_eq g f h.symm i
    exact ⟨j, hf ((ht j).trans hj)⟩
  exact ⟨Equiv.ofBijective t
    ((Fintype.bijective_iff_surjective_and_card t).mpr ⟨hsurj, hcard.symm⟩), ht⟩

end Langlands.VirtualRepresentation

namespace Langlands.SmoothRep

open IrreducibleGrothendieckProof CentralEigenspaceSplitting

variable {k : Type uK} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

/-- Exact-class equality preserves every simple quotient of a supplied
composition series whose factors are separated by one central element. -/
theorem exists_surjective_to_graded_of_class_eq
    (A C : SmoothRep.{uK,uG,uV} k G) (hA : A.HasFiniteLength) (hC : C.HasFiniteLength)
    {n : ℕ} (s : ObjectRepFiltration A.obj n) (hs : s.HasSimpleFactors)
    (z : G) (hz : ∀ g, z * g = g * z) (c : Fin n → k) (hc : Function.Injective c)
    (hgr : ∀ i v, (s.gradedRepresentation i).ρ z v = c i • v)
    (hEq : FiniteLengthGrothendieckGroup.ofRepresentation C hC =
      FiniteLengthGrothendieckGroup.ofRepresentation A hA) (i : Fin n) :
    ∃ q : C.representation.IntertwiningMap (s.gradedRepresentation i).ρ,
      Function.Surjective q := by
  classical
  let t := (chosenSeries ⟨C, hC⟩).2.val
  have ht : t.HasSimpleFactors := (chosenSeries ⟨C, hC⟩).2.property
  have hslabel : Function.Injective (fun j => irreducibleIsoClass (gradedSmooth s j) (hs j)) := by
    intro j l he
    obtain ⟨e⟩ := (irreducibleIsoClass_eq_iff_nonempty_equiv (hs j) (hs l)).mp he
    obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (hs j)
    have he' := apply_eq_smul_of_equiv e z (c l) (hgr l) v
    change (s.gradedRepresentation j).ρ z v = c l • v at he'
    have hzero : (c j - c l) • v = 0 := by
      rw [sub_smul, ← hgr j v, ← he', sub_self]
    exact hc (sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hv))
  have hsum : seriesClass s hs = seriesClass t ht := by
    have hf := congrArg factorMap hEq
    simpa only [factorMap_ofRepresentation,
      compositionFactors_eq_series ⟨A, hA⟩ s hs,
      compositionFactors_eq_series ⟨C, hC⟩ t ht] using hf.symm
  obtain ⟨e, he⟩ := exists_equiv_of_generator_sum_eq
    (fun j => irreducibleIsoClass (gradedSmooth s j) (hs j))
    (fun j => irreducibleIsoClass (gradedSmooth t j) (ht j)) hslabel hsum
  let d := c ∘ e
  have hd : Function.Injective d := hc.comp e.injective
  have htgr : ∀ j v, (t.gradedRepresentation j).ρ z v = d j • v := by
    intro j v
    obtain ⟨E⟩ := (irreducibleIsoClass_eq_iff_nonempty_equiv (ht j) (hs (e j))).mp
      (he j).symm
    exact apply_eq_smul_of_equiv E z (d j) (hgr (e j)) v
  let j := e.symm i
  have hlabel : irreducibleIsoClass (gradedSmooth t j) (ht j) =
      irreducibleIsoClass (gradedSmooth s i) (hs i) := by
    simpa only [j, Equiv.apply_symm_apply] using (he j).symm
  obtain ⟨E⟩ := (irreducibleIsoClass_eq_iff_nonempty_equiv (ht j) (hs i)).mp hlabel
  refine ⟨E.toIntertwiningMap.comp (centralGradedProjection t z hz d hd htgr j), ?_⟩
  exact E.surjective.comp (centralGradedProjection_surjective t z hz d hd htgr j)

/-- A nonzero map to an irreducible test object transfers across equality
of exact classes if a central element separates a supplied simple series. -/
theorem exists_surjective_to_simple_of_class_eq
    (A C : SmoothRep.{uK,uG,uV} k G) (hA : A.HasFiniteLength) (hC : C.HasFiniteLength)
    {n : ℕ} (s : ObjectRepFiltration A.obj n) (hs : s.HasSimpleFactors)
    (z : G) (hz : ∀ g, z * g = g * z) (c : Fin n → k) (hc : Function.Injective c)
    (hgr : ∀ i v, (s.gradedRepresentation i).ρ z v = c i • v)
    (hEq : FiniteLengthGrothendieckGroup.ofRepresentation C hC =
      FiniteLengthGrothendieckGroup.ofRepresentation A hA)
    (τ : Rep.{uW} k G) (hτ : τ.ρ.IsIrreducible)
    (f : A.representation.IntertwiningMap τ.ρ) (hf : f ≠ 0) :
    ∃ q : C.representation.IntertwiningMap τ.ρ, Function.Surjective q := by
  have hpos := SimpleMapMultiplicityDetectionProof.positive_of_simple_map hτ
    (s.factorMultiplicity τ) ⟨n, s, hs, rfl⟩ (Or.inr ⟨f, hf⟩)
  have hocc : ∃ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv τ.ρ) := by
    by_contra hn
    push Not at hn
    have : IsEmpty {i : Fin n // Nonempty ((s.gradedRepresentation i).ρ.Equiv τ.ρ)} :=
      ⟨fun i => (hn i.val).false i.property.some⟩
    simp [ObjectRepFiltration.factorMultiplicity] at hpos
  obtain ⟨i, ⟨E⟩⟩ := hocc
  obtain ⟨q, hq⟩ := exists_surjective_to_graded_of_class_eq A C hA hC s hs z hz c hc hgr hEq i
  exact ⟨E.toIntertwiningMap.comp q, E.surjective.comp hq⟩

end Langlands.SmoothRep
