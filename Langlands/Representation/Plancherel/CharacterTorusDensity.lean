import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Principal open subsets of complex character tori -/

noncomputable section

open Set Topology

namespace Langlands.Plancherel

universe u v

variable {ι : Type u}

/-- The nonvanishing locus of a polynomial on a complex multiplicative torus. -/
def complexTorusPrincipalOpen (p : MvPolynomial ι ℂ) : Set (ι → ℂˣ) :=
  {z | MvPolynomial.eval (fun i => (z i : ℂ)) p ≠ 0}

/-- Polynomial nonvanishing is open in the usual topology of the complex torus. -/
theorem isOpen_complexTorusPrincipalOpen (p : MvPolynomial ι ℂ) :
    IsOpen (complexTorusPrincipalOpen p) := by
  have h : Continuous (fun z : ι → ℂˣ =>
      MvPolynomial.eval (fun i => (z i : ℂ)) p) :=
    p.continuous_eval.comp (continuous_pi fun i =>
      Units.continuous_val.comp (continuous_apply i))
  exact isOpen_ne_fun h continuous_const

/-- A nonzero polynomial has dense nonvanishing locus in finite complex affine space. -/
theorem dense_complexPolynomial_nonvanishing [Finite ι]
    (p : MvPolynomial ι ℂ) (hp : p ≠ 0) :
    Dense {z : ι → ℂ | MvPolynomial.eval z p ≠ 0} := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨x, hx⟩
  by_contra h
  have hzero : ∀ z ∈ U, MvPolynomial.eval z p = 0 := by
    intro z hz
    by_contra hn
    exact h ⟨z, hz, hn⟩
  obtain ⟨s, hs, hsU⟩ := isOpen_pi_iff'.mp hU x hx
  apply hp
  apply MvPolynomial.funext_set s (fun i =>
    infinite_of_mem_nhds (x i) ((hs i).1.mem_nhds (hs i).2))
  intro z hz
  simpa only [map_zero] using hzero z (hsU hz)

/-- A nonzero polynomial has dense principal open locus in every finite complex torus,
including the torus of rank zero. -/
theorem dense_complexTorusPrincipalOpen [Finite ι]
    (p : MvPolynomial ι ℂ) (hp : p ≠ 0) :
    Dense (complexTorusPrincipalOpen p) := by
  have hopen : IsOpenMap (fun z : ι → ℂˣ => fun i => (z i : ℂ)) :=
    IsOpenMap.piMap (fun _ => Units.isOpenMap_val) (by simp)
  exact (dense_complexPolynomial_nonvanishing p hp).preimage hopen

/-- A finite intersection of principal open loci is the locus of the product. -/
theorem complexTorusPrincipalOpen_finsetProd {κ : Type v} (s : Finset κ)
    (p : κ → MvPolynomial ι ℂ) :
    complexTorusPrincipalOpen (∏ j ∈ s, p j) =
      ⋂ j ∈ s, complexTorusPrincipalOpen (p j) := by
  ext z
  simp only [complexTorusPrincipalOpen, mem_ofPred_eq, MvPolynomial.eval_prod,
    Finset.prod_ne_zero_iff, mem_iInter]

/-- Finitely many nonzero polynomial conditions hold on a dense subset of the torus. -/
theorem dense_iInter_complexTorusPrincipalOpen [Finite ι] {κ : Type v}
    (s : Finset κ) (p : κ → MvPolynomial ι ℂ) (hp : ∀ j ∈ s, p j ≠ 0) :
    Dense (⋂ j ∈ s, complexTorusPrincipalOpen (p j)) := by
  rw [← complexTorusPrincipalOpen_finsetProd s p]
  exact dense_complexTorusPrincipalOpen _ (Finset.prod_ne_zero_iff.mpr hp)

/-- Principal open nonvanishing is open after any actual torus coordinate homeomorphism. -/
theorem isOpen_complexTorusPrincipalOpen_preimage {A : Type v} [TopologicalSpace A]
    (e : A ≃ₜ (ι → ℂˣ)) (p : MvPolynomial ι ℂ) :
    IsOpen (e ⁻¹' complexTorusPrincipalOpen p) :=
  (isOpen_complexTorusPrincipalOpen p).preimage e.continuous

/-- Principal open density transports through any actual torus coordinate homeomorphism. -/
theorem dense_complexTorusPrincipalOpen_preimage [Finite ι]
    {A : Type v} [TopologicalSpace A] (e : A ≃ₜ (ι → ℂˣ))
    (p : MvPolynomial ι ℂ) (hp : p ≠ 0) :
    Dense (e ⁻¹' complexTorusPrincipalOpen p) :=
  (dense_complexTorusPrincipalOpen p hp).preimage e.isOpenMap

/-- A family containing a nonzero principal open coordinate locus is dense. -/
theorem dense_of_complexTorusPrincipalOpen_preimage_subset [Finite ι]
    {A : Type v} [TopologicalSpace A] (e : A ≃ₜ (ι → ℂˣ))
    (p : MvPolynomial ι ℂ) (hp : p ≠ 0) {S : Set A}
    (hS : e ⁻¹' complexTorusPrincipalOpen p ⊆ S) : Dense S :=
  (dense_complexTorusPrincipalOpen_preimage e p hp).mono hS

end Langlands.Plancherel
