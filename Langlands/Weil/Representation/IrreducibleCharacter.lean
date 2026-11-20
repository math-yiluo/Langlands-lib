import Langlands.LinearAlgebra.IrreducibleRepresentationSpan
import Langlands.Weil.Representation.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.RepresentationTheory.Character
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Trace comparison with an irreducible representation -/

noncomputable section

open scoped MonoidAlgebra

universe uk ug uv uw

namespace Langlands.FiniteRepresentation

/-- Equality of characters with an irreducible representation of the same rank
produces an actual linear intertwiner over the algebraically closed field. -/
def IrreducibleCharacterComparisonStatement : Prop :=
  ∀ {k : Type uk} [Field k] [IsAlgClosed k] {G : Type ug} [Monoid G]
    (A : FiniteRepresentation.{uk, ug, uv} k G) (B : FiniteRepresentation.{uk, ug, uw} k G),
    Representation.IsIrreducible A.representation → A.rank = B.rank →
    A.representation.character = B.representation.character → Nonempty (Equiv A B)

theorem irreducibleCharacterComparison : IrreducibleCharacterComparisonStatement.{uk, ug, uv, uw} := by
  intro k _ _ G _ A B hA hd χ
  let := hA
  let a := A.representation.asAlgebraHom
  let b := B.representation.asAlgebraHom
  have ha : Function.Surjective a :=
    Langlands.LinearAlgebra.asAlgebraHom_surjective_of_irreducible A.representation
  have htrace (x : k[G]) : LinearMap.trace k A (a x) = LinearMap.trace k B (b x) := by
    induction x using MonoidAlgebra.induction_on with
    | of g =>
      simpa only [a, b, Representation.asAlgebraHom_of, Representation.character]
        using congrFun χ g
    | add x y hx hy => simp only [map_add, hx, hy]
    | smul c x hx => simp only [map_smul, hx]
  have hker (x : k[G]) (hx : x ∈ RingHom.ker b) : a x = 0 := by
    have hx' : b x = 0 := hx
    ext v
    change a x v = 0
    by_contra hn
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero k hn
    obtain ⟨y, hy⟩ := ha (φ.smulRight v)
    have hprod : a (x * y) = φ.smulRight (a x v) := by
      rw [map_mul, hy]
      ext w
      simp only [Module.End.mul_apply, LinearMap.smulRight_apply, map_smul]
    have hzero := htrace (x * y)
    rw [hprod, LinearMap.trace_smulRight, map_mul b, hx', zero_mul, map_zero] at hzero
    exact hφ hzero
  let q := Ideal.Quotient.liftₐ (RingHom.ker b) a hker
  have hq (x : k[G]) : q (Ideal.Quotient.mk _ x) = a x :=
    congrArg (fun p : k[G] →ₐ[k] Module.End k A => p x)
      (Ideal.Quotient.liftₐ_comp _ a hker)
  have hqsurj : Function.Surjective q := by
    intro x
    obtain ⟨y, rfl⟩ := ha x
    exact ⟨Ideal.Quotient.mk _ y, hq y⟩
  let e := Ideal.quotientKerEquivRange b
  let f : b.range →ₐ[k] Module.End k A := q.comp e.symm.toAlgHom
  have hf : Function.Surjective f := hqsurj.comp e.symm.surjective
  have hdim : Module.finrank k (Module.End k A) = Module.finrank k (Module.End k B) := by
    simpa only [Module.End, Module.finrank_linearMap, rank]
      using congrArg (fun n : ℕ => n * n) hd
  have hrange : b.range.toSubmodule = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    exact (Submodule.finrank_le _).antisymm
      (hdim ▸ LinearMap.finrank_le_finrank_of_surjective (f := f.toLinearMap) hf)
  have hb : Function.Surjective b := by
    intro x
    have hx : x ∈ b.range.toSubmodule := by rw [hrange]; exact Submodule.mem_top
    exact hx
  let e' := Ideal.quotientKerAlgEquivOfSurjective hb
  let t := q.comp e'.symm.toAlgHom
  have ht : Function.Surjective t := hqsurj.comp e'.symm.surjective
  have ht' : Function.Injective t :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := t.toLinearMap) hdim.symm).mpr ht
  let c := AlgEquiv.ofBijective t ⟨ht', ht⟩
  obtain ⟨T, hT⟩ := c.eq_linearEquivConjAlgEquiv
  have htcomp (x : k[G]) : t (b x) = a x := by
    change q (e'.symm (b x)) = a x
    rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
    exact hq x
  refine ⟨(Representation.Equiv.mk T ?_).symm⟩
  intro g
  have hg : t (B.representation g) = A.representation g := by
    simpa only [a, b, Representation.asAlgebraHom_of] using htcomp (MonoidAlgebra.of k G g)
  have hc : T.conjAlgEquiv k (B.representation g) = A.representation g :=
    (congrArg (fun d : Module.End k B ≃ₐ[k] Module.End k A => d (B.representation g))
      hT.symm).trans hg
  ext v
  have hv := congrArg (fun F : Module.End k A => F (T v)) hc
  simpa only [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hv

end Langlands.FiniteRepresentation
