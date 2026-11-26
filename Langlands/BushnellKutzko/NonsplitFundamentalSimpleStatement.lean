import Langlands.BushnellKutzko.FundamentalStratum
import Langlands.BushnellKutzko.PureSimpleStratum
import Mathlib.RingTheory.SimpleModule.Basic

/-! # Simplicity of nonsplit fundamental strata (BK93 (2.4.13), printed p. 75) -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uO uK uF uE uV

section FiltrationQuotient

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K]
  [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

local notation "A" => Module.End K V

/-- Endomorphisms in the order that move the chain forward by at least one step. -/
def LatticeChain.firstFiltrationIdeal (L : LatticeChain O K V) : Ideal L.order where
  carrier := {x | (x : A) ∈ L.endFiltration 1}
  zero_mem' := by
    change (0 : A) ∈ L.endFiltration 1
    exact zero_mem _
  add_mem' := by
    intro x y hx hy
    change (x : A) + (y : A) ∈ L.endFiltration 1
    exact add_mem hx hy
  smul_mem' x y hy := by
    change (x : A) * (y : A) ∈ L.endFiltration 1
    simpa using L.mul_mem_endFiltration (m := 0) x.2 hy

instance (L : LatticeChain O K V) : L.firstFiltrationIdeal.IsTwoSided where
  mul_mem_of_left := by
    intro x y hx
    change (x : A) * (y : A) ∈ L.endFiltration 1
    simpa using L.mul_mem_endFiltration (n := 0) hx y.2

/-- The base residue ring acts on `𝔄/𝔓` since `𝔭` sends each lattice forward
by the period, which is at least one. -/
instance (L : LatticeChain O K V) :
    Algebra (O ⧸ Ring.jacobson O) (L.order ⧸ L.firstFiltrationIdeal) := by
  apply Ideal.Quotient.algebraQuotientOfLEComap
  intro a ha
  change algebraMap O A a ∈ L.endFiltration 1
  apply L.endFiltration_antitone (b := (L.period : ℤ)) (by exact_mod_cast L.period_pos)
  intro i v hv
  rw [L.lattice_add_period]
  simpa only [Module.algebraMap_end_apply] using Submodule.smul_mem_smul ha hv

private def Stratum.residueCentralizerLifts (S : Stratum O K V) : Subalgebra O S.chain.order where
  carrier := {x | adjointMap O S.b (x : A) ∈ S.chain.endFiltration (1 - S.n)}
  add_mem' := by
    intro x y hx hy
    change adjointMap O S.b (x : A) ∈ S.chain.endFiltration (1 - S.n) at hx
    change adjointMap O S.b (y : A) ∈ S.chain.endFiltration (1 - S.n) at hy
    change adjointMap O S.b ((x : A) + (y : A)) ∈ S.chain.endFiltration (1 - S.n)
    rw [map_add]
    exact add_mem hx hy
  mul_mem' := by
    intro x y hx hy
    change adjointMap O S.b ((x : A) * (y : A)) ∈ S.chain.endFiltration (1 - S.n)
    rw [show adjointMap O S.b ((x : A) * (y : A)) =
        (x : A) * adjointMap O S.b (y : A) + adjointMap O S.b (x : A) * (y : A) by
      simp only [adjointMap, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
      noncomm_ring]
    exact add_mem
      (by simpa using S.chain.mul_mem_endFiltration (m := 0) x.2 hy)
      (by simpa using S.chain.mul_mem_endFiltration (n := 0) hx y.2)
  algebraMap_mem' a := by
    change S.b * algebraMap O A a - algebraMap O A a * S.b ∈ S.chain.endFiltration (1 - S.n)
    rw [Algebra.commutes, sub_self]
    exact zero_mem _

/-- The subalgebra of `𝔄/𝔓` centralizing the symbol of `α` in degree `−n`. -/
def Stratum.residueCentralizer (S : Stratum O K V) :
    Subalgebra (O ⧸ Ring.jacobson O) (S.chain.order ⧸ S.chain.firstFiltrationIdeal) :=
  let C := S.residueCentralizerLifts.map (Ideal.Quotient.mkₐ O S.chain.firstFiltrationIdeal)
  { C.toSubsemiring with
    algebraMap_mem' := by
      intro a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact ⟨algebraMap O S.chain.order b, S.residueCentralizerLifts.algebraMap_mem b, rfl⟩ }

/-- The commutation test for residue classes can be checked on any lift. -/
theorem Stratum.mk_mem_residueCentralizer_iff (S : Stratum O K V)
    (hb : S.b ∈ S.chain.endFiltration (-S.n)) (x : S.chain.order) :
    Ideal.Quotient.mk S.chain.firstFiltrationIdeal x ∈ S.residueCentralizer ↔
      adjointMap O S.b (x : A) ∈ S.chain.endFiltration (1 - S.n) := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    change adjointMap O S.b (y : A) ∈ S.chain.endFiltration (1 - S.n) at hy
    have hxy : (x : A) - (y : A) ∈ S.chain.endFiltration 1 :=
      Ideal.Quotient.eq.mp hyx.symm
    have hcomm : adjointMap O S.b ((x : A) - (y : A)) ∈ S.chain.endFiltration (1 - S.n) := by
      change S.b * _ - _ * S.b ∈ _
      exact sub_mem
        (by simpa [sub_eq_add_neg, add_comm] using S.chain.mul_mem_endFiltration hb hxy)
        (by simpa [sub_eq_add_neg] using S.chain.mul_mem_endFiltration hxy hb)
    have hsum := add_mem hcomm hy
    rwa [map_sub, sub_add_cancel] at hsum
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The criterion on an individual stratum over its given integer ring. -/
def Stratum.NonsplitSimpleCriterion (S : Stratum O K V) : Prop :=
  1 ≤ S.n → S.IsNonsplit →
    ((∃ T : Stratum O K V,
        T.chain = S.chain ∧ T.n = S.n ∧ T.r = S.r ∧ S.Equivalent T ∧ T.IsSimple) ↔
      IsSemisimpleRing S.residueCentralizer)

end FiltrationQuotient

/-- The semisimplicity criterion over `F` and over the integral closure in
any finite extension `E/F`, the integer-ring model for derived strata. -/
def NonsplitFundamentalSimpleStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F],
    (∀ (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (S : Stratum 𝒪[F] F V), S.NonsplitSimpleCriterion) ∧
    (∀ (E : Type uE) [Field E] [Algebra F E] [FiniteDimensional F E]
      (V : Type uV) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (S : Stratum (subfieldIntegers F E) E V), S.NonsplitSimpleCriterion)

end Langlands.BushnellKutzko
