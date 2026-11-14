import Langlands.Representation.Conductor.OrderedUnramifiedWhittakerStatement
import Langlands.Representation.Conductor.SphericalCyclicity.Hecke

/-!
# Spherical cyclicity of norm-ordered unramified principal series

Proof of `Langlands.Conductor.OrderedUnramifiedSphericalCyclicityStatement` by induction on
the rank. In rank one every element of `GL_1` lies in the Borel subgroup, so the principal
series is the line spanned by the spherical section. In rank `n + 2`, a subrepresentation
`S` containing the spherical section contains the extension by zero of the spherical
section of rank `n + 1` with parameters `z ∘ Fin.succ` (`extend_sphericalSection_mem`); the
extensions by zero lying in `S` form a subrepresentation of rank `n + 1` (`pullback`), which
is everything by induction, and a subrepresentation containing every extension by zero is
everything (`eq_top_of_extend_mem`).
-/

noncomputable section

namespace Langlands.Conductor.SphericalCyclicity

open Langlands.GeneralLinear Langlands.Conductor
open Langlands.Conductor.UnramifiedPrincipalSeries

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : Fˣ}
  (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Every element of `GL_1` is upper triangular. -/
theorem mem_borel_zero (x : GL (Fin 1) F) : x ∈ Borel (F := F) 0 :=
  (mem_upperTriangularSubgroup_iff x).2 fun i j h =>
    absurd h (by rw [Subsingleton.elim i j]; exact lt_irrefl j)

/-- In rank one, every principal-series function is a multiple of the spherical section. -/
theorem eq_smul_sphericalSection_rank_one {q : ℕ} {hq : IsResidueCardinality (F := F) q}
    {z : Fin 1 → ℂˣ} (f : PrincipalSeries hϖ 0 hq z) :
    f = value hϖ 0 f 1 • sphericalSection hϖ 0 hq z := by
  refine ext_value hϖ fun x => ?_
  have hx := value_borel_mul hϖ f ⟨x, mem_borel_zero x⟩ 1
  have h0 := value_borel_mul hϖ (sphericalSection hϖ 0 hq z) ⟨x, mem_borel_zero x⟩ 1
  rw [mul_one] at hx h0
  rw [value_smul, hx, h0, sphericalSection_one, mul_one, mul_comm]

/-- **Rank one.** A subrepresentation containing the spherical section is everything. -/
theorem eq_top_rank_one {q : ℕ} {hq : IsResidueCardinality (F := F) q} {z : Fin 1 → ℂˣ}
    (S : Subrepresentation (principalSeries hϖ 0 hq z))
    (hS : sphericalSection hϖ 0 hq z ∈ S) : S = ⊤ := by
  apply Subrepresentation.toSubmodule_injective
  refine Submodule.eq_top_iff'.2 fun f => ?_
  rw [eq_smul_sphericalSection_rank_one hϖ f]
  exact S.toSubmodule.smul_mem _ hS

end Langlands.Conductor.SphericalCyclicity

namespace Langlands.Conductor

open Langlands.Conductor.SphericalCyclicity

universe uF

/-- Jacquet 2012, Lemma 1: the normalized spherical section generates the whole
upper-Borel unramified principal series when the norms of the parameters are
nondecreasing, over every nonarchimedean local field. -/
theorem orderedUnramifiedSphericalCyclicity :
    OrderedUnramifiedSphericalCyclicityStatement.{uF} := by
  intro F _ _ _ _ ϖ hϖ n
  induction n with
  | zero =>
    intro q hq z _ S hS
    exact eq_top_rank_one hϖ S hS
  | succ n ih =>
    intro q hq z hmono S hS
    have hmono' : Monotone fun i => ‖((tailParam z i : ℂˣ) : ℂ)‖ :=
      fun i j hij => hmono (Fin.succ_le_succ_iff.2 hij)
    have h0 := extend_sphericalSection_mem hϖ hmono S hS
    have htop := ih q hq (tailParam z) hmono' (pullback hϖ hq z S)
      ((mem_pullback hϖ hq z S _).2 h0)
    refine eq_top_of_extend_mem hϖ S fun ψ => ?_
    refine (mem_pullback hϖ hq z S ψ).1 ?_
    rw [htop]
    exact Submodule.mem_top

end Langlands.Conductor
