import Langlands.Global.ArchimedeanCompactOrbitSource
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-! # Families of smooth archimedean functions with one finite compact source -/

noncomputable section
universe u w
open Filter Topology
open scoped Classical TensorProduct Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

open DerivativeSmoothFunctions

/-- The product of the actual derivative smooth carriers, with product topology. -/
abbrev SmoothFamily (F : Type u) [Field F] [NumberField F] (n : ℕ) (ι : Type w) :=
  ι → DerivativeSmoothFunctions F n

namespace SmoothFamily

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} {ι : Type w}

/-- Right translation of every coordinate by the same archimedean element. -/
def rightRepresentation : Representation ℂ (InfiniteAdelicGL F n) (SmoothFamily F n ι) where
  toFun g := LinearMap.pi fun i => (rightAction F n g).comp (LinearMap.proj i)
  map_one' := by ext f i : 2; exact LinearMap.congr_fun ((rightAction F n).map_one) (f i)
  map_mul' g h := by
    ext f i : 2
    exact LinearMap.congr_fun ((rightAction F n).map_mul g h) (f i)

/-- The restriction of simultaneous right translation to the standard compact subgroup. -/
def compactRepresentation :
    Representation ℂ (standardInfiniteCompact F n) (SmoothFamily F n ι) :=
  rightRepresentation.comp (standardInfiniteCompact F n).subtype

@[simp]
theorem rightRepresentation_apply (g : InfiniteAdelicGL F n) (f : SmoothFamily F n ι) (i : ι) :
    rightRepresentation g f i = rightAction F n g (f i) := rfl

@[simp]
theorem compactRepresentation_apply (k : standardInfiniteCompact F n)
    (f : SmoothFamily F n ι) (i : ι) :
    compactRepresentation k f i = compactAction F n k (f i) := rfl

theorem continuous_compactRepresentation :
    Continuous (fun p : standardInfiniteCompact F n × SmoothFamily F n ι =>
      compactRepresentation p.1 p.2) :=
  continuous_pi fun i => (continuous_compactAction F n).comp
    (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))

/-- Joint covariance follows from the covariance for each actual smooth coordinate. -/
theorem compactRepresentation_enveloping_smul (k : standardInfiniteCompact F n)
    (a : EnvelopingAlgebra F n) (f : SmoothFamily F n ι) :
    compactRepresentation k (a • f) =
      envelopingConjugation F n k.val a • compactRepresentation k f := by
  funext i
  exact compactAction_enveloping_smul F n k a (f i)

private def evaluations : SmoothFamily F n ι →ₗ[ℂ] (ι → InfiniteAdelicGL F n → ℂ) :=
  LinearMap.pi fun i => LinearMap.pi fun x =>
    (evalCLM F n x).toLinearMap.comp (LinearMap.proj i)

private theorem evaluations_apply (f : SmoothFamily F n ι) (i : ι)
    (x : InfiniteAdelicGL F n) :
    evaluations f i x = (toSmooth F n (f i)).val x := by
  simp only [evaluations, LinearMap.pi_apply, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, LinearMap.proj_apply, evalCLM_apply]

private theorem evaluations_injective :
    Function.Injective (evaluations (F := F) (n := n) (ι := ι)) := by
  intro f g h
  funext i
  apply (toSmooth F n).injective
  apply Subtype.ext
  funext x
  simpa only [evaluations_apply] using congrFun (congrFun h i) x

private theorem realGenerator_mem (S : Subrepresentation
    (compactRepresentation (F := F) (n := n) (ι := ι)))
    [Module.Finite ℂ S.toSubmodule] (X : compactLieSubalgebra F n)
    (f : SmoothFamily F n ι) (hf : f ∈ S) :
    envelopingGenerator F n (complexify F n (X : RealLieAlgebra F n)) • f ∈ S := by
  obtain ⟨c, hc0, hc⟩ := compactTangentCurve F n X
  let a := envelopingGenerator F n (complexify F n (X : RealLieAlgebra F n))
  let q : ℝ → SmoothFamily F n ι := fun t =>
    ((t⁻¹ : ℝ) : ℂ) • (compactRepresentation (c t) f - f)
  let P := S.toSubmodule.map evaluations
  have hq (t : ℝ) : evaluations (q t) ∈ P :=
    Submodule.mem_map_of_mem (S.toSubmodule.smul_mem _ (S.toSubmodule.sub_mem
      (S.apply_mem_toSubmodule (c t) hf) hf))
  have hlim : Tendsto (evaluations ∘ q) (𝓝[≠] (0 : ℝ)) (𝓝 (evaluations (a • f))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro x
    have hd := (compactCurve_right_deriv F n (X : RealLieAlgebra F n) c hc0 hc
      (toSmooth F n (f i)) x).tendsto_slope_zero
    simp only [Function.comp_apply, evaluations_apply, q,
      compactRepresentation_apply, map_smul, map_sub, Submodule.coe_smul,
      Submodule.coe_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, compactAction_apply,
      toSmooth_rightAction_val, enveloping_smul_eq_operator, toSmooth_operator,
      a, envelopingAction_real_generator]
    simpa [hc0, Complex.real_smul] using hd
  have : Module.Finite ℂ P := Module.Finite.map _ _
  obtain ⟨g, hg, heq⟩ := P.closed_of_finiteDimensional.mem_of_tendsto hlim
    (Eventually.of_forall hq)
  exact evaluations_injective heq ▸ hg

/-- A finite-dimensional compact-stable space of families is stable under the
actual differentiated compact action, by simultaneous pointwise difference quotients. -/
theorem compactGenerator_mem (S : Subrepresentation
    (compactRepresentation (F := F) (n := n) (ι := ι)))
    [Module.Finite ℂ S.toSubmodule] (X : CompactComplexLieAlgebra F n)
    (f : SmoothFamily F n ι) (hf : f ∈ S) : compactEnvelopingGenerator F n X • f ∈ S := by
  induction X using TensorProduct.inductionOn with
  | tmul z Y =>
    have heq : compactEnvelopingGenerator F n (z ⊗ₜ[ℝ] Y) =
        z • envelopingGenerator F n (complexify F n (Y : RealLieAlgebra F n)) := by
      rw [compactEnvelopingGenerator_tmul, ← map_smul, complexify_apply,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [heq, smul_assoc]
    exact S.toSubmodule.smul_mem _ (realGenerator_mem S Y f hf)
  | add X Y hX hY =>
    rw [map_add, add_smul]
    exact S.toSubmodule.add_mem hX hY

set_option backward.isDefEq.respectTransparency true in
/-- An intertwiner from an algebraic finite-dimensional compact source factors through
its finite-dimensional image, on which the actual compact action is continuous. -/
theorem exists_continuous_source {m : ℕ}
    {σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ)}
    (j : σ.IntertwiningMap (compactRepresentation (F := F) (n := n) (ι := ι))) :
    ∃ (τ : ContinuousCompactRep F n) (i : τ.toRepresentation.IntertwiningMap
        (compactRepresentation (F := F) (n := n) (ι := ι))),
      LinearMap.range i.toLinearMap = LinearMap.range j.toLinearMap := by
  let S := j.range
  have : Module.Finite ℂ S.toSubmodule := Module.Finite.range j.toLinearMap
  let d := Module.finrank ℂ S.toSubmodule
  let e : (Fin d → ℂ) ≃ₗ[ℂ] S.toSubmodule :=
    (Module.finBasis ℂ S.toSubmodule).equivFun.symm
  let ρ : Representation ℂ (standardInfiniteCompact F n) (Fin d → ℂ) :=
    (e.symm.conjAlgEquiv ℂ : Module.End ℂ S.toSubmodule →*
      Module.End ℂ (Fin d → ℂ)).comp S.toRepresentation
  have hρ_apply (k : standardInfiniteCompact F n) (v : Fin d → ℂ) :
      ρ k v = e.symm (S.toRepresentation k (e v)) := rfl
  have hcont : Continuous fun p : standardInfiniteCompact F n × S.toSubmodule =>
      S.toRepresentation p.1 p.2 := by
    have hpair : Continuous fun p : standardInfiniteCompact F n × S.toSubmodule =>
        (p.1, (p.2 : SmoothFamily F n ι)) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    exact (continuous_compactRepresentation.comp hpair).subtype_mk _
  have he : Continuous e := e.toLinearMap.continuous_of_finiteDimensional
  have he' : Continuous e.symm := e.symm.toLinearMap.continuous_of_finiteDimensional
  have hpair : Continuous fun p : standardInfiniteCompact F n × (Fin d → ℂ) =>
      (p.1, e p.2) := continuous_fst.prodMk (he.comp continuous_snd)
  have hρ : Continuous fun p : standardInfiniteCompact F n × (Fin d → ℂ) =>
      ρ p.1 p.2 := by
    simpa only [hρ_apply, Function.comp_def] using he'.comp (hcont.comp hpair)
  let τ : ContinuousCompactRep F n := ⟨d, ρ, hρ⟩
  let i : τ.toRepresentation.IntertwiningMap
      (compactRepresentation (F := F) (n := n) (ι := ι)) :=
    { toLinearMap := S.toSubmodule.subtype.comp e.toLinearMap
      isIntertwining' := by
        intro k
        apply LinearMap.ext
        intro v
        change (e (ρ k v)).val = _
        rw [hρ_apply, LinearEquiv.apply_symm_apply]
        rfl }
  refine ⟨τ, i, le_antisymm ?_ ?_⟩
  · rintro _ ⟨v, rfl⟩
    exact (e v).property
  · intro f hf
    refine ⟨e.symm ⟨f, hf⟩, ?_⟩
    change (e (e.symm (⟨f, hf⟩ : S.toSubmodule))).val = f
    rw [LinearEquiv.apply_symm_apply]

end SmoothFamily
end Langlands.Global.ArchimedeanGL
