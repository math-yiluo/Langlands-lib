import Langlands.Automorphic.GroupSchemeForms
import Langlands.Automorphic.GroupSchemeInvariantForms

/-! # Realizing rational-invariant automorphic functions on the smooth carrier -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))

private local instance : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

/-- An unbundled automorphic function on the rational quotient is evaluated
by an actual automorphic vector in the original finite plot-smooth carrier. -/
def RationalAutomorphicRealizationStatement : Prop :=
  ∀ φ : AdelicGroupPoints F G → ℂ,
    IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho φ →
    ∃ f : FinitePlotSmoothRationalFunctions F G,
      IsAdelicAutomorphicForm F G Kinf rho hsmooth hcalc f ∧ evaluate F G f.val = φ

theorem rationalAutomorphicRealization :
    RationalAutomorphicRealizationStatement rho hsmooth hcalc Kinf := by
  intro φ hφ
  obtain ⟨hinv, ⟨hcont, hslices, L, ho, hlevel⟩, hfinite, hcenter, hgrowth⟩ := hφ
  let f₀ : ContinuousRationalFunctions F G :=
    ⟨⟨φ, fun a x => hinv _ ⟨a, rfl⟩ x⟩, hcont⟩
  let f : FinitePlotSmoothRationalFunctions F G := ⟨f₀, by
    refine ⟨(mem_infinitePlotSmoothSubrepresentation F G f₀).mpr hslices, ⟨⟨L, ho⟩, ?_⟩⟩
    intro l
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact hlevel l.val l.property g⟩
  refine ⟨f, ⟨?_, ?_, hgrowth⟩, rfl⟩
  · let ev : FinitePlotSmoothRationalFunctions F G →ₗ[ℂ] (AdelicGroupPoints F G → ℂ) :=
      { toFun := fun v => evaluate F G v.val
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hEv : Function.Injective ev := fun _ _ h => Subtype.ext (Subtype.ext (Subtype.ext h))
    let S := Langlands.FiniteVectors.orbitSpan (finitePlotSmoothInfiniteSubgroupAction F G Kinf) f
    have hS : S.map ev = Submodule.span ℂ (Set.range fun k : Kinf =>
        fun g => φ (g * ofInfinite F G k)) := by
      unfold S Langlands.FiniteVectors.orbitSpan
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    unfold IsInfiniteSubgroupFiniteFunction at hfinite
    rw [← hS] at hfinite
    exact (Module.Finite.equiv_iff (Submodule.equivMapOfInjective ev hEv S)).mpr hfinite
  · obtain ⟨J, hJ, hann⟩ := hcenter
    apply (isAdelicCenterFinite_iff_exists_ideal F G hsmooth hcalc f).mpr
    refine ⟨J, hJ, fun z hz => ?_⟩
    apply finitePlotSmoothSlice_injective F G
    funext b
    change finitePlotSmoothSlice F G b (finitePlotSmoothCenterAction F G hsmooth hcalc z f) =
      finitePlotSmoothSlice F G b 0
    rw [finitePlotSmoothSlice_centerAction, map_zero]
    exact hann z hz b (hslices b)

end Langlands.Automorphic.GroupSchemeFunctions
