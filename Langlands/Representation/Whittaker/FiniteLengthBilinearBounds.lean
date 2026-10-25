import Langlands.Representation.Whittaker.FunctionalBilinearBounds
import Langlands.Representation.Filtration.LengthCriterionProof

/-! Finite-length assembly of irreducible-pair bounds for full bilinear spaces. -/

noncomputable section

namespace Langlands.ObjectRepFiltration

universe uK uG uV

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]

/-- Choose an actual composition filtration from finite group-algebra length. -/
def ofFiniteLength (A : Rep.{uV} k G)
    (hA : IsFiniteLength (MonoidAlgebra k G) A.ρ.asModule) :
    Σ m : ℕ, {f : ObjectRepFiltration A m // f.HasSimpleFactors} :=
  let hs := isFiniteLength_iff_exists_compositionSeries.mp hA
  let s := Classical.choose hs
  let hb := Classical.choose_spec hs
  let hf := LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries s hb.1 hb.2
  ⟨s.length, Classical.choose hf, Classical.choose_spec hf⟩

end Langlands.ObjectRepFiltration

namespace Langlands.ObjectRepFiltration

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Every actual graded quotient of a smooth representation is smooth. -/
theorem isSmooth_gradedRepresentation {A : Rep.{uV} ℂ G} {m : ℕ}
    (f : ObjectRepFiltration A m) (hA : IsSmooth A.ρ) (i : Fin m) :
    IsSmooth (f.gradedRepresentation i).ρ := by
  let incl : (f.subrepresentation i.succ).toRepresentation.IntertwiningMap A.ρ :=
    { toLinearMap := (f.subrepresentation i.succ).toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  exact isSmooth_of_surjective (f.gradedProjection i).hom
    (f.gradedProjection_surjective i)
    (isSmooth_of_injective incl (Submodule.injective_subtype _) hA)

end Langlands.ObjectRepFiltration

namespace Langlands.InvariantBilinear

universe uZ uS uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (U U' : Subgroup G)
variable (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U)
variable (hU' : Jacquet.Localization.IsLimitOfCompactSubgroups U')
variable (θ : U →* ℂˣ) (θ' : U' →* ℂˣ)
variable (hθ : IsLocallyConstant (fun u : U => (θ u : ℂ)))
variable (hθ' : IsLocallyConstant (fun u : U' => (θ' u : ℂ)))

include hU hU' hθ hθ'

/-- Pairwise control only on smooth irreducibles suffices for finite-length
representations with one-dimensional functional spaces. -/
theorem exists_exception_length_le_one_of_finiteLength
    {Z : Type uZ} {S : Type uS} (z : S → Z) (χ : S → G → ℂ)
    (A : Rep.{uV} ℂ G) (B : Rep.{uW} ℂ G)
    (hA : IsSmooth A.ρ) (hB : IsSmooth B.ρ)
    (hfinA : IsFiniteLength (MonoidAlgebra ℂ G) A.ρ.asModule)
    (hfinB : IsFiniteLength (MonoidAlgebra ℂ G) B.ρ.asModule)
    (eA : Whittaker.functionals U θ A.ρ ≃ₗ[ℂ] ℂ)
    (eB : Whittaker.functionals U' θ' B.ρ ≃ₗ[ℂ] ℂ)
    (hpair : ∀ (C : Rep.{uV} ℂ G) (D : Rep.{uW} ℂ G),
      IsSmooth C.ρ → IsSmooth D.ρ →
      Representation.IsIrreducible C.ρ → Representation.IsIrreducible D.ρ →
      ∃ E : Finset Z, ∀ a : S, z a ∉ E →
        (length C.ρ D.ρ (χ a) ≠ 0 →
          Whittaker.HasFunctional (N := U) (θ := θ) C.ρ ∧
          Whittaker.HasFunctional (N := U') (θ := θ') D.ρ) ∧
        (Whittaker.HasFunctional (N := U) (θ := θ) C.ρ →
          Whittaker.HasFunctional (N := U') (θ := θ') D.ρ →
          length C.ρ D.ρ (χ a) ≤ 1)) :
    ∃ E : Finset Z, ∀ a : S, z a ∉ E → length A.ρ B.ρ (χ a) ≤ 1 := by
  let f := ObjectRepFiltration.ofFiniteLength A hfinA
  let g := ObjectRepFiltration.ofFiniteLength B hfinB
  apply exists_exception_length_le_one_of_functional_equiv U U' hU hU' θ θ' hθ hθ'
    f.2.val g.2.val z χ hA hB eA eB
  intro i j
  exact hpair (f.2.val.gradedRepresentation i) (g.2.val.gradedRepresentation j)
    (f.2.val.isSmooth_gradedRepresentation hA i) (g.2.val.isSmooth_gradedRepresentation hB j)
    (f.2.property i) (g.2.property j)

end Langlands.InvariantBilinear
