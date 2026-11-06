import Langlands.Representation.Unitary.AdmissibleSemisimplicityProof

/-! # Actual intertwiner extensions for the tempered uniqueness argument -/

noncomputable section

universe uG uV uW uU

namespace Langlands

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {U : Type uU} [AddCommGroup U] [Module ℂ U]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
  {τ : Representation ℂ G U}

/-- An actual equivariant retraction of an injective intertwiner. -/
structure IntertwiningRetraction (i : ρ.IntertwiningMap σ) where
  map : σ.IntertwiningMap ρ
  left_inverse : Function.LeftInverse map i

/-- Select an actual equivariant retraction using a complement in the
semisimple target. The two carrier universes are independent. -/
def semisimpleIntertwiningRetraction
    (hσ : Representation.IsSemisimpleRepresentation σ)
    (i : ρ.IntertwiningMap σ) (hi : Function.Injective i) :
    IntertwiningRetraction i := by
  let : IsSemisimpleModule (MonoidAlgebra ℂ G) σ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).mp hσ
  let I := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ i
  have hI : Function.Injective I := hi
  let r := Classical.choose (IsSemisimpleModule.extension_property I hI
    (LinearMap.id : ρ.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule))
  have hr : r.comp I = LinearMap.id := Classical.choose_spec
    (IsSemisimpleModule.extension_property I hI
      (LinearMap.id : ρ.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule))
  refine ⟨(Representation.IntertwiningMap.equivLinearMapAsModule σ ρ).symm r, ?_⟩
  intro v
  exact congrArg (fun f : ρ.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule => f v) hr

/-- Extend an actual intertwiner along an embedding into a semisimple
representation, preserving the original map exactly. -/
def semisimpleIntertwiningExtension
    (hσ : Representation.IsSemisimpleRepresentation σ)
    (i : ρ.IntertwiningMap σ) (hi : Function.Injective i)
    (j : ρ.IntertwiningMap τ) :
    {f : σ.IntertwiningMap τ // f.comp i = j} := by
  let r := semisimpleIntertwiningRetraction hσ i hi
  refine ⟨j.comp r.map, ?_⟩
  ext v
  change j (r.map (i v)) = j v
  rw [r.left_inverse]

/-- The chosen extension of a nonzero intertwiner remains nonzero. -/
def nonzeroSemisimpleIntertwiningExtension
    (hσ : Representation.IsSemisimpleRepresentation σ)
    (i : ρ.IntertwiningMap σ) (hi : Function.Injective i)
    (j : ρ.IntertwiningMap τ) (hj : j ≠ 0) :
    {f : σ.IntertwiningMap τ // f ≠ 0 ∧ f.comp i = j} := by
  let F := semisimpleIntertwiningExtension hσ i hi j
  refine ⟨F.val, ?_, F.property⟩
  intro hzero
  apply hj
  rw [← F.property, hzero]
  ext v
  rfl

/-- Use an admissible invariant positive form to choose the same actual
extension. Compact open subgroups are assumed cofinal as in the reused theorem. -/
def admissibleUnitaryIntertwiningExtension
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hσ : IsAdmissible σ) (b : InvariantPositiveForm σ)
    (i : ρ.IntertwiningMap σ) (hi : Function.Injective i)
    (j : ρ.IntertwiningMap τ) (hj : j ≠ 0) :
    {f : σ.IntertwiningMap τ // f ≠ 0 ∧ f.comp i = j} :=
  nonzeroSemisimpleIntertwiningExtension
    (admissibleUnitarySemisimplicity G hcofinal W σ hσ ⟨b⟩) i hi j hj

end Langlands
