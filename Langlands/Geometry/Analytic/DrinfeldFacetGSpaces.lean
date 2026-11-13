import Langlands.Geometry.Analytic.DrinfeldFacetSpaces
import Langlands.Geometry.Analytic.DrinfeldActionContinuityStatement
import Langlands.Geometry.Analytic.InvariantDomainContinuityStatement

/-! # Harris's domains `U(f)` as `H`-spaces, given continuity of the action -/

noncomputable section

universe u v

namespace Langlands.Analytic.DrinfeldUpperHalfSpace

open CategoryTheory SaturatedAtlasPresentation

variable {F : Type v} [NontriviallyNormedField F] {d : ℕ}

/-- The inclusion of a subgroup `H` of `GL_{d+1}(F)`, as a continuous homomorphism; `H` carries
the subspace topology. -/
def subgroupInclusion (H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F)) :
    H →ₜ* Matrix.GeneralLinearGroup (Fin (d + 1)) F :=
  { H.subtype with continuous_toFun := continuous_subtype_val }

@[simp]
theorem subgroupInclusion_apply (H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F))
    (h : H) : subgroupInclusion H h = h :=
  rfl

/-- The elements of the stabilizer `S(f)` whose determinant has absolute value one. -/
def facetStabilizerNormOne (S : Set (NormClass F (Fin (d + 1) → F))) :
    Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F) :=
  facetStabilizer S ⊓
    ((Units.map (normHom : F →*₀ ℝ).toMonoidHom).comp Matrix.GeneralLinearGroup.det).ker

theorem mem_facetStabilizerNormOne {S : Set (NormClass F (Fin (d + 1) → F))}
    {γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F} :
    γ ∈ facetStabilizerNormOne S ↔
      γ ∈ facetStabilizer S ∧ ‖((Matrix.GeneralLinearGroup.det γ : Fˣ) : F)‖ = 1 := by
  rw [facetStabilizerNormOne, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.comp_apply,
    Units.ext_iff]
  rfl

theorem facetStabilizerNormOne_le (S : Set (NormClass F (Fin (d + 1) → F))) :
    facetStabilizerNormOne S ≤ facetStabilizer S :=
  inf_le_left

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra F K] [ProperSpace F] [NeZero d]

/-- Drinfeld's upper half space `Ω` as a `GL_{d+1}(F)`-space, given that the action of
`GL_{d+1}(F)` is continuous. -/
def omegaGSpace (hΩ : IsContinuousAction (omegaAction F K d).ρAut) :
    GSpace.{u, u, u} K (Matrix.GeneralLinearGroup (Fin (d + 1)) F) :=
  ⟨omegaAction F K d, inferInstance, hΩ⟩

@[simp]
theorem omegaGSpace_obj (hΩ : IsContinuousAction (omegaAction F K d).ρAut) :
    (omegaGSpace K hΩ).obj = omegaAction F K d :=
  rfl

/-- The published statement `OmegaActionContinuityStatement` gives the continuity hypothesis of
`omegaGSpace`. -/
theorem isContinuousAction_omegaAction
    (h : OmegaActionContinuityStatement.{u, v}) :
    IsContinuousAction (omegaAction F K d).ρAut :=
  h F K d

variable {K} in
/-- The action of a subgroup `H ≤ S(f)` on `U(f)` is continuous if the action of
`GL_{d+1}(F)` on `Ω` is, granted the published statement
`InvariantDomainContinuityStatement`. -/
theorem isContinuousAction_facetAction (hΩ : IsContinuousAction (omegaAction F K d).ρAut)
    (hInv : InvariantDomainContinuityStatement.{u, u, u, v})
    {S : Set (NormClass F (Fin (d + 1) → F))} (hS : S.Finite) (ε : ℝ)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F)) (hH : H ≤ facetStabilizer S) :
    IsContinuousAction (facetAction K hS ε H hH).ρAut :=
  hInv K H ((GSpace.res (subgroupInclusion H)).obj (omegaGSpace K hΩ))
    (facetAnalyticDomain K hS ε) (isInvariantDomain_facetAnalyticDomain K hS ε H hH)

/-- Harris's `U(f)`, for a finite set of vertices `f`, as an `H`-space for a subgroup
`H ≤ S(f)`, given that the action of `H` on `U(f)` is continuous. -/
def facetGSpace {S : Set (NormClass F (Fin (d + 1) → F))} (hS : S.Finite) (ε : ℝ)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F)) (hH : H ≤ facetStabilizer S)
    (hc : IsContinuousAction (facetAction K hS ε H hH).ρAut) : GSpace.{u, u, u} K H :=
  ⟨facetAction K hS ε H hH, inferInstanceAs (T2Space (facetDomain K S ε)), hc⟩

@[simp]
theorem facetGSpace_obj {S : Set (NormClass F (Fin (d + 1) → F))} (hS : S.Finite) (ε : ℝ)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F)) (hH : H ≤ facetStabilizer S)
    (hc : IsContinuousAction (facetAction K hS ε H hH).ρAut) :
    (facetGSpace K hS ε H hH hc).obj = facetAction K hS ε H hH :=
  rfl

/-- The inclusion `U(f) → Ω` as a morphism of `H`-spaces, where `Ω` carries the restriction to
`H` of its `GL_{d+1}(F)`-space structure. -/
def facetGSpaceInclusion (hΩ : IsContinuousAction (omegaAction F K d).ρAut)
    {S : Set (NormClass F (Fin (d + 1) → F))} (hS : S.Finite) (ε : ℝ)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F)) (hH : H ≤ facetStabilizer S)
    (hc : IsContinuousAction (facetAction K hS ε H hH).ρAut) :
    facetGSpace K hS ε H hH hc ⟶ (GSpace.res (subgroupInclusion H)).obj (omegaGSpace K hΩ) :=
  ObjectProperty.homMk (facetInclusion K hS ε H hH)

@[simp]
theorem facetGSpaceInclusion_hom (hΩ : IsContinuousAction (omegaAction F K d).ρAut)
    {S : Set (NormClass F (Fin (d + 1) → F))} (hS : S.Finite) (ε : ℝ)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F)) (hH : H ≤ facetStabilizer S)
    (hc : IsContinuousAction (facetAction K hS ε H hH).ρAut) :
    (facetGSpaceInclusion K hΩ hS ε H hH hc).hom = facetInclusion K hS ε H hH :=
  rfl

/-- The same `H`-space as `facetGSpace`, built by the general construction
`invariantDomainGSpace` from the restriction of `Ω` to `H`. -/
theorem facetGSpace_eq_invariantDomainGSpace (hΩ : IsContinuousAction (omegaAction F K d).ρAut)
    {S : Set (NormClass F (Fin (d + 1) → F))} (hS : S.Finite) (ε : ℝ)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F)) (hH : H ≤ facetStabilizer S)
    (hc : IsContinuousAction (facetAction K hS ε H hH).ρAut) :
    facetGSpace K hS ε H hH hc =
      invariantDomainGSpace ((GSpace.res (subgroupInclusion H)).obj (omegaGSpace K hΩ))
        (facetAnalyticDomain K hS ε) (isInvariantDomain_facetAnalyticDomain K hS ε H hH) hc :=
  rfl

/-- For a facet `f`, `U(f)` as an `S(f)`-space, given that the action of `S(f)` on `U(f)` is
continuous. -/
abbrev facetStabilizerGSpace {S : Set (NormClass F (Fin (d + 1) → F))}
    (hS : NormClass.IsFacet S) (ε : ℝ)
    (hc : IsContinuousAction (facetStabilizerAction K hS ε).ρAut) :
    GSpace.{u, u, u} K (facetStabilizer S) :=
  facetGSpace K (IsFacet.finite hS) ε (facetStabilizer S) le_rfl hc

/-- For a facet `f`, `U(f)` as a space with a continuous action of the subgroup of `S(f)` of
elements whose determinant has absolute value one, given that this action is continuous. -/
abbrev facetNormOneGSpace {S : Set (NormClass F (Fin (d + 1) → F))}
    (hS : NormClass.IsFacet S) (ε : ℝ)
    (hc : IsContinuousAction (facetAction K (IsFacet.finite hS) ε (facetStabilizerNormOne S)
      (facetStabilizerNormOne_le S)).ρAut) :
    GSpace.{u, u, u} K (facetStabilizerNormOne S) :=
  facetGSpace K (IsFacet.finite hS) ε (facetStabilizerNormOne S) (facetStabilizerNormOne_le S) hc

end Langlands.Analytic.DrinfeldUpperHalfSpace
