import Langlands.AlgebraicGeometry.Modules.FinitePresentation
import Langlands.AlgebraicGeometry.Modules.FinitePresentationPullback
import Mathlib.Algebra.Module.FinitePresentation

/-! # Finitely presented affine sections from actual sheaf presentations -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Modules

variable {X : Scheme.{u}}

/-- A finite global sheaf presentation gives finite presentation of sections on
any affine open, without a noetherian hypothesis. -/
lemma finitePresentation_sections_of_presentation (M : X.Modules)
    (P : M.Presentation) [P.IsFinite] (U : X.Opens) (hU : IsAffineOpen U) :
    Module.FinitePresentation Γ(X, U) Γ(M, U) := by
  have : M.IsQuasicoherent := P.isQuasicoherent
  have : Epi P.generators.π := P.generators.epi
  have : Epi P.relations.π := P.relations.epi
  have : (kernel P.generators.π).IsQuasicoherent :=
    QuasicoherentLocal.isQuasicoherent_kernel P.generators.π
  have hK : HasFiniteAffineSections (kernel P.generators.π) :=
    HasFiniteAffineSections.of_epi P.relations.π
      (hasFiniteAffineSections_free X P.relations.I)
  have : Module.Finite Γ(X, U) Γ(kernel P.generators.π, U) := hK ⟨U, hU⟩
  have : Module.FinitePresentation Γ(X, U)
      Γ(SheafOfModules.free (R := X.ringCatSheaf) P.generators.I, U) :=
    Module.FinitePresentation.of_equiv (freeSectionsIso X P.generators.I U).symm.toLinearEquiv
  let f : Γ(SheafOfModules.free (R := X.ringCatSheaf) P.generators.I, U) →ₗ[Γ(X, U)]
      Γ(M, U) := (P.generators.π.val.app (op U)).hom
  let k : Γ(kernel P.generators.π, U) →ₗ[Γ(X, U)]
      Γ(SheafOfModules.free (R := X.ringCatSheaf) P.generators.I, U) :=
    ((kernel.ι P.generators.π).val.app (op U)).hom
  have hker : LinearMap.ker f = LinearMap.range k := by
    ext s
    constructor
    · intro hs
      exact QuasicoherentLocal.exists_kernel_ι_app_eq P.generators.π s hs
    · rintro ⟨t, rfl⟩
      exact QuasicoherentLocal.app_kernel_ι_app P.generators.π U t
  exact Module.finitePresentation_of_surjective f
    (QuasicoherentLocal.surjective_app_of_epi P.generators.π U hU)
    (hker ▸ Submodule.fg_range k)

/-- Local finite presentation supplies an actual finite presentation on an
open subscheme containing each point. -/
lemma exists_finitePresentation_restrict (M : X.Modules) [M.IsFinitePresentation] (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧
      ∃ (P : (M.restrict U.ι).Presentation), P.IsFinite := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  have hx : x ∈ ⨆ i, q.X i :=
    (_root_.Opens.coversTop_iff X q.X).mp q.coversTop ▸
      (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  have : (q.presentation i).IsFinite := hq.isFinite_presentation i
  exact ⟨q.X i, hxi, presentationRestrictOfOver M (q.X i) (q.presentation i), inferInstance⟩

/-- Every point has an open neighbourhood on which all affine section modules
are finitely presented. -/
lemma exists_locally_finitePresentation_sections (M : X.Modules) [M.IsFinitePresentation]
    (x : X) : ∃ (U : X.Opens), x ∈ U ∧
      ∀ (V : U.toScheme.affineOpens),
        Module.FinitePresentation Γ(U.toScheme, V.1) Γ(M.restrict U.ι, V.1) := by
  obtain ⟨U, hxU, P, hP⟩ := exists_finitePresentation_restrict M x
  let := hP
  exact ⟨U, hxU, fun V => finitePresentation_sections_of_presentation _ P V.1 V.2⟩

/-- Choose an actual open neighbourhood whose restricted sheaf has finitely
presented affine sections. No compatibility between choices is asserted. -/
def finitePresentationSectionNeighbourhood (M : X.Modules) [M.IsFinitePresentation]
    (x : X) : {U : X.Opens // x ∈ U ∧
      ∀ (V : U.toScheme.affineOpens),
        Module.FinitePresentation Γ(U.toScheme, V.1) Γ(M.restrict U.ι, V.1)} :=
  ⟨(exists_locally_finitePresentation_sections M x).choose,
    (exists_locally_finitePresentation_sections M x).choose_spec⟩

end Langlands.AlgebraicGeometry.Modules
