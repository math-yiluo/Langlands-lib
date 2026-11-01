import Langlands.AlgebraicGeometry.Modules.IntegralSupportDimensionStatement
import Langlands.AlgebraicGeometry.Modules.IntegralIdealOpenProof
import Langlands.AlgebraicGeometry.Picard.AmpleSectionExactDimensionProof
import Langlands.AlgebraicGeometry.Picard.IntegralAmpleSectionCokernelProof
import Langlands.AlgebraicGeometry.Picard.LineBundleEulerPolynomial

/-! # Full support of integral ideals and exact-dimensional coherent cuts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology Order
open Langlands.SchemeModule Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Modules

/-- A nonzero ideal on an integral scheme has full closed stalk support. -/
theorem closedStalkSupport_ideal_eq_top
    (X : Scheme.{u}) [IsIntegral X] (I : X.Modules)
    (ι : I ⟶ structureModule X) [Mono ι] (hI : ¬ IsZero I) :
    closedStalkSupport I = ⊤ := by
  obtain ⟨U, hU, hι⟩ := exists_nonempty_open_isIso_ideal X I ι hI
  exact closedStalkSupport_eq_top_of_restrict_iso I U hU
    (asIso ((Scheme.Modules.restrictFunctor U.ι).map ι) ≪≫
      Scheme.Modules.restrictUnitIso U.ι)

/-- The support dimension of a nonzero integral ideal is the scheme dimension. -/
theorem supportDimension_ideal
    (X : Scheme.{u}) [IsIntegral X] (I : X.Modules)
    (ι : I ⟶ structureModule X) [Mono ι] (hI : ¬ IsZero I) :
    supportDimension I = topologicalKrullDim X := by
  unfold supportDimension
  rw [closedStalkSupport_ideal_eq_top X I ι hI]
  exact IsHomeomorph.topologicalKrullDim_eq
    (Homeomorph.Set.univ X) (Homeomorph.Set.univ X).isHomeomorph

/-- A generically generating line-bundle section has closed cokernel support
exactly its vanishing locus. -/
theorem coe_closedStalkSupport_sectionHom_cokernel
    {X : Scheme.{u}} [IsIntegral X] (L : Picard.LineBundle X)
    (s : GlobalSections L.obj)
    (hs : (trivializationOpen L.obj s : Set X).Nonempty) :
    (closedStalkSupport (cokernel (sectionHom L.obj s)) : Set X) =
      (trivializationOpen L.obj s : Set X)ᶜ := by
  rw [coe_closedStalkSupport, Picard.stalkSupport_sectionHom_cokernel_eq L s hs,
    (trivializationOpen L.obj s).isOpen.isClosed_compl.closure_eq]

/-- The actual section cokernel's support dimension is the vanishing-set dimension. -/
theorem supportDimension_sectionHom_cokernel
    {X : Scheme.{u}} [IsIntegral X] (L : Picard.LineBundle X)
    (s : GlobalSections L.obj)
    (hs : (trivializationOpen L.obj s : Set X).Nonempty) :
    supportDimension (cokernel (sectionHom L.obj s)) =
      topologicalKrullDim {x : X // x ∉ trivializationOpen L.obj s} := by
  unfold supportDimension
  rw [coe_closedStalkSupport_sectionHom_cokernel L s hs]
  rfl

/-- An ample section supplies a coherent cokernel of exactly one lower dimension. -/
theorem exists_ampleSection_coherent_cokernel_dimension
    (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (L : Picard.LineBundle X) (hL : L.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X = ((d + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
      (L.sectionOpen s : Set X).Nonempty ∧
      (cokernel (sectionHom _ s)).IsQuasicoherent ∧
      HasFiniteAffineSections (cokernel (sectionHom _ s)) ∧
      supportDimension (cokernel (sectionHom _ s)) = (d : WithBot ℕ∞) := by
  obtain ⟨n, hn, s, hs, _, hcut⟩ :=
    Picard.exists_ampleSection_exact_dimension X (d + 1) (Nat.succ_pos d) hdim L hL
  let N : Picard.LineBundle X :=
    ⟨tensorPow L.obj n, Picard.tensorPow_isLocallyFreeRankOne X L n⟩
  let : N.obj.IsQuasicoherent := N.property.isQuasicoherent
  let : (structureModule X).IsQuasicoherent :=
    (Picard.LineBundle.trivial X).property.isQuasicoherent
  have hQ := QuasicoherentLocal.isQuasicoherent_cokernel (sectionHom N.obj s)
  refine ⟨n, hn, s, hs, hQ,
    (hasFiniteAffineSections_lineBundle N).cokernel (sectionHom N.obj s), ?_⟩
  rw [supportDimension_sectionHom_cokernel N s hs]
  apply le_antisymm
  · apply ENat.WithBot.lt_add_one_iff.mp
    apply ENat.WithBot.add_one_le_natCast_iff.mp
    exact hcut.le
  · by_contra h
    have hlt : topologicalKrullDim {x : X // x ∉ L.sectionOpen s} <
        (d : WithBot ℕ∞) := lt_of_not_ge h
    have hle := ENat.WithBot.add_one_le_natCast_iff.mpr hlt
    rw [hcut] at hle
    have : d + 1 ≤ d := by exact_mod_cast hle
    exact Nat.not_succ_le_self d this

/-- Actual full-support ideals and exact-dimensional coherent ample cuts. -/
theorem integralSupportDimension : IntegralSupportDimensionStatement.{u} := by
  refine ⟨?_, @supportDimension_sectionHom_cokernel, exists_ampleSection_coherent_cokernel_dimension⟩
  intro X _ I ι _ hI
  exact ⟨closedStalkSupport_ideal_eq_top X I ι hI, supportDimension_ideal X I ι hI⟩

end Langlands.AlgebraicGeometry.Modules
