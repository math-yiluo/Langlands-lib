import Langlands.AlgebraicGeometry.Picard.LineBundleSectionVanishingDimensionStatement
import Langlands.AlgebraicGeometry.Picard.SectionCutDimensionProof
import Langlands.AlgebraicGeometry.Modules.UnitEndResidueStalkProof
import Langlands.AbelianScheme.SmoothGeometricIntegralityProof
import Langlands.AlgebraicGeometry.FieldSmoothTopologicalKrullDimProof
import Mathlib.RingTheory.KrullDimension.Regular

/-! # Exact topological dimension of the first smooth line-bundle cut -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Opposite
open scoped Pointwise
open Langlands.SchemeModule

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard

/-- On a frame neighborhood, the scalar coefficient has precisely the
pullback of the original section's generation open as its basic open. -/
theorem localFrame_basicOpen_coeff
    {X : Scheme.{u}} (L : LineBundle X) (s : GlobalSections L.obj)
    (U : X.Opens) (e : L.obj.restrict U.ι ≅ structureModule U.toScheme) :
    let ψ : structureModule U.toScheme ⟶ structureModule U.toScheme :=
      (Scheme.Modules.restrictUnitIso U.ι).inv ≫
        (Scheme.Modules.restrictFunctor U.ι).map (sectionHom L.obj s) ≫ e.hom
    ∀ z : U.toScheme,
      z ∈ U.toScheme.basicOpen (unitEndCoefficient ψ ⊤) ↔
        U.ι z ∈ trivializationOpen L.obj s := by
  intro ψ z
  have hψ : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} z).map ψ.mapPresheaf) ↔
      IsStalkFrame L.obj s (U.ι z) := by
    change IsIso (((Scheme.Modules.toPresheaf U.toScheme) ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} z).map ψ) ↔ _
    simp only [ψ, Functor.map_comp, isIso_comp_left_iff, isIso_comp_right_iff]
    exact isIso_stalk_restrict_iff (sectionHom L.obj s) U z
  rw [Scheme.mem_basicOpen_top, ← IsLocalRing.residue_ne_zero_iff_isUnit]
  have h := (unitEnd_stalkIso_iff_residue_ne_zero ψ z).symm.trans hψ
  change _ ↔ U.ι z ∈ ({x : X | IsStalkFrame L.obj s x} : Set X) at h
  rwa [lineBundle_stalkFrame_set_eq] at h

/-- A compact irreducible locally Noetherian scheme with the given
closed-point stalk dimensions has an exact dimension formula for any
line-bundle section with nonempty generation open and complement. -/
theorem lineBundle_vanishing_dim_add_one
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X] [IrreducibleSpace X]
    (g : ℕ) (hX : topologicalKrullDim X ≤ (g : WithBot ℕ∞))
    (hstalk : ∀ x : X, IsClosed ({x} : Set X) →
      ringKrullDim (X.presheaf.stalk x) = (g : WithBot ℕ∞))
    (L : LineBundle X) (s : GlobalSections L.obj)
    (hs : ∃ x : X, x ∈ trivializationOpen L.obj s)
    (hz : ∃ x : X, x ∉ trivializationOpen L.obj s) :
    topologicalKrullDim {x : X // x ∉ trivializationOpen L.obj s} + 1 =
      (g : WithBot ℕ∞) := by
  let Z : Set X := (trivializationOpen L.obj s : Set X)ᶜ
  have hZ : IsClosed Z := (trivializationOpen L.obj s).isOpen.isClosed_compl
  have hproper : Z ≠ Set.univ := by
    rintro h
    obtain ⟨x, hx⟩ := hs
    exact (show x ∈ Z from h.symm ▸ Set.mem_univ x) hx
  apply le_antisymm
  · exact (topologicalKrullDim_add_one_le_of_isClosed Z hZ hproper).trans hX
  · obtain ⟨x, hx, hxc⟩ := hZ.exists_closed_singleton hz
    obtain ⟨U, hxU, ⟨e⟩⟩ := L.property x
    let y : U.toScheme := ⟨x, hxU⟩
    let ψ : structureModule U.toScheme ⟶ structureModule U.toScheme :=
      (Scheme.Modules.restrictUnitIso U.ι).inv ≫
        (Scheme.Modules.restrictFunctor U.ι).map (sectionHom L.obj s) ≫ e.hom
    let c : Γ(U.toScheme, ⊤) := unitEndCoefficient ψ ⊤
    have hcoeff (z : U.toScheme) : z ∈ U.toScheme.basicOpen c ↔
        U.ι z ∈ trivializationOpen L.obj s := localFrame_basicOpen_coeff L s U e z
    have hyn : y ∉ U.toScheme.basicOpen c := by
      intro hy
      exact hx ((hcoeff y).mp hy)
    have hm : U.toScheme.presheaf.germ ⊤ y trivial c ∈
        IsLocalRing.maximalIdeal (U.toScheme.presheaf.stalk y) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rwa [← Scheme.mem_basicOpen_top]
    have hlocal := ringKrullDim_le_ringKrullDim_quotSMulTop_succ hm
    have heq :
        U.toScheme.presheaf.germ ⊤ y trivial c •
          (⊤ : Ideal (U.toScheme.presheaf.stalk y)) =
        Ideal.span {U.toScheme.presheaf.germ ⊤ y trivial c} := by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
    rw [heq] at hlocal
    have hdimlocal : ringKrullDim (U.toScheme.presheaf.stalk y) = (g : WithBot ℕ∞) := by
      rw [← ringKrullDim_eq_of_ringEquiv
        (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv]
      exact hstalk x hxc
    have hquot := ringKrullDim_quotient_germ_le_vanishing U.toScheme y c
    have hmaps (z : {z : U.toScheme // z ∉ U.toScheme.basicOpen c}) :
        U.ι z.1 ∈ Z := by
      intro hz'
      exact z.2 ((hcoeff z.1).mpr hz')
    have hsub :=
      (U.ι.isEmbedding.isInducing.comp IsInducing.subtypeVal).codRestrict hmaps
    have hglobal := hsub.topologicalKrullDim_le
    calc (g : WithBot ℕ∞) = ringKrullDim (U.toScheme.presheaf.stalk y) := hdimlocal.symm
      _ ≤ ringKrullDim (U.toScheme.presheaf.stalk y ⧸
        Ideal.span {U.toScheme.presheaf.germ ⊤ y trivial c}) + 1 := hlocal
      _ ≤ topologicalKrullDim {z : U.toScheme // z ∉ U.toScheme.basicOpen c} + 1 :=
        add_le_add hquot le_rfl
      _ ≤ topologicalKrullDim {x : X // x ∉ trivializationOpen L.obj s} + 1 :=
        add_le_add hglobal le_rfl

/-- The actual vanishing set of a nontrivial section on a smooth proper
geometrically connected field scheme has the expected dimension. -/
theorem lineBundleSectionVanishingDimension :
    LineBundleSectionVanishingDimensionStatement.{u} := by
  intro K _ X f g hs hp hc L s hne hz
  let : SmoothOfRelativeDimension g f := hs
  let : Smooth f := SmoothOfRelativeDimension.smooth g f
  let : IsProper f := hp
  let : GeometricallyConnected f := hc
  let : GeometricallyIntegral f :=
    Langlands.AbelianScheme.smoothGeometricIntegrality K X f inferInstance hc
  let : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  exact lineBundle_vanishing_dim_add_one X g
    (fieldSmoothTopologicalKrullDim K X f g hs inferInstance)
    (fieldSmoothClosedPointStalkDimension K X f g hs) L s hne hz

end Langlands.AlgebraicGeometry.Picard
