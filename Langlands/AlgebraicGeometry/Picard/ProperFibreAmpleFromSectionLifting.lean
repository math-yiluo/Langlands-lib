import Langlands.AlgebraicGeometry.Picard.ProperFibreSectionShrinking
import Langlands.AlgebraicGeometry.Picard.AmpleFiniteSectionCover
import Langlands.AlgebraicGeometry.Picard.PowerSectionDegreeGrowth
import Langlands.AlgebraicGeometry.Modules.FiniteFibreNeighbourhoodLifts
import Langlands.AlgebraicGeometry.Modules.FibreNeighbourhoodSectionBridge

/-! # From eventual fibre-section lifting to fixed-bundle ampleness spreading -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules

namespace Langlands.AlgebraicGeometry.Picard

/-- Eventual lifting of actual fibre power sections implies spreading of the
ampleness of the same fixed line bundle. -/
lemma properFibreAmpleSpreading_of_powerSectionLifting
    (h : ProperFibrePowerSectionLiftingStatement.{u}) :
    ProperFibreAmpleSpreadingStatement.{u} := by
  intro X S _ p _ L s hL
  let Ls : LineBundle (p.fiber s) := (LineBundle.pullback (p.fiberι s)).obj L
  let C := hL.finiteAffinePowerSectionCover
  obtain ⟨N, hN⟩ := h.finite_family X S p L s hL
  obtain ⟨n, hn, hNn, σ, hσ⟩ :=
    Ls.exists_sections_above_degree C.degree_pos C.sections N
  let e := actualPullbackTensorPowIso (p.fiberι s) L.obj n
  let σ₀ : Fin (C.dimension + 1) →
      GlobalSections ((Scheme.Modules.pullback (p.fiberι s)).obj (tensorPow L.obj n)) :=
    fun i => e.inv.app ⊤ (σ i)
  obtain ⟨D⟩ := hN n hNn σ₀
  let V : S.Opens := D.neighbourhood
  let A : X.Opens := p ⁻¹ᵁ V
  let L' : LineBundle A.toScheme := (LineBundle.pullback A.ι).obj L
  have hkrange : Set.range (p.fiberι s) ⊆ Set.range A.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact fibre_preimage_neighbourhood p s D.point_mem (show x ∈ ⊤ from trivial)
  let k : p.fiber s ⟶ A.toScheme := IsOpenImmersion.lift A.ι (p.fiberι s) hkrange
  have hk : k ≫ A.ι = p.fiberι s := IsOpenImmersion.lift_fac _ _ _
  let τ : Fin (C.dimension + 1) → L'.powSections n :=
    fun i => L.openPowSection A (D.sections i)
  have hτ (i : Fin (C.dimension + 1)) :
      k ⁻¹ᵁ L'.sectionOpen (τ i) = Ls.sectionOpen (σ i) := by
    rw [LineBundle.sectionOpen_openPowSection_fibre p s L D.point_mem k hk,
      D.restrict_eq]
    exact congrArg Ls.sectionOpen
      (congrArg (fun g : tensorPow Ls.obj n ⟶ tensorPow Ls.obj n =>
        g.app ⊤ (σ i)) e.inv_hom_id)
  let s' : V.toScheme := ⟨s, D.point_mem⟩
  let m : (p ∣_ V).fiber s' ⟶ p.fiber s := fibreRestrictionMap p V s'
  have hm : m ≫ k = (p ∣_ V).fiberι s' := by
    apply (cancel_mono A.ι).mp
    rw [Category.assoc, hk]
    exact fibreRestrictionMap_fiberι p V s'
  have hτ' (i : Fin (C.dimension + 1)) :
      (p ∣_ V).fiberι s' ⁻¹ᵁ L'.sectionOpen (τ i) =
        m ⁻¹ᵁ Ls.sectionOpen (σ i) := by
    rw [← hm, Scheme.Hom.comp_preimage, hτ]
  have hcover : ∀ x : (p ∣_ V).fiber s', ∃ i,
      x ∈ (p ∣_ V).fiberι s' ⁻¹ᵁ L'.sectionOpen (τ i) := by
    intro x
    obtain ⟨i, hi⟩ := C.covers (m x)
    refine ⟨i, ?_⟩
    rw [hτ', hσ]
    exact hi
  have haff : ∀ i, IsAffineOpen ((p ∣_ V).fiberι s' ⁻¹ᵁ
      L'.sectionOpen (τ i)) := by
    intro i
    rw [hτ', hσ]
    exact (C.affine i).preimage m
  exact exists_ample_neighbourhood_of_restrict p L s V D.point_mem
    (exists_ample_neighbourhood_of_fibre_sections (p ∣_ V) L' s' hn τ hcover haff)

/-- Choose an actual affine neighbourhood on which the fixed bundle is ample,
given the eventual fibre-power-section lifting statement. -/
def ampleNeighbourhoodOfPowerSectionLifting
    (h : ProperFibrePowerSectionLiftingStatement.{u})
    {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (p : X ⟶ S) [IsProper p] (L : LineBundle X) (s : S)
    (hL : ((LineBundle.pullback (p.fiberι s)).obj L).IsAmple) :
    {V : S.Opens // s ∈ V ∧ IsAffineOpen V ∧
      ((LineBundle.pullback (p ⁻¹ᵁ V).ι).obj L).IsAmple} :=
  ⟨(properFibreAmpleSpreading_of_powerSectionLifting h X S p L s hL).choose,
    (properFibreAmpleSpreading_of_powerSectionLifting h X S p L s hL).choose_spec⟩

end Langlands.AlgebraicGeometry.Picard
