import Langlands.AlgebraicGeometry.Picard.AmpleSectionExactDimensionStatement
import Langlands.AlgebraicGeometry.Picard.LineBundleSectionVanishingDimensionProof
import Langlands.AlgebraicGeometry.Picard.AmpleSectionOpenBasisProof

/-! # Ample sections with a vanishing set of exactly codimension one -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Order
open Langlands.SchemeModule Langlands.Scheme.Modules
open scoped Pointwise

namespace Langlands.AlgebraicGeometry.Picard

/-- A finite-dimensional quasi-compact scheme has a closed point whose
stalk has the full topological dimension. -/
theorem exists_closedPoint_stalk_dim_eq
    (X : Scheme.{u}) [CompactSpace X] (d : ℕ)
    (hdim : topologicalKrullDim X = (d : WithBot ℕ∞)) :
    ∃ x : X, IsClosed ({x} : Set X) ∧
      ringKrullDim (X.presheaf.stalk x) = (d : WithBot ℕ∞) := by
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp hdim.ge
  obtain ⟨x, hx, hxc⟩ := p.head.isClosed.exists_closed_singleton
    p.head.isIrreducible.nonempty
  let C : IrreducibleCloseds X := ⟨{x}, isIrreducible_singleton, hxc⟩
  have hCT : C ≤ p.head := Set.singleton_subset_iff.mpr hx
  have hlow : (d : ℕ∞) ≤ coheight C := by
    rw [← hp]
    exact Order.length_le_coheight_head.trans (Order.coheight_anti hCT)
  have hC : C = (irreducibleSetEquivPoints (α := X)).symm x :=
    IrreducibleCloseds.ext (by
      change ({x} : Set X) = closure {x}
      exact hxc.closure_eq.symm)
  have hcoe : coheight C = coheight x := by
    rw [hC]
    exact coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm x
  refine ⟨x, hxc, ?_⟩
  rw [ringKrullDim_stalk_eq_coheight, ← hcoe]
  apply le_antisymm
  · exact (coheight_le_krullDim C).trans hdim.le
  · exact_mod_cast hlow

/-- The local principal-quotient inequality bounds a stalk dimension
by one plus the dimension of the actual section vanishing set. -/
theorem lineBundle_stalk_dim_le_vanishing_add_one
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (L : LineBundle X) (s : GlobalSections L.obj)
    (x : X) (hx : x ∉ trivializationOpen L.obj s) :
    ringKrullDim (X.presheaf.stalk x) ≤
      topologicalKrullDim {x : X // x ∉ trivializationOpen L.obj s} + 1 := by
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
  have hdimlocal : ringKrullDim (U.toScheme.presheaf.stalk y) =
      ringKrullDim (X.presheaf.stalk x) := by
    exact (ringKrullDim_eq_of_ringEquiv
      (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv).symm
  have hquot := ringKrullDim_quotient_germ_le_vanishing U.toScheme y c
  let Z : Set X := (trivializationOpen L.obj s : Set X)ᶜ
  have hmaps (z : {z : U.toScheme // z ∉ U.toScheme.basicOpen c}) :
      U.ι z.1 ∈ Z := by
    intro hz'
    exact z.2 ((hcoeff z.1).mpr hz')
  have hsub :=
    (U.ι.isEmbedding.isInducing.comp IsInducing.subtypeVal).codRestrict hmaps
  have hglobal := hsub.topologicalKrullDim_le
  calc ringKrullDim (X.presheaf.stalk x) =
        ringKrullDim (U.toScheme.presheaf.stalk y) := hdimlocal.symm
    _ ≤ ringKrullDim (U.toScheme.presheaf.stalk y ⧸
      Ideal.span {U.toScheme.presheaf.germ ⊤ y trivial c}) + 1 := hlocal
    _ ≤ topologicalKrullDim {z : U.toScheme // z ∉ U.toScheme.basicOpen c} + 1 :=
      add_le_add hquot le_rfl
    _ ≤ topologicalKrullDim {x : X // x ∉ trivializationOpen L.obj s} + 1 :=
      add_le_add hglobal le_rfl

/-- A positive-dimensional irreducible locally Noetherian scheme with
an ample line bundle admits a positive-power section with a nonempty
vanishing set of exactly codimension one. -/
theorem exists_ampleSection_exact_dimension
    (X : Scheme.{u}) [IsLocallyNoetherian X] [IrreducibleSpace X]
    (d : ℕ) (hd : 0 < d) (hdim : topologicalKrullDim X = (d : WithBot ℕ∞))
    (L : LineBundle X) (hL : L.IsAmple) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
      (∃ y : X, y ∈ L.sectionOpen s) ∧
      (∃ x : X, x ∉ L.sectionOpen s) ∧
      topologicalKrullDim {x : X // x ∉ L.sectionOpen s} + 1 =
        (d : WithBot ℕ∞) := by
  classical
  let : CompactSpace X := hL.compactSpace
  obtain ⟨x, hxc, hxDim⟩ := exists_closedPoint_stalk_dim_eq X d hdim
  have hnt : Nontrivial X := by
    by_contra h
    let : Subsingleton X := not_nontrivial_iff_subsingleton.mp h
    have hzero := topologicalKrullDim_zero_of_discreteTopology X
    rw [hdim] at hzero
    have : d ≤ 0 := by exact_mod_cast hzero
    exact Nat.not_le_of_gt hd this
  let : Nontrivial X := hnt
  obtain ⟨y, hyx⟩ := exists_ne x
  let W : X.Opens := ⟨({x} : Set X)ᶜ, hxc.isOpen_compl⟩
  have hyW : y ∈ W := hyx
  obtain ⟨n, hn, s, hys, hsW⟩ := ampleSectionOpenBasis X L hL W y hyW
  have hxs : x ∉ L.sectionOpen s := by
    intro hx
    exact (hsW hx) (Set.mem_singleton x)
  refine ⟨n, hn, s, ⟨y, hys⟩, ⟨x, hxs⟩, ?_⟩
  let M : LineBundle X := ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne X L n⟩
  apply le_antisymm
  · apply le_trans (topologicalKrullDim_add_one_le_of_isClosed
      (L.sectionOpen s : Set X)ᶜ (L.sectionOpen s).isOpen.isClosed_compl ?_) hdim.le
    intro he
    exact (show y ∈ (L.sectionOpen s : Set X)ᶜ from he.symm ▸ Set.mem_univ y) hys
  · rw [← hxDim]
    exact lineBundle_stalk_dim_le_vanishing_add_one X M s x hxs

/-- Exact-dimensional ample section cuts, with the maximal-stalk point
existence assertion used in their construction. -/
theorem ampleSectionExactDimension : AmpleSectionExactDimensionStatement.{u} := by
  exact ⟨exists_closedPoint_stalk_dim_eq, exists_ampleSection_exact_dimension⟩

end Langlands.AlgebraicGeometry.Picard
