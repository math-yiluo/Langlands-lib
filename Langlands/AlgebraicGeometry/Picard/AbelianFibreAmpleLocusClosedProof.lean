import Langlands.AlgebraicGeometry.Picard.AbelianFibreAmpleLocusClosedStatement
import Langlands.AlgebraicGeometry.Picard.DvrAbelianAmpleSpecializationStatement
import Langlands.AlgebraicGeometry.Picard.FibreAmplenessBaseChange
import Langlands.AlgebraicGeometry.NoetherianDvrSpecialization
import Langlands.AlgebraicGeometry.Picard.DvrAbelianAmpleSpecializationProof

/-! # Closedness of the abelian ample-fibre locus: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard

/-- In a quasi-sober `T₀` space covered by open noetherian subspaces, an open
set that is stable under specialization is closed. -/
theorem isClosed_of_isOpen_of_stableUnderSpecialization_of_noetherianCover
    {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X]
    (hcover : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ NoetherianSpace U)
    {Z : Set X} (hZ : IsOpen Z) (hs : StableUnderSpecialization Z) : IsClosed Z := by
  rw [← closure_subset_iff_isClosed]
  intro x hx
  obtain ⟨U, hU, hxU, hN⟩ := hcover x
  let Y : Set X := Z ∩ U
  have : NoetherianSpace Y := NoetherianSpace.inter_of_right Z U
  have : QuasiSober Y := (hZ.inter hU).isOpenEmbedding_subtypeVal.quasiSober
  have hG : (genericPoints Y).Finite :=
    genericPoints.finite NoetherianSpace.finite_irreducibleComponents
  have hY : Y ⊆ closure (Subtype.val '' genericPoints Y) := by
    intro y hy
    have hmem : (⟨y, hy⟩ : Y) ∈ closure (genericPoints Y) := by
      rw [genericPoints.closure]
      trivial
    exact image_closure_subset_closure_image continuous_subtype_val ⟨⟨y, hy⟩, hmem, rfl⟩
  have hxY : x ∈ closure Y := by
    have h := hU.inter_closure (t := Z) ⟨hxU, hx⟩
    rwa [Set.inter_comm] at h
  have hx' : x ∈ closure (Subtype.val '' genericPoints Y) :=
    closure_minimal hY isClosed_closure hxY
  rw [← Set.biUnion_of_singleton (Subtype.val '' genericPoints Y),
    (hG.image _).closure_biUnion] at hx'
  obtain ⟨g, ⟨g', _, rfl⟩, hgx⟩ := Set.mem_iUnion₂.mp hx'
  exact hs (specializes_iff_mem_closure.mpr hgx) g'.2.1

/-- In a locally noetherian scheme, an open set stable under specialization
is closed. -/
theorem isClosed_of_isOpen_of_stableUnderSpecialization_of_isLocallyNoetherian
    (S : Scheme.{u}) [IsLocallyNoetherian S] {Z : Set S}
    (hZ : IsOpen Z) (hs : StableUnderSpecialization Z) : IsClosed Z := by
  refine isClosed_of_isOpen_of_stableUnderSpecialization_of_noetherianCover ?_ hZ hs
  intro x
  obtain ⟨W, hW, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) (by trivial)
  have := IsLocallyNoetherian.component_noetherian (X := S) ⟨W, hW⟩
  exact ⟨W, W.isOpen, hxW, noetherianSpace_of_isAffineOpen W hW⟩

/-- Generic-to-closed specialization of ampleness over discrete valuation
rings implies closedness of the ample-fibre locus on every abelian scheme over
a locally noetherian base. -/
theorem abelianFibreAmpleLocusClosed_of_dvrSpecialization
    (h : DvrAbelianAmpleSpecializationStatement.{u}) :
    AbelianFibreAmpleLocusClosedStatement.{u} := by
  intro S _ A L
  change IsClosed (ampleFibreLocus A.X.hom L)
  apply isClosed_of_isOpen_of_stableUnderSpecialization_of_isLocallyNoetherian S
    (isOpen_ampleFibreLocus A.X.hom L)
  intro η s hηs hη
  by_cases hne : η = s
  · subst hne
    exact hη
  obtain ⟨D⟩ := nonempty_dvrSpecialization S η s hηs hne
  let B := (Langlands.AbelianScheme.baseChange D.map).obj A
  have hpb : IsPullback (pullback.fst A.X.hom D.map) (pullback.snd A.X.hom D.map)
      A.X.hom D.map :=
    IsPullback.of_hasPullback _ _
  let LB : LineBundle B.X.left := (LineBundle.pullback (pullback.fst A.X.hom D.map)).obj L
  have hgen : (⟨⊥, inferInstance⟩ : PrimeSpectrum D.ring) ∈
      ampleFibreLocus (pullback.snd A.X.hom D.map)
        ((LineBundle.pullback (pullback.fst A.X.hom D.map)).obj L) := by
    rw [mem_ampleFibreLocus_iff_of_isPullback hpb, D.generic_image]
    exact hη
  have hclosed := h D.ring B LB hgen
  have hmem : IsLocalRing.closedPoint D.ring ∈
      ampleFibreLocus (pullback.snd A.X.hom D.map)
        ((LineBundle.pullback (pullback.fst A.X.hom D.map)).obj L) := hclosed
  rw [mem_ampleFibreLocus_iff_of_isPullback hpb, D.closed_image] at hmem
  exact hmem

/-- On an abelian scheme over a locally noetherian base, the set of points of
the base whose fibre of a given line bundle is ample is closed. -/
theorem abelianFibreAmpleLocusClosed : AbelianFibreAmpleLocusClosedStatement.{u} :=
  abelianFibreAmpleLocusClosed_of_dvrSpecialization dvrAbelianAmpleSpecialization

end Langlands.AlgebraicGeometry.Picard
