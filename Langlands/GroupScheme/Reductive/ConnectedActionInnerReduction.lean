import Langlands.GroupScheme.Reductive.InnerActionLocusStatement
import Langlands.GroupScheme.Rational.RootFactorPairExistenceReduction
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.Topology.Connected.Clopen

/-! # Connected fibres fill a clopen subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A clopen subset containing a section contains every connected residue fibre. -/
theorem clopen_eq_univ_of_section_connectedFibres
    {S X : Scheme.{u}} (p : X ⟶ S) (e : S ⟶ X) (he : e ≫ p = 𝟙 S)
    (hf : ∀ s : S, ConnectedSpace (p.fiber s))
    (Z : Set X) (hZ : IsClopen Z) (hZe : Set.range e ⊆ Z) : Z = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  let s := p x
  let := hf s
  have hsec : e s ∈ Set.range (p.fiberι s) := by
    rw [p.range_fiberι]
    change p (e s) = s
    rw [← Scheme.Hom.comp_apply, he]
    rfl
  obtain ⟨y, hy⟩ := hsec
  have hz : ((p.fiberι s) ⁻¹' Z).Nonempty := by
    refine ⟨y, ?_⟩
    change p.fiberι s y ∈ Z
    rw [hy]
    exact hZe ⟨s, rfl⟩
  have hall := (hZ.preimage (p.fiberι s).continuous).eq_univ hz
  have hx : p.asFiber x ∈ (p.fiberι s) ⁻¹' Z := by
    rw [hall]
    trivial
  change p.fiberι (p x) (p.asFiber x) ∈ Z at hx
  rwa [Scheme.Hom.fiberι_asFiber] at hx

/-- A clopen subgroup of a group scheme with connected residue fibres is the
whole group scheme. -/
theorem isIso_clopen_subgroup_of_connectedFibres
    {S : Scheme.{u}} {K H : GroupScheme S} (j : K ⟶ H)
    [IsOpenImmersion j.hom.hom.left] [IsClosedImmersion j.hom.hom.left]
    (hf : ∀ s : S,
      ConnectedSpace ((GroupScheme.baseChange (S.fromSpecResidueField s)).obj H).X.left) :
    IsIso j := by
  have hr : Set.range j.hom.hom.left = Set.univ := by
    apply clopen_eq_univ_of_section_connectedFibres H.X.hom η[H.X].left
      (Over.w η[H.X])
    · exact hf
    · exact ⟨j.hom.hom.left.isClosedEmbedding.isClosed_range,
        j.hom.hom.left.isOpenEmbedding.isOpen_range⟩
    · rintro _ ⟨s, rfl⟩
      refine ⟨η[K.X].left s, ?_⟩
      have hη := congrArg (fun f : Over.mk (𝟙 S) ⟶ H.X => f.left)
        (IsMonHom.one_hom j.hom.hom)
      exact congrArg (fun f : S ⟶ H.X.left => f s) hη
  have : Surjective j.hom.hom.left := ⟨Set.range_eq_univ.mp hr⟩
  have : IsIso j.hom.hom.left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  have : IsIso ((Over.forget _).map j.hom.hom) := ‹IsIso j.hom.hom.left›
  have : IsIso j.hom.hom := isIso_of_reflects_iso _ (Over.forget _)
  have : IsIso ((Mon.forget _).map j.hom) := ‹IsIso j.hom.hom›
  have : IsIso j.hom := isIso_of_reflects_iso _ (Mon.forget _)
  have : IsIso ((Grp.forget₂Mon _).map j) := ‹IsIso j.hom›
  exact isIso_of_reflects_iso j (Grp.forget₂Mon _)

/-- The isomorphism associated to a clopen subgroup over connected residue fibres. -/
def clopenSubgroupIsoOfConnectedFibres
    {S : Scheme.{u}} {K H : GroupScheme S} (j : K ⟶ H)
    [IsOpenImmersion j.hom.hom.left] [IsClosedImmersion j.hom.hom.left]
    (hf : ∀ s : S,
      ConnectedSpace ((GroupScheme.baseChange (S.fromSpecResidueField s)).obj H).X.left) :
    K ≅ H := by
  letI : IsIso j := isIso_clopen_subgroup_of_connectedFibres j hf
  exact asIso j

/-- The general-base inner-locus statement implies connected-action innerness. -/
theorem reductiveConnectedActionInner_of_innerActionLocus
    (hinner : ReductiveInnerActionLocusStatement.{u}) :
    ReductiveConnectedActionInnerStatement.{u} := by
  intro S G H hG hconn Gad p hp c hc a
  obtain ⟨K, j, φ, hopen, hclosed, hfac, huni⟩ := hinner S G H hG Gad p hp c hc a
  let : IsOpenImmersion j.hom.hom.left := hopen
  let : IsClosedImmersion j.hom.hom.left := hclosed
  have : IsIso j := isIso_clopen_subgroup_of_connectedFibres j hconn
  let ψ : H ⟶ Gad := inv j ≫ φ
  have hψ : c.restrict ψ = a := by
    dsimp only [ψ]
    rw [← AutomorphicAction.restrict_restrict, hfac, AutomorphicAction.restrict_restrict,
      IsIso.inv_hom_id, AutomorphicAction.restrict_id]
  refine ⟨ψ, hψ, ?_⟩
  intro x hx
  obtain ⟨f, ⟨hf, hfx⟩, _⟩ := huni H (𝟙 H) x
    (by simpa only [AutomorphicAction.restrict_id] using hx)
  have he : f = inv j := by
    apply (cancel_mono j).mp
    simpa only [IsIso.inv_hom_id] using hf
  rw [← hfx, he]

end Langlands.GroupScheme
