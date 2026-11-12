import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasComponentIncidence
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartFibreCount
import Langlands.AlgebraicGeometry.ClosedSubschemeFiberIncidence
import Langlands.Topology.ClosedCoverQuotientComponents

/-! # Closed-cover atlas incidence and its constructible image loci -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Topology TopologicalSpace

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {F : Presheaf S} {U : Over S} {ι : Type v}

/-- Members of a chart cover are incident when its represented kernel pair joins them. -/
def atlasCoverIncidence (a : (schemeYoneda S).obj U ⟶ F)
    (ha : IsRepresentableMorphism a) (s : ι → Set U.left) (i j : ι) : Prop :=
  ∃ r : (ha.pullback a).left,
    (ha.snd a).left r ∈ s i ∧ (ha.fst' a).left r ∈ s j

/-- Kernel-pair incidence of cover members is exactly intersection of their chart images. -/
theorem coverFibreRelation_chartPointMap_iff
    (a : (schemeYoneda S).obj U ⟶ F) (ha : IsRepresentableMorphism a)
    (s : ι → Set U.left) (i j : ι) :
    Langlands.Topology.coverFibreRelation (chartPointMap a) s i j ↔
      atlasCoverIncidence a ha s i j := by
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    obtain ⟨r, hrx, hry⟩ :=
      (chartPointMap_eq_iff_exists_pullback a a ha x y).mp hxy
    exact ⟨r, hrx ▸ hx, hry ▸ hy⟩
  · rintro ⟨r, hx, hy⟩
    exact ⟨_, hx, _, hy,
      (chartPointMap_eq_iff_exists_pullback a a ha _ _).mpr ⟨r, rfl, rfl⟩⟩

/-- A finite connected closed atlas cover computes the presheaf's connected components. -/
def atlasClosedCoverConnectedComponentsEquiv [Finite ι]
    (a : (schemeYoneda S).obj U ⟶ F) (ha : IsEtale a) (hs : IsSurjective a)
    (s : ι → Set U.left) (hclosed : ∀ i, IsClosed (s i))
    (hconn : ∀ i, _root_.IsConnected (s i)) (hcover : (⋃ i, s i) = Set.univ) :
    Quot (atlasCoverIncidence a ha.representable s) ≃
      @_root_.ConnectedComponents (Points F) (pointTopology F) := by
  letI := pointTopology F
  exact (Quot.congr (Equiv.refl ι) (fun i j =>
    (coverFibreRelation_chartPointMap_iff a ha.representable s i j).symm)).trans
      (Langlands.Topology.closedCoverQuotientComponentsEquiv (chartPointMap a)
        (isQuotientMap_chartPointMap a ha hs) s hclosed hconn hcover)

/-- The overlap of an étale chart locally of finite type is locally of finite type over the base. -/
theorem locallyOfFiniteType_atlasOverlapHom
    (a : (schemeYoneda S).obj U ⟶ F) (ha : IsEtale a)
    [LocallyOfFiniteType U.hom] :
    LocallyOfFiniteType (ha.representable.pullback a).hom := by
  let : Etale (ha.representable.snd a).left := ha.property_snd a
  rw [← Over.w (ha.representable.snd a)]
  infer_instance

/-- Quasi-separatedness makes the overlap of a quasi-compact finite-type chart Noetherian
over a Noetherian base. -/
theorem noetherian_atlasOverlap [IsNoetherian S]
    (X : AlgebraicSpace S) (hX : IsQuasiSeparated X)
    (a : (schemeYoneda S).obj U ⟶ X.presheaf) (ha : IsEtale a)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] :
    IsNoetherian (ha.representable.pullback a).left := by
  let : CompactSpace U.left := QuasiCompact.compactSpace_of_compactSpace U.hom
  let : CompactSpace (U ⊗ U).left := by
    change CompactSpace (Limits.pullback U.hom U.hom : Scheme.{u})
    infer_instance
  let : CompactSpace (ha.representable.pullback a).left :=
    EtaleChartFibreCount.compactSpace_selfPullback a hX
  let := locallyOfFiniteType_atlasOverlapHom a ha
  exact
    { toIsLocallyNoetherian :=
        LocallyOfFiniteType.isLocallyNoetherian (ha.representable.pullback a).hom
      toCompactSpace := inferInstance }

/-- The base locus hit by kernel-pair points whose two projections lie in the given cover members. -/
def atlasCoverIncidenceLocus (a : (schemeYoneda S).obj U ⟶ F)
    (ha : IsRepresentableMorphism a) (s : ι → Set U.left) (i j : ι) : Set S :=
  (ha.pullback a).hom ''
    ((ha.snd a).left ⁻¹' s i ∩ (ha.fst' a).left ⁻¹' s j)

/-- Each actual closed-cover overlap image is constructible over a Noetherian base. -/
theorem isConstructible_atlasCoverIncidenceLocus [IsNoetherian S]
    (X : AlgebraicSpace S) (hX : IsQuasiSeparated X)
    (a : (schemeYoneda S).obj U ⟶ X.presheaf) (ha : IsEtale a)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (s : ι → Set U.left) (hclosed : ∀ i, IsClosed (s i)) (i j : ι) :
    IsConstructible (atlasCoverIncidenceLocus a ha.representable s i j) := by
  let := noetherian_atlasOverlap X hX a ha
  let := locallyOfFiniteType_atlasOverlapHom a ha
  apply (ha.representable.pullback a).hom.isConstructible_image
  have hc : IsClosed ((ha.representable.snd a).left ⁻¹' s i ∩
      (ha.representable.fst' a).left ⁻¹' s j) :=
    ((hclosed i).preimage (ha.representable.snd a).left.continuous).inter
      ((hclosed j).preimage (ha.representable.fst' a).left.continuous)
  exact ((NoetherianSpace.isCompact _).isConstructible hc.isOpen_compl).of_compl

/-- All finitely many closed-cover overlap image predicates are constant near a generic point. -/
theorem exists_open_atlasCoverIncidenceLoci [Finite ι] [IsNoetherian S]
    (X : AlgebraicSpace S) (hX : IsQuasiSeparated X)
    (a : (schemeYoneda S).obj U ⟶ X.presheaf) (ha : IsEtale a)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (s : ι → Set U.left) (hclosed : ∀ i, IsClosed (s i))
    {η : S} (hη : IsGenericPoint η (Set.univ : Set S)) :
    ∃ V : Set S, IsOpen V ∧ η ∈ V ∧ ∀ y ∈ V, ∀ i j,
      (y ∈ atlasCoverIncidenceLocus a ha.representable s i j ↔
        η ∈ atlasCoverIncidenceLocus a ha.representable s i j) := by
  obtain ⟨V, hV, hηV, hpattern⟩ :=
    GenericImagePattern.exists_open_finite_constructible_membership hη
      (fun ij : ι × ι => atlasCoverIncidenceLocus a ha.representable s ij.1 ij.2)
      (fun ij => isConstructible_atlasCoverIncidenceLocus X hX a ha s hclosed ij.1 ij.2)
  exact ⟨V, hV, hηV, fun y hy i j => hpattern y hy (i, j)⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
