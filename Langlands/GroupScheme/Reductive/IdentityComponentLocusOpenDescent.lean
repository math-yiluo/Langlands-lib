import Langlands.GroupScheme.Reductive.IdentityComponentLocusBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Cover.Open

/-! # Open descent for the actual reductive identity-component locus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

local instance locusDescent_smooth_pullback {S T : Scheme.{u}} (G : GroupScheme S)
    [Smooth G.X.hom] (b : T ⟶ S) : Smooth ((baseChange b).obj G).X.hom :=
  inferInstanceAs (Smooth (Limits.pullback.snd G.X.hom b))

local instance locusDescent_affine_pullback {S T : Scheme.{u}} (G : GroupScheme S)
    [IsAffineHom G.X.hom] (b : T ⟶ S) : IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

variable {S : Scheme.{u}} (G : GroupScheme S)
  [Smooth G.X.hom] [IsAffineHom G.X.hom]

/-- An actual open neighbourhood of a specified original base point, together
with reductivity of every geometric identity component over that open. -/
structure IdentityComponentReductiveOpenNeighbourhood (s : S) where
  neighbourhood : S.Opens
  mem_neighbourhood : s ∈ neighbourhood
  subset_locus : (neighbourhood : Set S) ⊆ identityComponentReductiveLocus G

/-- Construct a good open neighbourhood in the original base as the actual
image of a good open subset under the specified open base map. -/
def identityComponentReductiveOpenNeighbourhood_of_openMap
    {T : Scheme.{u}} (b : T ⟶ S) (hb : IsOpenMap b)
    (t : T) {U : Set T} (hU : IsOpen U) (ht : t ∈ U)
    (hred : U ⊆ identityComponentReductiveLocus ((baseChange b).obj G)) :
    IdentityComponentReductiveOpenNeighbourhood G (b t) where
  neighbourhood := ⟨b '' U, hb U hU⟩
  mem_neighbourhood := ⟨t, ht, rfl⟩
  subset_locus := by
    rintro _ ⟨x, hx, rfl⟩
    have h := hred hx
    rwa [identityComponentReductiveLocus_baseChange] at h

/-- A good open neighbourhood over any open base map gives a good open
neighbourhood at its image in the original base. -/
theorem exists_open_identityComponentReductiveLocus_of_openMap
    {T : Scheme.{u}} (b : T ⟶ S) (hb : IsOpenMap b)
    (t : T) {U : Set T} (hU : IsOpen U) (ht : t ∈ U)
    (hred : U ⊆ identityComponentReductiveLocus ((baseChange b).obj G)) :
    ∃ V : Set S, V ⊆ identityComponentReductiveLocus G ∧ IsOpen V ∧ b t ∈ V := by
  let d := identityComponentReductiveOpenNeighbourhood_of_openMap G b hb t hU ht hred
  exact ⟨d.neighbourhood, d.subset_locus, d.neighbourhood.isOpen, d.mem_neighbourhood⟩

/-- Pointwise neighbourhoods with reductive geometric identity components
over open base maps imply openness of the original locus. -/
theorem isOpen_identityComponentReductiveLocus_of_openLocal
    (hlocal : ∀ s ∈ identityComponentReductiveLocus G,
      ∃ (T : Scheme.{u}) (b : T ⟶ S) (t : T) (U : Set T),
        IsOpenMap b ∧ b t = s ∧ IsOpen U ∧ t ∈ U ∧
          U ⊆ identityComponentReductiveLocus ((baseChange b).obj G)) :
    IsOpen (identityComponentReductiveLocus G) := by
  apply isOpen_iff_forall_mem_open.mpr
  intro s hs
  obtain ⟨T, b, t, U, hb, hbt, hU, ht, hred⟩ := hlocal s hs
  simpa only [hbt] using
    exists_open_identityComponentReductiveLocus_of_openMap G b hb t hU ht hred

/-- In particular, it suffices to construct pointwise good open
neighbourhoods after affine etale base change. -/
theorem isOpen_identityComponentReductiveLocus_of_affineEtaleLocal
    (hlocal : ∀ s ∈ identityComponentReductiveLocus G,
      ∃ (R : CommRingCat.{u}) (b : Spec R ⟶ S) (t : Spec R) (U : Set (Spec R)),
        Etale b ∧ b t = s ∧ IsOpen U ∧ t ∈ U ∧
          U ⊆ identityComponentReductiveLocus ((baseChange b).obj G)) :
    IsOpen (identityComponentReductiveLocus G) := by
  apply isOpen_identityComponentReductiveLocus_of_openLocal G
  intro s hs
  obtain ⟨R, b, t, U, hb, hbt, hU, ht, hred⟩ := hlocal s hs
  let : Etale b := hb
  exact ⟨Spec R, b, t, U, b.isOpenMap, hbt, hU, ht, hred⟩

/-- Openness descends along any surjective open morphism of base schemes. -/
theorem isOpen_identityComponentReductiveLocus_of_surjective_openMap
    {T : Scheme.{u}} (b : T ⟶ S) (hb : IsOpenMap b) (hsurj : Function.Surjective b)
    (hopen : IsOpen (identityComponentReductiveLocus ((baseChange b).obj G))) :
    IsOpen (identityComponentReductiveLocus G) := by
  apply isOpen_identityComponentReductiveLocus_of_openLocal G
  intro s hs
  obtain ⟨t, hbt⟩ := hsurj s
  refine ⟨T, b, t, _, hb, hbt, hopen, ?_, Set.Subset.rfl⟩
  rw [identityComponentReductiveLocus_baseChange]
  change b t ∈ identityComponentReductiveLocus G
  rwa [hbt]

/-- A proof over arbitrary affine base schemes suffices for the exact
arbitrary-scheme openness proposition. -/
theorem identityComponentReductiveLocusOpen_of_affine
    (haffine : ∀ (R : CommRingCat.{u}) (H : GroupScheme (Spec R))
      [Smooth H.X.hom] [IsAffineHom H.X.hom],
        IsOpen (identityComponentReductiveLocus H)) :
    IdentityComponentReductiveLocusOpenStatement.{u} := by
  intro S G _ _
  apply isOpen_identityComponentReductiveLocus_of_openLocal G
  intro s hs
  let j := S.affineOpenCover.idx s
  let R := S.affineOpenCover.X j
  let b : Spec R ⟶ S := S.affineOpenCover.f j
  obtain ⟨t, hbt⟩ := S.affineOpenCover.covers s
  refine ⟨Spec R, b, t, identityComponentReductiveLocus ((baseChange b).obj G),
    b.isOpenMap, hbt, haffine R _, ?_, Set.Subset.rfl⟩
  rw [identityComponentReductiveLocus_baseChange]
  change b t ∈ identityComponentReductiveLocus G
  rwa [hbt]

end Langlands.GroupScheme
