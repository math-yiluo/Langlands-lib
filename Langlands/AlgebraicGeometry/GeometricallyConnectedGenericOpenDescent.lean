import Langlands.AlgebraicGeometry.SplitGenericFiberConnectedness
import Langlands.AlgebraicGeometry.SchemeFiberGeometryLoci
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Actual open-image descent of generic fibre connectedness constancy -/

noncomputable section

universe u

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- All actual residue-field fibres over a given set have the same
geometric-connectedness truth value. The set is allowed to be empty. -/
def GeometricallyConnectedFiberConstantOn {X Y : Scheme.{u}} (f : X ⟶ Y)
    (S : Set Y) : Prop :=
  ∀ y ∈ S, ∀ z ∈ S,
    GeometricallyConnected (f.fiberToSpecResidueField y) ↔
      GeometricallyConnected (f.fiberToSpecResidueField z)

variable {P X Y' Y : Scheme.{u}}
  {a : P ⟶ X} {b : P ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Uniform fibre connectedness descends to the actual image of any
cartesian base-change set. No openness or surjectivity is needed here. -/
theorem geometricallyConnectedFiberConstantOn_image
    (h : IsPullback a b f g) {S : Set Y'}
    (hc : GeometricallyConnectedFiberConstantOn b S) :
    GeometricallyConnectedFiberConstantOn f (g '' S) := by
  rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
  exact (geometricallyConnected_fiberBaseChange_iff h y).symm.trans
    ((hc y hy z hz).trans (geometricallyConnected_fiberBaseChange_iff h z))

/-- Constancy near any point upstairs gives constancy near the generic point
downstairs when the base-change map is open. -/
theorem geometricallyConnectedFiberConstancyAt_of_open_baseChange
    (h : IsPullback a b f g) (hg : IsOpenMap g)
    {η : Y} (hη : IsGenericPoint η (Set.univ : Set Y)) {η' : Y'}
    (hc : GeometricallyConnectedFiberConstancyAt b η') :
    GeometricallyConnectedFiberConstancyAt f η := by
  obtain ⟨W, hW, hη'W, hconst⟩ := hc
  have hconstant : GeometricallyConnectedFiberConstantOn b W := by
    intro y hy z hz
    exact (hconst y hy).trans (hconst z hz).symm
  have hconstant' := geometricallyConnectedFiberConstantOn_image h hconstant
  have hopen : IsOpen (g '' W) := hg W hW
  have hηW : η ∈ g '' W :=
    (hη.mem_open_set_iff hopen).mpr
      ⟨g η', Set.mem_univ _, ⟨η', hη'W, rfl⟩⟩
  exact ⟨g '' W, hopen, hηW, fun y hy => hconstant' y hy η hηW⟩

/-- The full splitting and irreducibility-spreading statements and the
field closed-cover criterion imply Boolean generic constancy over any
Noetherian base with a whole-space generic point. -/
theorem geometricallyConnectedFiberConstancyAt_of_generic_splitting
    (hsplit : FiniteTypeFiniteEtaleGenericComponentSplitting.{u})
    (hspread : FiniteTypeGeometricallyIrreducibleGenericSpreading.{u})
    (hcriterion : ComponentIncidence.FiniteClosedGeometricallyConnectedCoverCriterion.{u, u})
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    {η : Y} (hη : IsGenericPoint η (Set.univ : Set Y)) :
    GeometricallyConnectedFiberConstancyAt f η := by
  let : IrreducibleSpace Y := (irreducibleSpace_def Y).mpr hη.isIrreducible
  obtain ⟨V, _, Y', g, _, hirr, hsurj, hfinite, hetale, _, _, _, η', hη', hgeom⟩ :=
    hsplit f
  let := hirr
  let := hsurj
  let := hfinite
  let := hetale
  let : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := isCompact_iff_compactSpace.mp
        (NoetherianSpace.isCompact (V : Set Y)) }
  let : IsNoetherian Y' :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian g
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace g }
  have hc := GenericImagePattern.geometricallyConnectedFiberConstancyAt_of_split_components
    hspread hcriterion (pullback.snd (f ∣_ V) g) hη' hgeom
  exact geometricallyConnectedFiberConstancyAt_of_open_baseChange
    ((IsPullback.of_hasPullback (f ∣_ V) g).paste_horiz
      (isPullback_morphismRestrict f V).flip)
    (V.ι.isOpenEmbedding.isOpenMap.comp g.isOpenMap) hη hc

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
