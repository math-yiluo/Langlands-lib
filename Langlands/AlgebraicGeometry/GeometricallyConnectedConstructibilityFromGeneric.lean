import Langlands.AlgebraicGeometry.GeometricallyConnectedGenericOpenDescent
import Langlands.AlgebraicGeometry.GeometricallyConnectedFiberGenericConstancy

/-! # Noetherian generic constancy and actual-fibre constructibility -/

noncomputable section

universe u

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- The actual geometric-connectedness truth value is constant near a
whole-space generic point of every Noetherian finite-type family. -/
def NoetherianGeometricallyConnectedFiberGenericConstancy : Prop :=
  ∀ {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] (η : Y),
    IsGenericPoint η (Set.univ : Set Y) →
      GeometricallyConnectedFiberConstancyAt f η

/-- The splitting, spreading and closed-cover inputs supply the
Noetherian generic-constancy premise. -/
theorem noetherianGeometricallyConnectedFiberGenericConstancy_of_generic_splitting
    (hsplit : FiniteTypeFiniteEtaleGenericComponentSplitting.{u})
    (hspread : FiniteTypeGeometricallyIrreducibleGenericSpreading.{u})
    (hcriterion : ComponentIncidence.FiniteClosedGeometricallyConnectedCoverCriterion.{u, u}) :
    NoetherianGeometricallyConnectedFiberGenericConstancy.{u} := by
  intro X Y _ f _ _ η hη
  exact geometricallyConnectedFiberConstancyAt_of_generic_splitting
    hsplit hspread hcriterion f hη

/-- Noetherian whole-space generic constancy gives the Boolean alternative
on every actual irreducible closed subset by its reduced induced scheme. -/
theorem exists_open_irreducibleClosed_geometricallyConnectedFiberLocus_of_noetherianGeneric
    (h : NoetherianGeometricallyConnectedFiberGenericConstancy.{u})
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f]
    (Z : Set Y) (hZ : IsClosed Z) (hirr : IsIrreducible Z) :
    ∃ V : Set Y, IsOpen V ∧ (Z ∩ V).Nonempty ∧
      (Z ∩ V ⊆ geometricallyConnectedFiberLocus f ∨
        Disjoint (Z ∩ V) (geometricallyConnectedFiberLocus f)) := by
  classical
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨Z, hZ⟩ : TopologicalSpace.Closeds Y)
  let g := I.subschemeι
  have hrange : Set.range g = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  let : IsNoetherian I.subscheme :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian g
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace g }
  let : IrreducibleSpace I.subscheme := by
    change IrreducibleSpace Z
    exact isIrreducible_iff_irreducibleSpace.mp hirr
  let η := genericPoint I.subscheme
  obtain ⟨W, hW, hηW, hconst⟩ :=
    h (pullback.snd f g) η (genericPoint_spec I.subscheme)
  have hconstant : GeometricallyConnectedFiberConstantOn (pullback.snd f g) W := by
    intro y hy z hz
    exact (hconst y hy).trans (hconst z hz).symm
  have hconstant' := geometricallyConnectedFiberConstantOn_image
    (IsPullback.of_hasPullback f g) hconstant
  obtain ⟨V, hV, himage⟩ := g.isEmbedding.isInducing.image_eq_isOpen_inter_range hW
  have himage' : g '' W = Z ∩ V := by
    simpa only [hrange, Set.inter_comm] using himage
  rw [himage'] at hconstant'
  have hηV : g η ∈ Z ∩ V := himage' ▸ Set.mem_image_of_mem g hηW
  refine ⟨V, hV, ⟨g η, hηV⟩, ?_⟩
  by_cases hc : g η ∈ geometricallyConnectedFiberLocus f
  · exact Or.inl (fun y hy => (hconstant' y hy (g η) hηV).mpr hc)
  · refine Or.inr (Set.disjoint_left.mpr ?_)
    intro y hy hyc
    exact hc ((hconstant' y hy (g η) hηV).mp hyc)

/-- The existing topological induction yields constructibility over any
Noetherian scheme once whole-space generic constancy is supplied. -/
theorem isConstructible_geometricallyConnectedFiberLocus_of_noetherianGeneric
    (h : NoetherianGeometricallyConnectedFiberGenericConstancy.{u})
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] :
    IsConstructible (geometricallyConnectedFiberLocus f) :=
  isConstructible_of_irreducibleClosed_genericConstancy _
    (exists_open_irreducibleClosed_geometricallyConnectedFiberLocus_of_noetherianGeneric h f)

/-- Actual Noetherian approximation then gives local constructibility on
arbitrary finite-presentation families, conditionally on generic constancy. -/
theorem geometricallyConnectedFiberLocalConstructibility_of_noetherianGeneric
    (h : NoetherianGeometricallyConnectedFiberGenericConstancy.{u}) :
    GeometricallyConnectedFiberLocalConstructibility.{u} := by
  apply geometricallyConnectedFiberLocalConstructibility_iff_noetherianAffine.mpr
  intro R _ _ X f _ _ _
  exact isConstructible_geometricallyConnectedFiberLocus_of_noetherianGeneric h f

/-- The general local-constructibility target follows from the three exact
geometric inputs, with no Noetherian hypothesis on its final families. -/
theorem geometricallyConnectedFiberLocalConstructibility_of_generic_splitting
    (hsplit : FiniteTypeFiniteEtaleGenericComponentSplitting.{u})
    (hspread : FiniteTypeGeometricallyIrreducibleGenericSpreading.{u})
    (hcriterion : ComponentIncidence.FiniteClosedGeometricallyConnectedCoverCriterion.{u, u}) :
    GeometricallyConnectedFiberLocalConstructibility.{u} :=
  geometricallyConnectedFiberLocalConstructibility_of_noetherianGeneric
    (noetherianGeometricallyConnectedFiberGenericConstancy_of_generic_splitting
      hsplit hspread hcriterion)

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
