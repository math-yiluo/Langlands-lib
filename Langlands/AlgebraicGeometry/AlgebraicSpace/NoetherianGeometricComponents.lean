import Langlands.AlgebraicGeometry.AlgebraicSpace.GenericGeometricComponents

/-! # Geometric component counts over Noetherian scheme bases -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open SchemeFiberGeometry GeometricComponentTransport

variable {S T : Scheme.{u}} {U : Over S}

/-- The actual geometric fibre component cardinality over an arbitrary scheme base. -/
def schemeGeometricFibreComponentCount (X : AlgebraicSpace S) (p : S) : ℕ∞ :=
  ENat.card
    (@_root_.ConnectedComponents
      (Points (X.presheaf ⨯ (schemeYoneda S).obj
        (Over.mk (componentCountGeometricPoint p)))) (pointTopology _))

/-- On an affine base this is the exact count used in the host statement. -/
theorem schemeGeometricFibreComponentCount_affine
    (B : Type u) [CommRing B] (X : AlgebraicSpace (Spec (CommRingCat.of B)))
    (p : Spec (CommRingCat.of B)) :
    schemeGeometricFibreComponentCount X p = geometricFibreComponentCount B X p := rfl

/-- The scheme-base count commutes with arbitrary base change. -/
theorem schemeGeometricFibreComponentCount_baseChange
    (g : T ⟶ S) (X : AlgebraicSpace S)
    (a : (schemeYoneda S).obj U ⟶ X.presheaf) (ha : IsEtale a) (hs : IsSurjective a)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] (q : T) :
    schemeGeometricFibreComponentCount (baseChange g X) q =
      schemeGeometricFibreComponentCount X (g q) :=
  ENat.card_congr (baseChangeGeometricFibreEquiv g X a ha hs q)

/-- The component count is constant on a nonempty relatively open subset of
each irreducible closed subset of a Noetherian base. -/
theorem exists_open_irreducibleClosed_geometricFibreComponentCount
    [IsNoetherian S] (X : AlgebraicSpace S) (hX : IsQuasiSeparated X)
    (a : (schemeYoneda S).obj U ⟶ X.presheaf) (ha : IsEtale a) (hs : IsSurjective a)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (Z : Set S) (hZ : IsClosed Z) (hirr : IsIrreducible Z) :
    ∃ V : Set S, IsOpen V ∧ (Z ∩ V).Nonempty ∧ ∀ p ∈ Z ∩ V, ∀ q ∈ Z ∩ V,
      schemeGeometricFibreComponentCount X p = schemeGeometricFibreComponentCount X q := by
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨Z, hZ⟩ : TopologicalSpace.Closeds S)
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
  let : LocallyOfFiniteType ((Over.pullback g).obj U).hom := by
    change LocallyOfFiniteType (Limits.pullback.snd U.hom g)
    infer_instance
  let : QuasiCompact ((Over.pullback g).obj U).hom := by
    change QuasiCompact (Limits.pullback.snd U.hom g)
    infer_instance
  obtain ⟨W, hW, hne, hcomp⟩ :=
    exists_open_geometricComponentsEquiv (baseChange g X)
      (IsQuasiSeparated.baseChange hX) (restrictAtlas g a)
      (relative_restrictAtlas _ ha) (relative_restrictAtlas _ hs)
  obtain ⟨V, hV, himage⟩ := g.isEmbedding.isInducing.image_eq_isOpen_inter_range hW
  have himage' : g '' W = Z ∩ V := by
    simpa only [hrange, Set.inter_comm] using himage
  refine ⟨V, hV, himage' ▸ hne.image g, ?_⟩
  rw [← himage']
  rintro p ⟨p', hp', rfl⟩ q ⟨q', hq', rfl⟩
  exact (schemeGeometricFibreComponentCount_baseChange g X a ha hs p').symm.trans
    ((ENat.card_congr (hcomp p' hp' q' hq').some).trans
      (schemeGeometricFibreComponentCount_baseChange g X a ha hs q'))

/-- Every level set of the actual geometric component count is constructible
over a Noetherian base. -/
theorem isConstructible_schemeGeometricFibreComponentCount
    [IsNoetherian S] (X : AlgebraicSpace S) (hX : IsQuasiSeparated X)
    (a : (schemeYoneda S).obj U ⟶ X.presheaf) (ha : IsEtale a) (hs : IsSurjective a)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] (c : ℕ∞) :
    IsConstructible {p : S | schemeGeometricFibreComponentCount X p = c} := by
  classical
  apply isConstructible_of_irreducibleClosed_genericConstancy
  intro Z hZ hirr
  obtain ⟨V, hV, hne, hconst⟩ :=
    exists_open_irreducibleClosed_geometricFibreComponentCount X hX a ha hs Z hZ hirr
  obtain ⟨p, hp⟩ := hne
  refine ⟨V, hV, ⟨p, hp⟩, ?_⟩
  by_cases hc : schemeGeometricFibreComponentCount X p = c
  · exact Or.inl (fun q hq => (hconst q hq p hp).trans hc)
  · refine Or.inr (Set.disjoint_left.mpr ?_)
    intro q hq hqc
    exact hc ((hconst p hp q hq).trans hqc)

/-- The exact host component-count level sets are constructible over every
Noetherian ring, with no restriction on the natural number of components. -/
theorem isConstructible_geometricFibreComponentCount_noetherian
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    (X : AlgebraicSpace (Spec (CommRingCat.of B))) (hX : IsQuasiSeparated X)
    (hfp : FinitePresentationOverRing B X) (n : ℕ) :
    IsConstructible {p : Spec (CommRingCat.of B) | geometricFibreComponentCount B X p = n} := by
  obtain ⟨U, a, ha, hs, hU⟩ := hfp
  let := hU.1
  let := hU.2
  exact isConstructible_schemeGeometricFibreComponentCount X hX a ha hs n

end Langlands.AlgebraicGeometry.AlgebraicSpace
