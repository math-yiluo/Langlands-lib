import Langlands.GroupScheme.Reductive.CorootCellProjection

/-! # Extending the coroot cell map from a negative-simple translation law -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {J : Type u} {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom]
  (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base)

omit [Fintype I] [DecidableEq I] [IsAffineHom G.X.hom] in
/-- Positive-factor relations transfer tautologically to trivial root maps. -/
theorem positiveLawRelations_trivial (W : ∀ α, SimpleWord P b α)
    (u : J → (Ga R ⟶ G)) {n : ℕ} (pos : Fin n → J) :
    PositiveLawRelations b W u (fun _ : J => (0 : Ga R ⟶ H)) pos := by
  intro A _ _ _ s a ha c w z h
  rw [show weylFamily P W (fun _ : J => (0 : Ga R ⟶ H)) =
    (fun _ : J => (0 : Ga R ⟶ H)) from funext (weylFamily_trivial P b W)]
  simp only [orderedProduct_trivial, rootPoint,
    trivialRootMap_hom, MonObj.comp_one, mul_one]

end Langlands.GroupScheme.LocalSplitCell

namespace Langlands.GroupScheme.RelativeDerived

open LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {J : Type u} {G : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- For the coroot cell map the negative-simple translation law is the
remaining generator relation needed for compatibility on all scheme tests. -/
theorem cellCompatible_corootCellProjection_of_negSimpleRelations
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) {b : P.Base}
    (W : ∀ α, SimpleWord P b α) (u : J → (Ga R ⟶ G))
    (hu : ∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a))
    (hw : ∀ a ∈ b.support,
      IsWeylPoint i (rootWeylPoint P u a) (P.reflection a))
    {m n : ℕ} (neg : Fin m ≃ {α // ¬ b.IsPos α})
    (pos : Fin n ≃ {α // b.IsPos α})
    (hN : NegSimpleRelations P
      (cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J)))
      (corootCellProjection R I P m n) b u
      (fun _ : J => (0 : Ga R ⟶ (corootQuotient (CommRingCat.of R) P).toGrp))) :
    CellGluing.CellCompatible
      (cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J)))
      (corootCellProjection R I P m n) := by
  let q := corootProjection (CommRingCat.of R) P
  let u₀ : J → (Ga R ⟶ (corootQuotient (CommRingCat.of R) P).toGrp) := fun _ => 0
  have hmap : cellMap q (weylFamily P W u₀)
      (fun k => (neg k : J)) (fun k => (pos k : J)) =
      corootCellProjection R I P m n := by
    rw [show weylFamily P W u₀ = u₀ from
      funext (weylFamily_trivial P b W)]
    exact cellMap_trivial q (fun k => (neg k : J)) (fun k => (pos k : J))
  have hW := isRootParametrization_weylFamily hu hw W
  have := LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP b _ hW neg pos
  let : IsAffine (corootQuotient (CommRingCat.of R) P).X.left :=
    isAffine_of_isAffineHom (corootQuotient (CommRingCat.of R) P).X.hom
  rw [← hmap] at hN ⊢
  apply cellCompatible_of_generatorRelations hG
  · exact torusRelations_of_equivariant
      (fun α Z t c => (hW α).equivariant Z t c)
      (by
        rw [show weylFamily P W u₀ = u₀ from
          funext (weylFamily_trivial P b W)]
        exact torusEquivariant_trivial q (fun α => P.root α))
  · exact rootRelations_weylFamily (hasCellFactors_cellMap hG) W
      (simpleRootRelations_of_positiveLawRelations hG hmax hP W hu hw neg pos
        (positiveLawRelations_trivial P b W u _)) hN

section Extension

variable {u : J → (Ga R ⟶ G)} {m n : ℕ}
  {neg : Fin m → J} {pos : Fin n → J}
  [IsOpenImmersion (cellMap i u neg pos).left]

/-- A compatible coroot cell map extends to an actual group-scheme homomorphism. -/
def corootCellExtension (hG : IsReductive G)
    (hc : CellGluing.CellCompatible (cellMap i u neg pos)
      (corootCellProjection R I P m n)) :
    G ⟶ (corootQuotient (CommRingCat.of R) P).toGrp :=
  have := hG.smooth
  have := hG.geometricallyIrreducible
  CellGluing.glueHom hc (cellUnit R I m n) (cellUnit_comp_cellMap i u neg pos)

omit [IsAffineHom G.X.hom] in
/-- The extension agrees with the actual coroot projection on the cell. -/
theorem cell_comp_corootCellExtension (hG : IsReductive G)
    (hc : CellGluing.CellCompatible (cellMap i u neg pos)
      (corootCellProjection R I P m n)) :
    cellMap i u neg pos ≫ (corootCellExtension hG hc).hom.hom =
      corootCellProjection R I P m n := by
  have := hG.smooth
  have := hG.geometricallyIrreducible
  exact CellGluing.cell_comp_glueHom hc (cellUnit R I m n)
    (cellUnit_comp_cellMap i u neg pos)

omit [DecidableEq I] [IsAffineHom G.X.hom]
  [IsOpenImmersion (cellMap i u neg pos).left] in
/-- The source cell restricts to the supplied torus inclusion. -/
theorem torusCellSection_comp_cellMap :
    torusCellSection R I m n ≫ cellMap i u neg pos = i.hom.hom := by
  have hneg : negCoord (torusCellSection R I m n) = 0 := by
    rw [negCoord, torusCellSection, lift_fst_assoc, lift_fst, map_one]
    rfl
  have hpos : posCoord (torusCellSection R I m n) = 0 := by
    rw [posCoord, torusCellSection, lift_snd, map_one]
    rfl
  have htor : torusCoord (torusCellSection R I m n) = 𝟙 _ := by
    rw [torusCoord, torusCellSection, lift_fst_assoc, lift_snd]
  rw [comp_cellMap, cellPoint, hneg, hpos, htor, orderedProduct_zero,
    orderedProduct_zero, one_mul, mul_one, Category.id_comp]

omit [IsAffineHom G.X.hom] in
/-- The extended homomorphism has exactly the required restriction on the
coordinate maximal torus. -/
theorem inclusion_comp_corootCellExtension (hG : IsReductive G)
    (hc : CellGluing.CellCompatible (cellMap i u neg pos)
      (corootCellProjection R I P m n)) :
    i ≫ corootCellExtension hG hc = corootProjection (CommRingCat.of R) P := by
  apply Grp.hom_ext
  rw [Grp.comp_hom_hom, ← torusCellSection_comp_cellMap (i := i) (u := u)
    (neg := neg) (pos := pos), Category.assoc, cell_comp_corootCellExtension,
    torusCellSection_comp_corootCellProjection]

omit [IsAffineHom G.X.hom] in
/-- Surjectivity of the cell projection gives surjectivity of its extension. -/
theorem surjective_corootCellExtension [Finite J] (hG : IsReductive G)
    (hc : CellGluing.CellCompatible (cellMap i u neg pos)
      (corootCellProjection R I P m n)) :
    Surjective (corootCellExtension hG hc).hom.hom.left := by
  have h : Surjective ((cellMap i u neg pos).left ≫
      (corootCellExtension hG hc).hom.hom.left) := by
    change Surjective (cellMap i u neg pos ≫ (corootCellExtension hG hc).hom.hom).left
    rw [cell_comp_corootCellExtension]
    exact surjective_corootCellProjection R I P m n
  exact Surjective.of_comp (cellMap i u neg pos).left
    (corootCellExtension hG hc).hom.hom.left

end Extension

end Langlands.GroupScheme.RelativeDerived
