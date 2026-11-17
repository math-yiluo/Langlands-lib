import Langlands.GroupScheme.Reductive.AffineSplitIsogenyRootMap
import Langlands.GroupScheme.Reductive.CorootCellExtension
import Langlands.GroupScheme.Reductive.LocalSplitRootPairCommutator

/-! # Powered big-cell maps and their conditional extensions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] {I J : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))}

/-- A cell point with one negative coordinate is the corresponding root point. -/
theorem mkCellPoint_single_neg_comp_cellMap
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (u : J → (Ga R ⟶ G))
    {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    (Z : Over (Spec (CommRingCat.of R))) (k : Fin m) (c : Γ(Z.left, ⊤)) :
    mkCellPoint Z (Pi.single k c) 1 (0 : Fin n → Γ(Z.left, ⊤)) ≫
        cellMap i u neg pos = rootPoint (u (neg k)) Z c := by
  have ht : torusCoord (mkCellPoint (I := I) Z (Pi.single k c) 1
      (0 : Fin n → Γ(Z.left, ⊤))) = 1 :=
    (splitTorus.pointsEquiv I Z).injective (by rw [torusCoord_mkCellPoint, map_one])
  rw [comp_cellMap, cellPoint, negCoord_mkCellPoint, posCoord_mkCellPoint, ht,
    orderedProduct_zero, MonObj.one_comp, mul_one, mul_one]
  rw [orderedProduct_eq_rootPoint_of_eq_zero u neg Z _ k
    (fun l hl => by simp [hl]), Pi.single_eq_same]

/-- A cell point with one positive coordinate is the corresponding root point. -/
theorem mkCellPoint_single_pos_comp_cellMap
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (u : J → (Ga R ⟶ G))
    {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    (Z : Over (Spec (CommRingCat.of R))) (k : Fin n) (c : Γ(Z.left, ⊤)) :
    mkCellPoint Z (0 : Fin m → Γ(Z.left, ⊤)) 1 (Pi.single k c) ≫
        cellMap i u neg pos = rootPoint (u (pos k)) Z c := by
  have ht : torusCoord (mkCellPoint (I := I) Z (0 : Fin m → Γ(Z.left, ⊤)) 1
      (Pi.single k c)) = 1 :=
    (splitTorus.pointsEquiv I Z).injective (by rw [torusCoord_mkCellPoint, map_one])
  rw [comp_cellMap, cellPoint, negCoord_mkCellPoint, posCoord_mkCellPoint, ht,
    orderedProduct_zero, MonObj.one_comp, one_mul, one_mul]
  rw [orderedProduct_eq_rootPoint_of_eq_zero u pos Z _ k
    (fun l hl => by simp [hl]), Pi.single_eq_same]

end Langlands.GroupScheme.LocalSplitCell

namespace Langlands.GroupScheme.AffineRootDatumIsogeny

open LocalSplitCell

variable {R : Type u} [CommRing R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced] {p : ℕ}
  {G H : GroupScheme (Spec (CommRingCat.of R))}

/-- The target root family, indexed by source roots and precomposed with their powers. -/
def poweredRootFamily (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)
    (u' : J' → (Ga R ⟶ H)) (j : J) : Ga R ⟶ H :=
  rootMap f hchar (f.indexEquiv.symm j) (u' (f.indexEquiv.symm j))

/-- The powered family has the prescribed formula on every scheme test. -/
theorem rootPoint_poweredRootFamily (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)
    (u' : J' → (Ga R ⟶ H)) (j : J)
    (Z : Over (Spec (CommRingCat.of R))) (c : Γ(Z.left, ⊤)) :
    rootPoint (poweredRootFamily f hchar u' j) Z c =
      rootPoint (u' (f.indexEquiv.symm j)) Z (c ^ f.rootFactor (f.indexEquiv.symm j)) :=
  rootPoint_rootMap f hchar _ _ Z c

/-- The powered target family has the source root characters under the prescribed torus map. -/
theorem poweredRootFamily_equivariant
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)
    (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    (u' : J' → (Ga R ⟶ H))
    (hu' : ∀ j', IsRootParametrization i' (Q.root j') (u' j')) :
    TorusEquivariant (torusMap _ f ≫ i') (fun j => P.root j)
      (poweredRootFamily f hchar u') := by
  intro j Z t c
  simpa only [poweredRootFamily, torusChar, Equiv.apply_symm_apply] using
    rootMap_equivariant f hchar (f.indexEquiv.symm j) i' _ (hu' _) Z t c

/-- The actual powered cell map, with the torus map and each root factor prescribed by `f`. -/
def poweredCellMap (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)
    (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    (u' : J' → (Ga R ⟶ H)) {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J) :
    cellObj R I m n ⟶ H.X :=
  cellMap (torusMap _ f ≫ i') (poweredRootFamily f hchar u') neg pos

variable (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
  (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}
  {u : J → (Ga R ⟶ G)} {u' : J' → (Ga R ⟶ H)}
  {m n : ℕ} {neg : Fin m → J} {pos : Fin n → J}

/-- Torus translation transfers to the powered cell over every base ring. -/
theorem torusRelations_poweredCellMap [Mono (cellMap i u neg pos)]
    (hu : ∀ j, IsRootParametrization i (P.root j) (u j))
    (hu' : ∀ j', IsRootParametrization i' (Q.root j') (u' j')) :
    TorusRelations (cellMap i u neg pos) (poweredCellMap f hchar i' u' neg pos)
      i (torusMap _ f ≫ i') :=
  torusRelations_of_equivariant (fun j Z t c => (hu j).equivariant Z t c)
    (poweredRootFamily_equivariant f hchar i' u' hu')

/-- The root translation relations are the remaining premise for powered-cell compatibility. -/
theorem cellCompatible_poweredCellMap_of_rootRelations
    [IsAffine H.X.left] [IsOpenImmersion (cellMap i u neg pos).left]
    (hG : IsReductive G)
    (hu : ∀ j, IsRootParametrization i (P.root j) (u j))
    (hu' : ∀ j', IsRootParametrization i' (Q.root j') (u' j'))
    (hR : RootRelations (cellMap i u neg pos) (poweredCellMap f hchar i' u' neg pos)
      u (poweredRootFamily f hchar u')) :
    CellGluing.CellCompatible (cellMap i u neg pos)
      (poweredCellMap f hchar i' u' neg pos) := by
  have : Mono (cellMap i u neg pos) := Over.mono_of_mono_left _
  exact cellCompatible_of_generatorRelations hG
    (torusRelations_poweredCellMap f hchar hu hu') hR

section Extension

variable [IsOpenImmersion (cellMap i u neg pos).left]
  (hG : IsReductive G)
  (hc : CellGluing.CellCompatible (cellMap i u neg pos)
    (poweredCellMap f hchar i' u' neg pos))

/-- A compatible powered cell extends to an actual homomorphism of the ambient groups. -/
def poweredCellExtension : G ⟶ H :=
  have := hG.smooth
  have := hG.geometricallyIrreducible
  CellGluing.glueHom hc (cellUnit R I m n) (cellUnit_comp_cellMap i u neg pos)

/-- The extension agrees with the supplied powered map on the entire source cell. -/
theorem cell_comp_poweredCellExtension :
    cellMap i u neg pos ≫ (poweredCellExtension f hchar hG hc).hom.hom =
      poweredCellMap f hchar i' u' neg pos := by
  have := hG.smooth
  have := hG.geometricallyIrreducible
  exact CellGluing.cell_comp_glueHom hc (cellUnit R I m n)
    (cellUnit_comp_cellMap i u neg pos)

/-- The extension has exactly the prescribed restriction to the source torus. -/
theorem inclusion_comp_poweredCellExtension :
    i ≫ poweredCellExtension f hchar hG hc = torusMap _ f ≫ i' := by
  apply Grp.hom_ext
  rw [Grp.comp_hom_hom, ← RelativeDerived.torusCellSection_comp_cellMap
    (i := i) (u := u) (neg := neg) (pos := pos), Category.assoc,
    cell_comp_poweredCellExtension]
  exact RelativeDerived.torusCellSection_comp_cellMap

/-- The extension has the powered formula on every root appearing in either cell ordering. -/
theorem rootPoint_comp_poweredCellExtension
    (j : J) (hj : (∃ k, neg k = j) ∨ ∃ k, pos k = j)
    (Z : Over (Spec (CommRingCat.of R))) (c : Γ(Z.left, ⊤)) :
    rootPoint (u j) Z c ≫ (poweredCellExtension f hchar hG hc).hom.hom =
      rootPoint (u' (f.indexEquiv.symm j)) Z (c ^ f.rootFactor (f.indexEquiv.symm j)) := by
  rw [← rootPoint_poweredRootFamily f hchar]
  rcases hj with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [← mkCellPoint_single_neg_comp_cellMap i u neg pos Z k c, Category.assoc,
      cell_comp_poweredCellExtension]
    exact mkCellPoint_single_neg_comp_cellMap _ _ neg pos Z k c
  · rw [← mkCellPoint_single_pos_comp_cellMap i u neg pos Z k c, Category.assoc,
      cell_comp_poweredCellExtension]
    exact mkCellPoint_single_pos_comp_cellMap _ _ neg pos Z k c

/-- Matching the powered cell determines the ambient homomorphism uniquely. -/
theorem poweredCellExtension_unique (φ : G ⟶ H)
    (hφ : cellMap i u neg pos ≫ φ.hom.hom = poweredCellMap f hchar i' u' neg pos) :
    φ = poweredCellExtension f hchar hG hc := by
  have := hG.smooth
  have := hG.geometricallyIrreducible
  apply CellGluing.hom_ext_cell (cellUnit R I m n) (cellUnit_comp_cellMap i u neg pos)
  exact hφ.trans (cell_comp_poweredCellExtension f hchar hG hc).symm

end Extension

end Langlands.GroupScheme.AffineRootDatumIsogeny
