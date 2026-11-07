import Langlands.GroupScheme.Reductive.LocalSplitWeylFamily
import Langlands.GroupScheme.Reductive.LocalSplitFieldComparison
import Langlands.GroupScheme.CellFieldCompatibility
import Langlands.GroupScheme.SmoothProducts
import Langlands.GroupScheme.CorepresentedSmooth
import Langlands.AlgebraicGeometry.SmoothReducedBase
import Langlands.GroupScheme.Reductive.ReductiveFibreIrreducibility

/-! # Isomorphisms of reductive groups over a reduced ring from big cells and field points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G H : GroupScheme (Spec (CommRingCat.of R))}

/-- The unit point `(0, 1, 0)` of the cell source `𝔾ₐᵐ × T × 𝔾ₐⁿ`. -/
def cellUnit (R : Type u) [CommRing R] (I : Type u) [Fintype I] (m n : ℕ) :
    𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ cellObj R I m n :=
  lift (lift 1 1) 1

omit [Fintype I] in
theorem orderedProduct_zero (u : J → (Ga R ⟶ G)) {r : ℕ} (e : Fin r → J)
    (Z : Over (Spec (CommRingCat.of R))) : orderedProduct u e Z 0 = 1 := by
  simp [orderedProduct, rootPoint_zero]

/-- The cell map sends the unit point to the identity. -/
theorem cellUnit_comp_cellMap (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (u : J → (Ga R ⟶ G)) {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J) :
    cellUnit R I m n ≫ cellMap i u neg pos = 1 := by
  have hneg : negCoord (cellUnit R I m n) = 0 := by
    rw [negCoord, cellUnit, lift_fst_assoc, lift_fst, map_one]
    rfl
  have hpos : posCoord (cellUnit R I m n) = 0 := by
    rw [posCoord, cellUnit, lift_snd, map_one]
    rfl
  have htor : torusCoord (cellUnit R I m n) = 1 := by
    rw [torusCoord, cellUnit, lift_fst_assoc, lift_snd]
  rw [comp_cellMap, cellPoint, hneg, hpos, htor, orderedProduct_zero, orderedProduct_zero,
    MonObj.one_comp, mul_one, one_mul]

theorem smooth_cellObj (m n : ℕ) : Smooth (cellObj R I m n).hom := by
  have hV : ∀ d, Smooth (VectorGroup.groupScheme (CommRingCat.of R) d).X.hom := fun d =>
    Corepresented.smooth_groupScheme_iff.mpr inferInstance
  exact GroupScheme.smooth_tensor _ _
    (GroupScheme.smooth_tensor _ _ (hV m) (smooth_splitTorus I)) (hV n)

/-- Over a reduced ring the square of the cell source is reduced. -/
theorem isReduced_cellObj_tensor [IsReduced R] (m n : ℕ) :
    IsReduced (cellObj R I m n ⊗ cellObj R I m n).left := by
  have : Smooth (cellObj R I m n ⊗ cellObj R I m n).hom :=
    GroupScheme.smooth_tensor _ _ (smooth_cellObj m n) (smooth_cellObj m n)
  exact Langlands.AlgebraicGeometry.SmoothReducedBase.isReduced_of_smooth_of_isReduced
    (cellObj R I m n ⊗ cellObj R I m n).hom

/-- **Gluing from field points.** Let `G` and `H` be reductive over a reduced ring `R`, with
tori `i`, `i'` and families `u`, `u'` of maps from `𝔾ₐ` whose big-cell maps are open
immersions. Suppose that over every field point `s : Spec K ⟶ Spec R` there is an isomorphism
of point groups `G(s) ≃ H(s)` matching the torus points and all root points. Then `G ≅ H`. -/
theorem nonempty_iso_of_fieldPoints [IsReduced R] (hG : IsReductive G) (hH : IsReductive H)
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} {u : J → (Ga R ⟶ G)}
    {u' : J → (Ga R ⟶ H)} {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    [IsOpenImmersion (cellMap i u neg pos).left] [IsOpenImmersion (cellMap i' u' neg pos).left]
    (hF : ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)),
      ∃ Ψ : (Over.mk s ⟶ G.X) ≃* (Over.mk s ⟶ H.X),
        (∀ t : Over.mk s ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X,
          Ψ (t ≫ i.hom.hom) = t ≫ i'.hom.hom) ∧
        ∀ α c, Ψ (rootPoint (u α) _ c) = rootPoint (u' α) _ c) :
    Nonempty (G ≅ H) := by
  have := hG.smooth
  have := hH.smooth
  have := hG.isAffineHom
  have := hH.isAffineHom
  have := hG.geometricallyIrreducible
  have := hH.geometricallyIrreducible
  have := isReduced_cellObj_tensor (R := R) (I := I) m n
  have hc : CellGluing.CellCompatible (cellMap i u neg pos) (cellMap i' u' neg pos) := by
    apply CellFieldCompatibility.cellCompatible_of_fieldCompatible
    intro K _ s x y c h
    obtain ⟨Ψ, hi, hu⟩ := hF K s
    exact cellRelation_of_map Ψ.toMonoidHom hi hu neg pos x y c h
  have hc' : CellGluing.CellCompatible (cellMap i' u' neg pos) (cellMap i u neg pos) := by
    apply CellFieldCompatibility.cellCompatible_of_fieldCompatible
    intro K _ s x y c h
    obtain ⟨Ψ, hi, hu⟩ := hF K s
    refine cellRelation_of_map Ψ.symm.toMonoidHom (fun t => ?_) (fun α c => ?_) neg pos x y c h
    · exact (Ψ.symm_apply_eq.mpr (hi t).symm)
    · exact (Ψ.symm_apply_eq.mpr (hu α c).symm)
  obtain ⟨ψ, -⟩ := CellGluing.exists_iso_of_cellCompatible (cellMap i u neg pos)
    (cellMap i' u' neg pos) (cellUnit R I m n) (cellUnit_comp_cellMap i u neg pos)
    (cellUnit_comp_cellMap i' u' neg pos) hc hc'
  exact ⟨ψ⟩

/-- The points over the base change of the unit object along a field algebra `R → K`. -/
abbrev fieldPoint (R : Type u) [CommRing R] (K : Type u) [CommRing K] [Algebra R K] :
    Over (Spec (CommRingCat.of R)) :=
  (Over.map (algebraBaseMap R K)).obj (𝟙_ (Over (Spec (CommRingCat.of K))))

/-- Precomposition with an isomorphism of test objects, as an isomorphism of point groups. -/
def precompPointsEquiv {Z Z' : Over (Spec (CommRingCat.of R))} (e : Z ≅ Z')
    (G : GroupScheme (Spec (CommRingCat.of R))) : (Z' ⟶ G.X) ≃* (Z ⟶ G.X) where
  toFun x := e.hom ≫ x
  invFun y := e.inv ≫ y
  left_inv x := by simp
  right_inv y := by simp
  map_mul' x y := MonObj.comp_mul _ _ _

/-- **Gluing from field algebras.** The variant of `nonempty_iso_of_fieldPoints` where the
point-group isomorphisms are only supplied over the base changes `fieldPoint R K` of the
unit object along field algebras `R → K`. -/
theorem nonempty_iso_of_fieldAlgebras [IsReduced R] (hG : IsReductive G) (hH : IsReductive H)
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} {u : J → (Ga R ⟶ G)}
    {u' : J → (Ga R ⟶ H)} {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    [IsOpenImmersion (cellMap i u neg pos).left] [IsOpenImmersion (cellMap i' u' neg pos).left]
    (hF : ∀ (K : Type u) [Field K] [Algebra R K],
      ∃ Ψ : (fieldPoint R K ⟶ G.X) ≃* (fieldPoint R K ⟶ H.X),
        (∀ t : fieldPoint R K ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X,
          Ψ (t ≫ i.hom.hom) = t ≫ i'.hom.hom) ∧
        ∀ α c, Ψ (rootPoint (u α) _ c) = rootPoint (u' α) _ c) :
    Nonempty (G ≅ H) := by
  apply nonempty_iso_of_fieldPoints (i := i) (i' := i') (u := u) (u' := u') hG hH neg pos
  intro K _ s
  let φ := Spec.preimage s
  let : Algebra R K := φ.hom.toAlgebra
  have hs : algebraBaseMap R K = s := by
    change Spec.map (CommRingCat.ofHom φ.hom) = s
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨Ψ₀, hi₀, hu₀⟩ := hF K
  let e : Over.mk s ≅ fieldPoint R K := Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ 𝟙 _ ≫ algebraBaseMap R K = s
    rw [Category.id_comp, Category.id_comp, hs])
  refine ⟨((precompPointsEquiv e G).symm.trans Ψ₀).trans (precompPointsEquiv e H),
    fun t => ?_, fun α c => ?_⟩
  · change e.hom ≫ Ψ₀ (e.inv ≫ t ≫ i.hom.hom) = t ≫ i'.hom.hom
    rw [← Category.assoc, hi₀, ← Category.assoc, Iso.hom_inv_id_assoc]
  · change e.hom ≫ Ψ₀ (e.inv ≫ rootPoint (u α) _ c) = rootPoint (u' α) _ c
    rw [comp_rootPoint, hu₀, ← comp_rootPoint, Iso.hom_inv_id_assoc]

end Langlands.GroupScheme.LocalSplitCell
