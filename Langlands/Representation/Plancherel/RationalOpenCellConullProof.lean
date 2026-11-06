import Langlands.Representation.Plancherel.RationalOpenCellConullStatement
import Langlands.Representation.Plancherel.RationalOpenCellBoundaryProof
import Langlands.AlgebraicGeometry.PointTopology.RationalLocalDensityProof
import Langlands.AlgebraicGeometry.PointTopology.RationalPointHaarProof
import Langlands.MeasureTheory.Group.NoetherianNullProof
import Langlands.GroupScheme.Rational.CharacterLatticeProof
import Langlands.GroupScheme.OrbitMapFlatProof

/-! # Haar conullness through actual algebraic boundaries -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TopologicalSpace
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace Langlands.Plancherel

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace RationalCellConull

/-- A smooth connected affine group over a field has an integral Noetherian
underlying scheme. -/
theorem noetherian_and_integral (F : Type u) [Field F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left] :
    NoetherianSpace G.X.left ∧ IsIntegral G.X.left := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsLocallyNoetherian G.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  let : IsNoetherian G.X.left := {}
  exact ⟨inferInstance, CharacterLatticeProof.isIntegral_of_smooth F G.X.hom⟩

/-- Left translation by an actual rational point acts on the underlying scheme. -/
def leftTranslationHomeomorph (F : Type u) [Field F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (g : RationalPoint F G.X) :
    G.X.left ≃ₜ G.X.left := by
  let : IsIso (FiniteIndexTransfer.leftMul G g).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (FiniteIndexTransfer.leftMul G g)))
  exact Scheme.homeoOfIso (asIso (FiniteIndexTransfer.leftMul G g).left)

/-- Evaluation intertwines the actual Hom group law with scheme translation. -/
theorem evaluation_mul (F : Type u) [Field F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (g h : RationalPoint F G.X) :
    (g * h).left (IsLocalRing.closedPoint F) =
      leftTranslationHomeomorph F G g (h.left (IsLocalRing.closedPoint F)) := by
  have heq : h ≫ FiniteIndexTransfer.leftMul G g = g * h := by
    rw [FiniteIndexTransfer.comp_leftMul]
    have hu : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of F)))) =
        𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of F)))) := by
      apply Over.OverMorphism.ext
      rfl
    rw [hu, Category.id_comp]
  change (g * h).left (IsLocalRing.closedPoint F) =
    (h ≫ FiniteIndexTransfer.leftMul G g).left (IsLocalRing.closedPoint F)
  rw [heq]

/-- A proper closed set has analytically empty interior under actual evaluation. -/
theorem interior_evaluation_preimage_eq_empty
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (X : Over (Spec (CommRingCat.of F)))
    [IsAffine X.left] [Smooth X.hom] [IsIntegral X.left]
    (Z : Closeds X.left) (hZ : Z ≠ ⊤) :
    letI : TopologicalSpace (RationalPoint F X) := rationalPointTopology F X
    interior ((fun p : RationalPoint F X =>
      p.left (IsLocalRing.closedPoint F)) ⁻¹' (Z : Set X.left)) = ∅ := by
  let : TopologicalSpace (RationalPoint F X) := rationalPointTopology F X
  by_contra hn
  have hd := (rationalLocalDensity F X).2 _ isOpen_interior
    (Set.nonempty_iff_ne_empty.mpr hn)
  have hsub : (fun p : RationalPoint F X => p.left (IsLocalRing.closedPoint F)) ''
      interior ((fun p : RationalPoint F X => p.left (IsLocalRing.closedPoint F)) ⁻¹'
        (Z : Set X.left)) ⊆ (Z : Set X.left) := by
    rintro _ ⟨p, hp, rfl⟩
    have hp' : p ∈ (fun p : RationalPoint F X =>
        p.left (IsLocalRing.closedPoint F)) ⁻¹' (Z : Set X.left) := interior_subset hp
    exact hp'
  have hcl := Z.isClosed.closure_subset_iff.mpr hsub
  apply hZ
  apply Closeds.coe_eq_univ.mp
  apply Set.eq_univ_of_univ_subset
  rwa [← hd.closure_eq]

end RationalCellConull

/-- The exact actual dynamic open-cell Haar-conullness proposition. -/
theorem rationalDynamicOpenCellConull : RationalDynamicOpenCellConullStatement.{u} := by
  intro F _ _ _ _ G hG
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  let : MeasurableSpace (RationalPoint F G.X) := borel (RationalPoint F G.X)
  intro χ mu hmu
  let := hG.smooth
  let := hG.connectedSpace
  obtain ⟨hnoeth, hint⟩ := RationalCellConull.noetherian_and_integral F G
  let := hnoeth
  let := hint
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  let : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
  let := rationalPoint_isTopologicalGroup F G
  let := rationalPoint_t2Space F G
  let := rationalPoint_locallyCompactSpace F G
  let := hmu
  let : mu.InnerRegular := (rationalPointHaarRegularity F G).2 mu hmu |>.2
  obtain ⟨Z, hZ, hproper, hboundary⟩ := rationalDynamicOpenCellBoundary F G χ
  rw [← hboundary]
  apply Langlands.MeasureTheory.noetherianClosedNull
    (RationalPoint F G.X) G.X.left mu
    (fun p : RationalPoint F G.X => p.left (IsLocalRing.closedPoint F))
    (rationalLocalDensity F G.X).1
    (RationalCellConull.leftTranslationHomeomorph F G)
    (RationalCellConull.evaluation_mul F G)
    (RationalCellConull.interior_evaluation_preimage_eq_empty F G.X)
    (⟨Z, hZ⟩ : Closeds G.X.left)
  intro ht
  exact hproper (congrArg (fun W : Closeds G.X.left => (W : Set G.X.left)) ht)

end Langlands.Plancherel
