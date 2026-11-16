import Langlands.GroupScheme.SimplyConnected.OuterTypeARankOneHermitianReduction
import Langlands.GroupScheme.SimplyConnected.OuterTypeAUnitarySplitPresentationProof
import Langlands.GroupScheme.SimplyConnected.LocalOuterTypeAHermitianModelAssembly
import Langlands.GroupScheme.SimplyConnected.TypeARankOneOrbit
import Langlands.GroupScheme.Rational.HermitianMatrixSplitRankUpper
import Langlands.GroupScheme.Examples.HermitianHyperbolicSplitRankLower
import Langlands.GroupScheme.Examples.HermitianLocalIsotropy
import Langlands.Algebra.LocalUnitaryDivisionCommutativeProof

/-!
# Rank-one outer type-A models and their local dimension bound

An actual all-test Hermitian presentation and split rank one give the existing
anisotropic-middle rank-one model. Unitary splitting supplies the presentation
for an outer type-A group, without a hypothesis on its distinguished vertices.
Over a local field the anisotropic middle has dimension at most two, so the
absolute type is A₂ or A₃. The exact endpoint marking is not asserted here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace HermitianMatrix.SchemeModel.Presentation

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {n : ℕ} {J : Form (SU3Root.fieldInvolution K L) (Fin (n + 1))}

/-- An actual Hermitian presentation with split rank one has an anisotropic
middle in its actual rank-one group-scheme model. -/
theorem nonempty_rankOneModel (p : Presentation K L J G)
    (hn : 1 ≤ n) (hrank : splitRank G = 1) :
    Nonempty (HermitianRoot.SchemeModel.RankOneModel K L n G) := by
  classical
  let ρ (T : Over (Spec (CommRingCat.of K))) :
      (T ⟶ G.X) →* Matrix.GeneralLinearGroup (Fin (n + 1))
        (SpecialLinear.WeilRoot.tensorAlgebra K L T) :=
    (tensorPoints K L J T).subtype.comp (p.pointsEquiv T).toMonoidHom
  have hinj (T) : Function.Injective (ρ T) := by
    intro x y h
    exact (p.pointsEquiv T).injective (Subtype.ext h)
  have himage (T : Over (Spec (CommRingCat.of K)))
      (g : Matrix.GeneralLinearGroup (Fin (n + 1))
        (SpecialLinear.WeilRoot.tensorAlgebra K L T)) :
      (∃ x : T ⟶ G.X, ρ T x = g) ↔
        ((g : Matrix (Fin (n + 1)) (Fin (n + 1))
            (SpecialLinear.WeilRoot.tensorAlgebra K L T)).map
          (SU3Root.SchemeModel.coefficientInvolution K L T).bar).transpose *
            (J.gram : Matrix (Fin (n + 1)) (Fin (n + 1)) L).map
              (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L T)) *
            (g : Matrix (Fin (n + 1)) (Fin (n + 1))
              (SpecialLinear.WeilRoot.tensorAlgebra K L T)) =
          (J.gram : Matrix (Fin (n + 1)) (Fin (n + 1)) L).map
            (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L T)) ∧
          Matrix.GeneralLinearGroup.det g = 1 := by
    change (∃ x, ρ T x = g) ↔ g ∈ tensorPoints K L J T
    constructor
    · rintro ⟨x, rfl⟩
      exact (p.pointsEquiv T x).property
    · intro hg
      exact ⟨(p.pointsEquiv T).symm ⟨g, hg⟩,
        congrArg Subtype.val ((p.pointsEquiv T).apply_symm_apply ⟨g, hg⟩)⟩
  have hnat {T T' : Over (Spec (CommRingCat.of K))}
      (a : T' ⟶ T) (x : T ⟶ G.X) :
      (ρ T' (a ≫ x) : Matrix (Fin (n + 1)) (Fin (n + 1))
        (SpecialLinear.WeilRoot.tensorAlgebra K L T')) =
      (ρ T x : Matrix (Fin (n + 1)) (Fin (n + 1))
        (SpecialLinear.WeilRoot.tensorAlgebra K L T)).map
          (SpecialLinear.WeilRoot.tensorMap K L a) :=
    p.matrix_naturality a x
  have hupper : splitRank G ≤ (J.wittIndex : ℕ∞) :=
    splitRank_le_wittIndex_of_matrixRepresentation J ρ hinj hnat
      (fun T x => ((himage T (ρ T x)).mp ⟨x, rfl⟩).1)
  have hwitt : (J.wittIndex : ℕ∞) = 1 :=
    (le_antisymm p.wittIndex_le_splitRank hupper).trans hrank
  have hatt : ∃ W : Submodule L (Fin (n + 1) → L),
      (∀ a b : W, J.linearFirst a.val b.val = 0) ∧
        (Module.finrank L W : ℕ∞) = 1 := by
    obtain ⟨W, hW, hdim⟩ := J.exists_totallyIsotropic_finrank_eq_wittIndex
    refine ⟨W, ?_, by rw [hdim, hwitt]⟩
    intro a b
    exact (J.totallyIsotropic_iff_linearFirst W).mp hW a.val a.property b.val b.property
  have hbound (W : Submodule L (Fin (n + 1) → L))
      (hW : ∀ a b : W, J.linearFirst a.val b.val = 0) :
      (Module.finrank L W : ℕ∞) ≤ 1 := by
    rw [← hrank]
    apply p.finrank_le_splitRank W
    apply (J.totallyIsotropic_iff_linearFirst W).mpr
    intro a ha b hb
    exact hW ⟨a, ha⟩ ⟨b, hb⟩
  exact HermitianRoot.SchemeModel.nonempty_rankOneModel_of_attained_presentation K L
    hn (Fintype.card_fin _) J.linearFirst J.bar_linearFirst
    J.gram J.linearFirst_eq_dotProduct J.linearFirst_nondegenerate hatt hbound
    ρ hinj himage hnat

end HermitianMatrix.SchemeModel.Presentation

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G) {n : ℕ}

/-- Unitary splitting produces an actual rank-one Hermitian model from the
absolute type-A numbering and nontrivial full star action. -/
theorem nonempty_outerTypeARankOneHermitianModel_of_unitarySplitting
    (hK : UnitaryInvolutionSplitting K)
    (hsc : IsSimplyConnected G) (haas : IsAbsolutelyAlmostSimple G)
    (e : d.Vertex ≃ Fin n)
    (hA : ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b))
    (hnot : ¬ d.StarIsTrivial) (hrank : splitRank G = 1) :
    Nonempty (OuterTypeARankOneHermitianModel K G n) := by
  classical
  have hmove : ∃ (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
      (a : d.Vertex), d.star σ a ≠ a := by
    simpa only [TitsIndexData.StarIsTrivial, not_forall] using hnot
  have hn : 2 ≤ n := two_le_of_star_moves e hmove
  obtain ⟨L, _, _, _, _, J, ⟨p⟩⟩ :=
    outerTypeAUnitarySplitPresentation K hK G d n hsc haas ⟨e, hA⟩ hmove
  obtain ⟨model⟩ := p.nonempty_rankOneModel (by omega) hrank
  exact ⟨⟨L, inferInstance, inferInstance, inferInstance, inferInstance, model⟩⟩

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Choose the actual anisotropic-middle model for a local rank-one outer
type-A group, with no hypothesis on the distinguished positions. -/
def localOuterTypeARankOneHermitianModel
    (hsc : IsSimplyConnected G) (haas : IsAbsolutelyAlmostSimple G)
    (e : d.Vertex ≃ Fin n)
    (hA : ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b))
    (hnot : ¬ d.StarIsTrivial) (hrank : splitRank G = 1) :
    OuterTypeARankOneHermitianModel K G n :=
  Classical.choice (nonempty_outerTypeARankOneHermitianModel_of_unitarySplitting d
    (Algebra.CentralSimple.unitaryDivisionSplitting K (localUnitaryDivisionCommutative K))
    hsc haas e hA hnot hrank)

/-- A local simply connected absolutely almost-simple outer type-A group of
split rank one has absolute type A₂ or A₃. -/
theorem TitsIndexData.rank_one_outer_A_rank_bounds
    (hsc : IsSimplyConnected G) (haas : IsAbsolutelyAlmostSimple G)
    (e : d.Vertex ≃ Fin n)
    (hA : ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b))
    (hnot : ¬ d.StarIsTrivial) (hrank : splitRank G = 1) :
    n = 2 ∨ n = 3 := by
  obtain ⟨L, _, _, _, _, H, w, hw, hH, iso⟩ :=
    localOuterTypeARankOneHermitianModel d hsc haas e hA hnot hrank
  have hbound := H.card_le_two_of_isAnisotropic hH
  rw [Fintype.card_fin] at hbound
  have hn := (d.starImagePair_of_A e hA hnot).two_le
  omega

end Langlands.GroupScheme
