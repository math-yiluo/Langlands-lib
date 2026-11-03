import Langlands.GroupScheme.Torus.WeightBaseChangeComparison
import Langlands.GroupScheme.Torus.WeightRestriction
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType
import Langlands.GroupScheme.Reductive.FieldExtensionStatement
import Langlands.GroupScheme.Torus.MaximalBaseChangeStatement
import Langlands.GroupScheme.Reductive.RootDatumStatement
import Langlands.GroupScheme.Rational.RelativeRootNegationStatement

/-! # Lifting actual relative roots to a splitting field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

section FieldExtensionRestriction

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {T M : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local notation "b" => algebraBaseMap k K
local notation "G_K" => Functor.obj (GroupScheme.baseChange b) G
local notation "M_K" => Functor.obj (CommGroupScheme.baseChange b) M

local instance : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

local instance : LocallyOfFiniteType ((GroupScheme.baseChange b).obj G).X.hom := by
  change LocallyOfFiniteType (pullback.snd G.X.hom b)
  infer_instance

/-- An original root is precisely a nonzero character whose pullback is the
restriction of a root for a containing torus split over the extension field. -/
theorem mem_roots_iff_exists_splittingField_restriction
    (hT : IsSplitTorus T.toGrp)
    (hM : IsSplitTorus ((GroupScheme.baseChange b).obj M.toGrp))
    (f : T ⟶ M) (j : M.toGrp ⟶ G) (α : characterLattice T) :
    α ∈ roots (CommGroupScheme.groupHom f ≫ j) ↔
      α ≠ 0 ∧ ∃ β ∈ roots ((GroupScheme.baseChange b).map j),
        (CommGroupScheme.baseChange b).map f ≫ β =
          characterLattice.baseChange b T α := by
  have hα0 : characterLattice.baseChange b T α ≠ 0 ↔ α ≠ 0 := by
    exact (characterLattice.baseChangeEquiv b T hT).map_ne_zero_iff
  rw [← mem_roots_baseChange_iff (K := K) _ _ hT (CommGroupScheme.groupHom f ≫ j) α,
    Functor.map_comp]
  change characterLattice.baseChange b T α ∈ roots
    (CommGroupScheme.groupHom ((CommGroupScheme.baseChange b).map f) ≫
      (GroupScheme.baseChange b).map j) ↔ _
  rw [mem_roots_comp_iff hM (hT.baseChange b)]
  exact and_congr hα0 Iff.rfl

/-- Choose an actual root of the containing torus over its splitting field
restricting to the pullback of the given original root. -/
def splittingFieldRootLift
    (hT : IsSplitTorus T.toGrp)
    (hM : IsSplitTorus ((GroupScheme.baseChange b).obj M.toGrp))
    (f : T ⟶ M) (j : M.toGrp ⟶ G)
    (α : roots (CommGroupScheme.groupHom f ≫ j)) :
    roots (T := M_K) (G := G_K) ((GroupScheme.baseChange b).map j) := by
  let h := ((mem_roots_iff_exists_splittingField_restriction hT hM f j α.val).mp
    α.property).2
  exact ⟨h.choose, h.choose_spec.1⟩

/-- The chosen lift restricts to the actual pulled-back original character. -/
theorem splittingFieldRootLift_restriction
    (hT : IsSplitTorus T.toGrp)
    (hM : IsSplitTorus ((GroupScheme.baseChange b).obj M.toGrp))
    (f : T ⟶ M) (j : M.toGrp ⟶ G)
    (α : roots (CommGroupScheme.groupHom f ≫ j)) :
    (CommGroupScheme.baseChange b).map f ≫
      (splittingFieldRootLift hT hM f j α : characterLattice M_K) =
        characterLattice.baseChange b T α.val := by
  exact (((mem_roots_iff_exists_splittingField_restriction hT hM f j α.val).mp
    α.property).2.choose_spec).2

/-- Opposite roots of a containing torus over a splitting field imply opposite
roots of the original split-torus action. -/
theorem roots_negation_of_splittingField_restriction
    (hT : IsSplitTorus T.toGrp)
    (hM : IsSplitTorus ((GroupScheme.baseChange b).obj M.toGrp))
    (f : T ⟶ M) (j : M.toGrp ⟶ G)
    (hneg : ∀ β ∈ roots (T := M_K) (G := G_K) ((GroupScheme.baseChange b).map j),
      -β ∈ roots ((GroupScheme.baseChange b).map j)) :
    ∀ α ∈ roots (CommGroupScheme.groupHom f ≫ j),
      -α ∈ roots (CommGroupScheme.groupHom f ≫ j) := by
  intro α hα
  obtain ⟨hα0, β, hβ, hβα⟩ :=
    (mem_roots_iff_exists_splittingField_restriction hT hM f j α).mp hα
  apply (mem_roots_iff_exists_splittingField_restriction hT hM f j (-α)).mpr
  refine ⟨neg_ne_zero.mpr hα0, -β, hneg β hβ, ?_⟩
  rw [Preadditive.comp_neg, hβα, map_neg]

end FieldExtensionRestriction

section RootDatum

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

/-- The actual roots identified with the roots of a root datum have opposites. -/
theorem IsRootDatumOf.neg_mem_roots {J : Type*}
    {i : T.toGrp ⟶ G} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i P) {α : characterLattice T} (hα : α ∈ roots i) :
    -α ∈ roots i := by
  rw [← hP.2.1] at hα ⊢
  exact P.neg_mem_range_root_iff.mpr hα

end RootDatum

/-- Root-datum existence for split maximal tori, reductivity under field
extension, and maximality under field extension together give the exact
unconditional relative-root negation statement. The three structural statements
remain explicit hypotheses of this reduction. -/
theorem relativeRootNegationStatement_of_rootDatum_fieldExtension_maximalTorus
    (hroot : RootDatumExistenceStatement.{u})
    (hext : ConnectedReductiveFieldExtensionStatement.{u})
    (hmax : MaximalTorusBaseChangeStatement.{u}) :
    RelativeRootNegationStatement.{u} := by
  intro k _ G hG T i hi
  have := hG.isAffineHom
  have := hG.smooth
  obtain ⟨M, j, hj, f, hf⟩ :=
    exists_maximalTorus_extension_of_finiteType G i hi.1.1.isTorus hi.1.2
  obtain ⟨K, _, _, hMK⟩ := hj.1
  let b := algebraBaseMap k K
  let G_K := (GroupScheme.baseChange b).obj G
  let M_K := (CommGroupScheme.baseChange b).obj M
  have hGK : IsConnectedReductive G_K := hext k K G hG
  have := hGK.isAffineHom
  have hjK : IsMaximalTorus (T := M_K) ((GroupScheme.baseChange b).map j) :=
    (hmax k K G M j hj.1 hj.2.1).mp hj
  obtain ⟨J, _, P, hP, _⟩ :=
    hroot K G_K hGK M_K hMK ((GroupScheme.baseChange b).map j) hjK
  have hneg : ∀ α ∈ roots (f ≫ j), -α ∈ roots (f ≫ j) :=
    roots_negation_of_splittingField_restriction
      hi.1.1 hMK (Additive.ofMul f) j (fun _ hβ => hP.neg_mem_roots hβ)
  change ∀ α ∈ roots i, -α ∈ roots i
  rwa [hf] at hneg

end Langlands.GroupScheme
