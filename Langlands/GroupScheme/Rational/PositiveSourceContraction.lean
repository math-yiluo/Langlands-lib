import Langlands.GroupScheme.Rational.ActionLieRigidity
import Langlands.GroupScheme.Rational.ActionCocharacterWeights
import Langlands.GroupScheme.Dynamic.ActionFunctoriality
import Langlands.GroupScheme.AutomorphicAction.BaseChangeCompatibility
import Langlands.GroupScheme.Absolute.SplitTorusDynamicDescent
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Actual contraction from strictly positive intrinsic source weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section Split

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom U.X.hom] [LocallyOfFiniteType U.X.hom]
    (d : AutomorphicAction T.toGrp U) (hT : IsSplitTorus T.toGrp)
    (ν : cocharacterLattice T)
    (hpos : ∀ χ : characterLattice T,
      RelativeRoot.actionWeightSpace d χ ≠ ⊥ → 0 < latticePairing T χ ν)

include hT hpos

/-- Positivity on every nonbottom source weight fills the positive
weight span of the actual cocharacter-restricted action. -/
theorem AutomorphicAction.positiveWeightSpan_eq_top_of_source_weights :
    (d.restrict (CommGroupScheme.groupHom ν)).positiveWeightSpan = ⊤ := by
  rw [AutomorphicAction.positiveWeightSpan,
    ← RelativeRoot.semigroupWeightSpan_positive_eq_restrict d hT ν]
  apply top_unique
  rw [← RelativeRoot.iSup_actionWeightSpace_eq_top d hT]
  refine iSup_le fun χ => ?_
  by_cases hχ : RelativeRoot.actionWeightSpace d χ = ⊥
  · rw [hχ]
    exact bot_le
  · exact le_iSup (fun ψ : RelativeRoot.positiveSemigroup ν =>
      RelativeRoot.actionWeightSpace d ψ.val) ⟨χ, hpos χ hχ⟩

variable [Smooth U.X.hom] [ConnectedSpace U.X.left]

/-- A smooth connected affine source with strictly positive torus weights
is contracted by the given cocharacter on every test scheme. -/
theorem AutomorphicAction.unipotent_eq_top_of_source_weights :
    (d.restrict (CommGroupScheme.groupHom ν)).unipotent = ⊤ :=
  AutomorphicAction.unipotent_eq_top_of_positiveWeightSpan_eq_top _
    (d.positiveWeightSpan_eq_top_of_source_weights hT ν hpos)

variable {G : GroupScheme (Spec (CommRingCat.of k))}
    (t : T.toGrp ⟶ G) (i : U ⟶ G)
    (hi : d.IsEquivariant (AutomorphicAction.conjugation t) i)

include hi in
/-- All points of the image of a source with positive weights lie in the
ambient identity-limit subgroup. The map from the source need not be monic. -/
theorem AutomorphicAction.range_le_unipotent_of_source_weights :
    SubgroupFunctor.range i ≤
      Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ t) := by
  have hiν : (d.restrict (CommGroupScheme.groupHom ν)).IsEquivariant
      (AutomorphicAction.cocharacterAction (CommGroupScheme.groupHom ν ≫ t)) i := by
    intro V s x
    rw [AutomorphicAction.cocharacterAction_act]
    simpa only [AutomorphicAction.restrict_act, AutomorphicAction.conjugation_act,
      Grp.comp_hom_hom, Category.assoc] using
      hi (s ≫ (CommGroupScheme.groupHom ν).hom.hom) x
  have hle := hiν.unipotent_le_comap
  rw [d.unipotent_eq_top_of_source_weights hT ν hpos,
    AutomorphicAction.cocharacterAction_unipotent] at hle
  rintro V _ ⟨x, rfl⟩
  exact hle V (show x ∈ (⊤ : SubgroupFunctor U).carrier V from trivial)

end Split

section Extension

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {U G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom U.X.hom] [Smooth U.X.hom] [ConnectedSpace U.X.left]
    [IsAffine G.X.left]
    (d : AutomorphicAction T.toGrp U) (t : T.toGrp ⟶ G) (i : U ⟶ G)
    (hi : d.IsEquivariant (AutomorphicAction.conjugation t) i)

local notation "b" => algebraBaseMap k K
local notation "T_K" => Functor.obj (CommGroupScheme.baseChange b) T
local notation "t_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) t
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "U_K" => Functor.obj (GroupScheme.baseChange b) U

local instance positiveSourceContractionBaseChangeIsAffineHom :
    IsAffineHom (U_K).X.hom := by
  change IsAffineHom (Limits.pullback.snd U.X.hom b)
  infer_instance

local instance positiveSourceContractionBaseChangeSmooth :
    Smooth (U_K).X.hom := by
  change Smooth (Limits.pullback.snd U.X.hom b)
  infer_instance

local instance positiveSourceContractionBaseChangeConnectedSpace :
    ConnectedSpace (U_K).X.left :=
  U.connectedSpace_baseChange_of_smooth_affine b

include hi in
/-- It suffices to check positivity after any supplied field extension
splitting the acting torus; the image containment holds over the original field. -/
theorem AutomorphicAction.range_le_unipotent_of_source_weights_baseChange
    (hT : IsSplitTorus (T_K).toGrp) (ν : cocharacterLattice T)
    (hpos : ∀ χ : characterLattice T_K,
      RelativeRoot.actionWeightSpace (S := T_K) (d.baseChange b) χ ≠ ⊥ →
        0 < latticePairing T_K χ (cocharacterLattice.baseChange b T ν)) :
    SubgroupFunctor.range i ≤
      Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ t) := by
  have hiK : (d.baseChange b).IsEquivariant (AutomorphicAction.conjugation t_K) i_K := by
    intro V s x
    apply (baseChangePointsEquiv b G V).injective
    rw [baseChangePointsEquiv_comp, AutomorphicAction.baseChangePointsEquiv_act,
      AutomorphicAction.conjugation_act, map_mul, map_mul, map_inv,
      baseChangePointsEquiv_comp, baseChangePointsEquiv_comp]
    simpa only [AutomorphicAction.conjugation_act] using hi _ _
  have hK := (d.baseChange b).range_le_unipotent_of_source_weights hT
    (cocharacterLattice.baseChange b T ν) hpos t_K i_K hiK
  rw [cocharacterLattice.groupHom_baseChange_dynamic,
    ← Dynamic.baseChangeCocharacter_comp, Dynamic.unipotent_baseChange,
    SubgroupFunctor.range_baseChangeHom] at hK
  have hb : Flat b ∧ Surjective b :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap k K))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  let : Flat b := hb.1
  let : Surjective b := hb.2
  let χ := CommGroupScheme.groupHom ν ≫ t
  have hj := Dynamic.Affine.isRepresentedBy_unipotentHom χ
  let : Mono (Dynamic.Affine.unipotentHom χ).hom.hom := hj.1
  rw [← hj.2] at hK ⊢
  exact SubgroupFunctor.le_range_of_baseChange_le b
    (Dynamic.Affine.unipotentHom χ) hK

variable (hT : IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)
    (ν : cocharacterLattice T)
    (hpos : ∀ χ : characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T),
      RelativeRoot.actionWeightSpace
        (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        (d.baseChange (algebraBaseMap k K)) χ ≠ ⊥ →
        0 < latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) χ
          (cocharacterLattice.baseChange (algebraBaseMap k K) T ν))
    {V : GroupScheme (Spec (CommRingCat.of k))} {j : V ⟶ G}
    (hj : (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ t)).IsRepresentedBy j)

include hi in
/-- The actual factor of the source map through any supplied representative
of the ambient identity-limit subgroup. -/
def positiveSourceFactorHom : U ⟶ V :=
  hj.factorHom i
    (d.range_le_unipotent_of_source_weights_baseChange k K t i hi hT ν hpos)

include hi in
/-- The factor has the exact original composite. -/
theorem positiveSourceFactorHom_comp :
    positiveSourceFactorHom k K d t i hi hT ν hpos hj ≫ j = i :=
  hj.factorHom_comp i
    (d.range_le_unipotent_of_source_weights_baseChange k K t i hi hT ν hpos)

end Extension

end Langlands.GroupScheme
