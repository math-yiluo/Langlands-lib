import Langlands.GroupScheme.MatrixRepresentation.UnipotentPointMatrices
import Langlands.GroupScheme.Rational.ValuedRepresentationBaseChange
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent

/-! # Finite normal unipotent matrix subgroups of reductive groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- A closed normal subgroup of a connected reductive group is finite if it
acts unipotently in a closed faithful representation, over any field. -/
theorem IsConnectedReductive.isFinite_of_normal_of_unipotentPointMatrices
    (hG : IsConnectedReductive G)
    (ρ : MatrixRepresentation G n) (hc : IsClosedSubgroup ρ)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal)
    (hU : (ρ.restrict i).HasUnipotentPointMatrices) : IsFinite H.X.hom := by
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth (F.obj G).X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  have : IsAffineHom (F.obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  have hc' : IsClosedSubgroup (ρ.baseChange b) := by
    have : IsClosedImmersion (F.map ρ).hom.hom.left := hc.baseChange b
    have : IsIso (GeneralLinear.baseChangeIso n b).hom.hom.hom.left :=
      ((Grp.forget _) ⋙ Over.forget _).map_isIso (GeneralLinear.baseChangeIso n b).hom
    change IsClosedImmersion
      ((F.map ρ).hom.hom.left ≫ (GeneralLinear.baseChangeIso n b).hom.hom.hom.left)
    infer_instance
  have hn' : (SubgroupFunctor.range (F.map i)).IsNormal := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hn.baseChange b
  have hU' : ((ρ.baseChange b).restrict (F.map i)).HasUnipotentPointMatrices := by
    intro T x
    rw [MatrixRepresentation.pointMatrix_restrict,
      MatrixRepresentation.pointMatrix_baseChange, baseChangePointsEquiv_comp]
    exact hU ((Over.map b).obj T) (baseChangePointsEquiv b H T x)
  have hfin : IsFinite (F.obj H).X.hom :=
    _root_.Langlands.GroupScheme.isFinite_of_normal_of_unipotentPointMatrices
      hG.hasTrivialGeometricUnipotentRadical (ρ.baseChange b) hc'
      (F.map i) (hi.baseChange b) hn' hU'
  obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
  change IsFinite (pullback.snd H.X.hom b) at hfin
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @IsFinite) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨hs, hf⟩, hq⟩ hfin

end Langlands.GroupScheme
