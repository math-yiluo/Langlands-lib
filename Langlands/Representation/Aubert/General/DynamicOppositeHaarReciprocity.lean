import Langlands.Representation.Aubert.General.DynamicUnipotentHaarDeterminantProof
import Langlands.Representation.Aubert.General.RationalOppositeParabolic
import Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityStatement
import Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityReduction
import Langlands.GroupScheme.Dynamic.AdjointDeterminantStructureProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.GroupScheme.Rational.CocharacterMaximalSplitTorusProof
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups

/-! # Opposite Haar reciprocity on the Levi of an arbitrary cocharacter

For a cocharacter `χ` of a connected reductive group `G` over a nonarchimedean local field,
the Haar scaling characters of `N(χ⁻¹)(k)` and `N(χ)(k)` under conjugation by `M(χ)(k)` are
inverse. This is the reciprocity input `δ_{N̄} δ_N = 1` of Renard 2026, VI.9.6 (proof of
(VI.9.6.2)), for the parabolic of an arbitrary cocharacter.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance dynamicOppositeHaarReciprocityPointTopology :
    TopologicalSpace (rationalPoints G) :=
  pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- The vanishing of the sum of opposite adjoint determinants on a dynamic Levi implies
reciprocity of the Haar scaling characters of `N(χ⁻¹)(k)` and `N(χ)(k)` on `M(χ)(k)`, for an
arbitrary cocharacter `χ`. The subgroups are abstract subgroups equal to the dynamic ones. -/
theorem dynamicOppositeHaarReciprocity_of_leviAdjoint
    (h2 : Dynamic.LeviAdjointDeterminantReciprocityStatement.{u})
    (hG : IsConnectedReductive G) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (U M O : Subgroup (rationalPoints G))
    (hUχ : U = (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _)))
    (hMχ : M = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
    (hOχ : O = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
    (hU : IsClosed (U : Set (rationalPoints G))) (hO : IsClosed (O : Set (rationalPoints G)))
    (hMU : M ≤ Subgroup.normalizer (U : Set (rationalPoints G)))
    (hMO : M ≤ Subgroup.normalizer (O : Set (rationalPoints G))) (x : M) :
    HaarModulus.closedRestrictCharacter U hU M hMU x *
      HaarModulus.closedRestrictCharacter O hO M hMO x = 1 := by
  subst hUχ hMχ hOχ
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  obtain ⟨T, i, ζ, hi, hζ⟩ := cocharacterMaximalSplitTorus k G χ
  obtain ⟨χ', hχ'⟩ : ∃ χ', CommGroupScheme.groupHom (-ζ) ≫ i = χ' := ⟨_, rfl⟩
  have hinv : Dynamic.inverseCocharacter χ = χ' := by
    rw [← hζ, ← hχ']
    exact (groupHom_neg_comp_eq_oppositeCocharacter i ζ).symm
  revert hU hMU
  rw [hinv]
  intro hU hMU
  -- The common Levi model and the two unipotent models.
  let Z := Dynamic.Affine.centralizerScheme χ
  let iZ := Dynamic.Affine.centralizerHom χ
  have hZ : (Dynamic.centralizer χ).IsRepresentedBy iZ :=
    Dynamic.Affine.isRepresentedBy_centralizerHom χ
  have hZ' : (Dynamic.centralizer χ').IsRepresentedBy iZ := by
    rw [← hinv, Dynamic.centralizer_inverseCocharacter]
    exact hZ
  let Un := Dynamic.Affine.unipotentScheme χ
  let iU := Dynamic.Affine.unipotentHom χ
  have hUr : (Dynamic.unipotent χ).IsRepresentedBy iU :=
    Dynamic.Affine.isRepresentedBy_unipotentHom χ
  let V := Dynamic.Affine.unipotentScheme χ'
  let iV := Dynamic.Affine.unipotentHom χ'
  have hVr : (Dynamic.unipotent χ').IsRepresentedBy iV :=
    Dynamic.Affine.isRepresentedBy_unipotentHom χ'
  obtain ⟨-, hZa, hUa, -, -, -, -, -, -, -, -, -, -, d, ⟨c⟩⟩ :=
    dynamicAdjointDeterminantStructure k G hG χ _ Z Un
      (Dynamic.Affine.parabolicHom χ) iZ iU
      (Dynamic.Affine.isRepresentedBy_parabolicHom χ) hZ hUr
  obtain ⟨-, -, hVa, -, -, -, -, -, -, -, -, -, -, e, ⟨c'⟩⟩ :=
    dynamicAdjointDeterminantStructure k G hG χ' _ Z V
      (Dynamic.Affine.parabolicHom χ') iZ iV
      (Dynamic.Affine.isRepresentedBy_parabolicHom χ') hZ' hVr
  have : IsAffine Z.X.left := isAffine_of_isAffineHom Z.X.hom
  -- Lift `x` to a rational point of the Levi model.
  have hxZ : (x : rationalPoints G) ∈ (SubgroupFunctor.range iZ).carrier (Over.mk (𝟙 _)) := by
    rw [hZ.2]
    exact x.2
  obtain ⟨xZ, hxZ⟩ := SubgroupFunctor.mem_range.mp hxZ
  have hm : xZ ≫ iZ.hom.hom ∈ Subgroup.normalizer
      ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) : Set (rationalPoints G)) := by
    rw [hxZ]
    exact hMO x.2
  have hm' : xZ ≫ iZ.hom.hom ∈ Subgroup.normalizer
      ((Dynamic.unipotent χ').carrier (Over.mk (𝟙 _)) : Set (rationalPoints G)) := by
    rw [hxZ]
    exact hMU x.2
  have k1 := dynamicUnipotentHaarDeterminant k G hG χ hZ hUr c hO xZ hm
  have k2 := dynamicUnipotentHaarDeterminant k G hG χ' hZ' hVr c' hU xZ hm'
  have k3 := h2 k G hG T i hi ζ (Z := Z) (U := Un) (V := V) (iZ := iZ) (iU := iU) (iV := iV)
  rw [hζ, hχ'] at k3
  replace k3 := k3 hZ hZ' hUr hVr c c'
  apply Units.ext
  change (HaarModulus.closedNormalizerCharacter _ hU ⟨x, hMU x.2⟩ *
    HaarModulus.closedNormalizerCharacter _ hO ⟨x, hMO x.2⟩ : ℝ≥0ˣ).val = 1
  have hmm : (⟨x, hMO x.2⟩ : Subgroup.normalizer
      ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) : Set (rationalPoints G))) =
      ⟨xZ ≫ iZ.hom.hom, hm⟩ := Subtype.ext hxZ.symm
  have hmm' : (⟨x, hMU x.2⟩ : Subgroup.normalizer
      ((Dynamic.unipotent χ').carrier (Over.mk (𝟙 _)) : Set (rationalPoints G))) =
      ⟨xZ ≫ iZ.hom.hom, hm'⟩ := Subtype.ext hxZ.symm
  rw [Units.val_mul, hmm, hmm', k1, k2, ← map_mul, ← rationalCharacterEval_add, add_comm, k3,
    rationalCharacterEval_zero, map_one]

/-- Opposite Haar reciprocity on the Levi of an arbitrary cocharacter, from relative root
reflections and central split torus detection, using the proved reductivity of dynamic
centralizers. -/
theorem dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u})
    (hG : IsConnectedReductive G) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (U M O : Subgroup (rationalPoints G))
    (hUχ : U = (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _)))
    (hMχ : M = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
    (hOχ : O = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
    (hU : IsClosed (U : Set (rationalPoints G))) (hO : IsClosed (O : Set (rationalPoints G)))
    (hMU : M ≤ Subgroup.normalizer (U : Set (rationalPoints G)))
    (hMO : M ≤ Subgroup.normalizer (O : Set (rationalPoints G))) (x : M) :
    HaarModulus.closedRestrictCharacter U hU M hMU x *
      HaarModulus.closedRestrictCharacter O hO M hMO x = 1 :=
  dynamicOppositeHaarReciprocity_of_leviAdjoint
    (leviAdjointDeterminantReciprocity_of_structure hRefl hCST dynamicCentralizerReductive)
    hG χ U M O hUχ hMχ hOχ hU hO hMU hMO x

end Langlands.Aubert.General.RationalPointFamily
