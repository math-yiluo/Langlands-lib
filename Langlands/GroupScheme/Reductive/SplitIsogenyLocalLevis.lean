import Langlands.GroupScheme.Reductive.SplitRankOneIsogeny
import Langlands.GroupScheme.Reductive.SplitIsomorphismCentralizerRootData
import Langlands.GroupScheme.Reductive.SplitLeviGluingLocal

/-! # Prescribed isogenies on corresponding rank-one Levi subgroups -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.LinearAlgebra

variable {ι X Y ι' X' Y' : Type*}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y']
    [Finite ι] [Finite ι']
    [Module.Finite ℤ X] [Module.Finite ℤ Y]
    [Module.Finite ℤ X'] [Module.Finite ℤ Y']
    {P : RootDatum ι X Y} {P' : RootDatum ι' X' Y'}
    [P.IsReduced] [P'.IsReduced]

/-- Restricting the root indices preserves reducedness. -/
instance orthogonalRootPairing_isReduced (ν : Y) :
    (orthogonalRootPairing P ν).IsReduced where
  eq_or_eq_neg a b h := RootPairing.IsReduced.eq_or_eq_neg (P := P) a.1 b.1 h

namespace RootDatumIsogeny

variable {p : ℕ} (f : RootDatumIsogeny p P' P)

/-- Corresponding roots vanish on corresponding cocharacters simultaneously. -/
theorem mem_orthogonalIndices_iff (ν : Y) (a : ι') :
    a ∈ orthogonalIndices P' (f.coweightMap ν) ↔
      f.indexEquiv a ∈ orthogonalIndices P ν := by
  change P'.toLinearMap (P'.root a) (f.coweightMap ν) = 0 ↔
    P.toLinearMap (P.root (f.indexEquiv a)) ν = 0
  rw [← f.pairing_apply, f.root_weightMap, map_smul, LinearMap.smul_apply,
    smul_eq_mul]
  exact mul_eq_zero.trans (or_iff_right (by exact_mod_cast (f.rootFactor_pos a).ne'))

/-- The isogeny restricted to the roots annihilated by a cocharacter. The actual
lattice maps and all the retained root factors are unchanged. -/
def orthogonal (ν : Y) :
    RootDatumIsogeny p (orthogonalRootPairing P' (f.coweightMap ν))
      (orthogonalRootPairing P ν) where
  characteristicExponent := f.characteristicExponent
  weightMap := f.weightMap
  coweightMap := f.coweightMap
  indexEquiv := f.indexEquiv.subtypeEquiv (f.mem_orthogonalIndices_iff ν)
  weightMap_injective := f.weightMap_injective
  coweightMap_injective := f.coweightMap_injective
  weight_coweight_transpose := f.weight_coweight_transpose
  rootFactor a := f.rootFactor a.1
  rootFactor_pow a := f.rootFactor_pow a.1
  root_weightMap a := f.root_weightMap a.1
  coroot_coweightMap a := f.coroot_coweightMap a.1

/-- Dependence of corresponding roots is reflected by an isogeny. -/
theorem not_linearIndependent_of_images (a b : ι')
    (h : ¬ LinearIndependent ℤ ![P.root (f.indexEquiv a), P.root (f.indexEquiv b)]) :
    ¬ LinearIndependent ℤ ![P'.root a, P'.root b] := by
  intro hlin
  rw [LinearIndependent.pair_iff] at hlin
  have hqb : (f.rootFactor b : ℤ) ≠ 0 := by exact_mod_cast (f.rootFactor_pos b).ne'
  rcases RootPairing.IsReduced.eq_or_eq_neg (P := P)
      (f.indexEquiv a) (f.indexEquiv b) h with he | he
  · have hrel : (f.rootFactor b : ℤ) • P'.root a +
        (-(f.rootFactor a : ℤ)) • P'.root b = 0 := by
      apply f.weightMap_injective
      simp only [map_add, map_smul, map_neg, map_zero, f.root_weightMap, he, neg_smul]
      rw [smul_smul, smul_smul, mul_comm (f.rootFactor b : ℤ), add_neg_cancel]
    exact hqb (hlin _ _ hrel).1
  · have hrel : (f.rootFactor b : ℤ) • P'.root a +
        (f.rootFactor a : ℤ) • P'.root b = 0 := by
      apply f.weightMap_injective
      simp only [map_add, map_smul, map_zero, f.root_weightMap, he, smul_neg]
      rw [smul_smul, smul_smul, mul_comm (f.rootFactor b : ℤ), neg_add_cancel]
    exact hqb (hlin _ _ hrel).1

end RootDatumIsogeny
end Langlands.LinearAlgebra

namespace Langlands.GroupScheme.RootDatumIsogenyRealization

open Langlands.LinearAlgebra

variable {k : Type u} [Field k]
    {G G' Z Z' : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {J J' : Type u} [Finite J] [Finite J']
    [Module.Finite ℤ (characterLattice T)] [Module.Finite ℤ (cocharacterLattice T)]
    [Module.Finite ℤ (characterLattice T')] [Module.Finite ℤ (cocharacterLattice T')]
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    {P' : RootDatum J' (characterLattice T') (cocharacterLattice T')}
    [P.IsReduced] [P'.IsReduced]

/-- Any corresponding cocharacter centralizers of semisimple rank at most one
admit an actual isogeny over the originally prescribed torus morphism. -/
theorem exists_centralizer_isogeny
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G')
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hP' : haveI := hG'.isAffineHom; IsRootDatumOf i' P')
    (f : RootDatumIsogeny (ringExpChar k) P' P)
    (ν : cocharacterLattice T)
    (hrank : haveI := hG.isAffineHom; LeviGluing.IsRankOneDirection i ν)
    (z : Z ⟶ G) (z' : Z' ⟶ G')
    (hz : IsClosedSubgroup z) (hz' : IsClosedSubgroup z')
    (hrep : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy z)
    (hrep' : (Dynamic.centralizer
      (CommGroupScheme.groupHom (f.coweightMap ν) ≫ i')).IsRepresentedBy z')
    (j : T.toGrp ⟶ Z) (j' : T'.toGrp ⟶ Z')
    (hj : j ≫ z = i) (hj' : j' ≫ z' = i') :
    ∃ φ : Z ⟶ Z', IsIsogeny φ ∧
      j ≫ φ = CommGroupScheme.groupHom (torusMap hT' f) ≫ j' := by
  have hZ := dynamicCentralizerReductive k G hG _ Z z hz hrep
  have hZ' := dynamicCentralizerReductive k G' hG' _ Z' z' hz' hrep'
  let := hG.isAffineHom
  let := hG'.isAffineHom
  let := hZ.isAffineHom
  let := hZ'.isAffineHom
  have hjmax : IsMaximalTorus j := IsMaximalTorus.of_comp hz (by rwa [hj])
  have hjmax' : IsMaximalTorus j' := IsMaximalTorus.of_comp hz' (by rwa [hj'])
  have hroots := dynamicCentralizerRoots k G hG T hT i hi ν Z z hz hrep hZ j hj
  have hroots' := dynamicCentralizerRoots k G' hG' T' hT' i' hi'
    (f.coweightMap ν) Z' z' hz' hrep' hZ' j' hj'
  have hQ := hP.orthogonalRootPairing ν z hrep j hj hroots
  have hQ' := hP'.orthogonalRootPairing (f.coweightMap ν) z' hrep' j' hj' hroots'
  have hdep : ∀ α ∈ roots j, ∀ β ∈ roots j, ¬ LinearIndependent ℤ ![α, β] := by
    intro α hα β hβ
    rw [hroots] at hα hβ
    exact hrank α hα.1 β hβ.1 hα.2 hβ.2
  have hdep' : ∀ α ∈ roots j', ∀ β ∈ roots j', ¬ LinearIndependent ℤ ![α, β] := by
    intro α hα β hβ
    rw [← hQ'.2.1] at hα hβ
    obtain ⟨a, rfl⟩ := hα
    obtain ⟨b, rfl⟩ := hβ
    apply (f.orthogonal ν).not_linearIndependent_of_images a b
    exact hdep _ (hQ.2.1 ▸ Set.mem_range_self _) _ (hQ.2.1 ▸ Set.mem_range_self _)
  obtain ⟨φ, hφ, _, hsq, _, _⟩ := exists_realization_rank_le_one hZ hZ' hT hT'
    j j' hjmax hjmax' hQ hQ' hdep hdep' (f.orthogonal ν)
  exact ⟨φ, hφ, hsq⟩

end Langlands.GroupScheme.RootDatumIsogenyRealization
