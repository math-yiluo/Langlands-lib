import Langlands.GroupScheme.Reductive.SplitIsogenyTorusMap
import Langlands.GroupScheme.Reductive.SplitRankOnePowerIsogeny
import Langlands.GroupScheme.Reductive.SplitRankOneRootCellProof

/-! # Realization of root-datum isogenies in semisimple rank at most one -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RootDatumIsogenyRealization

variable {k : Type u} [Field k]
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {J J' : Type u} [Finite J] [Finite J']
    [Module.Finite ℤ (characterLattice T)] [Module.Finite ℤ (cocharacterLattice T)]
    [Module.Finite ℤ (characterLattice T')] [Module.Finite ℤ (cocharacterLattice T')]
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    {P' : RootDatum J' (characterLattice T') (cocharacterLattice T')}
    [P.IsReduced] [P'.IsReduced]

/-- The prescribed torus map satisfies the root equation with its root-dependent factor. -/
theorem torusMap_root {p : ℕ} (hT' : IsSplitTorus T'.toGrp)
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p P' P) (r' : J') :
    torusMap hT' f ≫ P'.root r' = f.rootFactor r' • P.root (f.indexEquiv r') := by
  rw [torusMap_comp, f.root_weightMap, Nat.cast_smul_eq_nsmul]

/-- The same actual torus map satisfies the covariant coroot equation. -/
theorem coroot_torusMap {p : ℕ} (hT' : IsSplitTorus T'.toGrp)
    (hP : P.toLinearMap = latticePairing T) (hP' : P'.toLinearMap = latticePairing T')
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p P' P) (r' : J') :
    P.coroot (f.indexEquiv r') ≫ torusMap hT' f = f.rootFactor r' • P'.coroot r' := by
  rw [comp_torusMap hT' hP hP', f.coroot_coweightMap, Nat.cast_smul_eq_nsmul]

variable {G G' : GroupScheme (Spec (CommRingCat.of k))}

/-- Actual rank-one root cells realize a prescribed root-datum isogeny, including
its root-dependent power on both root groups and its full-cell restriction. -/
theorem exists_rankOne_isogeny (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G') (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hP' : haveI := hG'.isAffineHom; IsRootDatumOf i' P')
    (hrank : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (hrank' : haveI := hG'.isAffineHom
      ∀ α ∈ roots i', ∀ β ∈ roots i', ¬ LinearIndependent ℤ ![α, β])
    (f : Langlands.LinearAlgebra.RootDatumIsogeny (ringExpChar k) P' P) (r' : J') :
    ∃ φ : G ⟶ G', IsIsogeny φ ∧
      i ≫ φ = CommGroupScheme.groupHom (torusMap hT' f) ≫ i' ∧
      ∃ (xp xm : RootCell.Ga k ⟶ G) (xp' xm' : RootCell.Ga k ⟶ G'),
        RootCell.IsRootCell i (P.root (f.indexEquiv r')) (P.coroot (f.indexEquiv r')) xp xm ∧
        RootCell.IsRootCell i' (P'.root r') (P'.coroot r') xp' xm' ∧
        xm.hom.hom ≫ φ.hom.hom = RootCell.gaPower (f.rootFactor r') ≫ xm'.hom.hom ∧
        xp.hom.hom ≫ φ.hom.hom = RootCell.gaPower (f.rootFactor r') ≫ xp'.hom.hom ∧
        Dynamic.tripleCellMultiplication xm i xp ≫ φ.hom.hom =
          RootCell.powerCell (torusMap hT' f) (f.rootFactor r') ≫
            Dynamic.tripleCellMultiplication xm' i' xp' := by
  obtain ⟨xp, xm, D⟩ := splitRankOneRootCell k G hG T hT i hi J P hP hrank (f.indexEquiv r')
  obtain ⟨xp', xm', D'⟩ := splitRankOneRootCell k G' hG' T' hT' i' hi' J' P' hP' hrank' r'
  have hD : RootCell.IsRootCell i (P.root (f.indexEquiv r'))
      (P.coroot (f.indexEquiv r')) xp xm :=
    ⟨D.1, D.2.1, D.2.2.1, D.2.2.2.1, D.2.2.2.2⟩
  have hD' : RootCell.IsRootCell i' (P'.root r') (P'.coroot r') xp' xm' :=
    ⟨D'.1, D'.2.1, D'.2.2.1, D'.2.2.2.1, D'.2.2.2.2⟩
  obtain ⟨e, he⟩ := f.rootFactor_pow r'
  have hroot : torusMap hT' f ≫ P'.root r' =
      (ringExpChar k) ^ e • P.root (f.indexEquiv r') := by
    rw [torusMap_root, he]
  have hcoroot : P.coroot (f.indexEquiv r') ≫ torusMap hT' f =
      (ringExpChar k) ^ e • P'.coroot r' := by
    rw [coroot_torusMap hT' hP.1 hP'.1, he]
  obtain ⟨φ, hφ, hsq, hm, hp, hcell⟩ := RootCell.exists_powerIsogeny hG hG' hD hD'
    (torusMap hT' f) (torusMap_isIsogeny hT hT' hP.1 hP'.1 f)
    (ringExpChar k) e hroot hcoroot
  exact ⟨φ, hφ, hsq, xp, xm, xp', xm', hD, hD',
    by simpa only [he] using hm, by simpa only [he] using hp,
    by simpa only [he] using hcell⟩

/-- Realization in semisimple rank at most one, also including the rootless case. -/
theorem exists_realization_rank_le_one (hG : IsConnectedReductive G)
    (hG' : IsConnectedReductive G') (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G') (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hP' : haveI := hG'.isAffineHom; IsRootDatumOf i' P')
    (hrank : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (hrank' : haveI := hG'.isAffineHom
      ∀ α ∈ roots i', ∀ β ∈ roots i', ¬ LinearIndependent ℤ ![α, β])
    (f : Langlands.LinearAlgebra.RootDatumIsogeny (ringExpChar k) P' P) :
    ∃ φ : G ⟶ G', IsIsogeny φ ∧
      IsIsogeny (CommGroupScheme.groupHom (torusMap hT' f)) ∧
      i ≫ φ = CommGroupScheme.groupHom (torusMap hT' f) ≫ i' ∧
      (∀ χ : characterLattice T', f.weightMap χ = torusMap hT' f ≫ χ) ∧
      (∀ ν : cocharacterLattice T, f.coweightMap ν = ν ≫ torusMap hT' f) := by
  rcases isEmpty_or_nonempty J' with hJ | ⟨⟨r'⟩⟩
  · obtain ⟨φ, hφ, ht, hsq, hw, hv⟩ := exists_central_realization hG hG' hT hT'
      i i' hi hi' hP hP' f (fun r => isEmptyElim r)
    exact ⟨φ, hφ.isIsogeny, ht, hsq, hw, hv⟩
  · obtain ⟨φ, hφ, hsq, -⟩ := exists_rankOne_isogeny hG hG' hT hT'
      i i' hi hi' hP hP' hrank hrank' f r'
    exact ⟨φ, hφ, torusMap_isIsogeny hT hT' hP.1 hP'.1 f, hsq,
      fun χ => (torusMap_comp hT' f χ).symm,
      fun ν => (comp_torusMap hT' hP.1 hP'.1 f ν).symm⟩

/-- The actual group homomorphism realizing the given root-datum isogeny in rank at most one. -/
def rankOneHom (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G') (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hP' : haveI := hG'.isAffineHom; IsRootDatumOf i' P')
    (hrank : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (hrank' : haveI := hG'.isAffineHom
      ∀ α ∈ roots i', ∀ β ∈ roots i', ¬ LinearIndependent ℤ ![α, β])
    (f : Langlands.LinearAlgebra.RootDatumIsogeny (ringExpChar k) P' P) : G ⟶ G' :=
  Classical.choose (exists_realization_rank_le_one hG hG' hT hT' i i' hi hi' hP hP'
    hrank hrank' f)

/-- The chosen rank-one map is an isogeny with both prescribed lattice maps. -/
theorem rankOneHom_spec (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G') (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hP' : haveI := hG'.isAffineHom; IsRootDatumOf i' P')
    (hrank : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (hrank' : haveI := hG'.isAffineHom
      ∀ α ∈ roots i', ∀ β ∈ roots i', ¬ LinearIndependent ℤ ![α, β])
    (f : Langlands.LinearAlgebra.RootDatumIsogeny (ringExpChar k) P' P) :
    IsIsogeny (rankOneHom hG hG' hT hT' i i' hi hi' hP hP' hrank hrank' f) ∧
      IsIsogeny (CommGroupScheme.groupHom (torusMap hT' f)) ∧
      i ≫ rankOneHom hG hG' hT hT' i i' hi hi' hP hP' hrank hrank' f =
        CommGroupScheme.groupHom (torusMap hT' f) ≫ i' ∧
      (∀ χ : characterLattice T', f.weightMap χ = torusMap hT' f ≫ χ) ∧
      (∀ ν : cocharacterLattice T, f.coweightMap ν = ν ≫ torusMap hT' f) :=
  Classical.choose_spec (exists_realization_rank_le_one hG hG' hT hT' i i' hi hi' hP hP'
    hrank hrank' f)

end Langlands.GroupScheme.RootDatumIsogenyRealization
