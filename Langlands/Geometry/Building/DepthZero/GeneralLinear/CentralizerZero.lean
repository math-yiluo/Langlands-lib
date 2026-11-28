import Langlands.Geometry.Building.KPCharacterValuationDescentProof
import Langlands.Geometry.Building.KPInducedTorusIwahoriProof
import Langlands.Geometry.Building.KPMinimalLeviZeroNormKernelReduction
import Langlands.GroupScheme.Torus.MaximalAmbient

/-!
# `Z(F)^0 = Z(F)^1` when the minimal Levi subgroup is a split torus

Let `E : ZeroSubgroupDatum i j` be data for `G(F)^0` (KP Definition 2.6.23) with minimal Levi
subgroup `j : Z → G`. If `Z` is a split torus, then every point of the norm-one subgroup
`Z(F)^1` lies in `Z(F)^0 = Z(K)^0 ∩ Z(F)`, `K` the maximal unramified extension of `F`.

The proof: a point of `Z(F)^1` lies in `Z(K)^1` (`characterValuationKernelDescent_proof`). The
maximal torus `T → Z_K` of the supplied `K`-datum is an isomorphism because `Z_K` is a torus
(`IsMaximalTorus.isIso_of_torus`), so `T` is split, hence induced
(`isInducedTorus_of_isSplitTorus`), and then `T(K)^0 = T(K)^1` (`inducedTorusIwahori`,
KP Lemma 2.5.18). The image of `T(K)^0` lies in `Z(K)^0` by definition.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.GeneralLinearParahoric

/-- A split torus over a field `k` is induced: the trivial extension `k / k` splits it and its
trivial Galois group fixes every basis of the character lattice. -/
theorem isInducedTorus_of_isSplitTorus {k : Type u} [Field k]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp) :
    IsInducedTorus T := by
  have hsplit : IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap k k)).obj T).toGrp :=
    hT.baseChange _
  obtain ⟨J, hJ, ⟨e⟩⟩ := hsplit
  let f := (characterLattice.congr (CommGroupScheme.isoOfGroupIso e)).trans
    (splitTorus.characterLatticeEquiv k J)
  refine ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, hT.baseChange _, J,
    (Pi.basisFun ℤ J).map f.symm.toIntLinearEquiv, fun σ i => ⟨i, ?_⟩⟩
  have hσ : σ = 1 := AlgEquiv.ext fun x => σ.commutes x
  rw [hσ, map_one]
  rfl

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {j : Z ⟶ G}

/-- For data of KP Definition 2.6.23(1) for a split `K`-torus `Z_K`, every point of `Z_K(K)^1`
is the image of a point of the Iwahori subgroup `T(K)^0` of the supplied maximal torus. -/
theorem exists_torusIwahori_map_eq
    (C : UnramifiedZeroDatum F (GaloisPointComparison.baseChanged F (UnramifiedClosure F) Z))
    (hZ : IsSplitTorus Z) {w : rationalPoints
      (GaloisPointComparison.baseChanged F (UnramifiedClosure F) Z)}
    (hw : w ∈ characterValuationKernel (LocalGalois.Separable.fixedFieldValuation F)
        (GaloisPointComparison.baseChanged F (UnramifiedClosure F) Z)) :
    ∃ t ∈ C.torusIwahori, rationalPoints.map C.i t = w := by
  have hZK : IsSplitTorus (GaloisPointComparison.baseChanged F (UnramifiedClosure F) Z) :=
    hZ.baseChange _
  have hiso : IsIso C.i := C.isMaximallySplitMaximalTorus.1.isIso_of_torus hZK.isTorus
  have hTsplit : IsSplitTorus C.T.toGrp := IsSplitTorus.of_iso (asIso C.i) hZK
  have hind : IsInducedTorus C.T := isInducedTorus_of_isSplitTorus C.T hTsplit
  have hIw : C.torusIwahori =
      characterValuationKernel (LocalGalois.Separable.fixedFieldValuation F) C.T.toGrp :=
    inducedTorusIwahori F C.T C.L C.isSplitTorus hind
  refine ⟨rationalPoints.map (inv C.i) w, ?_, ?_⟩
  · rw [hIw]
    exact map_characterValuationKernel_le _ (inv C.i) ⟨w, hw, rfl⟩
  · rw [rationalPoints.map_apply, rationalPoints.map_apply, Category.assoc,
      ← Grp.comp_hom_hom, IsIso.inv_hom_id]
    exact Category.comp_id w

/-- If the minimal Levi subgroup `Z` is a split torus, then `Z(F)^1 ≤ Z(F)^0`. -/
theorem rationalCommonNormKernel_le_centralizerZero (E : ZeroSubgroupDatum i j)
    (hZ : IsSplitTorus Z) :
    Plancherel.rationalCommonNormKernel Z ≤ E.centralizerZero := by
  intro z hz
  have : IsAffine Z.X.left := E.isAffine_centralizer
  have hzK : GaloisPointComparison.rationalExtend F (UnramifiedClosure F) Z z ∈
      characterValuationKernel (LocalGalois.Separable.fixedFieldValuation F)
        (GaloisPointComparison.baseChanged F (UnramifiedClosure F) Z) := by
    have h := characterValuationKernelDescent_proof F Z
    rw [← h] at hz
    exact hz
  obtain ⟨t, ht, hwt⟩ := exists_torusIwahori_map_eq E.centralizerDatum hZ hzK
  exact (mem_anisotropicZeroPoints).2
    (hwt ▸ E.centralizerDatum.map_torusIwahori_le_zeroPoints ⟨t, ht, rfl⟩)

/-- If the minimal Levi subgroup is a split torus, then the image of `Z(F)^1` lies in
`G(F)^0`. -/
theorem map_rationalCommonNormKernel_le_zeroSubgroup (E : ZeroSubgroupDatum i j)
    (hZ : IsSplitTorus Z) :
    (Plancherel.rationalCommonNormKernel Z).map (rationalPoints.map j) ≤ E.zeroSubgroup :=
  (Subgroup.map_mono (rationalCommonNormKernel_le_centralizerZero E hZ)).trans
    E.map_centralizerZero_le_zeroSubgroup

end Langlands.Geometry.Building.GeneralLinearParahoric
