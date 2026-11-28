import Langlands.Geometry.Building.DepthZero.GeneralLinear.RootGroups
import Langlands.Geometry.Building.DepthZero.GeneralLinear.CentralizerZero
import Langlands.Geometry.Building.DepthZero.Definitions
import Langlands.Geometry.Building.FullValidity.DatumTransportProof
import Langlands.Geometry.Building.ApartmentRootCover
import Langlands.Geometry.Building.SplitTorusValuation
import Langlands.Geometry.Building.ZeroSubgroupDatumIndependence
import Langlands.Geometry.Building.ZeroSubgroupCommutatorNormality
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Reductive.GeneralLinearIsConnectedReductiveProof

/-!
# `G(F)^0 = G(F)^1` for KP building data of `GL_N`

For building data `D` of `GL_N` over a nonarchimedean local field `F` satisfying the one-group
axioms, the zero subgroup `G(F)^0` of `D` (KP Definition 2.6.23) contains the norm-one subgroup
`G(F)^1 = {g | det g ∈ 𝒪_F^×}`; with `ZeroSubgroupDatum.zeroSubgroup_le_rationalCommonNormKernel`
the two are equal.

The proof transports `D` along an inner automorphism to data whose maximal split torus is the
diagonal torus (`KPBuildingDatum.basedTransport`, `maximalSplitTorusConjugacy`); the zero
subgroup does not change (`ZeroSubgroupDatum.zeroSubgroup_eq_of_datum`). For the transported
data:

* the minimal Levi subgroup represents the centralizer of the diagonal torus, which the diagonal
  torus itself represents (`maximalTorusCentralizer`), so it is a split torus and the invertible
  diagonal matrices with unit entries lie in `G(F)^0` (`rationalCommonNormKernel_le_centralizerZero`);
* a valuation of the root datum takes a finite value on some nontrivial point of the root group
  of `e_k - e_l`, that point is a transvection (`exists_eq_transvectionGL_of_mem_rootGroupPoints`)
  and lies in `G(F)^♮ ⊆ G(F)^0` (`ParahoricBuildingData.rootGroup_le_simplyConnectedImage`);
* `G(F)^0` is normal, so it contains `SL_N(F)` (`specialLinear_le_of_normal`), and every matrix of
  unit determinant is a matrix of determinant one times `diag(det, 1, …, 1)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.GeneralLinearParahoric

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {N : ℕ}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A rational point of the diagonal torus maps to the diagonal matrix of its coordinates. -/
theorem toMatrixGL_map_diagTorus (t : rationalPoints (diagonalSplitTorus F N).toGrp) :
    toMatrixGL (rationalPoints.map (diagTorus F N) t) =
      diagGL fun a => splitTorus.affinePointsEquiv (ULift.{u} (Fin N))
        (𝟙 (Spec (CommRingCat.of F))) t ⟨a⟩ := by
  ext p q : 2
  rw [toMatrixGL_apply, rationalPoints.map_apply, GeneralLinear.pointsEquiv_diagonalTorus_val,
    coe_diagGL, diagonal_apply, diagonal_apply]
  split_ifs
  · rfl
  · simp

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The value of the determinant character on a rational point is the determinant of its
matrix. -/
theorem rationalCharacterEval_determinantCharacter
    (g : rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))) :
    (rationalCharacterEval (GeneralLinear.determinantCharacter (Fin N) (CommRingCat.of F)) g :
        F) = ((toMatrixGL g : GL (Fin N) F) : Matrix (Fin N) (Fin N) F).det := by
  rw [rationalCharacterEval_val, GeneralLinear.characterEval_determinantCharacter,
    Matrix.GeneralLinearGroup.val_det_apply]
  exact RingHom.map_det _ _

/-- A point of `G(F)^1` has a determinant of valuation one. -/
theorem valuation_det_eq_one
    {g : rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))}
    (hg : g ∈ Plancherel.rationalCommonNormKernel
      (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))) :
    ValuativeRel.valuation F (((toMatrixGL g : GL (Fin N) F) : Matrix (Fin N) (Fin N) F).det) =
      1 := by
  rw [← characterValuationKernel_eq_rationalCommonNormKernel, mem_characterValuationKernel] at hg
  rw [← rationalCharacterEval_determinantCharacter]
  exact hg _

section Diagonal

variable (P : ParahoricBuildingData (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)))
  (σ : P.S ≅ diagonalSplitTorus F N)
  (f : GeneralLinear.groupScheme (Fin N) (CommRingCat.of F) ≅
    GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))
  (h : P.i ≫ f.hom = CommGroupScheme.groupHom σ.hom ≫ diagTorus F N)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The diagonal torus represents its own centralizer. -/
theorem isRepresentedBy_torusCentralizer_diagTorus :
    (torusCentralizer (diagTorus F N)).IsRepresentedBy (diagTorus F N) :=
  ⟨inferInstance, (maximalTorusCentralizer F _
    (isConnectedReductive_generalLinear (k := F) (n := Fin N)) _ _
    (GeneralLinear.isMaximalTorus_diagonalTorus F)).symm⟩

/-- For data whose maximal split torus is the diagonal torus, the minimal Levi subgroup is a
split torus. -/
theorem isSplitTorus_centralizer :
    IsSplitTorus (P.basedTransport σ f h).centralizer.Z :=
  IsSplitTorus.of_iso
    (SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
      isRepresentedBy_torusCentralizer_diagTorus
      (P.basedTransport σ f h).centralizer.isRepresentedBy).symm
    (isSplitTorus_splitTorus _)

/-- For data whose maximal split torus is the diagonal torus, every invertible diagonal matrix
with entries of valuation one lies in `G(F)^0`. -/
theorem diagGL_mem_zeroSubgroup (d : Fin N → Fˣ)
    (hd : ∀ a, ValuativeRel.valuation F (d a : F) = 1) :
    toMatrixGL.symm (diagGL d) ∈ (P.basedTransport σ f h).zeroSubgroup := by
  let P' := P.basedTransport σ f h
  let e := SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    isRepresentedBy_torusCentralizer_diagTorus P'.centralizer.isRepresentedBy
  have he : e.hom ≫ P'.centralizer.j = diagTorus F N :=
    SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _
  let t := (splitTorus.affinePointsEquiv (ULift.{u} (Fin N))
    (𝟙 (Spec (CommRingCat.of F)))).symm fun a => d a.down
  have ht : t ∈ characterValuationKernel (ValuativeRel.valuation F)
      (diagonalSplitTorus F N).toGrp := by
    rw [characterValuationKernel_eq_rationalCommonNormKernel,
      ← SplitTorusValuation.integralUnitKernel_eq_rationalCommonNormKernel,
      SplitTorusValuation.mem_integralUnitKernel]
    intro a
    simp only [t, MulEquiv.apply_symm_apply]
    exact (Valuation.mem_unitGroup_iff _ _ _).2 (hd a.down)
  have hz : rationalPoints.map e.hom t ∈ Plancherel.rationalCommonNormKernel P'.centralizer.Z := by
    rw [← characterValuationKernel_eq_rationalCommonNormKernel]
    exact map_characterValuationKernel_le _ e.hom ⟨t, ht, rfl⟩
  have hmem := map_rationalCommonNormKernel_le_zeroSubgroup P'.zeroDatum
    (isSplitTorus_centralizer P σ f h) ⟨_, hz, rfl⟩
  have hpt : rationalPoints.map P'.centralizer.j (rationalPoints.map e.hom t) =
      rationalPoints.map (diagTorus F N) t := by
    rw [rationalPoints.map_apply, rationalPoints.map_apply, rationalPoints.map_apply,
      Category.assoc, ← Grp.comp_hom_hom, he]
  rw [hpt] at hmem
  have hmat : toMatrixGL (rationalPoints.map (diagTorus F N) t) = diagGL d := by
    rw [toMatrixGL_map_diagTorus]
    congr 1
    funext a
    simp [t]
  rw [← hmat, MulEquiv.symm_apply_apply]
  exact hmem

/-- For data whose maximal split torus is the diagonal torus and which satisfy the apartment
axioms, `G(F)^0` contains a nontrivial transvection at each position `(k, l)`. -/
theorem exists_transvectionGL_mem_zeroSubgroup
    (hA : (P.basedTransport σ f h).apartment.SatisfiesApartmentAxioms
      (P.basedTransport σ f h).centralizer) {k l : Fin N} (hkl : k ≠ l) :
    ∃ t : F, t ≠ 0 ∧ toMatrixGL.symm (transvectionGL hkl t) ∈
      (P.basedTransport σ f h).zeroSubgroup := by
  let P' := P.basedTransport σ f h
  have ha : rootCharacter (F := F) k l ∈ relativeRoots P'.i := rootCharacter_mem_relativeRoots hkl
  obtain ⟨x⟩ := (inferInstance : Nonempty P'.Apartment)
  obtain ⟨u, hu, hne⟩ := x.isValuation.exists_ne_top ha
  have hu1 : u ≠ 1 := fun h1 => hne ((x.isValuation.eq_top_iff _ ha u hu).2 h1)
  have hu0 : u ∈ P'.zeroSubgroup :=
    P'.zeroDatum.simplyConnectedImage_le_zeroSubgroup
      (P'.rootGroup_le_simplyConnectedImage hA _ ha hu)
  obtain ⟨t, ht⟩ := exists_eq_transvectionGL_of_mem_rootGroupPoints hkl hu
  refine ⟨t, ?_, ?_⟩
  · rintro rfl
    apply hu1
    apply toMatrixGL.injective
    rw [ht, transvectionGL_zero, map_one]
  · rw [← ht, MulEquiv.symm_apply_apply]
    exact hu0

/-- For data whose maximal split torus is the diagonal torus and which satisfy the apartment
axioms, `G(F)^1 ≤ G(F)^0`. -/
theorem rationalCommonNormKernel_le_zeroSubgroup_of_diagonal
    (hA : (P.basedTransport σ f h).apartment.SatisfiesApartmentAxioms
      (P.basedTransport σ f h).centralizer) :
    Plancherel.rationalCommonNormKernel (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)) ≤
      (P.basedTransport σ f h).zeroSubgroup := by
  intro g hg
  let H := (P.basedTransport σ f h).zeroSubgroup.map toMatrixGL.toMonoidHom
  have hHn : H.Normal :=
    (P.basedTransport σ f h).normal_zeroSubgroup.map _ toMatrixGL.surjective
  have hmemH : ∀ y, toMatrixGL y ∈ H → y ∈ (P.basedTransport σ f h).zeroSubgroup := by
    rintro y ⟨y', hy', hyy⟩
    rw [← toMatrixGL.injective hyy]
    exact hy'
  apply hmemH
  rcases Nat.lt_or_ge N 1 with hN | hN
  · -- `N = 0`: the group is trivial.
    have : Subsingleton (GL (Fin N) F) := by
      obtain rfl : N = 0 := by omega
      infer_instance
    rw [Subsingleton.elim (toMatrixGL g) 1]
    exact H.one_mem
  · let i₀ : Fin N := ⟨0, hN⟩
    obtain ⟨M, hM⟩ := eq_toGL_mul_diagGL (toMatrixGL g) i₀
    rw [hM]
    refine H.mul_mem ?_ ?_
    · rcases Nat.lt_or_ge N 2 with hN2 | hN2
      · -- `N = 1`: a matrix of determinant one is the identity.
        obtain rfl : N = 1 := by omega
        have hM1 : M = 1 := by
          ext p q
          have hp : p = q := Subsingleton.elim p q
          subst hp
          have hdet := M.2
          rw [Matrix.det_unique] at hdet
          rw [Subsingleton.elim p default]
          simpa using hdet
        rw [hM1, map_one]
        exact H.one_mem
      · let i₁ : Fin N := ⟨1, hN2⟩
        have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
        obtain ⟨t, ht0, ht⟩ := exists_transvectionGL_mem_zeroSubgroup P σ f h hA h01
        exact specialLinear_le_of_normal hHn h01 ht0
          ⟨_, ht, MulEquiv.apply_symm_apply _ _⟩ M
    · refine ⟨_, diagGL_mem_zeroSubgroup P σ f h _ ?_, MulEquiv.apply_symm_apply _ _⟩
      intro a
      by_cases ha : a = i₀
      · subst ha
        simp only [Pi.mulSingle_eq_same]
        exact valuation_det_eq_one hg
      · simp [Pi.mulSingle_eq_of_ne ha]

end Diagonal

/-- **`G(F)^1 ≤ G(F)^0` for `GL_N`.** For building data `D` of `GL_N` satisfying the one-group
axioms, every point with determinant of valuation one lies in the zero subgroup of `D`. -/
theorem rationalCommonNormKernel_le_zeroSubgroup
    (D : KPBuildingDatum (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)))
    (hD : D.SatisfiesGroupAxioms) :
    Plancherel.rationalCommonNormKernel (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)) ≤
      D.base.zeroSubgroup := by
  obtain ⟨g, e, he⟩ := (maximalSplitTorusConjugacy F _ D.base.isConnectedReductive).1
    D.base.S (diagonalSplitTorus F N) D.base.i (diagTorus F N) D.base.isMaximalSplitTorus
    (GeneralLinear.isMaximalSplitTorus_diagonalTorus F)
  let σ : D.base.S ≅ diagonalSplitTorus F N :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  have hσ : D.base.i ≫ ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).innerIso g).hom =
      CommGroupScheme.groupHom σ.hom ≫ diagTorus F N := he
  have hD' := hD.basedTransport σ _ hσ
  have hA : (D.base.basedTransport σ _ hσ).apartment.SatisfiesApartmentAxioms
      (D.base.basedTransport σ _ hσ).centralizer :=
    hD'.affineRootSystem.apartmentAxioms
  have heq : D.base.zeroSubgroup = (D.base.basedTransport σ _ hσ).zeroSubgroup :=
    ZeroSubgroupDatum.zeroSubgroup_eq_of_datum _ _
  rw [heq]
  exact rationalCommonNormKernel_le_zeroSubgroup_of_diagonal D.base σ _ hσ hA

end Langlands.Geometry.Building.GeneralLinearParahoric
