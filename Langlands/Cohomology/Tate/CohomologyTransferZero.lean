import Langlands.Cohomology.Tate.CohomologyTransferNaturality

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R G : Type u} [CommRing R] [Group G]

/-- Standard homogeneous coordinates of an actual inhomogeneous cochain. -/
lemma cochainsIsoStandard_hom_single (A : Rep.{u} R G) (n : ℕ)
    (c : (Fin n → G) → A) (g : Fin (n + 1) → G) (r : R) :
    ((cochainsIsoStandard A).hom.f n c).hom (MonoidAlgebra.single g r) =
      r • A.ρ (g 0) (c (fun i => (g i.castSucc)⁻¹ * g i.succ)) := by
  change ((Rep.freeLiftLEquiv R G (Fin n → G) A).symm c).hom
    ((Rep.diagonalSuccIsoFree R G n).hom.hom (MonoidAlgebra.single g r)) = _
  rw [diagonalFree_hom_single]
  simp [Rep.freeLiftLEquiv, Representation.freeLiftLEquiv, Rep.homEquiv,
    Representation.freeLift_single_single]

/-- Recover an inhomogeneous cochain by evaluating on the partial-product tuple. -/
lemma cochainsIsoStandard_inv_apply (A : Rep.{u} R G) (n : ℕ)
    (f : (Rep.standardComplex R G).X n ⟶ A) (g : Fin n → G) :
    (cochainsIsoStandard A).inv.f n f g =
      f.hom (MonoidAlgebra.single (Fin.partialProd g) 1) := by
  change f.hom ((Rep.diagonalSuccIsoFree R G n).inv.hom
    (Finsupp.single g (MonoidAlgebra.single 1 1))) = _
  rw [diagonalFree_inv_single, one_smul]

variable (H : Subgroup G) [Fintype (G ⧸ H)]

/-- Ordinary cochain transfer sends an invariant zero-cocycle to its coset norm. -/
lemma ordinaryCorestrictionCochainMap_zero (A : Rep.{u} R G)
    (a : (Rep.res H.subtype A).ρ.invariants) :
    (groupCohomology.cochainsIso₀ A).hom
      ((ordinaryCorestrictionCochainMap H A).f 0
        ((groupCohomology.cochainsIso₀ (Rep.res H.subtype A)).inv a)) =
      (cosetNorm H A a : A) := by
  change (cochainsIsoStandard A).inv.f 0
      (homTransfer H ((Rep.standardComplex R G).X 0) A
        (standardCosetComparisonComponent H 0 ≫
          (cochainsIsoStandard (Rep.res H.subtype A)).hom.f 0 (fun _ => (a : A))))
      default = _
  rw [cochainsIsoStandard_inv_apply, homTransfer_apply]
  change (∑ q : G ⧸ H, A.ρ q.out
    (((cochainsIsoStandard (Rep.res H.subtype A)).hom.f 0 (fun _ => (a : A))).hom
      ((standardCosetComparisonComponent H 0).hom
        (Representation.ofMulAction R G (Fin 1 → G) q.out⁻¹
          (MonoidAlgebra.single (Fin.partialProd (default : Fin 0 → G)) 1))))) = _
  change _ = ∑ q : G ⧸ H, cosetAction H A a q
  apply Finset.sum_congr rfl
  intro q _
  rw [Representation.ofMulAction_single, standardCosetComparisonComponent_single,
    cochainsIsoStandard_hom_single, one_smul, cosetAction_out]
  exact congrArg (A.ρ q.out) (a.property _)

variable [Fintype G]

/-- On degree-zero homology the ordinary transfer comparison is the coset norm. -/
lemma transferCochainsToTate_zero_hom (A : Rep.{u} R G) :
    (zeroSpliceZeroEquiv (Rep.res H.subtype A)).inv ≫
        HomologicalComplex.homologyMap (transferCochainsToTate H A) 0 =
      ModuleCat.ofHom (cosetNorm H A) ≫ ModuleCat.ofHom (zeroClass A) := by
  let B := Rep.res H.subtype A
  let ψ : zeroSpliceShortComplex B ⟶ zeroShortComplex A :=
    (zeroSpliceShortComplexIso B).inv ≫
      (HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) 0).map
        (transferCochainsToTate H A) ≫ (zeroShortComplexIso A).hom
  let γ := ShortComplex.leftHomologyMapData ψ (zeroSpliceHomologyData B) (zeroHomologyData A)
  have hψ : ψ.τ₂ = (groupCohomology.cochainsIso₀ B).inv ≫
      (ordinaryCorestrictionCochainMap H A).f 0 ≫
        (groupCohomology.cochainsIso₀ A).hom := rfl
  have hK : γ.φK = ModuleCat.ofHom (cosetNorm H A) := by
    apply (cancel_mono (zeroHomologyData A).i).mp
    rw [γ.commi, hψ]
    ext a
    change B.ρ.invariants at a
    change (groupCohomology.cochainsIso₀ A).hom
      ((ordinaryCorestrictionCochainMap H A).f 0
        ((groupCohomology.cochainsIso₀ B).inv (a : B))) = (cosetNorm H A a : A)
    exact ordinaryCorestrictionCochainMap_zero H A a
  have hmap : HomologicalComplex.homologyMap (transferCochainsToTate H A) 0 =
      (zeroSpliceZeroEquiv B).hom ≫ γ.φH ≫ (zeroEquiv A).inv := by
    apply (cancel_mono (zeroEquiv A).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hh := congrArg
      (fun z => (ShortComplex.homologyMapIso (zeroSpliceShortComplexIso B)).hom ≫ z)
      γ.homologyMap_comm
    simp only [ψ, ShortComplex.homologyMap_comp, Category.assoc] at hh
    change (ShortComplex.homologyMapIso (zeroSpliceShortComplexIso B)).hom ≫
      (ShortComplex.homologyMapIso (zeroSpliceShortComplexIso B)).inv ≫
      HomologicalComplex.homologyMap (transferCochainsToTate H A) 0 ≫
      (ShortComplex.homologyMapIso (zeroShortComplexIso A)).hom ≫
      (zeroHomologyData A).homologyIso.hom =
      (ShortComplex.homologyMapIso (zeroSpliceShortComplexIso B)).hom ≫
      (zeroSpliceHomologyData B).homologyIso.hom ≫ γ.φH at hh
    simpa only [Iso.hom_inv_id_assoc, zeroSpliceZeroEquiv, zeroEquiv,
      Iso.trans_hom, Category.assoc] using hh
  have hπ : γ.φH =
      ModuleCat.ofHom (cosetNorm H A) ≫ ModuleCat.ofHom (normImage A).mkQ := by
    simpa only [hK, zeroSpliceHomologyData, zeroHomologyData, Category.id_comp] using γ.commπ
  rw [hmap]
  simp only [B, Category.assoc, Iso.inv_hom_id_assoc, hπ]
  rfl

lemma transferCochainsToTate_zero (A : Rep.{u} R G)
    (a : (Rep.res H.subtype A).ρ.invariants) :
    HomologicalComplex.homologyMap (transferCochainsToTate H A) 0
        ((zeroSpliceZeroEquiv (Rep.res H.subtype A)).inv a) =
      zeroClass A (cosetNorm H A a) :=
  ConcreteCategory.congr_hom (transferCochainsToTate_zero_hom H A) a

end Langlands.Tate
