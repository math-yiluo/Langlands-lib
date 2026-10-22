import Langlands.Cohomology.Tate.HomologyTransferRepresentatives
import Langlands.Cohomology.Tate.NegativeRestriction

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G]
variable (H : Subgroup G) [Fintype (G ⧸ H)]

/-- Ordinary transfer is natural in coefficients already on the actual chains. -/
theorem ordinaryTransferChainMap_naturality {A B : Rep.{u} R G} (f : A ⟶ B) :
    groupHomology.chainsMap (MonoidHom.id G) f ≫ ordinaryTransferChainMap H B =
      ordinaryTransferChainMap H A ≫
        groupHomology.chainsMap (MonoidHom.id H) ((Rep.resFunctor H.subtype).map f) := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro g
  apply LinearMap.ext
  intro a
  change (ordinaryTransferChainMap H B).f n
      ((groupHomology.chainsMap (MonoidHom.id G) f).f n (Finsupp.single g a)) =
    (groupHomology.chainsMap (MonoidHom.id H) ((Rep.resFunctor H.subtype).map f)).f n
      ((ordinaryTransferChainMap H A).f n (Finsupp.single g a))
  rw [groupHomology.chainsMap_f_single]
  change (ordinaryTransferChainMap H B).f n (Finsupp.single g (f.hom a)) = _
  rw [ordinaryTransferChainMap_single, ordinaryTransferChainMap_single, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [groupHomology.chainsMap_f_single]
  change Finsupp.single (transferTuple H n g q) (B.ρ q.out⁻¹ (f.hom a)) =
    Finsupp.single (transferTuple H n g q) (f.hom (A.ρ q.out⁻¹ a))
  exact congrArg (Finsupp.single (transferTuple H n g q)) (Rep.hom_comm_apply f q.out⁻¹ a).symm

/-- In chain degree zero the actual transfer is the inverse-coset sum. -/
lemma ordinaryTransferChainMap_zero (A : Rep.{u} R G) (a : A) :
    (ordinaryTransferChainMap H A).f 0 ((groupHomology.chainsIso₀ A).inv a) =
      (groupHomology.chainsIso₀ (Rep.res H.subtype A)).inv (inverseCosetSum H A a) := by
  classical
  change (ordinaryTransferChainMap H A).f 0 (Finsupp.single default a) =
    Finsupp.single default (inverseCosetSum H A a)
  rw [ordinaryTransferChainMap_single, inverseCosetSum_apply]
  change ∑ q : G ⧸ H, Finsupp.single (transferTuple H 0 default q) (A.ρ q.out⁻¹ a) =
    (Finsupp.lsingle default : A →ₗ[R] (Fin 0 → H) →₀ A)
      (∑ q : G ⧸ H, A.ρ q.out⁻¹ a)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact congrArg (fun g : Fin 0 → H => Finsupp.single g (A.ρ q.out⁻¹ a))
    (Subsingleton.elim _ _)

variable [Fintype G]

/-- The independently constructed ordinary transfer extends to the auxiliary splice. -/
def tateToTransferChains (A : Rep.{u} R G) :
    tateComplex A ⟶ zeroSpliceComplex (Rep.res H.subtype A) :=
  CochainComplex.ConnectData.map _ _ (ordinaryTransferChainMap H A) 0
    (by simp [zeroSpliceConnectData])

lemma tateToTransferChains_homology (A : Rep.{u} R G) (n : ℕ) [NeZero n] :
    HomologicalComplex.homologyMap (tateToTransferChains H A) (-(n + 1 : ℤ)) =
      ((TateCohomology.isoGroupHomology (-(n + 1 : ℤ)) n rfl).app A).hom ≫
        ordinaryHomologyTransfer H A n ≫
          ((zeroSpliceConnectData (Rep.res H.subtype A)).homologyIsoNeg
            n (-(n + 1 : ℤ)) rfl).inv :=
  CochainComplex.ConnectData.homologyMap_map_of_eq_neg_succ _ _ _ _ _ n _ rfl

/-- Coefficient naturality on the full comparison complexes. -/
lemma tateToTransferChains_naturality {A B : Rep.{u} R G} (f : A ⟶ B) :
    tateToTransferChains H A ≫ zeroSpliceMap ((Rep.resFunctor H.subtype).map f) =
      tateComplex.map f ≫ tateToTransferChains H B := by
  ext i : 1
  cases i with
  | ofNat n =>
    change (0 : _ ⟶ _) ≫ _ = _ ≫ (0 : _ ⟶ _)
    simp
  | negSucc n =>
    exact (congrArg (fun m => m.f n) (ordinaryTransferChainMap_naturality H f)).symm

/-- The transfer comparison on a short exact coefficient sequence. -/
def tateToTransferChainsSequence (S : ShortComplex (Rep.{u} R G)) :
    S.map (tateComplexFunctor R G) ⟶
      (S.map (Rep.resFunctor H.subtype)).map zeroSpliceFunctor where
  τ₁ := tateToTransferChains H S.X₁
  τ₂ := tateToTransferChains H S.X₂
  τ₃ := tateToTransferChains H S.X₃
  comm₁₂ := tateToTransferChains_naturality H S.f
  comm₂₃ := tateToTransferChains_naturality H S.g

/-- The transfer chain comparison commutes with the actual connecting morphisms. -/
lemma tateToTransferChains_delta (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact)
    (n : ℤ) :
    TateCohomology.δ hS n ≫
        HomologicalComplex.homologyMap (tateToTransferChains H S.X₁) (n + 1) =
      HomologicalComplex.homologyMap (tateToTransferChains H S.X₃) n ≫
        (zeroSplice_shortExact (hS.map_of_exact (Rep.resFunctor H.subtype))).δ
          n (n + 1) rfl :=
  HomologicalComplex.HomologySequence.δ_naturality
    (tateToTransferChainsSequence H S) (TateCohomology.map_tateComplexFunctor_shortExact hS)
    (zeroSplice_shortExact (hS.map_of_exact (Rep.resFunctor H.subtype))) n (n + 1) rfl

set_option maxRecDepth 4096 in
/-- The comparison sends a norm-zero representative to the transferred zero-chain class. -/
lemma tateToTransferChains_minusOne (A : Rep.{u} R G) (a : A) (ha : A.ρ.norm a = 0) :
    HomologicalComplex.homologyMap (tateToTransferChains H A) (-1) (minusOneClass A a ha) =
      zeroSpliceMinusOneClass (Rep.res H.subtype A) (inverseCosetSum H A a) := by
  rw [minusOneClass, homologyMap_cycleClass]
  have hrep : (tateToTransferChains H A).f (-1) ((groupHomology.chainsIso₀ A).inv a) =
      (groupHomology.chainsIso₀ (Rep.res H.subtype A)).inv (inverseCosetSum H A a) := by
    change (ordinaryTransferChainMap H A).f 0 ((groupHomology.chainsIso₀ A).inv a) = _
    exact ordinaryTransferChainMap_zero H A a
  dsimp only [zeroSpliceMinusOneClass]
  congr 1

end Langlands.Tate
