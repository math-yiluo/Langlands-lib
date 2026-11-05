import Langlands.Geometry.Building.KPMinimalLeviZeroStatement
import Langlands.Geometry.Building.KPCharacterValuationDescentProof
import Langlands.Geometry.Building.KPTorusIwahoriSurjectivityProof
import Langlands.Geometry.Building.KPInducedTorusIwahoriStatement
import Langlands.GroupScheme.Derived.CocenterQuotientStatement
import Langlands.GroupScheme.Rational.SplitTorusCentralizerCocenterStatement
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedStatement
import Langlands.GroupScheme.SimplyConnected.FieldExtensionStatement
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction

/-! # KP Lemma 2.6.27 for the actual minimal-Levi zero subgroup, from its structural inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

set_option maxHeartbeats 1000000 in
/-- The `K`-level core of KP Lemma 2.6.27, with `K = UnramifiedClosure F`. Let `H` be the
centralizer of a split subtorus `a` in a simply connected group `G'` over `K`, let `dH` be
its derived subgroup and `t : T → H` a maximal torus split over a finite Galois `L/K`.
Then every point of `H(K)` in the character-valuation kernel is a product of a point of
`D(K)` and the image of a point of `T(K)^0`. The three structural inputs not yet proved in
the Library are explicit hypotheses. -/
theorem characterValuationKernel_le_derivedRange_sup_torusNormIwahori
    (hC : CocenterQuotientExistenceStatement.{u})
    (hF : SplitTorusCentralizerCocenterInducedStatement.{u})
    (hB1 : InducedTorusIwahoriStatement.{u})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G' : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} (hG' : IsSimplyConnected G')
    {A : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} {a : A.toGrp ⟶ G'}
    (ha : IsSplitSubtorus a)
    {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} {jH : H ⟶ G'}
    (hjH : (torusCentralizer a).IsRepresentedBy jH) (hH : IsConnectedReductive H)
    {D : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} {dH : D ⟶ H}
    (hdH : IsDerivedSubgroup dH)
    {T : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffine T.X.left]
    {t : T.toGrp ⟶ H} (ht : IsMaximalTorus t)
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]
    (hTL : IsSplitTorus (GaloisPointComparison.baseChanged (UnramifiedClosure F) L T.toGrp)) :
    characterValuationKernel (LocalGalois.Separable.fixedFieldValuation F) H ≤
      (rationalPoints.map dH).range ⊔
        (torusNormIwahori (UnramifiedClosure F) L (intermediateValuation F L) T).map
          (rationalPoints.map t) := by
  intro m hm
  -- The cocenter `q : H → D'`: an induced torus, split over `L`.
  obtain ⟨D', q, hD'aff, hq, -, hcoch⟩ := hC (UnramifiedClosure F) H D dH hH hdH
  have := hD'aff
  obtain ⟨hD'split, hsurj⟩ := hcoch T t ht L hTL
  have hind : IsInducedTorus D' := hF (UnramifiedClosure F) G' hG' A a ha H jH hjH D dH hdH D' q hq
  -- `q(m) ∈ D'(K)^1 = D'(K)^0`, the image of `T(K)^0`.
  have hqm : rationalPoints.map q m ∈
      characterValuationKernel (LocalGalois.Separable.fixedFieldValuation F) D'.toGrp :=
    map_characterValuationKernel_le _ q ⟨m, hm, rfl⟩
  rw [← hB1 F D' L hD'split hind,
    ← torusIwahoriSurjectivity F T D' (Additive.ofMul (t ≫ q)) L hTL hD'split hsurj] at hqm
  obtain ⟨s, hs, hseq⟩ := hqm
  -- `t(s)⁻¹ m` lies in the kernel of `q`, which is the range of `dH`.
  have hseq' : rationalPoints.map q (rationalPoints.map t s) = rationalPoints.map q m := by
    rw [← hseq]
    simp only [rationalPoints.map_apply, Category.assoc]
    rfl
  obtain ⟨n, hn_def⟩ : ∃ n, n = (rationalPoints.map t s)⁻¹ * m := ⟨_, rfl⟩
  have hn : n ≫ q.hom.hom = 1 := by
    change rationalPoints.map q n = 1
    rw [hn_def, map_mul, map_inv, hseq', inv_mul_cancel]
  have hnD : n ∈ (SubgroupFunctor.range dH).carrier _ := by
    rw [← hq.2.2.2]
    exact (mem_range_kernelι_iff q n).mpr hn
  -- `m = t(s) · (t(s)⁻¹ m)`.
  have hm' : m = rationalPoints.map t s * n := by
    rw [hn_def, mul_inv_cancel_left]
  rw [hm']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨s, hs, rfl⟩) (Subgroup.mem_sup_left hnD)

namespace ZeroSubgroupDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {j : Z ⟶ G} (E : ZeroSubgroupDatum i j)

include E in
/-- The actual minimal-Levi inclusion `j : Z → G` is a closed subgroup: it represents the
centralizer of `S`, which the closed centralizer representative also represents. -/
theorem isClosedSubgroup_centralizer : IsClosedSubgroup j := by
  have : IsAffineHom G.X.hom := E.isSimplyConnectedDerivedCover.isConnectedReductive.isAffineHom
  have : IsAffineHom S.toGrp.X.hom := E.isMaximalSplitTorus.isSplitSubtorus.2.isAffineHom
  obtain ⟨C, c, hc, hcC⟩ := fieldCentralizerRepresentability F S G this i
  rw [← SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp E.isRepresentedBy hc]
  exact IsClosedSubgroup.iso_comp _ hcC

include E in
/-- The actual minimal Levi subgroup `Z` is affine. -/
theorem isAffine_centralizer : IsAffine Z.X.left := by
  have : IsAffineHom G.X.hom := E.isSimplyConnectedDerivedCover.isConnectedReductive.isAffineHom
  have : IsAffineHom Z.X.hom := E.isClosedSubgroup_centralizer.isAffineHom
  exact isAffine_of_isAffineHom Z.X.hom

set_option maxHeartbeats 1000000 in
set_option linter.defProp false in
/-- KP Lemma 2.6.27 for the actual zero datum: if `G` is simply connected, then
`Z(F)^0 = Z(F)^1`. The five structural inputs not yet proved in the Library are explicit
hypotheses. -/
def centralizerZeroNormKernel_of_inputs
    (hC : CocenterQuotientExistenceStatement.{u})
    (hF : SplitTorusCentralizerCocenterInducedStatement.{u})
    (hG : SplitTorusCentralizerDerivedSimplyConnectedStatement.{u})
    (hB1 : InducedTorusIwahoriStatement.{u})
    (hsc : IsSimplyConnectedFieldExtensionStatement.{u}) :
    E.CentralizerZeroNormKernelStatement := by
  intro hGsc
  apply le_antisymm E.centralizerZero_le_rationalCommonNormKernel
  intro m hm
  have := E.isAffine_centralizer
  set b := GaloisPointComparison.baseMap F (UnramifiedClosure F)
  set ZD := E.centralizerDatum
  have hcov := ZD.isSimplyConnectedDerivedCover
  have hder : IsDerivedSubgroup ZD.d := hcov.isDerivedSubgroup
  -- The base changes of `G`, `S ⊆ G` and `Z = Z_G(S)` to `K`.
  have hGK : IsSimplyConnected (GaloisPointComparison.baseChanged F (UnramifiedClosure F) G) :=
    hsc F (UnramifiedClosure F) G hGsc
  have hSK : IsSplitSubtorus (T := (CommGroupScheme.baseChange b).obj S)
      ((GroupScheme.baseChange b).map i) :=
    ⟨E.isMaximalSplitTorus.isSplitSubtorus.1.baseChange b,
      E.isMaximalSplitTorus.isSplitSubtorus.2.baseChange b⟩
  have hZK : (torusCentralizer (T := (CommGroupScheme.baseChange b).obj S)
      ((GroupScheme.baseChange b).map i)).IsRepresentedBy ((GroupScheme.baseChange b).map j) := by
    rw [torusCentralizer_baseChange]
    exact E.isRepresentedBy.baseChange b
  -- The derived subgroup of `Z_K` is simply connected, so `D(K) = Z(K)^♮`.
  have hDsc : IsSimplyConnected ZD.D := hG (UnramifiedClosure F) _ hGK _ _ hSK _ _ hZK ZD.D ZD.d hder
  have : IsIso ZD.π := hDsc.central_isogeny_isIso ZD.C ZD.π
    hcov.isSimplyConnectedCover.isSimplyConnected.isSemisimple
    hcov.isSimplyConnectedCover.isCentralIsogeny
  have hdC : (rationalPoints.map ZD.d).range ≤ ZD.simplyConnectedImage := by
    rintro _ ⟨y, rfl⟩
    refine mem_simplyConnectedImage.mpr ⟨rationalPoints.map (inv ZD.π) y, ?_⟩
    simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
    rw [← Category.assoc (inv ZD.π).hom.hom, ← Grp.comp_hom_hom, IsIso.inv_hom_id,
      Grp.id_hom_hom, Category.id_comp]
  -- `m ∈ Z(K)^1`, and the `K`-level core.
  rw [← characterValuationKernelDescent_proof F Z, Subgroup.mem_comap] at hm
  rw [centralizerZero, mem_anisotropicZeroPoints]
  have hcore := characterValuationKernel_le_derivedRange_sup_torusNormIwahori hC hF hB1 hGK hSK
    hZK hcov.isConnectedReductive hder ZD.isMaximallySplitMaximalTorus.1 ZD.L ZD.isSplitTorus hm
  exact sup_le (hdC.trans ZD.simplyConnectedImage_le_zeroPoints)
    ZD.map_torusIwahori_le_zeroPoints hcore

end ZeroSubgroupDatum

end Langlands.Geometry.Building
