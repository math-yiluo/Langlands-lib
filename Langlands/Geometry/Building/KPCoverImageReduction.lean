import Langlands.Geometry.Building.KPMinimalLeviZeroNormKernelReduction
import Langlands.Geometry.Building.KPCentralizerParahoricAssembly
import Langlands.Geometry.Building.UnramifiedZeroTransport
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerCoverPreimageStatement
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Derived.FieldBaseChangeAssembly
import Langlands.GroupScheme.CentralIsogeny.BaseChange

/-! # KP Corollary 2.6.28 for the actual minimal-Levi zero subgroup, from its structural inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.GroupScheme

/-- Evaluation of a multiple of a rational character is the power of the evaluation. -/
theorem rationalCharacterEval_nsmul {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (n : ℕ) (χ : rationalCharacters G)
    (g : rationalPoints G) :
    rationalCharacterEval (n • χ) g = rationalCharacterEval χ g ^ n := by
  induction n with
  | zero => rw [zero_smul, rationalCharacterEval_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, rationalCharacterEval_add, ih, pow_succ]

/-- Let `j' : M' ⟶ C` and `j : M ⟶ G` be homomorphisms with `j` a monomorphism, let
`f : C ⟶ G` and `p : M' ⟶ M` satisfy `j' ≫ f = p ≫ j`, and suppose the points of `M'` are
exactly the points of `C` whose image under `f` lies in `M`. If `f(c) = j(z)` for `k`-points
`c` of `C` and `z` of `M`, then `c = j'(m)` and `p(m) = z` for some `k`-point `m` of `M'`. -/
theorem exists_rationalPoint_of_range_eq_comap {k : Type u} [CommRing k]
    {G C M M' : GroupScheme (Spec (CommRingCat.of k))} {f : C ⟶ G} {j : M ⟶ G}
    {j' : M' ⟶ C} {p : M' ⟶ M} (hj : Mono j.hom.hom) (hcomm : j' ≫ f = p ≫ j)
    (hrange : SubgroupFunctor.range j' = (SubgroupFunctor.range j).comap f)
    {c : rationalPoints C} {z : rationalPoints M}
    (hc : rationalPoints.map f c = rationalPoints.map j z) :
    ∃ m : rationalPoints M', rationalPoints.map j' m = c ∧ rationalPoints.map p m = z := by
  have hcm : c ∈ (SubgroupFunctor.range j').carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    rw [hrange, SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range]
    refine ⟨z, ?_⟩
    simpa only [rationalPoints.map_apply] using hc.symm
  obtain ⟨m, hm⟩ := SubgroupFunctor.mem_range.mp hcm
  refine ⟨m, hm, ?_⟩
  have := hj
  apply (cancel_mono j.hom.hom).mp
  have hfac : (p ≫ j).hom.hom = j'.hom.hom ≫ f.hom.hom := by
    rw [← hcomm, Grp.comp_hom_hom]
  rw [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom, hfac, ← Category.assoc, hm]
  simpa only [rationalPoints.map_apply] using hc

end Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- If a positive multiple of every rational character of `M'` is the pullback along
`p : M' ⟶ M` of a rational character of `M`, then `p` maps no point outside the
character-valuation kernel of `M'` into that of `M`. -/
theorem comap_characterValuationKernel_le_of_nsmul {k : Type u} [Field k]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation k Γ₀)
    {M M' : GroupScheme (Spec (CommRingCat.of k))} {p : M' ⟶ M}
    (hchar : ∀ χ' : rationalCharacters M', ∃ n : ℕ, 0 < n ∧
      ∃ χ : rationalCharacters M, n • χ' = characterRestrict p χ) :
    (characterValuationKernel v M).comap (rationalPoints.map p) ≤
      characterValuationKernel v M' := by
  intro m hm
  rw [Subgroup.mem_comap, mem_characterValuationKernel] at hm
  rw [mem_characterValuationKernel]
  intro χ'
  obtain ⟨n, hn, χ, hχ⟩ := hchar χ'
  have hpow : v (rationalCharacterEval χ' m : k) ^ n = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← rationalCharacterEval_nsmul, hχ,
      rationalCharacterEval_characterRestrict]
    exact hm χ
  exact (pow_eq_one_iff_left hn.ne').mp hpow

/-- Let `EM` be data of KP Definition 2.6.23(1) for a `K`-group `M`, and `p : M' ⟶ M`. If the
derived subgroup `d' : D' ⟶ M'` lifts along `p` to the simply connected cover of `EM`, and a
torus `t' : T' ⟶ M'` maps along `p` into the maximal torus of `EM`, then `p` maps
`D'(K) · T'(K)^0` into `M(K)^0`, where `T'(K)^0` is formed with the splitting field of `EM`. -/
theorem derivedRange_sup_torusNormIwahori_le_comap_zeroPoints
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {M M' : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
    (EM : UnramifiedZeroDatum F M) {p : M' ⟶ M}
    {D' : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} {d' : D' ⟶ M'}
    {b : D' ⟶ EM.C} (hb : b ≫ EM.π ≫ EM.d = d' ≫ p)
    {T' : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffine T'.X.left]
    {t' : T'.toGrp ⟶ M'} {g : T' ⟶ EM.T}
    (htg : t' ≫ p = CommGroupScheme.groupHom g ≫ EM.i) :
    (rationalPoints.map d').range ⊔
        (torusNormIwahori (UnramifiedClosure F) EM.L (intermediateValuation F EM.L) T').map
          (rationalPoints.map t') ≤
      EM.zeroPoints.comap (rationalPoints.map p) := by
  refine sup_le ?_ ?_
  · rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_comap]
    refine EM.simplyConnectedImage_le_zeroPoints
      (mem_simplyConnectedImage.mpr ⟨rationalPoints.map b y, ?_⟩)
    have h := congrArg (fun f => rationalPoints.map f y) hb
    simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using h
  · rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_comap]
    refine EM.map_torusIwahori_le_zeroPoints (Subgroup.mem_map.mpr
      ⟨rationalPoints.map (CommGroupScheme.groupHom g) s,
        map_torusNormIwahori_le (UnramifiedClosure F) EM.L (intermediateValuation F EM.L) g
          (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩), ?_⟩)
    have h := congrArg (fun f => rationalPoints.map f s) htg
    simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using h.symm

set_option maxHeartbeats 1000000 in
/-- The `K`-level cover-image containment in the proof of KP Corollary 2.6.28, with
`K = UnramifiedClosure F`. Let `G` be connected reductive over `K` with derived subgroup
`d : D → G` and a central isogeny `π : C → D` from a simply connected `C`, and let
`j : M → G` be the centralizer of a split subtorus. Then every point of `M(K)` in the
character-valuation kernel whose image in `G(K)` comes from `C(K)` lies in `M(K)^0`, for the
supplied data `EM` of KP Definition 2.6.23(1) for `M`. The structural inputs not yet proved in
the Library are explicit hypotheses. -/
theorem coverImage_inf_characterValuationKernel_le_zeroPoints
    (hC : CocenterQuotientExistenceStatement.{u})
    (hF : SplitTorusCentralizerCocenterInducedStatement.{u})
    (hB1 : InducedTorusIwahoriStatement.{u})
    (hPL : SplitTorusCentralizerCoverPreimageStatement.{u})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G D C : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
    {d : D ⟶ G} {π : C ⟶ D} (hG : IsConnectedReductive G) (hd : IsDerivedSubgroup d)
    (hCsc : IsSimplyConnected C) (hπ : IsCentralIsogeny π)
    {A : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} {a : A.toGrp ⟶ G}
    (ha : IsSplitSubtorus a)
    {M : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} {j : M ⟶ G}
    (hj : (torusCentralizer a).IsRepresentedBy j) (EM : UnramifiedZeroDatum F M) :
    (simplyConnectedImage d π).comap (rationalPoints.map j) ⊓
        characterValuationKernel (LocalGalois.Separable.fixedFieldValuation F) M ≤
      EM.zeroPoints := by
  intro z hzmem
  obtain ⟨hzc, hz⟩ := Subgroup.mem_inf.mp hzmem
  rw [Subgroup.mem_comap] at hzc
  obtain ⟨c, hc⟩ := mem_simplyConnectedImage.mp hzc
  -- The preimage `M'` of `M` in `C`, with `p : M' → M`.
  obtain ⟨A', a', M', j', p, ha', hj', hM', hcomm, hrange, hchar, ⟨D', d', b, hd', hb⟩,
      ⟨T', t', g, ht', htg, hsplit⟩⟩ :=
    hPL (UnramifiedClosure F) G D C d π hG hd hCsc hπ A a ha M j hj EM.D EM.C EM.d EM.π
      EM.isSimplyConnectedDerivedCover EM.T EM.i EM.isMaximallySplitMaximalTorus.1
  have : IsAffineHom M'.X.hom := hM'.isAffineHom
  have : IsAffineHom T'.toGrp.X.hom := IsClosedSubgroup.isAffineHom ht'.2.1
  have : IsAffine T'.X.left := isAffine_of_isAffineHom T'.toGrp.X.hom
  -- `c = j'(m)` and `p(m) = z`.
  obtain ⟨m, -, hpm⟩ := exists_rationalPoint_of_range_eq_comap hj.1 hcomm hrange hc
  -- `m ∈ M'(K)^1`: a positive multiple of each character of `M'` comes from `M`.
  have hmK : m ∈ characterValuationKernel (LocalGalois.Separable.fixedFieldValuation F) M' :=
    comap_characterValuationKernel_le_of_nsmul _ hchar
      (Subgroup.mem_comap.mpr (by rw [hpm]; exact hz))
  -- The `K`-level core of KP Lemma 2.6.27 for `M' = Z_C(A')`, pushed forward along `p`.
  have hcore := characterValuationKernel_le_derivedRange_sup_torusNormIwahori hC hF hB1 hCsc
    ha' hj' hM' hd' ht' EM.L (hsplit EM.L EM.isSplitTorus) hmK
  rw [← hpm, ← Subgroup.mem_comap]
  exact derivedRange_sup_torusNormIwahori_le_comap_zeroPoints EM hb htg hcore

namespace ZeroSubgroupDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {j : Z ⟶ G} (E : ZeroSubgroupDatum i j)

set_option maxHeartbeats 1000000 in
/-- The cover-image containment in the proof of KP Corollary 2.6.28 for the actual zero
datum: `G(F)^♮ ∩ Z(F)^1 ⊆ Z(F)^0`. The structural inputs not yet proved in the Library are
explicit hypotheses. -/
theorem coverImageCentralizerNormKernel_of_inputs
    (hC : CocenterQuotientExistenceStatement.{u})
    (hF : SplitTorusCentralizerCocenterInducedStatement.{u})
    (hB1 : InducedTorusIwahoriStatement.{u})
    (hPL : SplitTorusCentralizerCoverPreimageStatement.{u})
    (hsc : IsSimplyConnectedFieldExtensionStatement.{u}) :
    E.CoverImageCentralizerNormKernelStatement := by
  intro z hzmem
  obtain ⟨hzc, hz⟩ := Subgroup.mem_inf.mp hzmem
  rw [Subgroup.mem_comap] at hzc
  have := E.isAffine_centralizer
  have hcov := E.isSimplyConnectedDerivedCover
  have : IsAffineHom G.X.hom := hcov.isConnectedReductive.isAffineHom
  set b := GaloisPointComparison.baseMap F (UnramifiedClosure F)
  -- The base changes to `K` of `G`, of its derived cover and of `S ⊆ G`, `Z = Z_G(S)`.
  have hGK : IsConnectedReductive
      (GaloisPointComparison.baseChanged F (UnramifiedClosure F) G) :=
    connectedReductiveFieldExtensionStatement F (UnramifiedClosure F) G
      hcov.isConnectedReductive
  have hdK : IsDerivedSubgroup ((GroupScheme.baseChange b).map E.d) :=
    hcov.isDerivedSubgroup.baseChange_of_eq _ (derivedSubgroup_baseChange_eq_of_field _ G)
  have hCK : IsSimplyConnected
      (GaloisPointComparison.baseChanged F (UnramifiedClosure F) E.C) :=
    hsc F (UnramifiedClosure F) E.C hcov.isSimplyConnectedCover.isSimplyConnected
  have hπK : IsCentralIsogeny ((GroupScheme.baseChange b).map E.π) :=
    hcov.isSimplyConnectedCover.isCentralIsogeny.baseChange _
  have hSK : IsSplitSubtorus (T := (CommGroupScheme.baseChange b).obj S)
      ((GroupScheme.baseChange b).map i) :=
    ⟨E.isMaximalSplitTorus.isSplitSubtorus.1.baseChange b,
      E.isMaximalSplitTorus.isSplitSubtorus.2.baseChange b⟩
  have hZK : (torusCentralizer (T := (CommGroupScheme.baseChange b).obj S)
      ((GroupScheme.baseChange b).map i)).IsRepresentedBy ((GroupScheme.baseChange b).map j) := by
    rw [torusCentralizer_baseChange]
    exact E.isRepresentedBy.baseChange b
  -- `z_K ∈ Z(K)^1`, and its image in `G(K)` comes from `G_sc(K)`.
  rw [← characterValuationKernelDescent_proof F Z, Subgroup.mem_comap] at hz
  obtain ⟨c, hc⟩ := mem_simplyConnectedImage.mp hzc
  have hcK : GaloisPointComparison.rationalExtend F (UnramifiedClosure F) Z z ∈
      (Building.simplyConnectedImage ((GroupScheme.baseChange b).map E.d)
        ((GroupScheme.baseChange b).map E.π)).comap
        (rationalPoints.map ((GroupScheme.baseChange b).map j)) := by
    rw [Subgroup.mem_comap]
    refine mem_simplyConnectedImage.mpr
      ⟨GaloisPointComparison.rationalExtend F (UnramifiedClosure F) E.C c, ?_⟩
    rw [← Functor.map_comp, ← GaloisPointComparison.rationalExtend_map,
      ← GaloisPointComparison.rationalExtend_map, hc]
  rw [centralizerZero, mem_anisotropicZeroPoints]
  exact coverImage_inf_characterValuationKernel_le_zeroPoints hC hF hB1 hPL hGK hdK hCK hπK
    hSK hZK E.centralizerDatum (Subgroup.mem_inf.mpr ⟨hcK, hz⟩)

/-- The second assertion of KP Corollary 2.6.28 for the actual zero datum:
`G(F)^0 ∩ Z(F)^1 = Z(F)^0`. The structural inputs not yet proved in the Library are explicit
hypotheses. -/
theorem centralizerZeroIntersection_of_inputs
    (hC : CocenterQuotientExistenceStatement.{u})
    (hF : SplitTorusCentralizerCocenterInducedStatement.{u})
    (hB1 : InducedTorusIwahoriStatement.{u})
    (hPL : SplitTorusCentralizerCoverPreimageStatement.{u})
    (hsc : IsSimplyConnectedFieldExtensionStatement.{u}) :
    E.CentralizerZeroIntersectionStatement :=
  E.centralizerZeroIntersection_of_coverImage
    (E.coverImageCentralizerNormKernel_of_inputs hC hF hB1 hPL hsc)

set_option linter.defProp false in
/-- KP Lemma 2.6.27 and Corollary 2.6.28 for the actual zero datum. The six structural inputs
not yet proved in the Library are explicit hypotheses. -/
def minimalLeviZeroComparison_of_inputs
    (hC : CocenterQuotientExistenceStatement.{u})
    (hF : SplitTorusCentralizerCocenterInducedStatement.{u})
    (hG : SplitTorusCentralizerDerivedSimplyConnectedStatement.{u})
    (hB1 : InducedTorusIwahoriStatement.{u})
    (hPL : SplitTorusCentralizerCoverPreimageStatement.{u})
    (hsc : IsSimplyConnectedFieldExtensionStatement.{u}) :
    E.MinimalLeviZeroComparisonStatement :=
  ⟨E.centralizerZeroNormKernel_of_inputs hC hF hG hB1 hsc,
    E.centralizerZeroIntersection_of_inputs hC hF hB1 hPL hsc⟩

end ZeroSubgroupDatum

end Langlands.Geometry.Building
