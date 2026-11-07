import Langlands.GroupScheme.HomScheme.TorusChartInjective
import Langlands.GroupScheme.HomScheme.SplitTorusRangeKernel
import Langlands.Algebra.TorusChartExistence

/-! # Openness of torus charts on affine tests -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.HomScheme.TorusChart

open Langlands.Algebra Langlands.Algebra.TorusChartRing Langlands.Algebra.TorusChartAlgebra
  Langlands.AlgebraicGeometry TorusSubgroupModuli

/-- Étale-local splitting of a closed torus subgroup over an affine test into closed
split-torus Hopf points. -/
def EtaleSplitStatement : Prop :=
  ∀ {R : Type u} [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
    {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left] {L : GroupScheme T.left}
    (i : L ⟶ (GroupScheme.baseChange T.hom).obj G), IsClosedSubgroup i →
    RelativeTorus.IsTorus L →
    ∃ (n : ℕ) (C : Fin n → Type u) (_ : ∀ k, CommRing (C k)) (_ : ∀ k, Algebra R (C k))
      (b : ∀ k, FiniteSource.specOver R (C k) ⟶ T) (I : Fin n → Type u)
      (_ : ∀ k, Fintype (I k)) (_ : ∀ k, DecidableEq (I k))
      (f : ∀ k, {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C k ⊗[R]
        AddMonoidAlgebra R (I k → ℤ) // FiniteBialgebraHom.IsHopfPoint R f}),
      (∀ k, Etale (b k).left) ∧ (∀ t : T.left, ∃ k, t ∈ Set.range (b k).left.base) ∧
      (∀ k, Function.Surjective (AlgHom.liftEquiv R (C k) _ _ (f k).1)) ∧
      ∀ k, TorusSubgroupModuli.evaluate i (b k) =
        SubgroupFunctor.range ((SplitTorusPoint.splitPointEquiv G (C k)).symm (f k))

section General

variable {S₀ : Scheme.{u}} {G : GroupScheme S₀} {U M : Over S₀}
  {K : GroupScheme U.left} {L : GroupScheme M.left}

/-- Equality of evaluations descends along faithfully flat quasi-compact test maps. -/
theorem evaluate_eq_of_comp_fpqc (j : K ⟶ (GroupScheme.baseChange U.hom).obj G)
    (i : L ⟶ (GroupScheme.baseChange M.hom).obj G) (hj : IsClosedSubgroup j)
    (hi : IsClosedSubgroup i) {T₁ T₂ : Over S₀} (π : T₂ ⟶ T₁) [QuasiCompact π.left]
    [Flat π.left] [Surjective π.left] (a : T₁ ⟶ U) (b : T₁ ⟶ M)
    (h : TorusSubgroupModuli.evaluate j (π ≫ a) = TorusSubgroupModuli.evaluate i (π ≫ b)) : TorusSubgroupModuli.evaluate j a = TorusSubgroupModuli.evaluate i b := by
  rw [← TorusSubgroupModuli.evaluate_comp, ← TorusSubgroupModuli.evaluate_comp] at h
  let : IsClosedImmersion (TorusSubgroupModuli.familyHom j a).hom.hom.left := TorusSubgroupModuli.isClosedSubgroup_familyHom j hj a
  let : IsClosedImmersion (TorusSubgroupModuli.familyHom i b).hom.hom.left := TorusSubgroupModuli.isClosedSubgroup_familyHom i hi b
  let : Mono (TorusSubgroupModuli.familyHom j a).hom.hom := Over.mono_of_mono_left _
  let : Mono (TorusSubgroupModuli.familyHom i b).hom.hom := Over.mono_of_mono_left _
  apply SubgroupFunctor.range_eq_of_baseChange_eq π.left (TorusSubgroupModuli.familyHom j a) (TorusSubgroupModuli.familyHom i b)
  rw [← SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.range_baseChangeHom]
  exact (SubgroupFunctor.range_comp_iso_eq_iff _ _
    (Descent.pullbackComparison T₁.hom π.left T₂.hom (Over.w π) G)).mp h

/-- Injectivity on affine tests implies injectivity on all tests. -/
theorem injective_all_of_affine (j : K ⟶ (GroupScheme.baseChange U.hom).obj G)
    (hinj : ∀ T : Over S₀, IsAffine T.left → ∀ a b : T ⟶ U, TorusSubgroupModuli.evaluate j a = TorusSubgroupModuli.evaluate j b → a = b)
    (T : Over S₀) (a b : T ⟶ U) (h : TorusSubgroupModuli.evaluate j a = TorusSubgroupModuli.evaluate j b) : a = b := by
  apply Over.OverMorphism.ext
  apply T.left.affineCover.hom_ext
  intro k
  have hk := hinj (SubgroupFunctor.coverObj T.left.affineCover k)
    (inferInstanceAs (IsAffine (T.left.affineCover.X k)))
    (SubgroupFunctor.coverMap T.left.affineCover k ≫ a)
    (SubgroupFunctor.coverMap T.left.affineCover k ≫ b)
    (TorusSubgroupModuli.evaluate_eq_comp j j a b h (SubgroupFunctor.coverMap T.left.affineCover k))
  exact congrArg (fun f => f.left) hk

/-- Parameters glue along open covers, given injectivity on affine tests. -/
theorem exists_evaluate_of_openCover (j : K ⟶ (GroupScheme.baseChange U.hom).obj G)
    (hj : IsClosedSubgroup j)
    (hinj : ∀ T : Over S₀, IsAffine T.left → ∀ a b : T ⟶ U, TorusSubgroupModuli.evaluate j a = TorusSubgroupModuli.evaluate j b → a = b)
    (i : L ⟶ (GroupScheme.baseChange M.hom).obj G) (hi : IsClosedSubgroup i)
    {T : Over S₀} (b : T ⟶ M) (𝒰 : Scheme.OpenCover.{u} T.left)
    (h : ∀ k, ∃ a : SubgroupFunctor.coverObj 𝒰 k ⟶ U,
      TorusSubgroupModuli.evaluate j a = TorusSubgroupModuli.evaluate i (SubgroupFunctor.coverMap 𝒰 k ≫ b)) :
    ∃ a : T ⟶ U, TorusSubgroupModuli.evaluate j a = TorusSubgroupModuli.evaluate i b := by
  classical
  choose a ha using h
  have hc (k l : 𝒰.I₀) :
      pullback.fst (𝒰.f k) (𝒰.f l) ≫ (a k).left =
        pullback.snd (𝒰.f k) (𝒰.f l) ≫ (a l).left := by
    let W : Over S₀ :=
      Over.mk (pullback.fst (𝒰.f k) (𝒰.f l) ≫ 𝒰.f k ≫ T.hom)
    let p : W ⟶ SubgroupFunctor.coverObj 𝒰 k := Over.homMk (pullback.fst (𝒰.f k) (𝒰.f l))
    let q : W ⟶ SubgroupFunctor.coverObj 𝒰 l := Over.homMk (pullback.snd (𝒰.f k) (𝒰.f l))
      (by simpa only [W, SubgroupFunctor.coverObj, Over.mk_hom] using
        (pullback.condition_assoc (f := 𝒰.f k) (g := 𝒰.f l) T.hom).symm)
    have hpq : p ≫ SubgroupFunctor.coverMap 𝒰 k = q ≫ SubgroupFunctor.coverMap 𝒰 l := by
      apply Over.OverMorphism.ext
      exact pullback.condition
    have he : p ≫ a k = q ≫ a l := by
      apply injective_all_of_affine j hinj
      exact (TorusSubgroupModuli.evaluate_eq_comp j i (a k) (SubgroupFunctor.coverMap 𝒰 k ≫ b) (ha k) p).trans
        (by rw [← Category.assoc, hpq, Category.assoc]
            exact (TorusSubgroupModuli.evaluate_eq_comp j i (a l) (SubgroupFunctor.coverMap 𝒰 l ≫ b) (ha l) q).symm)
    exact congrArg (fun f => f.left) he
  let d := 𝒰.glueMorphisms (fun k => (a k).left) hc
  have hd (k : 𝒰.I₀) : 𝒰.f k ≫ d = (a k).left :=
    𝒰.ι_glueMorphisms _ hc k
  have hw : d ≫ U.hom = T.hom := by
    apply 𝒰.hom_ext
    intro k
    rw [← Category.assoc, hd]
    exact Over.w (a k)
  let a' : T ⟶ U := Over.homMk d hw
  refine ⟨a', (TorusSubgroupModuli.evaluate_eq_iff_openCover j i hj hi a' b 𝒰).mpr ?_⟩
  intro k
  have he : SubgroupFunctor.coverMap 𝒰 k ≫ a' = a k := by
    apply Over.OverMorphism.ext
    exact hd k
  rw [he]
  exact ha k

/-- Parameters over an étale map from an affine scheme descend to an open neighbourhood of
any point of its image, given injectivity on affine tests. -/
theorem exists_good_open_of_etale (j : K ⟶ (GroupScheme.baseChange U.hom).obj G)
    (hj : IsClosedSubgroup j)
    (hinj : ∀ T : Over S₀, IsAffine T.left → ∀ a b : T ⟶ U,
      TorusSubgroupModuli.evaluate j a = TorusSubgroupModuli.evaluate j b → a = b)
    (i : L ⟶ (GroupScheme.baseChange M.hom).obj G) (hi : IsClosedSubgroup i)
    {T : Over S₀} (hT : IsAffine T.left) (b₀ : T ⟶ M) {E : Over S₀} (hE : IsAffine E.left)
    (e : E ⟶ T) [Etale e.left] (aE : E ⟶ U)
    (h : TorusSubgroupModuli.evaluate j aE = TorusSubgroupModuli.evaluate i (e ≫ b₀))
    (t : T.left) (ht : t ∈ Set.range e.left.base) :
    ∃ W : T.left.Opens, t ∈ W ∧ ∃ aW : Over.mk (W.ι ≫ T.hom) ⟶ U,
      TorusSubgroupModuli.evaluate j aW =
        TorusSubgroupModuli.evaluate i ((Over.homMk W.ι rfl : Over.mk (W.ι ≫ T.hom) ⟶ T) ≫ b₀) := by
  let O : T.left.Opens := ⟨Set.range e.left.base, e.left.isOpenMap.isOpen_range⟩
  obtain ⟨hf, hle, htW⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := O) ⟨t, ht⟩
    (Set.mem_univ t)
  let W := T.left.basicOpen hf
  have hW : IsAffineOpen W := (isAffineOpen_top T.left).basicOpen hf
  have : IsAffine W.toScheme := hW
  refine ⟨W, htW, ?_⟩
  let π := pullback.snd e.left W.ι
  let πE := pullback.fst e.left W.ι
  have : Surjective π := by
    refine ⟨fun w => ?_⟩
    have hw : W.ι w ∈ O := hle (by simp)
    obtain ⟨x, hx⟩ := hw
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback x w hx
    exact ⟨z, hz⟩
  let WO : Over S₀ := Over.mk (W.ι ≫ T.hom)
  let ιO : WO ⟶ T := Over.homMk W.ι rfl
  let PO : Over S₀ := Over.mk (π ≫ W.ι ≫ T.hom)
  let πO : PO ⟶ WO := Over.homMk π rfl
  have hπE : πE ≫ E.hom = PO.hom := by
    change πE ≫ E.hom = π ≫ W.ι ≫ T.hom
    rw [← Over.w e, ← Category.assoc, pullback.condition, Category.assoc]
  let πEO : PO ⟶ E := Over.homMk πE hπE
  have hcomm : πEO ≫ e = πO ≫ ιO := Over.OverMorphism.ext pullback.condition
  let aP := πEO ≫ aE
  have haP : TorusSubgroupModuli.evaluate j aP =
      TorusSubgroupModuli.evaluate i (πO ≫ ιO ≫ b₀) := by
    have := TorusSubgroupModuli.evaluate_eq_comp j i aE (e ≫ b₀) h πEO
    rwa [← Category.assoc, hcomm, Category.assoc] at this
  have hc : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ pullback e.left W.ι), g₁ ≫ π = g₂ ≫ π →
      g₁ ≫ aP.left = g₂ ≫ aP.left := by
    intro Z g₁ g₂ hg
    let ZO : Over S₀ := Over.mk (g₁ ≫ PO.hom)
    let g₁O : ZO ⟶ PO := Over.homMk g₁ rfl
    let g₂O : ZO ⟶ PO := Over.homMk g₂ (by
      change g₂ ≫ π ≫ W.ι ≫ T.hom = g₁ ≫ π ≫ W.ι ≫ T.hom
      rw [← Category.assoc, ← hg, Category.assoc])
    have hg' : g₁O ≫ πO = g₂O ≫ πO := Over.OverMorphism.ext hg
    have he := injective_all_of_affine j hinj ZO (g₁O ≫ aP) (g₂O ≫ aP) (by
      rw [TorusSubgroupModuli.evaluate_eq_comp j i aP (πO ≫ ιO ≫ b₀) haP g₁O,
        TorusSubgroupModuli.evaluate_eq_comp j i aP (πO ≫ ιO ≫ b₀) haP g₂O,
        ← Category.assoc, hg', Category.assoc])
    exact congrArg (fun f => f.left) he
  let dW := EffectiveEpi.desc π aP.left hc
  have hfac : π ≫ dW = aP.left := EffectiveEpi.fac π aP.left hc
  have hw : dW ≫ U.hom = WO.hom := by
    apply (cancel_epi π).mp
    rw [← Category.assoc, hfac, Over.w aP]
    rfl
  let aW : WO ⟶ U := Over.homMk dW hw
  refine ⟨aW, ?_⟩
  have hπa : πO ≫ aW = aP := Over.OverMorphism.ext hfac
  have : IsAffine (pullback e.left W.ι) := inferInstance
  have : QuasiCompact πO.left := by
    change QuasiCompact π
    infer_instance
  have : Flat πO.left := by
    change Flat π
    infer_instance
  have : Surjective πO.left := by
    change Surjective π
    infer_instance
  apply evaluate_eq_of_comp_fpqc j i hj hi πO aW (ιO ≫ b₀)
  rw [hπa]
  exact haP

end General

section Local

open HopfPointClosedLocus HopfPointWeightWindow HopfPointWeightLocus HopfPointExtension
  LatticeConfiguration TorusChartExistence

variable {R : Type u} [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
  [Algebra.FinitePresentation R (AffineCoordinates.hopfAlgebra G)]
  {r : Type u} [Fintype r] [DecidableEq r] {m : ℕ} [NeZero m]
  {σ' : Type u} {gen : σ' → AffineCoordinates.hopfAlgebra G} {n : ℕ}
  (d : Datum R (AffineCoordinates.hopfAlgebra G) r m gen n)

omit [Algebra.FinitePresentation R (AffineCoordinates.hopfAlgebra G)] in
/-- Twisting a closed split Hopf point by an isomorphism of character lattices does not change
the range. -/
theorem range_twist_eq {I : Type u} [Fintype I] [DecidableEq I] {C : Type u} [CommRing C]
    [Algebra R C]
    (f : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R (I → ℤ) //
      FiniteBialgebraHom.IsHopfPoint R f})
    (hf : Function.Surjective (AlgHom.liftEquiv R C _ _ f.1)) (T : (I → ℤ) ≃+ (r → ℤ)) :
    SubgroupFunctor.range ((SplitTorusPoint.splitPointEquiv G C).symm f) =
      SubgroupFunctor.range ((SplitTorusPoint.splitPointEquiv G C).symm
        ⟨ofGroupAlgebra ((AddMonoidAlgebra.mapDomainAlgHom R C T.toAddMonoidHom).comp
          (HopfPointBridge.toGroupAlgebra f.1)),
          isHopfPoint_ofGroupAlgebra (((HopfPointBridge.isHopfPoint_iff f.1).mp f.2).mapDomain
            T.toAddMonoidHom)⟩) := by
  have hs : Function.Surjective (scalarExt (HopfPointBridge.toGroupAlgebra f.1)) :=
    (surjective_liftEquiv_iff f.1).mp hf
  apply (SplitTorusPoint.range_splitPointEquiv_symm_eq_iff_ker₂ f _ hf ?_).mpr
  · rw [ker_liftEquiv, ker_liftEquiv, toGroupAlgebra_ofGroupAlgebra,
      ker_scalarExt_mapDomain_addEquiv₂]
  · rw [surjective_liftEquiv_iff, toGroupAlgebra_ofGroupAlgebra]
    exact surjective_scalarExt_mapDomain _ T.surjective hs

/-- Over a field, a closed split torus with the same range as the window torus at a point of the
window piece is a twist of it. -/
theorem exists_twist_of_range_eq {I : Type u} [Fintype I] [DecidableEq I] {K : Type u} [Field K]
    [Algebra R K]
    (f : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] K ⊗[R] AddMonoidAlgebra R (I → ℤ) //
      FiniteBialgebraHom.IsHopfPoint R f})
    (hf : Function.Surjective (AlgHom.liftEquiv R K _ _ f.1)) (b' : Bf d →ₐ[R] K)
    (h : SubgroupFunctor.range ((SplitTorusPoint.splitPointEquiv G K).symm f) =
      SubgroupFunctor.range ((SplitTorusPoint.splitPointEquiv G K).symm
        ⟨FiniteBialgebraHom.pushPoint R b' (fS G d).1, (fS G d).2.pushPoint R b'⟩)) :
    ∃ T : (I → ℤ) ≃+ (r → ℤ), (AddMonoidAlgebra.mapDomainAlgHom R K T.toAddMonoidHom).comp
      (HopfPointBridge.toGroupAlgebra f.1) = d.pushα (b'.comp (uS d)) := by
  have hker := (SplitTorusPoint.range_splitPointEquiv_symm_eq_iff_ker₂ f
    ⟨FiniteBialgebraHom.pushPoint R b' (fS G d).1, (fS G d).2.pushPoint R b'⟩ hf
    (surjective_pushPoint_fS G d b')).mp h
  have hker' : RingHom.ker (scalarExt (HopfPointBridge.toGroupAlgebra f.1)) =
      RingHom.ker (scalarExt (d.pushα (b'.comp (uS d)))) := by
    rw [← ker_liftEquiv]
    ext x
    have := congrArg (fun I => x ∈ I) hker
    simp only [RingHom.mem_ker, eq_iff_iff] at this ⊢
    rw [← liftEquiv_pushPoint_fS_eq_zero_iff G d b']
    exact this
  have hs : Function.Surjective (scalarExt (HopfPointBridge.toGroupAlgebra f.1)) :=
    (surjective_liftEquiv_iff f.1).mp hf
  obtain ⟨τ, hτ⟩ := HopfPointConnected.exists_tau_of_ker_le hs hker'.le
  obtain ⟨τ', hτ'⟩ := HopfPointConnected.exists_tau_of_ker_le (d.surjective_pushα _) hker'.ge
  exact HopfPointConnected.exists_addEquiv_of_comp
    HopfPointConnected.isIdempotentElem_eq_zero_or_one_of_isLocalRing
    ((HopfPointBridge.isHopfPoint_iff f.1).mp f.2) (d.isHopfPoint_pushα _) hs
    (d.surjective_pushα _) τ τ' hτ hτ'

theorem toAlgHom_W_Bf :
    IsScalarTower.toAlgHom R (W R (AffineCoordinates.hopfAlgebra G) r m) (Bf d) =
      (IsScalarTower.toAlgHom R d.B (Bf d)).comp
        (IsScalarTower.toAlgHom R (W R (AffineCoordinates.hopfAlgebra G) r m) d.B) := by
  apply AlgHom.ext
  intro w
  exact IsScalarTower.algebraMap_apply _ d.B (Bf d) w

theorem isUnit_algebraMap_Bf_N_mul_f :
    IsUnit (algebraMap (W R (AffineCoordinates.hopfAlgebra G) r m) (Bf d) (d.N * d.f)) := by
  rw [IsScalarTower.algebraMap_apply _ d.B (Bf d), map_mul, map_mul]
  exact ((IsLocalization.Away.algebraMap_isUnit d.N).map (algebraMap d.B (Bf d))).mul
    (IsLocalization.Away.algebraMap_isUnit _)

set_option maxHeartbeats 1000000 in
/-- Openness of the chart locus at a point of an étale splitting: a closed split Hopf point of
rank `r` which agrees with the window torus at a field point is the window torus over a
principal open around that point. -/
theorem exists_local_lift {V : Submodule R (AffineCoordinates.hopfAlgebra G)} [Module.Finite R V]
    {δ : V →ₗ[R] V ⊗[R] AffineCoordinates.hopfAlgebra G} (hδ : IsCoassoc δ)
    (hι : (Coalgebra.comul (R := R) (A := AffineCoordinates.hopfAlgebra G)) ∘ₗ V.subtype =
      V.subtype.rTensor _ ∘ₗ δ)
    (hgenV : ∀ i, gen i ∈ V) {N₀ : ℕ} (hP : IsBoundedPresentation (R := R) gen N₀)
    (hN₀ : 1 ≤ N₀) (dw : WindowDatum R (AffineCoordinates.hopfAlgebra G) r m gen n V δ N₀)
    {C : Type u} [CommRing C] [Algebra R C]
    {α' : AffineCoordinates.hopfAlgebra G →ₐ[R] AddMonoidAlgebra C (r → ℤ)}
    (hα' : IsHopfPoint α') {K : Type u} [Field K] [Algebra R K] (ψ : C →ₐ[R] K)
    (yK : Bf dw.toDatum →ₐ[R] K)
    (hψ : (AddMonoidAlgebra.mapAlgHom (r → ℤ) ψ).comp α' =
      dw.toDatum.pushα (yK.comp (uS dw.toDatum))) :
    ∃ g : C, ψ g ≠ 0 ∧ ∃ b'' : Bf dw.toDatum →ₐ[R] Localization.Away g,
      (AddMonoidAlgebra.mapAlgHom (r → ℤ) (IsScalarTower.toAlgHom R C (Localization.Away g))).comp
        α' = dw.toDatum.pushα (b''.comp (uS dw.toDatum)) := by
  classical
  let d := dw.toDatum
  -- weights at the field point
  have hwK : WeightsIn δ ((AddMonoidAlgebra.mapAlgHom (r → ℤ) ψ).comp α')
      (box r n : Set (r → ℤ)) := by
    rw [hψ]
    exact weightsIn_mapAlgHom δ _ dw.weights
  obtain ⟨hP₁, ι₁, hι₁⟩ := exists_residueLift ψ
  have hw₁ : WeightsIn δ ((AddMonoidAlgebra.mapAlgHom (r → ℤ)
      (IsScalarTower.toAlgHom R C (RingHom.ker ψ).ResidueField)).comp α')
      (box r n : Set (r → ℤ)) := by
    apply weightsIn_of_mapAlgHom δ ι₁ (rTensor_injective_of_field ι₁)
    rw [← AlgHom.comp_assoc, mapAlgHom_comp_mapAlgHom, hι₁]
    exact hwK
  obtain ⟨g₁, hg₁, hW₁⟩ := exists_away_weightsIn δ hδ hα' (box r n : Set (r → ℤ))
    (RingHom.ker ψ) hw₁
  have hψg₁ : ψ g₁ ≠ 0 := fun h => hg₁ (by simpa [RingHom.mem_ker] using h)
  let α₁ := (AddMonoidAlgebra.mapAlgHom (r → ℤ)
    (IsScalarTower.toAlgHom R C (Localization.Away g₁))).comp α'
  have hα₁ : IsHopfPoint α₁ := HopfPointWindowExtension.IsHopfPoint.mapAlgHom _ hα'
  have hsupp₁ : ∀ i, ↑(α₁ (gen i)).coeff.support ⊆ (box r n : Set (r → ℤ)) := fun i =>
    support_subset_of_weightsIn δ α₁ hW₁ V.subtype hι ⟨gen i, hgenV i⟩
  -- the point of `W`
  obtain ⟨w₁, hw₁p⟩ := exists_point_of_hopfPoint (A := AffineCoordinates.hopfAlgebra G) (m := m)
    (hα₁.mapDomain (red r m))
  obtain ⟨ψ₁, hψ₁⟩ := exists_lift_away ψ hψg₁
  have hψ₁' : ∀ x, ψ₁ (algebraMap C (Localization.Away g₁) x) = ψ x :=
    fun x => congrArg (fun F => F x) hψ₁
  have hwy : ψ₁.comp w₁ = yK.comp (IsScalarTower.toAlgHom R
      (W R (AffineCoordinates.hopfAlgebra G) r m) (Bf d)) := by
    apply pointOf_injective
    rw [pointOf_comp, hw₁p, ← AlgHom.comp_assoc, HopfPointWindowExtension.mapAlgHom_comp_mapDomain,
      AlgHom.comp_assoc]
    change (AddMonoidAlgebra.mapDomainAlgHom R K (red r m)).comp
      (((AddMonoidAlgebra.mapAlgHom (r → ℤ) ψ₁).comp (AddMonoidAlgebra.mapAlgHom (r → ℤ)
        (IsScalarTower.toAlgHom R C (Localization.Away g₁)))).comp α') = _
    rw [mapAlgHom_comp_mapAlgHom, hψ₁, hψ, d.red_comp_pushα, ← uS_comp d, ← AlgHom.comp_assoc]
  -- inverting `N f`
  have hψe : ψ₁ (w₁ (d.N * d.f)) ≠ 0 := by
    have := congrArg (fun F => F (d.N * d.f)) hwy
    simp only [AlgHom.comp_apply] at this
    rw [this]
    exact ((isUnit_algebraMap_Bf_N_mul_f G d).map yK).ne_zero
  obtain ⟨w₂, k, hw₂⟩ := exists_numerator g₁ (w₁ (d.N * d.f))
  have hψw₂ : ψ w₂ ≠ 0 := by
    have e := congrArg ψ₁ hw₂
    rw [map_mul, hψ₁', hψ₁', map_pow] at e
    rw [← e]
    exact mul_ne_zero hψe (pow_ne_zero _ hψg₁)
  obtain ⟨ρ, hρ⟩ := exists_away_dvd (R := R) g₁ w₂
  have hρ' : ∀ x, ρ (algebraMap C (Localization.Away g₁) x) =
      algebraMap C (Localization.Away (g₁ * w₂)) x := fun x => congrArg (fun F => F x) hρ
  let w := ρ.comp w₁
  have hwNf : IsUnit (w (d.N * d.f)) := by
    have e := congrArg ρ hw₂
    rw [map_mul, hρ', hρ'] at e
    have hu : IsUnit (algebraMap C (Localization.Away (g₁ * w₂)) w₂) :=
      isUnit_of_dvd_unit (map_dvd _ (dvd_mul_left w₂ g₁))
        (IsLocalization.Away.algebraMap_isUnit _)
    rw [← e] at hu
    exact isUnit_of_mul_isUnit_left hu
  rw [map_mul] at hwNf
  obtain ⟨b₀, hb₀⟩ := exists_factor_away w (isUnit_of_mul_isUnit_left hwNf)
  have hb₀f : IsUnit (b₀ (algebraMap (W R (AffineCoordinates.hopfAlgebra G) r m) d.B d.f)) := by
    have := congrArg (fun F => F d.f) hb₀
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at this
    rw [this]
    exact isUnit_of_mul_isUnit_right hwNf
  obtain ⟨b'', hb''⟩ := exists_factor_away b₀ hb₀f
  have hb''W : b''.comp (IsScalarTower.toAlgHom R (W R (AffineCoordinates.hopfAlgebra G) r m)
      (Bf d)) = w := by
    apply AlgHom.ext
    intro x
    have h1 := congrArg (fun F => F (algebraMap (W R (AffineCoordinates.hopfAlgebra G) r m) d.B x))
      hb''
    have h2 := congrArg (fun F => F x) hb₀
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at h1 h2 ⊢
    rw [IsScalarTower.algebraMap_apply (W R (AffineCoordinates.hopfAlgebra G) r m) d.B (Bf d), h1,
      h2]
  refine ⟨g₁ * w₂, by rw [map_mul]; exact mul_ne_zero hψg₁ hψw₂, b'', ?_⟩
  -- uniqueness of extensions
  have hαg : (AddMonoidAlgebra.mapAlgHom (r → ℤ)
      (IsScalarTower.toAlgHom R C (Localization.Away (g₁ * w₂)))).comp α' =
      (AddMonoidAlgebra.mapAlgHom (r → ℤ) ρ).comp α₁ := by
    rw [← AlgHom.comp_assoc, mapAlgHom_comp_mapAlgHom, hρ]
  have hgs : ∀ i, ↑((pointOf R (AffineCoordinates.hopfAlgebra G) r m w) (gen i)).coeff.support
      ⊆ (red r m) '' (box r n : Set (r → ℤ)) := by
    intro i
    rw [pointOf_comp, AlgHom.comp_apply, hw₁p, AlgHom.comp_apply]
    exact (support_mapAlgHom_subset ρ _).trans (support_mapDomainAlgHom_subset (R := R) (red r m)
      (hsupp₁ i))
  obtain ⟨_, -, huniq⟩ := existsUnique_hopfPoint_extension hP hN₀ (red r m) dw.injOn
    (isHopfPoint_pointOf R _ r m w) hgs
  have h1 := huniq ((AddMonoidAlgebra.mapAlgHom (r → ℤ)
      (IsScalarTower.toAlgHom R C (Localization.Away (g₁ * w₂)))).comp α')
    ⟨HopfPointWindowExtension.IsHopfPoint.mapAlgHom _ hα', by
      intro i
      rw [hαg]
      exact (support_mapAlgHom_subset ρ _).trans (hsupp₁ i), by
      rw [hαg, ← AlgHom.comp_assoc, ← HopfPointWindowExtension.mapAlgHom_comp_mapDomain,
        AlgHom.comp_assoc]
      change (AddMonoidAlgebra.mapAlgHom (r → ZMod m) ρ).comp
        ((AddMonoidAlgebra.mapDomainAlgHom R (Localization.Away g₁) (red r m)).comp α₁) = _
      rw [← hw₁p, ← pointOf_comp]⟩
  have h2 := huniq (d.pushα (b''.comp (uS d)))
    ⟨d.isHopfPoint_pushα _, d.support_pushα _, by
      rw [d.red_comp_pushα, AlgHom.comp_assoc, uS_comp, hb''W]⟩
  rw [h1, h2]

omit [Algebra.FinitePresentation R (AffineCoordinates.hopfAlgebra G)] in
theorem ofGroupAlgebra_toGroupAlgebra {C : Type u} [CommRing C] [Algebra R C] {M : Type u}
    [AddCommGroup M]
    (f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R M) :
    ofGroupAlgebra (HopfPointBridge.toGroupAlgebra f) = f := by
  apply AlgHom.ext
  intro a
  simp [ofGroupAlgebra, HopfPointBridge.toGroupAlgebra]

omit [Algebra.FinitePresentation R (AffineCoordinates.hopfAlgebra G)] in
theorem evaluate_comp_of_eq_range {T : Over (Spec (CommRingCat.of R))} {L : GroupScheme T.left}
    (i : L ⟶ (GroupScheme.baseChange T.hom).obj G) {C D : Type u} [CommRing C] [Algebra R C]
    [CommRing D] [Algebra R D] (bk : FiniteSource.specOver R C ⟶ T) {I : Type u} [Fintype I]
    [DecidableEq I]
    (fk : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R (I → ℤ) //
      FiniteBialgebraHom.IsHopfPoint R f})
    (hev : TorusSubgroupModuli.evaluate i bk =
      SubgroupFunctor.range ((SplitTorusPoint.splitPointEquiv G C).symm fk))
    (g : C →ₐ[R] D) :
    TorusSubgroupModuli.evaluate i (FiniteSource.specMap g ≫ bk) =
      SubgroupFunctor.range ((SplitTorusPoint.splitPointEquiv G D).symm
        ⟨FiniteBialgebraHom.pushPoint R g fk.1, fk.2.pushPoint R g⟩) := by
  have h1 := TorusSubgroupModuli.evaluate_eq_comp i ((SplitTorusPoint.splitPointEquiv G C).symm fk)
    bk (𝟙 _) (hev.trans (TorusSubgroupModuli.evaluate_id _).symm) (FiniteSource.specMap g)
  rw [Category.comp_id] at h1
  rw [h1, SplitTorusPoint.evaluate_splitPointEquiv_symm_eq_range]

set_option maxHeartbeats 1000000 in
/-- The window torus on an étale piece of a splitting, near a point where it agrees with the
torus to be parametrized. -/
theorem exists_piece_lift {V : Submodule R (AffineCoordinates.hopfAlgebra G)} [Module.Finite R V]
    {δ : V →ₗ[R] V ⊗[R] AffineCoordinates.hopfAlgebra G} (hδ : IsCoassoc δ)
    (hι : (Coalgebra.comul (R := R) (A := AffineCoordinates.hopfAlgebra G)) ∘ₗ V.subtype =
      V.subtype.rTensor _ ∘ₗ δ)
    (hgenV : ∀ i, gen i ∈ V) {N₀ : ℕ} (hP : IsBoundedPresentation (R := R) gen N₀)
    (hN₀ : 1 ≤ N₀) (dw : WindowDatum R (AffineCoordinates.hopfAlgebra G) r m gen n V δ N₀)
    {T : Over (Spec (CommRingCat.of R))} {L : GroupScheme T.left}
    (i : L ⟶ (GroupScheme.baseChange T.hom).obj G) {C : Type u} [CommRing C] [Algebra R C]
    (bk : FiniteSource.specOver R C ⟶ T) {I : Type u} [Fintype I] [DecidableEq I]
    (fk : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R (I → ℤ) //
      FiniteBialgebraHom.IsHopfPoint R f})
    (hfk : Function.Surjective (AlgHom.liftEquiv R C _ _ fk.1))
    (hev : TorusSubgroupModuli.evaluate i bk =
      SubgroupFunctor.range ((SplitTorusPoint.splitPointEquiv G C).symm fk))
    {K : Type u} [Field K] [Algebra R K] (x' : C →ₐ[R] K) (y' : Bf dw.toDatum →ₐ[R] K)
    (hK : SubgroupFunctor.range ((SplitTorusPoint.splitPointEquiv G K).symm
        ⟨FiniteBialgebraHom.pushPoint R x' fk.1, fk.2.pushPoint R x'⟩) =
      SubgroupFunctor.range ((SplitTorusPoint.splitPointEquiv G K).symm
        ⟨FiniteBialgebraHom.pushPoint R y' (fS G dw.toDatum).1,
          (fS G dw.toDatum).2.pushPoint R y'⟩)) :
    ∃ g : C, x' g ≠ 0 ∧ ∃ b'' : Bf dw.toDatum →ₐ[R] Localization.Away g,
      TorusSubgroupModuli.evaluate i
          (FiniteSource.specMap (IsScalarTower.toAlgHom R C (Localization.Away g)) ≫ bk) =
        TorusSubgroupModuli.evaluate (j G dw.toDatum)
          (FiniteSource.specMap b'' ≫ pOver dw.toDatum) := by
  let d := dw.toDatum
  have hsurjPush : ∀ {D : Type u} [CommRing D] [Algebra R D] (g : C →ₐ[R] D),
      Function.Surjective (AlgHom.liftEquiv R D _ _ (FiniteBialgebraHom.pushPoint R g fk.1)) := by
    intro D _ _ g
    rw [surjective_liftEquiv_iff, HopfPointBridge.toGroupAlgebra_pushPoint]
    exact surjective_scalarExt_mapAlgHom g ((surjective_liftEquiv_iff fk.1).mp hfk)
  obtain ⟨T, hT⟩ := exists_twist_of_range_eq G d
    ⟨FiniteBialgebraHom.pushPoint R x' fk.1, fk.2.pushPoint R x'⟩ (hsurjPush x') y' hK
  let α' := (AddMonoidAlgebra.mapDomainAlgHom R C T.toAddMonoidHom).comp
    (HopfPointBridge.toGroupAlgebra fk.1)
  have hα' : IsHopfPoint α' :=
    ((HopfPointBridge.isHopfPoint_iff fk.1).mp fk.2).mapDomain T.toAddMonoidHom
  have hpush : ∀ {D : Type u} [CommRing D] [Algebra R D] (g : C →ₐ[R] D),
      (AddMonoidAlgebra.mapAlgHom (r → ℤ) g).comp α' =
        (AddMonoidAlgebra.mapDomainAlgHom R D T.toAddMonoidHom).comp
          (HopfPointBridge.toGroupAlgebra (FiniteBialgebraHom.pushPoint R g fk.1)) := by
    intro D _ _ g
    rw [HopfPointBridge.toGroupAlgebra_pushPoint, ← AlgHom.comp_assoc,
      HopfPointWindowExtension.mapAlgHom_comp_mapDomain, AlgHom.comp_assoc]
  obtain ⟨g, hg, b'', hb''⟩ := exists_local_lift G hδ hι hgenV hP hN₀ dw hα' x' y'
    (by rw [hpush]; exact hT)
  refine ⟨g, hg, b'', ?_⟩
  rw [evaluate_comp_of_eq_range G i bk fk hev, range_twist_eq G
    ⟨FiniteBialgebraHom.pushPoint R (IsScalarTower.toAlgHom R C (Localization.Away g)) fk.1,
      fk.2.pushPoint R _⟩ (hsurjPush _) T, evaluate_j_comp_pOver, evaluate_iS_specMap]
  have hpt : (⟨ofGroupAlgebra ((AddMonoidAlgebra.mapDomainAlgHom R (Localization.Away g)
      T.toAddMonoidHom).comp (HopfPointBridge.toGroupAlgebra (FiniteBialgebraHom.pushPoint R
        (IsScalarTower.toAlgHom R C (Localization.Away g)) fk.1))), isHopfPoint_ofGroupAlgebra
          (((HopfPointBridge.isHopfPoint_iff _).mp (fk.2.pushPoint R _)).mapDomain
            T.toAddMonoidHom)⟩ :
      {f : AffineCoordinates.hopfAlgebra G →ₐ[R] Localization.Away g ⊗[R]
        AddMonoidAlgebra R (r → ℤ) // FiniteBialgebraHom.IsHopfPoint R f}) =
      ⟨FiniteBialgebraHom.pushPoint R b'' (fS G d).1, (fS G d).2.pushPoint R b''⟩ := by
    apply Subtype.ext
    change ofGroupAlgebra _ = _
    rw [← hpush, hb'', ← toGroupAlgebra_pushPoint_fS G d b'', ofGroupAlgebra_toGroupAlgebra]
  rw [hpt]

/-- The core of openness: every point of the image of a test admitting a parameter has an open
neighbourhood admitting a parameter. -/
theorem exists_good_open (hP3 : EtaleSplitStatement.{u})
    {V : Submodule R (AffineCoordinates.hopfAlgebra G)} [Module.Finite R V]
    {δ : V →ₗ[R] V ⊗[R] AffineCoordinates.hopfAlgebra G} (hδ : IsCoassoc δ)
    (hι : (Coalgebra.comul (R := R) (A := AffineCoordinates.hopfAlgebra G)) ∘ₗ V.subtype =
      V.subtype.rTensor _ ∘ₗ δ)
    (hgenV : ∀ i, gen i ∈ V) {N₀ : ℕ} (hP : IsBoundedPresentation (R := R) gen N₀)
    (hN₀ : 1 ≤ N₀) (dw : WindowDatum R (AffineCoordinates.hopfAlgebra G) r m gen n V δ N₀)
    {T : Over (Spec (CommRingCat.of R))} (hT : IsAffine T.left) {L : GroupScheme T.left}
    (i : L ⟶ (GroupScheme.baseChange T.hom).obj G) (hi : IsClosedSubgroup i)
    (hL : RelativeTorus.IsTorus L) {T' : Over (Spec (CommRingCat.of R))} (b : T' ⟶ T)
    (a : T' ⟶ U dw.toDatum)
    (hab : TorusSubgroupModuli.evaluate (j G dw.toDatum) a = TorusSubgroupModuli.evaluate i b)
    (t' : T'.left) :
    ∃ W : T.left.Opens, b.left t' ∈ W ∧ ∃ aW : Over.mk (W.ι ≫ T.hom) ⟶ U dw.toDatum,
      TorusSubgroupModuli.evaluate (j G dw.toDatum) aW =
        TorusSubgroupModuli.evaluate i (Over.homMk W.ι rfl : Over.mk (W.ι ≫ T.hom) ⟶ T) := by
  let d := dw.toDatum
  obtain ⟨nk, C, _, _, bk, I, _, _, f, hEt, hcov, hsurj, hev⟩ := @hP3 R _ G _ T hT L i hi hL
  obtain ⟨k, z, hz⟩ := hcov (b.left t')
  -- the common field point
  obtain ⟨q, hq₁, hq₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := (bk k).left)
    (g := b.left) z t' hz
  let a₁ := pullback.snd (bk k).left b.left ≫ a.left
  obtain ⟨s', hs'⟩ := (inferInstance : Surjective (p d)).surj (a₁ q)
  obtain ⟨q₂, hq₂₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := a₁) (g := p d) q s'
    hs'.symm
  let P2 := pullback a₁ (p d)
  let K := P2.residueField q₂
  let ξ := P2.fromSpecResidueField q₂
  let xs : Spec K ⟶ (FiniteSource.specOver R (C k)).left :=
    ξ ≫ pullback.fst a₁ (p d) ≫ pullback.fst (bk k).left b.left
  let x's : Spec K ⟶ T'.left := ξ ≫ pullback.fst a₁ (p d) ≫ pullback.snd (bk k).left b.left
  let ys : Spec K ⟶ (S d).left := ξ ≫ pullback.snd a₁ (p d)
  have h1 : xs ≫ (bk k).left = x's ≫ b.left := by
    simp only [xs, x's, Category.assoc, pullback.condition]
  have h2 : x's ≫ a.left = ys ≫ p d := by
    simp only [x's, ys, Category.assoc]
    exact congrArg (ξ ≫ ·) (pullback.condition (f := a₁) (g := p d))
  -- the algebra structure on the field
  let φK : CommRingCat.of R ⟶ K := Spec.preimage (xs ≫ (FiniteSource.specOver R (C k)).hom)
  let : Algebra R K := φK.hom.toAlgebra
  have hKhom : (FiniteSource.specOver R K).hom = xs ≫ (FiniteSource.specOver R (C k)).hom := by
    change Spec.map (CommRingCat.ofHom φK.hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let xO : FiniteSource.specOver R K ⟶ FiniteSource.specOver R (C k) :=
    Over.homMk xs hKhom.symm
  let x'O : FiniteSource.specOver R K ⟶ T' := Over.homMk x's (by
    change x's ≫ T'.hom = (FiniteSource.specOver R K).hom
    rw [hKhom, ← Over.w b, ← Category.assoc, ← h1, Category.assoc, Over.w (bk k)])
  let yO : FiniteSource.specOver R K ⟶ S d := Over.homMk ys (by
    change ys ≫ (S d).hom = (FiniteSource.specOver R K).hom
    rw [← p_qR, ← Category.assoc, ← h2, Category.assoc]
    change x's ≫ a.left ≫ (U d).hom = _
    rw [Over.w a]
    exact Over.w x'O)
  have hxb : xO ≫ bk k = x'O ≫ b := Over.OverMorphism.ext h1
  have hxa : x'O ≫ a = yO ≫ pOver d := Over.OverMorphism.ext h2
  have hevK : TorusSubgroupModuli.evaluate i (xO ≫ bk k) =
      TorusSubgroupModuli.evaluate (iS G d) yO := by
    rw [hxb, ← TorusSubgroupModuli.evaluate_eq_comp (j G d) i a b hab x'O, hxa,
      evaluate_j_comp_pOver]
  let x' := FiniteSource.specOverHomEquiv xO
  let y' := FiniteSource.specOverHomEquiv yO
  have hx' : FiniteSource.specMap x' = xO := FiniteSource.specOverHomEquiv.symm_apply_apply _
  have hy' : FiniteSource.specMap y' = yO := FiniteSource.specOverHomEquiv.symm_apply_apply _
  have hK : SubgroupFunctor.range ((SplitTorusPoint.splitPointEquiv G K).symm
        ⟨FiniteBialgebraHom.pushPoint R x' (f k).1, (f k).2.pushPoint R x'⟩) =
      SubgroupFunctor.range ((SplitTorusPoint.splitPointEquiv G K).symm
        ⟨FiniteBialgebraHom.pushPoint R y' (fS G d).1, (fS G d).2.pushPoint R y'⟩) := by
    rw [← evaluate_comp_of_eq_range G i (bk k) (f k) (hev k) x', ← evaluate_iS_specMap, hx', hy']
    exact hevK
  obtain ⟨g, hg, b'', heq⟩ := exists_piece_lift G hδ hι hgenV hP hN₀ dw i (bk k) (f k) (hsurj k)
    (hev k) x' y' hK
  -- the étale piece and the point
  let e : FiniteSource.specOver R (Localization.Away g) ⟶ T :=
    FiniteSource.specMap (IsScalarTower.toAlgHom R (C k) (Localization.Away g)) ≫ bk k
  have : Etale e.left := by
    have := hEt k
    change Etale (Spec.map (CommRingCat.ofHom (algebraMap (C k) (Localization.Away g))) ≫
      (bk k).left)
    infer_instance
  have ht : b.left t' ∈ Set.range e.left.base := by
    obtain ⟨x'', hx''⟩ := exists_lift_away x' hg
    have hxs : xs = (FiniteSource.specMap x'').left ≫
        (FiniteSource.specMap (IsScalarTower.toAlgHom R (C k) (Localization.Away g))).left := by
      have e0 : xs = (FiniteSource.specMap x').left := by rw [hx']; rfl
      rw [e0]
      change Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← hx'']
      rfl
    let pt : Spec K := default
    refine ⟨(FiniteSource.specMap x'').left pt, ?_⟩
    have e0' : ξ pt = q₂ := Scheme.fromSpecResidueField_apply q₂ pt
    have e1 : x's pt = t' := by
      change pullback.snd (bk k).left b.left (pullback.fst a₁ (p d) (ξ pt)) = t'
      rw [e0', hq₂₁, hq₂]
    have e2 : (FiniteSource.specMap x'').left ≫ e.left = x's ≫ b.left := by
      rw [← h1, hxs]
      simp only [e, Over.comp_left, Category.assoc]
    rw [← e1]
    exact congrArg (fun F => F pt) e2
  obtain ⟨W, htW, aW, haW⟩ := exists_good_open_of_etale (j G d) (isClosedSubgroup_j G d)
    (injective_affine G d) i hi hT (𝟙 T) (inferInstanceAs (IsAffine (Spec _))) e
    (FiniteSource.specMap b'' ≫ pOver d) (by rw [Category.comp_id]; exact heq.symm) (b.left t') ht
  refine ⟨W, htW, aW, ?_⟩
  rw [haW, Category.comp_id]

/-- The openness condition of an open chart, on affine targets. -/
theorem isOpen_affine (hP3 : EtaleSplitStatement.{u})
    {V : Submodule R (AffineCoordinates.hopfAlgebra G)} [Module.Finite R V]
    {δ : V →ₗ[R] V ⊗[R] AffineCoordinates.hopfAlgebra G} (hδ : IsCoassoc δ)
    (hι : (Coalgebra.comul (R := R) (A := AffineCoordinates.hopfAlgebra G)) ∘ₗ V.subtype =
      V.subtype.rTensor _ ∘ₗ δ)
    (hgenV : ∀ i, gen i ∈ V) {N₀ : ℕ} (hP : IsBoundedPresentation (R := R) gen N₀)
    (hN₀ : 1 ≤ N₀) (dw : WindowDatum R (AffineCoordinates.hopfAlgebra G) r m gen n V δ N₀)
    (T : Over (Spec (CommRingCat.of R))) (hT : IsAffine T.left) (L : GroupScheme T.left)
    (i : L ⟶ (GroupScheme.baseChange T.hom).obj G) (hi : IsClosedSubgroup i)
    (hL : RelativeTorus.IsTorus L) :
    ∃ V' : T.left.Opens, ∀ (T' : Over (Spec (CommRingCat.of R))) (b : T' ⟶ T),
      ((∃ a : T' ⟶ U dw.toDatum,
        TorusSubgroupModuli.evaluate (j G dw.toDatum) a = TorusSubgroupModuli.evaluate i b) ↔
        Set.range b.left.base ⊆ V') := by
  let d := dw.toDatum
  let good : T.left.Opens → Prop := fun W => ∃ aW : Over.mk (W.ι ≫ T.hom) ⟶ U d,
    TorusSubgroupModuli.evaluate (j G d) aW =
      TorusSubgroupModuli.evaluate i (Over.homMk W.ι rfl : Over.mk (W.ι ≫ T.hom) ⟶ T)
  refine ⟨⨆ W : {W // good W}, W.1, fun T' b => ⟨?_, ?_⟩⟩
  · rintro ⟨a, ha⟩ _ ⟨t', rfl⟩
    obtain ⟨W, hW, hgood⟩ := exists_good_open G hP3 hδ hι hgenV hP hN₀ dw hT i hi hL b a ha t'
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hgood⟩, hW⟩
  · intro hsub
    have hpt : ∀ t' : T'.left, ∃ W : {W // good W}, b.left t' ∈ W.1 := fun t' =>
      TopologicalSpace.Opens.mem_iSup.mp (hsub ⟨t', rfl⟩)
    choose Wt hWt using hpt
    let Ucov : T'.left → T'.left.Opens := fun t' => b.left ⁻¹ᵁ (Wt t').1
    have hcov : TopologicalSpace.IsOpenCover Ucov := by
      rw [TopologicalSpace.IsOpenCover, eq_top_iff]
      intro x _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hWt x⟩
    let 𝒰 := T'.left.openCoverOfIsOpenCover Ucov hcov
    apply exists_evaluate_of_openCover (j G d) (isClosedSubgroup_j G d)
      (fun T hT a b h => injective_affine G d T hT a b h) i hi b 𝒰
    intro t'
    obtain ⟨aW, haW⟩ := (Wt t').2
    let W := (Wt t').1
    have hrange : Set.range ((Ucov t').ι ≫ b.left).base ⊆ Set.range W.ι.base := by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact x.2
    let c := IsOpenImmersion.lift W.ι ((Ucov t').ι ≫ b.left) hrange
    have hc : c ≫ W.ι = (Ucov t').ι ≫ b.left := IsOpenImmersion.lift_fac _ _ _
    let cO : SubgroupFunctor.coverObj 𝒰 t' ⟶ Over.mk (W.ι ≫ T.hom) := Over.homMk c (by
      change c ≫ W.ι ≫ T.hom = (Ucov t').ι ≫ T'.hom
      rw [← Category.assoc, hc, Category.assoc, Over.w b])
    refine ⟨cO ≫ aW, ?_⟩
    rw [TorusSubgroupModuli.evaluate_eq_comp (j G d) i aW _ haW cO]
    congr 1
    exact Over.OverMorphism.ext hc

/-- Smoothness of the chart from smoothness of the representing algebra. -/
theorem smooth_qR_of_algebraSmooth
    [Algebra.Smooth R (W R (AffineCoordinates.hopfAlgebra G) r m)]
    (d : Datum R (AffineCoordinates.hopfAlgebra G) r m gen n) : Smooth (qR d) := by
  apply smooth_qR
  rw [HasRingHomProperty.Spec_iff (P := @Smooth), CommRingCat.hom_ofHom, RingHom.smooth_algebraMap]
  infer_instance

/-- A window chart datum is an open chart on affine tests. -/
theorem isOpenChartOnAffines (hP3 : EtaleSplitStatement.{u})
    [Algebra.Smooth R (W R (AffineCoordinates.hopfAlgebra G) r m)]
    {V : Submodule R (AffineCoordinates.hopfAlgebra G)} [Module.Finite R V]
    {δ : V →ₗ[R] V ⊗[R] AffineCoordinates.hopfAlgebra G} (hδ : IsCoassoc δ)
    (hι : (Coalgebra.comul (R := R) (A := AffineCoordinates.hopfAlgebra G)) ∘ₗ V.subtype =
      V.subtype.rTensor _ ∘ₗ δ)
    (hgenV : ∀ i, gen i ∈ V) {N₀ : ℕ} (hP : IsBoundedPresentation (R := R) gen N₀)
    (hN₀ : 1 ≤ N₀) (dw : WindowDatum R (AffineCoordinates.hopfAlgebra G) r m gen n V δ N₀) :
    IsOpenChartOnAffines (j G dw.toDatum) where
  isClosedSubgroup := isClosedSubgroup_j G dw.toDatum
  isTorus := isTorus_K G dw.toDatum
  smooth := smooth_qR_of_algebraSmooth G dw.toDatum
  injective := fun T hT a b h => injective_affine G dw.toDatum T hT a b h
  isOpen := fun T hT L i hi hL => by
    obtain ⟨V', hV'⟩ := isOpen_affine G hP3 hδ hι hgenV hP hN₀ dw T hT L i hi hL
    exact ⟨V', fun T' b _ => hV' T' b⟩

end Local

end Langlands.GroupScheme.HomScheme.TorusChart
