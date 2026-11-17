import Langlands.GroupScheme.HomScheme.MultiplicativeTypeChartInjective
import Langlands.GroupScheme.HomScheme.FppfParameterDescent
import Langlands.GroupScheme.HomScheme.MultiplicativeTypeSubgroupChartAffineTests
import Langlands.Algebra.MixedChartExistence

/-! # Openness of multiplicative-type charts on affine tests -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.HomScheme.MultiplicativeTypeChart

open Langlands.Algebra Langlands.Algebra.MixedChartRing Langlands.Algebra.MixedChartAlgebra
  Langlands.AlgebraicGeometry DiagonalizablePoint

/-- fppf-local splitting of a closed multiplicative-type subgroup over an affine test into
closed diagonalizable Hopf points. -/
def FppfSplitStatement : Prop :=
  ∀ {R : Type u} [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
    {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left] {L : GroupScheme T.left}
    (i : L ⟶ (GroupScheme.baseChange T.hom).obj G), IsClosedSubgroup i →
    RelativeMultiplicativeType.IsMultiplicativeType L →
    ∃ (n : ℕ) (C : Fin n → Type u) (_ : ∀ k, CommRing (C k)) (_ : ∀ k, Algebra R (C k))
      (b : ∀ k, FiniteSource.specOver R (C k) ⟶ T) (Λ : Fin n → Type u)
      (_ : ∀ k, AddCommGroup (Λ k)) (_ : ∀ k, AddGroup.FG (Λ k))
      (f : ∀ k, {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C k ⊗[R]
        AddMonoidAlgebra R (Λ k) // FiniteBialgebraHom.IsHopfPoint R f}),
      (∀ k, Flat (b k).left) ∧ (∀ k, LocallyOfFinitePresentation (b k).left) ∧
      (∀ t : T.left, ∃ k, t ∈ Set.range (b k).left.base) ∧
      (∀ k, Function.Surjective (AlgHom.liftEquiv R (C k) _ _ (f k).1)) ∧
      ∀ k, TorusSubgroupModuli.evaluate i (b k) =
        SubgroupFunctor.range ((diagPointEquiv G (C k)).symm (f k))

section Generic

open HopfPointClosedLocus HopfPointWeightWindow HopfPointWeightLocus HopfPointExtension
  MixedLatticeConfiguration TorusChartExistence

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [HopfAlgebra R A]
  [Algebra.FinitePresentation R A] {r : Type u} [Fintype r] [DecidableEq r]
  {F : Type u} [AddCommGroup F] [Fintype F] {m : ℕ} [NeZero m]
  {σ' : Type u} {gen : σ' → A} {n : ℕ}

local notation "Lb" => (r → ZMod m) × F
local notation "Λ₀" => (r → ℤ) × F

theorem toAlgHom_W_Bf (d : Datum R A r F m gen n) :
    IsScalarTower.toAlgHom R (W R A Lb) (Bf d) =
      (IsScalarTower.toAlgHom R d.B (Bf d)).comp (IsScalarTower.toAlgHom R (W R A Lb) d.B) := by
  apply AlgHom.ext
  intro w
  exact IsScalarTower.algebraMap_apply _ d.B (Bf d) w

theorem isUnit_algebraMap_Bf_N_mul_f (d : Datum R A r F m gen n) :
    IsUnit (algebraMap (W R A Lb) (Bf d) (d.N * d.f)) := by
  rw [IsScalarTower.algebraMap_apply _ d.B (Bf d), map_mul, map_mul]
  exact ((IsLocalization.Away.algebraMap_isUnit d.N).map (algebraMap d.B (Bf d))).mul
    (IsLocalization.Away.algebraMap_isUnit _)

set_option maxHeartbeats 1000000 in
/-- Openness of the chart locus at a point of an fppf splitting: a closed diagonalizable Hopf
point of type `ℤ^r × F` which agrees with the window subgroup at a field point is the window
subgroup over a principal open around that point. -/
theorem exists_local_lift {V : Submodule R A} [Module.Finite R V]
    {δ : V →ₗ[R] V ⊗[R] A} (hδ : IsCoassoc δ)
    (hι : (Coalgebra.comul (R := R) (A := A)) ∘ₗ V.subtype =
      V.subtype.rTensor _ ∘ₗ δ)
    (hgenV : ∀ i, gen i ∈ V) {N₀ : ℕ} (hP : IsBoundedPresentation (R := R) gen N₀)
    (hN₀ : 1 ≤ N₀) (dw : MixedChartExistence.WindowDatum R A r F m gen n V δ N₀)
    {C : Type u} [CommRing C] [Algebra R C]
    {α' : A →ₐ[R] AddMonoidAlgebra C Λ₀}
    (hα' : IsHopfPoint α') {K : Type u} [Field K] [Algebra R K] (ψ : C →ₐ[R] K)
    (yK : Bf dw.toDatum →ₐ[R] K)
    (hψ : (AddMonoidAlgebra.mapAlgHom Λ₀ ψ).comp α' =
      dw.toDatum.pushα (yK.comp (uS dw.toDatum))) :
    ∃ g : C, ψ g ≠ 0 ∧ ∃ b'' : Bf dw.toDatum →ₐ[R] Localization.Away g,
      (AddMonoidAlgebra.mapAlgHom Λ₀ (IsScalarTower.toAlgHom R C (Localization.Away g))).comp
        α' = dw.toDatum.pushα (b''.comp (uS dw.toDatum)) := by
  classical
  let d := dw.toDatum
  -- weights at the field point
  have hwK : WeightsIn δ ((AddMonoidAlgebra.mapAlgHom Λ₀ ψ).comp α')
      (mbox r F n : Set Λ₀) := by
    rw [hψ]
    exact weightsIn_mapAlgHom δ _ dw.weights
  obtain ⟨hP₁, ι₁, hι₁⟩ := exists_residueLift ψ
  have hw₁ : WeightsIn δ ((AddMonoidAlgebra.mapAlgHom Λ₀
      (IsScalarTower.toAlgHom R C (RingHom.ker ψ).ResidueField)).comp α')
      (mbox r F n : Set Λ₀) := by
    apply weightsIn_of_mapAlgHom δ ι₁ (rTensor_injective_of_field ι₁)
    rw [← AlgHom.comp_assoc, mapAlgHom_comp_mapAlgHom, hι₁]
    exact hwK
  obtain ⟨g₁, hg₁, hW₁⟩ := exists_away_weightsIn δ hδ hα' (mbox r F n : Set Λ₀)
    (RingHom.ker ψ) hw₁
  have hψg₁ : ψ g₁ ≠ 0 := fun h => hg₁ (by simpa [RingHom.mem_ker] using h)
  let α₁ := (AddMonoidAlgebra.mapAlgHom Λ₀
    (IsScalarTower.toAlgHom R C (Localization.Away g₁))).comp α'
  have hα₁ : IsHopfPoint α₁ := HopfPointWindowExtension.IsHopfPoint.mapAlgHom _ hα'
  have hsupp₁ : ∀ i, ↑(α₁ (gen i)).coeff.support ⊆ (mbox r F n : Set Λ₀) := fun i =>
    support_subset_of_weightsIn δ α₁ hW₁ V.subtype hι ⟨gen i, hgenV i⟩
  -- the point of `W`
  obtain ⟨w₁, hw₁p⟩ := MixedChartExistence.exists_point_of_hopfPoint (A := A) (L := Lb)
    (hα₁.mapDomain (mred r F m))
  obtain ⟨ψ₁, hψ₁⟩ := exists_lift_away ψ hψg₁
  have hψ₁' : ∀ x, ψ₁ (algebraMap C (Localization.Away g₁) x) = ψ x :=
    fun x => congrArg (fun φ => φ x) hψ₁
  have hwy : ψ₁.comp w₁ = yK.comp (IsScalarTower.toAlgHom R
      (W R A Lb) (Bf d)) := by
    apply pointOf_injective
    rw [pointOf_comp, hw₁p, ← AlgHom.comp_assoc, HopfPointWindowExtension.mapAlgHom_comp_mapDomain,
      AlgHom.comp_assoc]
    change (AddMonoidAlgebra.mapDomainAlgHom R K (mred r F m)).comp
      (((AddMonoidAlgebra.mapAlgHom Λ₀ ψ₁).comp (AddMonoidAlgebra.mapAlgHom Λ₀
        (IsScalarTower.toAlgHom R C (Localization.Away g₁)))).comp α') = _
    rw [mapAlgHom_comp_mapAlgHom, hψ₁, hψ, d.red_comp_pushα, ← uS_comp d, ← AlgHom.comp_assoc]
  -- inverting `N f`
  have hψe : ψ₁ (w₁ (d.N * d.f)) ≠ 0 := by
    have := congrArg (fun φ => φ (d.N * d.f)) hwy
    simp only [AlgHom.comp_apply] at this
    rw [this]
    exact ((isUnit_algebraMap_Bf_N_mul_f d).map yK).ne_zero
  obtain ⟨w₂, k, hw₂⟩ := exists_numerator g₁ (w₁ (d.N * d.f))
  have hψw₂ : ψ w₂ ≠ 0 := by
    have e := congrArg ψ₁ hw₂
    rw [map_mul, hψ₁', hψ₁', map_pow] at e
    rw [← e]
    exact mul_ne_zero hψe (pow_ne_zero _ hψg₁)
  obtain ⟨ρ, hρ⟩ := exists_away_dvd (R := R) g₁ w₂
  have hρ' : ∀ x, ρ (algebraMap C (Localization.Away g₁) x) =
      algebraMap C (Localization.Away (g₁ * w₂)) x := fun x => congrArg (fun φ => φ x) hρ
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
  have hb₀f : IsUnit (b₀ (algebraMap (W R A Lb) d.B d.f)) := by
    have := congrArg (fun φ => φ d.f) hb₀
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at this
    rw [this]
    exact isUnit_of_mul_isUnit_right hwNf
  obtain ⟨b'', hb''⟩ := exists_factor_away b₀ hb₀f
  have hb''W : b''.comp (IsScalarTower.toAlgHom R (W R A Lb)
      (Bf d)) = w := by
    apply AlgHom.ext
    intro x
    have h1 := congrArg (fun φ => φ (algebraMap (W R A Lb) d.B x))
      hb''
    have h2 := congrArg (fun φ => φ x) hb₀
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at h1 h2 ⊢
    rw [IsScalarTower.algebraMap_apply (W R A Lb) d.B (Bf d), h1,
      h2]
  refine ⟨g₁ * w₂, by rw [map_mul]; exact mul_ne_zero hψg₁ hψw₂, b'', ?_⟩
  -- uniqueness of extensions
  have hαg : (AddMonoidAlgebra.mapAlgHom Λ₀
      (IsScalarTower.toAlgHom R C (Localization.Away (g₁ * w₂)))).comp α' =
      (AddMonoidAlgebra.mapAlgHom Λ₀ ρ).comp α₁ := by
    rw [← AlgHom.comp_assoc, mapAlgHom_comp_mapAlgHom, hρ]
  have hgs : ∀ i, ↑((pointOf R A Lb w) (gen i)).coeff.support
      ⊆ (mred r F m) '' (mbox r F n : Set Λ₀) := by
    intro i
    rw [pointOf_comp, AlgHom.comp_apply, hw₁p, AlgHom.comp_apply]
    exact (TorusChartRing.support_mapAlgHom_subset ρ _).trans
      (support_mapDomainAlgHom_subset (R := R) (mred r F m)
      (hsupp₁ i))
  obtain ⟨_, -, huniq⟩ := existsUnique_hopfPoint_extension hP hN₀ (mred r F m) dw.injOn
    (isHopfPoint_pointOf R _ Lb w) hgs
  have h1 := huniq ((AddMonoidAlgebra.mapAlgHom Λ₀
      (IsScalarTower.toAlgHom R C (Localization.Away (g₁ * w₂)))).comp α')
    ⟨HopfPointWindowExtension.IsHopfPoint.mapAlgHom _ hα', by
      intro i
      rw [hαg]
      exact (TorusChartRing.support_mapAlgHom_subset ρ _).trans (hsupp₁ i), by
      rw [hαg, ← AlgHom.comp_assoc, ← HopfPointWindowExtension.mapAlgHom_comp_mapDomain,
        AlgHom.comp_assoc]
      change (AddMonoidAlgebra.mapAlgHom Lb ρ).comp
        ((AddMonoidAlgebra.mapDomainAlgHom R (Localization.Away g₁) (mred r F m)).comp α₁) = _
      rw [← hw₁p, ← pointOf_comp]⟩
  have h2 := huniq (d.pushα (b''.comp (uS d)))
    ⟨d.isHopfPoint_pushα _, d.support_pushα _, by
      rw [d.red_comp_pushα, AlgHom.comp_assoc, uS_comp, hb''W]⟩
  rw [h1, h2]

end Generic

section Local

open HopfPointClosedLocus HopfPointWeightWindow HopfPointWeightLocus HopfPointExtension
  MixedLatticeConfiguration TorusChartExistence

variable {R : Type u} [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
  [Algebra.FinitePresentation R (AffineCoordinates.hopfAlgebra G)]
  {r : Type u} [Fintype r] [DecidableEq r] {F : Type u} [AddCommGroup F] [Fintype F]
  {m : ℕ} [NeZero m]
  {σ' : Type u} {gen : σ' → AffineCoordinates.hopfAlgebra G} {n : ℕ}
  (d : Datum R (AffineCoordinates.hopfAlgebra G) r F m gen n)

omit [Algebra.FinitePresentation R (AffineCoordinates.hopfAlgebra G)] [Fintype r] [DecidableEq r]
  [Fintype F] in
/-- Twisting a closed diagonalizable Hopf point by an isomorphism of character groups does not
change the range. -/
theorem range_twist_eq {Λ' : Type u} [AddCommGroup Λ'] {C : Type u} [CommRing C]
    [Algebra R C]
    (f : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R Λ' //
      FiniteBialgebraHom.IsHopfPoint R f})
    (hf : Function.Surjective (AlgHom.liftEquiv R C _ _ f.1)) (T : Λ' ≃+ (r → ℤ) × F) :
    SubgroupFunctor.range ((diagPointEquiv G C).symm f) =
      SubgroupFunctor.range ((diagPointEquiv G C).symm
        ⟨TorusChartRing.ofGroupAlgebra
          ((AddMonoidAlgebra.mapDomainAlgHom R C T.toAddMonoidHom).comp
            (HopfPointBridge.toGroupAlgebra f.1)),
          TorusChartRing.isHopfPoint_ofGroupAlgebra
            (((HopfPointBridge.isHopfPoint_iff f.1).mp f.2).mapDomain T.toAddMonoidHom)⟩) := by
  have hs : Function.Surjective (scalarExt (HopfPointBridge.toGroupAlgebra f.1)) :=
    (TorusChartRing.surjective_liftEquiv_iff f.1).mp hf
  apply (range_diagPointEquiv_symm_eq_iff_ker₂ (G := G) f _ hf ?_).mpr
  · rw [TorusChartRing.ker_liftEquiv, TorusChartRing.ker_liftEquiv,
      TorusChartRing.toGroupAlgebra_ofGroupAlgebra,
      TorusChartRing.ker_scalarExt_mapDomain_addEquiv₂]
  · rw [TorusChartRing.surjective_liftEquiv_iff, TorusChartRing.toGroupAlgebra_ofGroupAlgebra]
    exact TorusChartRing.surjective_scalarExt_mapDomain _ T.surjective hs

/-- Over a field, a closed diagonalizable Hopf point with the same range as the window subgroup
at a point of the window piece is a twist of it. -/
theorem exists_twist_of_range_eq {Λ' : Type u} [AddCommGroup Λ'] {K : Type u} [Field K]
    [Algebra R K]
    (f : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] K ⊗[R] AddMonoidAlgebra R Λ' //
      FiniteBialgebraHom.IsHopfPoint R f})
    (hf : Function.Surjective (AlgHom.liftEquiv R K _ _ f.1)) (b' : Bf d →ₐ[R] K)
    (h : SubgroupFunctor.range ((diagPointEquiv G K).symm f) =
      SubgroupFunctor.range ((diagPointEquiv G K).symm
        ⟨FiniteBialgebraHom.pushPoint R b' (fS G d).1, (fS G d).2.pushPoint R b'⟩)) :
    ∃ T : Λ' ≃+ (r → ℤ) × F, (AddMonoidAlgebra.mapDomainAlgHom R K T.toAddMonoidHom).comp
      (HopfPointBridge.toGroupAlgebra f.1) = d.pushα (b'.comp (uS d)) := by
  have hker : RingHom.ker (AlgHom.liftEquiv R K _ _ f.1) =
      RingHom.ker (AlgHom.liftEquiv R K _ _ (FiniteBialgebraHom.pushPoint R b' (fS G d).1)) :=
    (range_diagPointEquiv_symm_eq_iff_ker₂ (G := G) (Λ := Λ') (Λ' := (r → ℤ) × F) f
      ⟨FiniteBialgebraHom.pushPoint R b' (fS G d).1, (fS G d).2.pushPoint R b'⟩ hf
      (surjective_pushPoint_fS G d b')).mp h
  have hker' : RingHom.ker (scalarExt (HopfPointBridge.toGroupAlgebra f.1)) =
      RingHom.ker (scalarExt (d.pushα (b'.comp (uS d)))) := by
    rw [← TorusChartRing.ker_liftEquiv]
    ext x
    rw [RingHom.mem_ker, RingHom.mem_ker, ← liftEquiv_pushPoint_fS_eq_zero_iff G d b',
      ← RingHom.mem_ker, ← RingHom.mem_ker, hker]
  have hs : Function.Surjective (scalarExt (HopfPointBridge.toGroupAlgebra f.1)) :=
    (TorusChartRing.surjective_liftEquiv_iff f.1).mp hf
  obtain ⟨τ, hτ⟩ := HopfPointConnected.exists_tau_of_ker_le hs hker'.le
  obtain ⟨τ', hτ'⟩ := HopfPointConnected.exists_tau_of_ker_le (d.surjective_pushα _) hker'.ge
  exact HopfPointConnected.exists_addEquiv_of_comp
    HopfPointConnected.isIdempotentElem_eq_zero_or_one_of_isLocalRing
    ((HopfPointBridge.isHopfPoint_iff f.1).mp f.2) (d.isHopfPoint_pushα _) hs
    (d.surjective_pushα _) τ τ' hτ hτ'

omit [Algebra.FinitePresentation R (AffineCoordinates.hopfAlgebra G)] in
theorem evaluate_comp_of_eq_range {T : Over (Spec (CommRingCat.of R))} {L : GroupScheme T.left}
    (i : L ⟶ (GroupScheme.baseChange T.hom).obj G) {C D : Type u} [CommRing C] [Algebra R C]
    [CommRing D] [Algebra R D] (bk : FiniteSource.specOver R C ⟶ T) {Λ' : Type u} [AddCommGroup Λ']
    (fk : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R Λ' //
      FiniteBialgebraHom.IsHopfPoint R f})
    (hev : TorusSubgroupModuli.evaluate i bk =
      SubgroupFunctor.range ((diagPointEquiv G C).symm fk))
    (g : C →ₐ[R] D) :
    TorusSubgroupModuli.evaluate i (FiniteSource.specMap g ≫ bk) =
      SubgroupFunctor.range ((diagPointEquiv G D).symm
        ⟨FiniteBialgebraHom.pushPoint R g fk.1, fk.2.pushPoint R g⟩) := by
  have h1 := TorusSubgroupModuli.evaluate_eq_comp i ((diagPointEquiv G C).symm fk)
    bk (𝟙 _) (hev.trans (TorusSubgroupModuli.evaluate_id _).symm) (FiniteSource.specMap g)
  rw [Category.comp_id] at h1
  rw [h1, evaluate_diagPointEquiv_symm_eq_range]

set_option maxHeartbeats 1000000 in
/-- The window subgroup on a flat piece of a splitting, near a point where it agrees with the
subgroup to be parametrized. -/
theorem exists_piece_lift {V : Submodule R (AffineCoordinates.hopfAlgebra G)} [Module.Finite R V]
    {δ : V →ₗ[R] V ⊗[R] AffineCoordinates.hopfAlgebra G} (hδ : IsCoassoc δ)
    (hι : (Coalgebra.comul (R := R) (A := AffineCoordinates.hopfAlgebra G)) ∘ₗ V.subtype =
      V.subtype.rTensor _ ∘ₗ δ)
    (hgenV : ∀ i, gen i ∈ V) {N₀ : ℕ} (hP : IsBoundedPresentation (R := R) gen N₀)
    (hN₀ : 1 ≤ N₀)
    (dw : MixedChartExistence.WindowDatum R (AffineCoordinates.hopfAlgebra G) r F m gen n V δ N₀)
    {T : Over (Spec (CommRingCat.of R))} {L : GroupScheme T.left}
    (i : L ⟶ (GroupScheme.baseChange T.hom).obj G) {C : Type u} [CommRing C] [Algebra R C]
    (bk : FiniteSource.specOver R C ⟶ T) {Λ' : Type u} [AddCommGroup Λ']
    (fk : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R Λ' //
      FiniteBialgebraHom.IsHopfPoint R f})
    (hfk : Function.Surjective (AlgHom.liftEquiv R C _ _ fk.1))
    (hev : TorusSubgroupModuli.evaluate i bk =
      SubgroupFunctor.range ((diagPointEquiv G C).symm fk))
    {K : Type u} [Field K] [Algebra R K] (x' : C →ₐ[R] K) (y' : Bf dw.toDatum →ₐ[R] K)
    (hK : SubgroupFunctor.range ((diagPointEquiv G K).symm
        ⟨FiniteBialgebraHom.pushPoint R x' fk.1, fk.2.pushPoint R x'⟩) =
      SubgroupFunctor.range ((diagPointEquiv G K).symm
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
    rw [TorusChartRing.surjective_liftEquiv_iff, HopfPointBridge.toGroupAlgebra_pushPoint]
    exact surjective_scalarExt_mapAlgHom g ((TorusChartRing.surjective_liftEquiv_iff fk.1).mp hfk)
  obtain ⟨T, hT⟩ := exists_twist_of_range_eq G d
    ⟨FiniteBialgebraHom.pushPoint R x' fk.1, fk.2.pushPoint R x'⟩ (hsurjPush x') y' hK
  let α' := (AddMonoidAlgebra.mapDomainAlgHom R C T.toAddMonoidHom).comp
    (HopfPointBridge.toGroupAlgebra fk.1)
  have hα' : IsHopfPoint α' :=
    ((HopfPointBridge.isHopfPoint_iff fk.1).mp fk.2).mapDomain T.toAddMonoidHom
  have hpush : ∀ {D : Type u} [CommRing D] [Algebra R D] (g : C →ₐ[R] D),
      (AddMonoidAlgebra.mapAlgHom ((r → ℤ) × F) g).comp α' =
        (AddMonoidAlgebra.mapDomainAlgHom R D T.toAddMonoidHom).comp
          (HopfPointBridge.toGroupAlgebra (FiniteBialgebraHom.pushPoint R g fk.1)) := by
    intro D _ _ g
    rw [HopfPointBridge.toGroupAlgebra_pushPoint, ← AlgHom.comp_assoc,
      HopfPointWindowExtension.mapAlgHom_comp_mapDomain, AlgHom.comp_assoc]
  obtain ⟨g, hg, b'', hb''⟩ := exists_local_lift hδ hι hgenV hP hN₀ dw hα' x' y'
    (by rw [hpush]; exact hT)
  refine ⟨g, hg, b'', ?_⟩
  rw [evaluate_comp_of_eq_range G i bk fk hev, range_twist_eq G
    ⟨FiniteBialgebraHom.pushPoint R (IsScalarTower.toAlgHom R C (Localization.Away g)) fk.1,
      fk.2.pushPoint R _⟩ (hsurjPush _) T, evaluate_j_comp_pOver, evaluate_iS_specMap]
  have hpt : (⟨TorusChartRing.ofGroupAlgebra
      ((AddMonoidAlgebra.mapDomainAlgHom R (Localization.Away g) T.toAddMonoidHom).comp
        (HopfPointBridge.toGroupAlgebra (FiniteBialgebraHom.pushPoint R
          (IsScalarTower.toAlgHom R C (Localization.Away g)) fk.1))),
      TorusChartRing.isHopfPoint_ofGroupAlgebra
        (((HopfPointBridge.isHopfPoint_iff _).mp (fk.2.pushPoint R _)).mapDomain
          T.toAddMonoidHom)⟩ :
      {f : AffineCoordinates.hopfAlgebra G →ₐ[R] Localization.Away g ⊗[R]
        AddMonoidAlgebra R ((r → ℤ) × F) // FiniteBialgebraHom.IsHopfPoint R f}) =
      ⟨FiniteBialgebraHom.pushPoint R b'' (fS G d).1, (fS G d).2.pushPoint R b''⟩ := by
    apply Subtype.ext
    change TorusChartRing.ofGroupAlgebra _ = _
    rw [← hpush, hb'', ← toGroupAlgebra_pushPoint_fS G d b'',
      TorusChart.ofGroupAlgebra_toGroupAlgebra]
  rw [hpt]

/-- The core of openness: every point of the image of a test admitting a parameter has an open
neighbourhood admitting a parameter. -/
theorem exists_good_open (hP3 : FppfSplitStatement.{u})
    {V : Submodule R (AffineCoordinates.hopfAlgebra G)} [Module.Finite R V]
    {δ : V →ₗ[R] V ⊗[R] AffineCoordinates.hopfAlgebra G} (hδ : IsCoassoc δ)
    (hι : (Coalgebra.comul (R := R) (A := AffineCoordinates.hopfAlgebra G)) ∘ₗ V.subtype =
      V.subtype.rTensor _ ∘ₗ δ)
    (hgenV : ∀ i, gen i ∈ V) {N₀ : ℕ} (hP : IsBoundedPresentation (R := R) gen N₀)
    (hN₀ : 1 ≤ N₀)
    (dw : MixedChartExistence.WindowDatum R (AffineCoordinates.hopfAlgebra G) r F m gen n V δ N₀)
    {T : Over (Spec (CommRingCat.of R))} (hT : IsAffine T.left) {L : GroupScheme T.left}
    (i : L ⟶ (GroupScheme.baseChange T.hom).obj G) (hi : IsClosedSubgroup i)
    (hL : RelativeMultiplicativeType.IsMultiplicativeType L) {T' : Over (Spec (CommRingCat.of R))}
    (b : T' ⟶ T)
    (a : T' ⟶ U dw.toDatum)
    (hab : TorusSubgroupModuli.evaluate (j G dw.toDatum) a = TorusSubgroupModuli.evaluate i b)
    (t' : T'.left) :
    ∃ W : T.left.Opens, b.left t' ∈ W ∧ ∃ aW : Over.mk (W.ι ≫ T.hom) ⟶ U dw.toDatum,
      TorusSubgroupModuli.evaluate (j G dw.toDatum) aW =
        TorusSubgroupModuli.evaluate i (Over.homMk W.ι rfl : Over.mk (W.ι ≫ T.hom) ⟶ T) := by
  let d := dw.toDatum
  obtain ⟨nk, C, _, _, bk, Λk, _, _, f, hFl, hLfp, hcov, hsurj, hev⟩ :=
    @hP3 R _ G _ T hT L i hi hL
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
  have hK : SubgroupFunctor.range ((diagPointEquiv G K).symm
        ⟨FiniteBialgebraHom.pushPoint R x' (f k).1, (f k).2.pushPoint R x'⟩) =
      SubgroupFunctor.range ((diagPointEquiv G K).symm
        ⟨FiniteBialgebraHom.pushPoint R y' (fS G d).1, (fS G d).2.pushPoint R y'⟩) := by
    rw [← evaluate_comp_of_eq_range G i (bk k) (f k) (hev k) x', ← evaluate_iS_specMap, hx', hy']
    exact hevK
  obtain ⟨g, hg, b'', heq⟩ := exists_piece_lift G hδ hι hgenV hP hN₀ dw i (bk k) (f k) (hsurj k)
    (hev k) x' y' hK
  -- the flat piece and the point
  let e : FiniteSource.specOver R (Localization.Away g) ⟶ T :=
    FiniteSource.specMap (IsScalarTower.toAlgHom R (C k) (Localization.Away g)) ≫ bk k
  have : Flat e.left := by
    have := hFl k
    change Flat (Spec.map (CommRingCat.ofHom (algebraMap (C k) (Localization.Away g))) ≫
      (bk k).left)
    infer_instance
  have : LocallyOfFinitePresentation e.left := by
    have := hLfp k
    change LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap (C k) (Localization.Away g))) ≫ (bk k).left)
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
    exact congrArg (fun φ => φ pt) e2
  have heq' : TorusSubgroupModuli.evaluate (j G d) (FiniteSource.specMap b'' ≫ pOver d) =
      TorusSubgroupModuli.evaluate i (e ≫ 𝟙 T) :=
    heq.symm.trans (congrArg (TorusSubgroupModuli.evaluate i) (Category.comp_id e).symm)
  obtain ⟨W, htW, aW, haW⟩ := FppfParameterDescent.exists_good_open_of_flat (j G d)
    (isClosedSubgroup_j G d) (injective_affine G d) i hi hT (𝟙 T)
    (inferInstanceAs (IsAffine (Spec _))) e (FiniteSource.specMap b'' ≫ pOver d) heq' (b.left t') ht
  exact ⟨W, htW, aW, haW.trans (congrArg (TorusSubgroupModuli.evaluate i) (Category.comp_id _))⟩

/-- The openness condition of an open chart, on affine targets. -/
theorem isOpen_affine (hP3 : FppfSplitStatement.{u})
    {V : Submodule R (AffineCoordinates.hopfAlgebra G)} [Module.Finite R V]
    {δ : V →ₗ[R] V ⊗[R] AffineCoordinates.hopfAlgebra G} (hδ : IsCoassoc δ)
    (hι : (Coalgebra.comul (R := R) (A := AffineCoordinates.hopfAlgebra G)) ∘ₗ V.subtype =
      V.subtype.rTensor _ ∘ₗ δ)
    (hgenV : ∀ i, gen i ∈ V) {N₀ : ℕ} (hP : IsBoundedPresentation (R := R) gen N₀)
    (hN₀ : 1 ≤ N₀)
    (dw : MixedChartExistence.WindowDatum R (AffineCoordinates.hopfAlgebra G) r F m gen n V δ N₀)
    (T : Over (Spec (CommRingCat.of R))) (hT : IsAffine T.left) (L : GroupScheme T.left)
    (i : L ⟶ (GroupScheme.baseChange T.hom).obj G) (hi : IsClosedSubgroup i)
    (hL : RelativeMultiplicativeType.IsMultiplicativeType L) :
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
    apply TorusChart.exists_evaluate_of_openCover (j G d) (isClosedSubgroup_j G d)
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
    [Algebra.Smooth R (W R (AffineCoordinates.hopfAlgebra G) ((r → ZMod m) × F))]
    (d : Datum R (AffineCoordinates.hopfAlgebra G) r F m gen n) : Smooth (qR d) := by
  apply smooth_qR
  rw [HasRingHomProperty.Spec_iff (P := @Smooth), CommRingCat.hom_ofHom, RingHom.smooth_algebraMap]
  infer_instance

/-- A window chart datum is an open chart on affine tests. -/
theorem isOpenChartOnAffines (hP3 : FppfSplitStatement.{u})
    [Algebra.Smooth R (W R (AffineCoordinates.hopfAlgebra G) ((r → ZMod m) × F))]
    {V : Submodule R (AffineCoordinates.hopfAlgebra G)} [Module.Finite R V]
    {δ : V →ₗ[R] V ⊗[R] AffineCoordinates.hopfAlgebra G} (hδ : IsCoassoc δ)
    (hι : (Coalgebra.comul (R := R) (A := AffineCoordinates.hopfAlgebra G)) ∘ₗ V.subtype =
      V.subtype.rTensor _ ∘ₗ δ)
    (hgenV : ∀ i, gen i ∈ V) {N₀ : ℕ} (hP : IsBoundedPresentation (R := R) gen N₀)
    (hN₀ : 1 ≤ N₀)
    (dw : MixedChartExistence.WindowDatum R (AffineCoordinates.hopfAlgebra G) r F m gen n V δ N₀) :
    MultiplicativeTypeSubgroupModuli.IsOpenChartOnAffines (j G dw.toDatum) where
  isClosedSubgroup := isClosedSubgroup_j G dw.toDatum
  isMultiplicativeType := isMultiplicativeType_K G dw.toDatum
  smooth := smooth_qR_of_algebraSmooth G dw.toDatum
  injective := fun T hT a b h => injective_affine G dw.toDatum T hT a b h
  isOpen := fun T hT L i hi hL => by
    obtain ⟨V', hV'⟩ := isOpen_affine G hP3 hδ hι hgenV hP hN₀ dw T hT L i hi hL
    exact ⟨V', fun T' b _ => hV' T' b⟩

end Local

end Langlands.GroupScheme.HomScheme.MultiplicativeTypeChart
