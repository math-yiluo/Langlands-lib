import Langlands.Representation.Intertwining.PQOuterLeviOperator
import Langlands.GroupScheme.Rational.ParabolicLeviIntersectionReduction
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.Representation.Aubert.General.SemidirectRestriction
import Langlands.Representation.Aubert.General.RationalStandardInductionNonzero
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility

/-! # Regularity transfer of Renard VII.3.5 (iii)

If `i_{P'}^L(σ)` is `Q₁Q₂`-regular, then `σ` is `P₁P₂`-regular.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands

section GroupAlgebra

variable {H₁ H₂ B₁ B₂ : Type*} [Monoid H₁] [Monoid H₂] [Monoid B₁] [Monoid B₂]
  {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]

/-- An equivariant linear map intertwines the group-algebra actions along `κ_*`. -/
theorem asAlgebraHom_mapDomain_apply (ρ₁ : Representation ℂ H₁ V₁)
    (ρ₂ : Representation ℂ H₂ V₂) (φ₁ : B₁ →* H₁) (φ₂ : B₂ →* H₂) (κ : B₁ →* B₂)
    (Ψ : V₁ →ₗ[ℂ] V₂) (hΨ : ∀ z v, Ψ (ρ₁ (φ₁ z) v) = ρ₂ (φ₂ (κ z)) (Ψ v))
    (x : MonoidAlgebra ℂ B₁) (v : V₁) :
    Representation.asAlgebraHom (ρ₂.comp φ₂) (MonoidAlgebra.mapDomainRingHom ℂ κ x) (Ψ v) =
      Ψ (Representation.asAlgebraHom (ρ₁.comp φ₁) x v) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | single z c =>
    simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
      Representation.asAlgebraHom_single, LinearMap.smul_apply, MonoidHom.coe_comp,
      Function.comp_apply, map_smul, hΨ]

/-- A surjective equivariant linear map pushes the group-algebra kernel forward along `κ_*`. -/
theorem map_groupAlgebraKernel_le (ρ₁ : Representation ℂ H₁ V₁)
    (ρ₂ : Representation ℂ H₂ V₂) (φ₁ : B₁ →* H₁) (φ₂ : B₂ →* H₂) (κ : B₁ →* B₂)
    (Ψ : V₁ →ₗ[ℂ] V₂) (hsurj : Function.Surjective Ψ)
    (hΨ : ∀ z v, Ψ (ρ₁ (φ₁ z) v) = ρ₂ (φ₂ (κ z)) (Ψ v)) :
    Ideal.map (MonoidAlgebra.mapDomainRingHom ℂ κ) (groupAlgebraKernel ρ₁ φ₁) ≤
      groupAlgebraKernel ρ₂ φ₂ := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, mem_groupAlgebraKernel_iff]
  rw [mem_groupAlgebraKernel_iff] at hx
  ext w
  obtain ⟨v, rfl⟩ := hsurj w
  rw [asAlgebraHom_mapDomain_apply ρ₁ ρ₂ φ₁ φ₂ κ Ψ hΨ, hx]
  simp

/-- Comaximality is preserved by a ring map sending each ideal into the corresponding one. -/
theorem sup_eq_top_of_map_le {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    {I J : Ideal R} {I' J' : Ideal S} (h : I ⊔ J = ⊤) (hI : I.map f ≤ I')
    (hJ : J.map f ≤ J') : I' ⊔ J' = ⊤ := by
  rw [eq_top_iff, ← Ideal.map_top f, ← h, Ideal.map_sup]
  exact sup_le_sup hI hJ

end GroupAlgebra

end Langlands

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section SplitComponent

variable {k : Type u} [Field k]

/-- For `P₁ = MN₁ ⊂ G` and `P' = MN'` a parabolic of a Levi `L` of `Q₁` with the same `M`,
the split component of `L` factors through any split component of `M`. -/
theorem exists_outer_splitComponent_factor
    {G M P₁ L Q₁ P' : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {p₁ : P₁ ⟶ G} {l₁ : M ⟶ P₁} (hp₁ : IsParabolicSubgroup p₁)
    (hl₁ : IsRationalLeviSubgroup l₁)
    {q₁ : Q₁ ⟶ G} {lQ₁ : L ⟶ Q₁} (hq₁ : IsParabolicSubgroup q₁)
    (hlQ₁ : IsRationalLeviSubgroup lQ₁)
    {p' : P' ⟶ L} {l' : M ⟶ P'} (hp' : IsParabolicSubgroup p')
    (hl' : IsRationalLeviSubgroup l') (hM : l' ≫ p' ≫ lQ₁ ≫ q₁ = l₁ ≫ p₁)
    {A AL : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a) {aL : AL.toGrp ⟶ L} (haL : IsSplitComponent aL) :
    ∃ f : AL.toGrp ⟶ A.toGrp, f ≫ a ≫ l' ≫ p' = aL := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨ψ, -, hψ⟩ := DynamicLeviConjugacy.exists_cocharacter_parabolic_levi parabolicDynamic
    dynamicGeometricUnipotentRadical hG hp₁ hl₁
  have hjc : IsClosedSubgroup (lQ₁ ≫ q₁) := hlQ₁.isClosedSubgroup.comp hq₁.isClosedSubgroup
  have hmc : IsClosedSubgroup (l₁ ≫ p₁) := hl₁.isClosedSubgroup.comp hp₁.isClosedSubgroup
  have hic : IsClosedSubgroup (l' ≫ p') := hl'.isClosedSubgroup.comp hp'.isClosedSubgroup
  have hjm : Mono (lQ₁ ≫ q₁).hom.hom := hjc.mono_overHom
  have hjrep : (SubgroupFunctor.range (lQ₁ ≫ q₁)).IsRepresentedBy (lQ₁ ≫ q₁) :=
    ⟨hjm, rfl⟩
  have hmrep : (SubgroupFunctor.range (l₁ ≫ p₁)).IsRepresentedBy (l₁ ≫ p₁) :=
    ⟨hmc.mono_overHom, rfl⟩
  have hM' : (l' ≫ p') ≫ lQ₁ ≫ q₁ = l₁ ≫ p₁ := by
    rw [Category.assoc]
    exact hM
  -- the cocharacter `ψ` lies in `M`, hence in `L`
  have hψM : SubgroupFunctor.range ψ ≤ SubgroupFunctor.range (l₁ ≫ p₁) := by
    rw [hψ, ← torusCentralizer_gm_eq_dynamicCentralizer]
    exact range_le_torusCentralizer ψ
  have hψL : SubgroupFunctor.range ψ ≤ SubgroupFunctor.range (lQ₁ ≫ q₁) := by
    refine hψM.trans ?_
    rw [← hM']
    exact RepresentedParabolicLeviIntersection.range_comp_le (l' ≫ p') (lQ₁ ≫ q₁)
  let chiL := hjrep.factorHom ψ hψL
  have hchi : chiL ≫ lQ₁ ≫ q₁ = ψ := hjrep.factorHom_comp ψ hψL
  -- the central map `aL` lands in `M`
  have hrange : SubgroupFunctor.range (aL ≫ lQ₁ ≫ q₁) ≤ SubgroupFunctor.range (l₁ ≫ p₁) := by
    rw [hψ]
    rintro T _ ⟨x, rfl⟩
    change T ⟶ AL.X at x
    have hz := center_le_dynamicCentralizer chiL T (haL.isCentralSplitTorus.isCentral T x)
    have hz' := Dynamic.centralizer_le_comap chiL (lQ₁ ≫ q₁) T hz
    rw [SubgroupFunctor.mem_comap, hchi] at hz'
    change (x ≫ aL.hom.hom) ≫ (lQ₁ ≫ q₁).hom.hom ∈ _ at hz'
    change x ≫ (aL ≫ lQ₁ ≫ q₁).hom.hom ∈ _
    rw [Grp.comp_hom_hom, ← Category.assoc]
    exact hz'
  let b := hmrep.factorHom (aL ≫ lQ₁ ≫ q₁) hrange
  have hb : b ≫ l₁ ≫ p₁ = aL ≫ lQ₁ ≫ q₁ := hmrep.factorHom_comp _ _
  have hb' : b ≫ l' ≫ p' = aL := by
    apply Grp.hom_ext
    apply (cancel_mono (lQ₁ ≫ q₁).hom.hom).mp
    change (b ≫ (l' ≫ p') ≫ lQ₁ ≫ q₁).hom.hom = (aL ≫ lQ₁ ≫ q₁).hom.hom
    rw [hM', hb]
  have hbc : IsCentral b :=
    IsCentral.of_comp hic.mono_overHom (by rw [hb']; exact haL.isCentralSplitTorus.isCentral)
  have : IsAffineHom M.X.hom := hl₁.isConnectedReductive.isAffineHom
  obtain ⟨f, hf⟩ := ha.exists_factor haL.1.1.1 hbc
  exact ⟨f, by rw [← Category.assoc, hf, hb']⟩

end SplitComponent

section Modulus

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [LocallyCompactSpace H]

/-- The Haar modulus of conjugation by an element commuting with a closed subgroup is `1`. -/
theorem closedNormalizerCharacter_eq_one_of_commute' (U : Subgroup H)
    (hU : IsClosed (U : Set H)) (g : Subgroup.normalizer (U : Set H))
    (hg : ∀ u ∈ U, (g : H) * u = u * g) :
    HaarModulus.closedNormalizerCharacter U hU g = 1 := by
  have he : HaarModulus.normalizerConj U g = ContinuousMulEquiv.refl U := by
    refine ContinuousMulEquiv.ext fun u => Subtype.ext ?_
    rw [HaarModulus.normalizerConj_apply, hg u u.2, mul_inv_cancel_right]
    rfl
  apply Units.ext
  simp only [HaarModulus.closedNormalizerCharacter, HaarModulus.normalizerCharacter_apply, he,
    MeasureTheory.mulEquivHaarChar_refl, Units.val_one]

/-- The half modulus `δ^{1/2}` at an element commuting with the closed subgroup is `1`. -/
theorem closedHalfCharacter_eq_one_of_commute (U P : Subgroup H) (hU : IsClosed (U : Set H))
    (hPU : P ≤ Subgroup.normalizer (U : Set H)) (g : P)
    (hg : ∀ u ∈ U, (g : H) * u = u * g) :
    HaarModulus.closedHalfCharacter U hU P hPU g = 1 := by
  have h1 : HaarModulus.closedRestrictCharacter U hU P hPU g = 1 :=
    closedNormalizerCharacter_eq_one_of_commute' U hU _ hg
  apply Units.ext
  simp only [HaarModulus.closedHalfCharacter, Jacquet.complexCharacter_apply,
    Jacquet.positiveHalfCharacter_apply, h1, Units.val_one, NNReal.sqrt_one, NNReal.coe_one,
    Complex.ofReal_one]

/-- The inverse half modulus only depends on the value of the Haar modulus. -/
theorem closedInverseHalfCharacter_eq_of_eq {U U' M M' : Subgroup H}
    (hU : IsClosed (U : Set H)) (hU' : IsClosed (U' : Set H))
    (hMU : M ≤ Subgroup.normalizer (U : Set H)) (hMU' : M' ≤ Subgroup.normalizer (U' : Set H))
    (m : M) (m' : M')
    (h : HaarModulus.closedNormalizerCharacter U hU ⟨m, hMU m.2⟩ =
      HaarModulus.closedNormalizerCharacter U' hU' ⟨m', hMU' m'.2⟩) :
    HaarModulus.closedInverseHalfCharacter U hU M hMU m =
      HaarModulus.closedInverseHalfCharacter U' hU' M' hMU' m' := by
  have h' : HaarModulus.closedRestrictCharacter U hU M hMU m =
      HaarModulus.closedRestrictCharacter U' hU' M' hMU' m' := h
  apply Units.ext
  simp only [HaarModulus.closedInverseHalfCharacter, Jacquet.inverseHalfCharacter_apply, h']

end Modulus

section Regularity

/-- Rational points are functorial. -/
theorem outer_rationalPoints_map_comp_apply {k : Type u} [CommRing k]
    {H M G : GroupScheme (Spec (CommRingCat.of k))}
    (f : H ⟶ M) (g : M ⟶ G) (y : rationalPoints H) :
    rationalPoints.map (f ≫ g) y = rationalPoints.map g (rationalPoints.map f y) := by
  simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G M P₁ N₁ P₂ N₂ L Q₁ U₁ Q₂ U₂ P' N' : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

local instance outerRegularityPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (hG : IsConnectedReductive G)
  {p₁ : P₁ ⟶ G} {l₁ : M ⟶ P₁} {r₁ : N₁ ⟶ P₁} (hp₁ : IsParabolicSubgroup p₁)
  (hl₁ : IsRationalLeviSubgroup l₁) (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
  (hmul₁ : IsIso (subgroupMultiplication l₁ r₁))
  {p₂ : P₂ ⟶ G} {l₂ : M ⟶ P₂} {r₂ : N₂ ⟶ P₂} (hp₂ : IsParabolicSubgroup p₂)
  (hl₂ : IsRationalLeviSubgroup l₂) (hr₂ : LeviSubgroup.IsGeometricUnipotentRadical r₂)
  (hmul₂ : IsIso (subgroupMultiplication l₂ r₂))
  {q₁ : Q₁ ⟶ G} {lQ₁ : L ⟶ Q₁} {rQ₁ : U₁ ⟶ Q₁} (hq₁ : IsParabolicSubgroup q₁)
  (hlQ₁ : IsRationalLeviSubgroup lQ₁) (hrQ₁ : LeviSubgroup.IsGeometricUnipotentRadical rQ₁)
  (hmulQ₁ : IsIso (subgroupMultiplication lQ₁ rQ₁))
  {q₂ : Q₂ ⟶ G} {lQ₂ : L ⟶ Q₂} {rQ₂ : U₂ ⟶ Q₂} (hq₂ : IsParabolicSubgroup q₂)
  (hlQ₂ : IsRationalLeviSubgroup lQ₂) (hrQ₂ : LeviSubgroup.IsGeometricUnipotentRadical rQ₂)
  (hmulQ₂ : IsIso (subgroupMultiplication lQ₂ rQ₂))
  {p' : P' ⟶ L} {l' : M ⟶ P'} {r' : N' ⟶ P'} (hp' : IsParabolicSubgroup p')
  (hl' : IsRationalLeviSubgroup l') (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
  (hmul' : IsIso (subgroupMultiplication l' r'))
  (hlev₂ : l₂ ≫ p₂ = l₁ ≫ p₁) (hlevQ₂ : lQ₂ ≫ q₂ = lQ₁ ≫ q₁)
  (hPQ₁ : pointImage p₁ ≤ pointImage q₁) (hPQ₂ : pointImage p₂ ≤ pointImage q₂)
  (hM : l' ≫ p' ≫ lQ₁ ≫ q₁ = l₁ ≫ p₁)
  (hP'₁ : pointImage (p' ≫ lQ₁ ≫ q₁) = pointImage p₁ ⊓ pointImage (lQ₁ ≫ q₁))
  (hP'₂ : pointImage (p' ≫ lQ₁ ≫ q₁) = pointImage p₂ ⊓ pointImage (lQ₁ ≫ q₁))

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
include hq₁ hlQ₁ hp' hl' hr' hmul' in
/-- `I_X ⊂ I_σ` along `A_L(F) → A(F)`, for `X = i_{P'}^L(σ)`: a point `z` of the split
component of `L` acts on `X` through the value at `1` by `σ(z)`. -/
theorem outer_splitComponentKernel_map_le
    {A AL : CommGroupScheme (Spec (CommRingCat.of k))} (a : A.toGrp ⟶ M) (aL : AL.toGrp ⟶ L)
    (haL : IsSplitComponent aL) (f : AL.toGrp ⟶ A.toGrp) (hf : f ≫ a ≫ l' ≫ p' = aL) :
    haveI := hlQ₁.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology lQ₁ hlQ₁
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q₁ lQ₁ hq₁ hlQ₁
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q₁ lQ₁ hq₁ hlQ₁
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l' hl'
    ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      Ideal.map (MonoidAlgebra.mapDomainRingHom ℂ (rationalPoints.map f))
          (splitComponentKernel lQ₁ hlQ₁ aL
            ((leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj σ)) ≤
        splitComponentKernel l' hl' a σ := by
  have := hlQ₁.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology lQ₁ hlQ₁
  have : LocallyCompactSpace (rationalPoints L) := leviPoints_locallyCompactSpace q₁ lQ₁ hq₁ hlQ₁
  have : NonarchimedeanGroup (rationalPoints L) := leviPoints_nonarchimedeanGroup q₁ lQ₁ hq₁ hlQ₁
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l' hl'
  intro σ
  let h' := isSemidirectDecomposition_pointImage p' l' r' hp'.isClosedSubgroup hr' hmul'
  let hc' := isClosed_pointImage_comp p' r' hp'.isClosedSubgroup hr'.1.isClosedSubgroup
  let τ := SmoothRep.pullback (leviPointsEquiv p' l' hp' hl').symm σ
  let X := (leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj σ
  let ev : X →ₗ[ℂ] σ :=
    { toFun := fun φ => Induction.eval (pointImage p') (inducingRepresentation h' hc' τ) φ 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsurj : Function.Surjective ev :=
    normalizedInduction_eval_surjective h' hc'
      (continuous_projection_pointImage p' l' r' hp' hl' hr' hmul') τ
  refine map_groupAlgebraKernel_le X.representation σ.representation (rationalPoints.map aL)
    (rationalPoints.map a) (rationalPoints.map f) ev hsurj ?_
  intro z φ
  -- the image of `z` in `L(F)` is the image of `m = a (f z)` in the Levi of `P'`
  set m : rationalPoints M := rationalPoints.map a (rationalPoints.map f z) with hm
  have hy : rationalPoints.map aL z = rationalPoints.map (l' ≫ p') m := by
    rw [hm, ← outer_rationalPoints_map_comp_apply, ← outer_rationalPoints_map_comp_apply, hf]
  have hyM : rationalPoints.map aL z ∈ pointImage (l' ≫ p') := ⟨m, hy.symm⟩
  let y : pointImage (l' ≫ p') := ⟨rationalPoints.map aL z, hyM⟩
  have hcent : rationalPoints.map aL z ∈ Subgroup.center (rationalPoints L) :=
    haL.isCentralSplitTorus.isCentral.map_mem_center z
  have hlevi : (leviPointsEquiv p' l' hp' hl').symm y = m := by
    rw [ContinuousMulEquiv.symm_apply_eq]
    exact Subtype.ext hy
  have h1 : ev (X.representation (rationalPoints.map aL z) φ) =
      Induction.eval (pointImage p') (inducingRepresentation h' hc' τ) φ
        ((rationalPoints.map aL z) * 1) := by
    rw [mul_one]
    change Induction.eval _ _ φ (1 * rationalPoints.map aL z) = _
    rw [one_mul]
    rfl
  refine h1.trans ((normalizedInductionFunctor_covariant h' hc' τ φ ⟨y, h'.levi_le y.2⟩ 1).trans ?_)
  have h2 : HaarModulus.closedHalfCharacter (pointImage (r' ≫ p')) hc' (pointImage p')
      h'.le_normalizer ⟨y, h'.levi_le y.2⟩ = 1 :=
    closedHalfCharacter_eq_one_of_commute _ _ hc' h'.le_normalizer _
      (fun u _ => ((Subgroup.mem_center_iff.mp hcent) u).symm)
  rw [h2, Units.val_one, one_smul, h'.projection_levi y]
  change σ.representation ((leviPointsEquiv p' l' hp' hl').symm y) (ev φ) = _
  rw [hlevi]

include hG hp₂ hl₂ hr₂ hmul₂ hq₂ hlQ₂ hrQ₂ hmulQ₂ hp' hl' hr' hmul' hlev₂ hlevQ₂ hPQ₂ hM
  hP'₂ in
/-- `δ_{N₂}(g) = δ_{U₂}(g)` for `g` in `M(F)` central in `L(F)`: `N₂ = (L ∩ N₂) U₂` and `g`
centralizes `L ∩ N₂`. -/
theorem outer_modulus_eq (y : rationalPoints L) (hy : y ∈ Subgroup.center (rationalPoints L))
    (hyM : rationalPoints.map (lQ₂ ≫ q₂) y ∈ pointImage (l₂ ≫ p₂)) :
    HaarModulus.closedNormalizerCharacter (pointImage (r₂ ≫ p₂))
        (isClosed_pointImage_comp p₂ r₂ hp₂.isClosedSubgroup hr₂.1.isClosedSubgroup)
        ⟨rationalPoints.map (lQ₂ ≫ q₂) y, pointImage_le_normalizer p₂ l₂ r₂ hr₂ hyM⟩ =
      HaarModulus.closedNormalizerCharacter (pointImage (rQ₂ ≫ q₂))
        (isClosed_pointImage_comp q₂ rQ₂ hq₂.isClosedSubgroup hrQ₂.1.isClosedSubgroup)
        ⟨rationalPoints.map (lQ₂ ≫ q₂) y,
          pointImage_le_normalizer q₂ lQ₂ rQ₂ hrQ₂ ⟨y, rfl⟩⟩ := by
  have : SecondCountableTopology (rationalPoints G) :=
    RationalPointFamily.reductiveRationalPoint_secondCountable k G hG
  have hU₂N₂ := outer_radical₂_le hG hp₂ hl₂ hr₂ hmul₂ hq₂ hlQ₂ hrQ₂ hmulQ₂ hp' hl' hr' hmul'
    hlev₂ hlevQ₂ hPQ₂ hM hP'₂
  have hN₂Q₂ : pointImage (r₂ ≫ p₂) ≤ pointImage q₂ := (pointImage_comp_le p₂ r₂).trans hPQ₂
  let d0 := isSemidirectDecomposition_pointImage q₂ lQ₂ rQ₂ hq₂.isClosedSubgroup hrQ₂ hmulQ₂
  let d := d0.restrict hN₂Q₂ hU₂N₂
  have hd : Continuous d.projection :=
    d0.continuous_restrict_projection hN₂Q₂ hU₂N₂
      (continuous_projection_pointImage q₂ lQ₂ rQ₂ hq₂ hlQ₂ hrQ₂ hmulQ₂)
  have hN₂ := isClosed_pointImage_comp p₂ r₂ hp₂.isClosedSubgroup hr₂.1.isClosedSubgroup
  have hU₂ := isClosed_pointImage_comp q₂ rQ₂ hq₂.isClosedSubgroup hrQ₂.1.isClosedSubgroup
  have hL := isClosed_pointImage_comp q₂ lQ₂ hq₂.isClosedSubgroup hlQ₂.isClosedSubgroup
  have hcomm : ∀ x ∈ pointImage (lQ₂ ≫ q₂),
      rationalPoints.map (lQ₂ ≫ q₂) y * x = x * rationalPoints.map (lQ₂ ≫ q₂) y := by
    rintro _ ⟨x, rfl⟩
    exact ((map_mul _ y x).symm.trans (congrArg (rationalPoints.map (lQ₂ ≫ q₂))
      (Subgroup.mem_center_iff.mp hy x).symm)).trans (map_mul _ x y)
  have hgL : rationalPoints.map (lQ₂ ≫ q₂) y ∈
      Subgroup.normalizer ((pointImage (lQ₂ ≫ q₂) : Subgroup (rationalPoints G)) :
        Set (rationalPoints G)) :=
    Subgroup.le_normalizer ⟨y, rfl⟩
  have hgW : rationalPoints.map (lQ₂ ≫ q₂) y ∈
      Subgroup.normalizer ((pointImage (lQ₂ ≫ q₂) ⊓ pointImage (r₂ ≫ p₂) :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hN := Subgroup.mem_normalizer_iff.mp (pointImage_le_normalizer p₂ l₂ r₂ hr₂ hyM) x
    have hLx := Subgroup.mem_normalizer_iff.mp hgL x
    simp only [Subgroup.mem_inf] at hN hLx ⊢
    exact and_congr hLx hN
  have hprod := d.closedNormalizerCharacter_eq_mul hd hN₂ (hL.inter hN₂) hU₂
    (rationalPoints.map (lQ₂ ≫ q₂) y) (pointImage_le_normalizer p₂ l₂ r₂ hr₂ hyM) hgW
    (pointImage_le_normalizer q₂ lQ₂ rQ₂ hrQ₂ ⟨y, rfl⟩)
  have h1 : HaarModulus.closedNormalizerCharacter
      (pointImage (lQ₂ ≫ q₂) ⊓ pointImage (r₂ ≫ p₂)) (hL.inter hN₂)
      ⟨rationalPoints.map (lQ₂ ≫ q₂) y, hgW⟩ = 1 :=
    closedNormalizerCharacter_eq_one_of_commute' _ _ _
      (fun x hx => hcomm x (Subgroup.mem_inf.mp hx).1)
  refine hprod.trans ?_
  rw [h1, one_mul]

include hG hp₁ hl₁ hr₁ hmul₁ hp₂ hl₂ hr₂ hmul₂ hq₁ hlQ₁ hrQ₁ hmulQ₁ hq₂ hlQ₂ hrQ₂ hmulQ₂
  hp' hl' hr' hmul' hlev₂ hlevQ₂ hPQ₁ hPQ₂ hM hP'₁ hP'₂ in
/-- If `Φ₁ f` vanishes on the boundary of `Q₁(F)Q₂(F)`, then `f` vanishes on the boundary of
`P₁(F)P₂(F)`. -/
theorem outer_mem_boundaryVanishing_of_stages :
    haveI := hlQ₁.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology lQ₁ hlQ₁
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q₁ lQ₁ hq₁ hlQ₁
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q₁ lQ₁ hq₁ hlQ₁
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l₁ hl₁
    ∀ (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (f : (leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ),
      SmoothRep.hom ((leviInductionStagesIso p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
          q₁ lQ₁ rQ₁ hq₁ hlQ₁ hrQ₁ hmulQ₁ p' l' r' hp' hl' hr' hmul' hPQ₁ hM
          (hP'₁.trans (inf_comm _ _)) hG).hom.app σ) f ∈
        (boundaryVanishingSubfunctor q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁ q₂
          (identityParabolicDoubleCoset q₁ q₂)).obj
            ((leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj σ) →
      f ∈ (boundaryVanishingSubfunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂
          (identityParabolicDoubleCoset p₁ p₂)).obj σ := by
  have := hlQ₁.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology lQ₁ hlQ₁
  have : LocallyCompactSpace (rationalPoints L) := leviPoints_locallyCompactSpace q₁ lQ₁ hq₁ hlQ₁
  have : NonarchimedeanGroup (rationalPoints L) := leviPoints_nonarchimedeanGroup q₁ lQ₁ hq₁ hlQ₁
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l₁ hl₁
  intro σ f hF
  let X := (leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj σ
  let Φ₁ := (leviInductionStagesIso p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
    q₁ lQ₁ rQ₁ hq₁ hlQ₁ hrQ₁ hmulQ₁ p' l' r' hp' hl' hr' hmul' hPQ₁ hM
    (hP'₁.trans (inf_comm _ _)) hG).app σ
  let evalG₁ : (leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ → rationalPoints G → σ :=
    fun f g =>
    Induction.eval (pointImage p₁)
      (inducingRepresentation
        (isSemidirectDecomposition_pointImage p₁ l₁ r₁ hp₁.isClosedSubgroup hr₁ hmul₁)
        (isClosed_pointImage_comp p₁ r₁ hp₁.isClosedSubgroup hr₁.1.isClosedSubgroup)
        (SmoothRep.pullback (leviPointsEquiv p₁ l₁ hp₁ hl₁).symm σ)) f g
  let evalL : X → rationalPoints L → σ := fun φ x =>
    Induction.eval (pointImage p')
      (inducingRepresentation
        (isSemidirectDecomposition_pointImage p' l' r' hp'.isClosedSubgroup hr' hmul')
        (isClosed_pointImage_comp p' r' hp'.isClosedSubgroup hr'.1.isClosedSubgroup)
        (SmoothRep.pullback (leviPointsEquiv p' l' hp' hl').symm σ)) φ x
  let evalQ₁ : (leviInductionFunctor.{u, max u v} q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁).obj X →
      rationalPoints G → X := fun F g =>
    Induction.eval (pointImage q₁)
      (inducingRepresentation
        (isSemidirectDecomposition_pointImage q₁ lQ₁ rQ₁ hq₁.isClosedSubgroup hrQ₁ hmulQ₁)
        (isClosed_pointImage_comp q₁ rQ₁ hq₁.isClosedSubgroup hrQ₁.1.isClosedSubgroup)
        (SmoothRep.pullback (leviPointsEquiv q₁ lQ₁ hq₁ hlQ₁).symm X)) F g
  have hΦ₁ : ∀ f g, evalL (evalQ₁ (SmoothRep.hom Φ₁.hom f) g) 1 = evalG₁ f g := by
    intro f g
    refine (leviInductionStagesIso_eval' p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
      q₁ lQ₁ rQ₁ hq₁ hlQ₁ hrQ₁ hmulQ₁ p' l' r' hp' hl' hr' hmul' hPQ₁ hM
      (hP'₁.trans (inf_comm _ _)) hG σ f g 1).trans ?_
    simp only [map_one, Units.val_one, inv_one, one_smul, one_mul]
    rfl
  have hQ := (Geometric.mem_rawSmoothVanishingSubfunctor_iff (R := ℂ) (pointImage q₁)
    (pointImage q₂) _
    (Geometric.boundary_doubleCoset_mul_mem _ _ (identityParabolicDoubleCoset q₁ q₂))
    ((leviInducingFunctor q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁).obj X) _).mp hF
  refine (Geometric.mem_rawSmoothVanishingSubfunctor_iff (R := ℂ) (pointImage p₁)
    (pointImage p₂) _
    (Geometric.boundary_doubleCoset_mul_mem _ _ (identityParabolicDoubleCoset p₁ p₂))
    ((leviInducingFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ) f).mpr ?_
  intro g hg
  have h0 : evalQ₁ (SmoothRep.hom Φ₁.hom f) g = 0 :=
    hQ g (outer_boundary_subset hG hp₁ hl₁ hr₁ hmul₁ hp₂ hl₂ hr₂ hmul₂ hq₁ hlQ₁ hrQ₁ hmulQ₁
      hq₂ hlQ₂ hrQ₂ hmulQ₂ hp' hl' hr' hmul' hlev₂ hlevQ₂ hPQ₁ hPQ₂ hM hP'₁ hP'₂ hg)
  change evalG₁ f g = 0
  calc evalG₁ f g = evalL (evalQ₁ (SmoothRep.hom Φ₁.hom f) g) 1 := (hΦ₁ f g).symm
    _ = evalL 0 1 := by rw [h0]
    _ = 0 := rfl

include hG hp₁ hl₁ hr₁ hmul₁ hp₂ hl₂ hr₂ hmul₂ hq₁ hlQ₁ hrQ₁ hmulQ₁ hq₂ hlQ₂ hrQ₂ hmulQ₂
  hp' hl' hr' hmul' hlev₂ hlevQ₂ hPQ₁ hPQ₂ hM hP'₁ hP'₂ in
/-- `I^{Q₁Q₂}_X ⊂ I^{P₁P₂}_σ` along `A_L(F) → A(F)`: `Φ₁⁻¹` induces an `A_L(F)`-equivariant
surjection `r_{Q₂}(i_{Q₁}X)/F^{<1̄} → r_{P₂}(i_{P₁}σ)/F^{<1̄}`. -/
theorem outer_pqRegularityKernel_map_le
    {A AL : CommGroupScheme (Spec (CommRingCat.of k))} (a : A.toGrp ⟶ M) (aL : AL.toGrp ⟶ L)
    (haL : IsSplitComponent aL) (f : AL.toGrp ⟶ A.toGrp) (hf : f ≫ a ≫ l' ≫ p' = aL) :
    haveI := hlQ₁.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology lQ₁ hlQ₁
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q₁ lQ₁ hq₁ hlQ₁
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q₁ lQ₁ hq₁ hlQ₁
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l₁ hl₁
    ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      Ideal.map (MonoidAlgebra.mapDomainRingHom ℂ (rationalPoints.map f))
          (pqRegularityKernel q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁ q₂ lQ₂ rQ₂ hq₂ hrQ₂ hlQ₂ hmulQ₂ aL
            ((leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj σ)) ≤
        pqRegularityKernel p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂ a σ := by
  have := hlQ₁.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology lQ₁ hlQ₁
  have : LocallyCompactSpace (rationalPoints L) := leviPoints_locallyCompactSpace q₁ lQ₁ hq₁ hlQ₁
  have : NonarchimedeanGroup (rationalPoints L) := leviPoints_nonarchimedeanGroup q₁ lQ₁ hq₁ hlQ₁
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l₁ hl₁
  intro σ
  let X := (leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj σ
  let Φ₁ := (leviInductionStagesIso p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
    q₁ lQ₁ rQ₁ hq₁ hlQ₁ hrQ₁ hmulQ₁ p' l' r' hp' hl' hr' hmul' hPQ₁ hM
    (hP'₁.trans (inf_comm _ _)) hG).app σ
  let πQ := (leviInductionFunctor.{u, max u v} q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁).obj X
  let πP := (leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ
  let JQ := (leviJacquetInductionFunctor.{u, max u v} q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁
    q₂ lQ₂ rQ₂ hq₂ hrQ₂ hlQ₂ hmulQ₂).obj X
  let JP := (leviJacquetInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁
    p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂).obj σ
  let SQ := (boundarySupportImage q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁ q₂ lQ₂ rQ₂ hq₂ hrQ₂ hlQ₂ hmulQ₂
    (identityParabolicDoubleCoset q₁ q₂)).obj X
  let SP := (boundarySupportImage p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂
    (identityParabolicDoubleCoset p₁ p₂)).obj σ
  let mkQ : πQ →ₗ[ℂ] JQ :=
    Jacquet.Localization.mk πQ.representation (pointImage (rQ₂ ≫ q₂)) 1
  let mkP : πP →ₗ[ℂ] JP :=
    Jacquet.Localization.mk πP.representation (pointImage (r₂ ≫ p₂)) 1
  let Φinv : πQ →ₗ[ℂ] πP := (SmoothRep.hom Φ₁.inv).toLinearMap
  have hU₂N₂ := outer_radical₂_le hG hp₂ hl₂ hr₂ hmul₂ hq₂ hlQ₂ hrQ₂ hmulQ₂ hp' hl' hr' hmul'
    hlev₂ hlevQ₂ hPQ₂ hM hP'₂
  have hrel : ∀ (u : pointImage (rQ₂ ≫ q₂)) (w : πQ),
      (mkP ∘ₗ Φinv) (πQ.representation u w) =
        (((1 : pointImage (rQ₂ ≫ q₂) →* ℂˣ) u : ℂˣ) : ℂ) • (mkP ∘ₗ Φinv) w := by
    intro u w
    have hΦ : Φinv (πQ.representation u w) = πP.representation u (Φinv w) :=
      LinearMap.congr_fun ((SmoothRep.hom Φ₁.inv).isIntertwining' u) w
    rw [MonoidHom.one_apply, Units.val_one, one_smul, LinearMap.comp_apply, hΦ]
    have h := Jacquet.Localization.mk_apply_subgroup πP.representation (pointImage (r₂ ≫ p₂)) 1
      ⟨u, hU₂N₂ u.2⟩ (Φinv w)
    rw [MonoidHom.one_apply, Units.val_one, one_smul] at h
    exact h
  let Ψ₀ : JQ →ₗ[ℂ] JP :=
    Jacquet.Localization.lift πQ.representation (pointImage (rQ₂ ≫ q₂)) 1 (mkP ∘ₗ Φinv) hrel
  have hΨ₀ : ∀ F : πQ, Ψ₀ (mkQ F) = mkP (Φinv F) := fun F => rfl
  have hle : SQ.toSubmodule ≤ SP.toSubmodule.comap Ψ₀ := by
    rintro _ ⟨F, hF, rfl⟩
    refine ⟨Φinv F, ?_, (hΨ₀ F).symm⟩
    refine outer_mem_boundaryVanishing_of_stages hG hp₁ hl₁ hr₁ hmul₁ hp₂ hl₂ hr₂ hmul₂
      hq₁ hlQ₁ hrQ₁ hmulQ₁ hq₂ hlQ₂ hrQ₂ hmulQ₂ hp' hl' hr' hmul' hlev₂ hlevQ₂ hPQ₁ hPQ₂ hM
      hP'₁ hP'₂ σ (Φinv F) ?_
    change SmoothRep.hom Φ₁.hom (SmoothRep.hom Φ₁.inv F) ∈ _
    rw [smoothRep_iso_hom_inv_apply]
    exact hF
  let Ψ : (JQ ⧸ SQ.toSubmodule) →ₗ[ℂ] (JP ⧸ SP.toSubmodule) :=
    SQ.toSubmodule.mapQ SP.toSubmodule Ψ₀ hle
  have hsurj : Function.Surjective Ψ := by
    intro w
    induction w using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective πP.representation
        (pointImage (r₂ ≫ p₂)) 1 x
      refine ⟨Submodule.Quotient.mk (mkQ (SmoothRep.hom Φ₁.hom v)), ?_⟩
      change Submodule.Quotient.mk (Ψ₀ (mkQ (SmoothRep.hom Φ₁.hom v))) = _
      rw [hΨ₀]
      change Submodule.Quotient.mk (mkP (SmoothRep.hom Φ₁.inv (SmoothRep.hom Φ₁.hom v))) = _
      rw [smoothRep_iso_inv_hom_apply]
      rfl
  let ρQ := JQ.ρ.quotient SQ.toSubmodule (fun g _ hv => SQ.apply_mem_toSubmodule g hv)
  let ρP := JP.ρ.quotient SP.toSubmodule (fun g _ hv => SP.apply_mem_toSubmodule g hv)
  show Ideal.map _ (groupAlgebraKernel ρQ (rationalPoints.map aL)) ≤
    groupAlgebraKernel ρP (rationalPoints.map a)
  refine map_groupAlgebraKernel_le ρQ ρP (rationalPoints.map aL) (rationalPoints.map a)
    (rationalPoints.map f) Ψ hsurj ?_
  intro z w
  induction w using Submodule.Quotient.induction_on with
  | H x =>
  obtain ⟨F, rfl⟩ := Jacquet.Localization.mk_surjective πQ.representation
    (pointImage (rQ₂ ≫ q₂)) 1 x
  let m : rationalPoints M := rationalPoints.map a (rationalPoints.map f z)
  have hy : rationalPoints.map aL z = rationalPoints.map (l' ≫ p') m := by
    change _ = rationalPoints.map (l' ≫ p')
      (rationalPoints.map a (rationalPoints.map f z))
    rw [← outer_rationalPoints_map_comp_apply, ← outer_rationalPoints_map_comp_apply, hf]
  have hg : rationalPoints.map (lQ₂ ≫ q₂) (rationalPoints.map aL z) =
      rationalPoints.map (l₂ ≫ p₂) m := by
    rw [hy, ← outer_rationalPoints_map_comp_apply, Category.assoc,
      outer_levi₂_eq hlev₂ hlevQ₂ hM]
  have hyM : rationalPoints.map (lQ₂ ≫ q₂) (rationalPoints.map aL z) ∈ pointImage (l₂ ≫ p₂) :=
    ⟨m, hg.symm⟩
  have hcent : rationalPoints.map aL z ∈ Subgroup.center (rationalPoints L) :=
    haL.isCentralSplitTorus.isCentral.map_mem_center z
  let gQ : rationalPoints G := leviPointsEquiv q₂ lQ₂ hq₂ hlQ₂ (rationalPoints.map aL z)
  let cU : ℂˣ := HaarModulus.closedInverseHalfCharacter (pointImage (rQ₂ ≫ q₂))
    (isClosed_pointImage_comp q₂ rQ₂ hq₂.isClosedSubgroup hrQ₂.1.isClosedSubgroup)
    (pointImage (lQ₂ ≫ q₂)) (pointImage_le_normalizer q₂ lQ₂ rQ₂ hrQ₂)
    (leviPointsEquiv q₂ lQ₂ hq₂ hlQ₂ (rationalPoints.map aL z))
  let cN : ℂˣ := HaarModulus.closedInverseHalfCharacter (pointImage (r₂ ≫ p₂))
    (isClosed_pointImage_comp p₂ r₂ hp₂.isClosedSubgroup hr₂.1.isClosedSubgroup)
    (pointImage (l₂ ≫ p₂)) (pointImage_le_normalizer p₂ l₂ r₂ hr₂)
    (leviPointsEquiv p₂ l₂ hp₂ hl₂ m)
  have hc : cU = cN := by
    refine closedInverseHalfCharacter_eq_of_eq _ _ _ _ _ _ ?_
    refine (outer_modulus_eq hG hp₂ hl₂ hr₂ hmul₂ hq₂ hlQ₂ hrQ₂ hmulQ₂ hp' hl' hr' hmul' hlev₂
      hlevQ₂ hPQ₂ hM hP'₂ _ hcent hyM).symm.trans ?_
    exact congrArg _ (Subtype.ext hg)
  have hL : Ψ (ρQ (rationalPoints.map aL z) (Submodule.Quotient.mk (mkQ F))) =
      Submodule.Quotient.mk ((cU : ℂ) • mkP (Φinv (πQ.representation gQ F))) := by
    change Submodule.Quotient.mk (Ψ₀ ((cU : ℂ) • mkQ (πQ.representation gQ F))) = _
    rw [map_smul]
    rfl
  have hR : ρP (rationalPoints.map a (rationalPoints.map f z))
        (Ψ (Submodule.Quotient.mk (mkQ F))) =
      Submodule.Quotient.mk ((cN : ℂ) • mkP (πP.representation
        (leviPointsEquiv p₂ l₂ hp₂ hl₂ m : rationalPoints G) (Φinv F))) :=
    rfl
  have hΦ : Φinv (πQ.representation gQ F) = πP.representation gQ (Φinv F) :=
    LinearMap.congr_fun ((SmoothRep.hom Φ₁.inv).isIntertwining' gQ) F
  have hgQ : gQ = (leviPointsEquiv p₂ l₂ hp₂ hl₂ m : rationalPoints G) := hg
  refine hL.trans (Eq.trans ?_ hR.symm)
  rw [hc, hΦ, hgQ]

include hG hp₁ hl₁ hr₁ hmul₁ hp₂ hl₂ hr₂ hmul₂ hq₁ hlQ₁ hrQ₁ hmulQ₁ hq₂ hlQ₂ hrQ₂ hmulQ₂
  hp' hl' hr' hmul' hlev₂ hlevQ₂ hPQ₁ hPQ₂ hM hP'₁ hP'₂ in
/-- Renard VII.3.5 (iii), regularity: if `i_{P'}^L(σ)` is `Q₁Q₂`-regular (for the split
component of `L`), then `σ` is `P₁P₂`-regular (for any split component of `M`). -/
theorem outer_isPQRegular
    {A AL : CommGroupScheme (Spec (CommRingCat.of k))} (a : A.toGrp ⟶ M)
    (ha : IsSplitComponent a) (aL : AL.toGrp ⟶ L) (haL : IsSplitComponent aL) :
    haveI := hlQ₁.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology lQ₁ hlQ₁
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q₁ lQ₁ hq₁ hlQ₁
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q₁ lQ₁ hq₁ hlQ₁
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l₁ hl₁
    ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      IsPQRegular q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁ q₂ lQ₂ rQ₂ hq₂ hrQ₂ hlQ₂ hmulQ₂ aL
          ((leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj σ) →
        IsPQRegular p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂ a σ := by
  have := hlQ₁.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology lQ₁ hlQ₁
  have : LocallyCompactSpace (rationalPoints L) := leviPoints_locallyCompactSpace q₁ lQ₁ hq₁ hlQ₁
  have : NonarchimedeanGroup (rationalPoints L) := leviPoints_nonarchimedeanGroup q₁ lQ₁ hq₁ hlQ₁
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l₁ hl₁
  intro σ hreg
  obtain ⟨f, hf⟩ := exists_outer_splitComponent_factor hG hp₁ hl₁ hq₁ hlQ₁ hp' hl' hM ha haL
  exact sup_eq_top_of_map_le (MonoidAlgebra.mapDomainRingHom ℂ (rationalPoints.map f)) hreg
    (outer_splitComponentKernel_map_le hq₁ hlQ₁ hp' hl' hr' hmul' a aL haL f hf σ)
    (outer_pqRegularityKernel_map_le hG hp₁ hl₁ hr₁ hmul₁ hp₂ hl₂ hr₂ hmul₂ hq₁ hlQ₁ hrQ₁ hmulQ₁
      hq₂ hlQ₂ hrQ₂ hmulQ₂ hp' hl' hr' hmul' hlev₂ hlevQ₂ hPQ₁ hPQ₂ hM hP'₁ hP'₂ a aL haL f hf σ)

end Regularity

end Langlands.Aubert.General.RepresentedParabolic
