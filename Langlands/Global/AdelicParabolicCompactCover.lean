import Langlands.Global.AdelicIwasawaAssembly
import Langlands.Global.FinitePlaceIwasawaLocalInput
import Langlands.Global.FiniteCompletionLocalField
import Langlands.Global.InfinitePlaceIwasawaProof
import Langlands.Global.IntegralIwasawaFamilyProof
import Langlands.Global.AdelicLocalCharacterNorm
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactProof
import Langlands.Global.AdelicPositiveDecompositionReduction
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Langlands.Global.AdelicStandardSiegelFactors
import Langlands.Global.AdelicSiegelReductionStatement

/-! # Compact parabolic covers of actual adelic points -/

noncomputable section

universe u v w x y

open scoped Pointwise
open Filter Topology

namespace Langlands.Global.CoordinateCompactAssembly

variable {I : Type u} {A : Type v} [Group A] [TopologicalSpace A]
  {H : I → Type w} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
  {B : Type x} [Group B] {Q : I → Type y} [∀ i, Group (Q i)]

/-- Set version of the coordinate covering assembly. Compact local sets inside
subgroups with a continuous product lift, almost-everywhere absorption and local
source-left covering give one compact global set with source-left covering. -/
theorem exists_isCompact_range_mul_eq_univ
    {π : ∀ i, A →* H i} {K : ∀ i, Subgroup (H i)} (D : CompactProductLift π K)
    (hsep : ∀ a b : A, (∀ i, π i a = π i b) → a = b)
    (f : B →* A) (ρ : ∀ i, B →* Q i) (φ : ∀ i, Q i →* H i)
    (Ω : ∀ i, Set (H i)) (hΩK : ∀ i, Ω i ⊆ K i) (hΩ : ∀ i, IsCompact (Ω i))
    (hcompat : ∀ i b, π i (f b) = φ i (ρ i b))
    (hgood : ∀ a : A, ∀ᶠ i in cofinite, π i a ∈ Ω i)
    (hfiniteLift : ∀ q : ∀ i, Q i, (∀ᶠ i in cofinite, q i = 1) →
      ∃ b : B, ∀ i, ρ i b = q i)
    (hcover : ∀ i, Set.range (φ i) * Ω i = Set.univ) :
    ∃ Ω' : Set A, IsCompact Ω' ∧ (∀ a ∈ Ω', ∀ i, π i a ∈ Ω i) ∧
      Set.range f * Ω' = Set.univ := by
  classical
  let S : Set (∀ i, K i) := Set.univ.pi fun i => Subtype.val ⁻¹' Ω i
  have hS : IsCompact S := by
    apply isCompact_univ_pi
    intro i
    exact IsInducing.subtypeVal.isCompact_preimage' (hΩ i)
      (fun z hz => ⟨⟨z, hΩK i hz⟩, rfl⟩)
  refine ⟨D.lift '' S, hS.image D.continuous_lift, ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩ i
    rw [D.eval_lift]
    exact hk i (Set.mem_univ i)
  · apply Set.eq_univ_of_forall
    intro a
    have hlocal (i : I) : ∃ q : Q i, (φ i q)⁻¹ * π i a ∈ Ω i := by
      have hm : π i a ∈ Set.range (φ i) * Ω i := by
        rw [hcover i]
        exact Set.mem_univ _
      rcases hm with ⟨_, ⟨q, rfl⟩, k, hk, heq⟩
      refine ⟨q, ?_⟩
      rw [← heq, inv_mul_cancel_left]
      exact hk
    let q : ∀ i, Q i := fun i =>
      if π i a ∈ Ω i then 1 else Classical.choose (hlocal i)
    have hq (i : I) : (φ i (q i))⁻¹ * π i a ∈ Ω i := by
      by_cases hi : π i a ∈ Ω i
      · simp [q, hi]
      · simpa [q, hi] using Classical.choose_spec (hlocal i)
    have hqfinite : ∀ᶠ i in cofinite, q i = 1 :=
      (hgood a).mono fun i hi => by simp [q, hi]
    obtain ⟨b, hb⟩ := hfiniteLift q hqfinite
    have hcoord (i : I) : π i ((f b)⁻¹ * a) = (φ i (q i))⁻¹ * π i a := by
      rw [map_mul, map_inv, hcompat i b, hb i]
    let k : ∀ i, K i := fun i =>
      ⟨π i ((f b)⁻¹ * a), by rw [hcoord]; exact hΩK i (hq i)⟩
    have hk : D.lift k = (f b)⁻¹ * a := hsep _ _ fun i => by rw [D.eval_lift]
    refine ⟨f b, ⟨b, rfl⟩, (f b)⁻¹ * a, ⟨k, fun i _ => ?_, hk⟩, mul_inv_cancel_left _ _⟩
    change π i ((f b)⁻¹ * a) ∈ Ω i
    rw [hcoord]
    exact hq i

end Langlands.Global.CoordinateCompactAssembly

namespace Langlands.QuotientIntegration

variable {H : Type u} [Group H] [TopologicalSpace H]

/-- Compactness of a left coset space passes along a continuous surjective
homomorphism carrying the first subgroup into the second. -/
theorem compactSpace_leftQuotient_of_surjective {H' : Type v} [Group H'] [TopologicalSpace H']
    (e : H →* H') (he : Continuous e) (hsurj : Function.Surjective e)
    {Γ : Subgroup H} {Γ' : Subgroup H'} (hΓ : Γ.map e ≤ Γ')
    [CompactSpace (LeftQuotient Γ)] : CompactSpace (LeftQuotient Γ') := by
  have hr : ∀ a b, QuotientGroup.rightRel Γ a b → QuotientGroup.rightRel Γ' (e a) (e b) := by
    intro a b h
    rw [QuotientGroup.rightRel_apply] at h ⊢
    have hm := hΓ ⟨_, h, rfl⟩
    simpa only [map_mul, map_inv] using hm
  let q : LeftQuotient Γ → LeftQuotient Γ' := Quotient.map' e hr
  have hq : Continuous q := he.quotient_map' hr
  have hqs : Function.Surjective q := by
    intro z
    induction z using Quotient.inductionOn with
    | h z =>
      obtain ⟨a, rfl⟩ := hsurj z
      exact ⟨Quotient.mk _ a, rfl⟩
  exact ⟨hqs.range_eq ▸ isCompact_range hq⟩

variable [IsTopologicalGroup H] [LocallyCompactSpace H]

/-- In a locally compact group, a subgroup with compact left coset space has a
compact set of right representatives: `Γ * Ω` is the whole group. -/
theorem exists_isCompact_mul_eq_univ (Γ : Subgroup H) [CompactSpace (LeftQuotient Γ)] :
    ∃ Ω : Set H, IsCompact Ω ∧ (Γ : Set H) * Ω = Set.univ := by
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : H)
  have h1 : (1 : H) ∈ interior C := mem_interior_iff_mem_nhds.mpr hC1
  have hπ : IsOpenMap (leftQuotientMap Γ) := (leftQuotient_isOpenQuotientMap Γ).isOpenMap
  let U : H → Set (LeftQuotient Γ) := fun g =>
    leftQuotientMap Γ '' ((fun z => g * z) '' interior C)
  have hU (g : H) : IsOpen (U g) := hπ _ (isOpenMap_mul_left g _ isOpen_interior)
  have hcov : (Set.univ : Set (LeftQuotient Γ)) ⊆ ⋃ g, U g := by
    intro z _
    induction z using Quotient.inductionOn with
    | h g => exact Set.mem_iUnion.mpr ⟨g, g, ⟨1, h1, mul_one g⟩, rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU hcov
  refine ⟨⋃ g ∈ t, (fun z => g * z) '' C,
    t.isCompact_biUnion fun g _ => hC.image (continuous_const_mul g), ?_⟩
  apply Set.eq_univ_of_forall
  intro h
  have hh := ht (Set.mem_univ (leftQuotientMap Γ h))
  simp only [Set.mem_iUnion] at hh
  obtain ⟨g, hg, _, ⟨c, hc, rfl⟩, hx⟩ := hh
  have hrel : h * (g * c)⁻¹ ∈ Γ :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact hx)
  refine ⟨h * (g * c)⁻¹, hrel, g * c, ?_, inv_mul_cancel_right h (g * c)⟩
  exact Set.mem_biUnion hg ⟨c, interior_subset hc, rfl⟩

end Langlands.QuotientIntegration

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Global.FinitePlaceGroupPoints

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- At every finite place, the actual points of a parabolic subgroup times one
compact set cover the actual completion points. -/
theorem exists_isCompact_parabolic_cover (hG : IsConnectedReductive G)
    {P : GroupScheme (Spec (CommRingCat.of F))} (p : P ⟶ G)
    (hp : IsParabolicSubgroup p) (v : FinitePlace F) :
    ∃ Ω : Set (PlaceGroupPoints F G (.inr v)), IsCompact Ω ∧
      Set.range (P.affinePointsTarget p (placeCompletion F (.inr v))) * Ω = Set.univ := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  let : ValuativeRel (FiniteCompletion F v) := FiniteCompletion.valuativeRel v
  have : IsNonarchimedeanLocalField (FiniteCompletion F v) :=
    FiniteCompletion.isNonarchimedeanLocalField v
  have hG' := baseChanged_isConnectedReductive F G hG v
  let : IsAffineHom (baseChangedGroup F G v).X.hom := hG'.isAffineHom
  let p' := (GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v))).map p
  have hp' : IsParabolicSubgroup p' := baseChange_isParabolicSubgroup F G hG p hp v
  let : TopologicalSpace (rationalPoints (baseChangedGroup F G v)) :=
    Aubert.General.RationalPointFamily.pointTopology
  have := Aubert.General.RepresentedParabolic.compactSpace_leftQuotient_pointImage_of_dynamic
    parabolicDynamic BruhatTits.dynamicParabolicQuotientCompact hG' p' hp'
  let e := baseChangeContinuousMulEquiv F G v
  let Γ : Subgroup (PlaceGroupPoints F G (.inr v)) :=
    (P.affinePointsTarget p (placeCompletion F (.inr v))).range
  have : CompactSpace (QuotientIntegration.LeftQuotient Γ) := by
    refine QuotientIntegration.compactSpace_leftQuotient_of_surjective
      (Γ := Aubert.General.RepresentedParabolic.pointImage p')
      e.toMonoidHom e.continuous e.surjective ?_
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨baseChangeMulEquiv F P v z, (baseChangeMulEquiv_map F G p v z).symm⟩
  obtain ⟨Ω, hΩ, hcover⟩ := QuotientIntegration.exists_isCompact_mul_eq_univ Γ
  exact ⟨Ω, hΩ, hcover⟩

end Langlands.Global.FinitePlaceGroupPoints

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- A compact set of actual adelic points whose product with the actual adelic
image of `p`, parabolic factor on the left, is the whole adelic group. Unlike
`IsParabolicIwasawaCompact`, the compact factor need not be a subgroup. -/
def HasCompactParabolicCover (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G) :
    Prop :=
  ∃ Ω : Set (AdelicGroupPoints F G), IsCompact Ω ∧
    Set.range (map F P G p) * Ω = Set.univ

/-- The same cover with the compact set inside the actual norm-one subgroup. -/
def HasCompactNormOneParabolicCover (P : GroupScheme (Spec (CommRingCat.of F)))
    (p : P ⟶ G) : Prop :=
  ∃ Ω : Set (AdelicGroupPoints F G), IsCompact Ω ∧
    Ω ⊆ (normOneSubgroup F G : Set (AdelicGroupPoints F G)) ∧
    Set.range (map F P G p) * Ω = Set.univ

/-- Local compact covers at every place and one almost-everywhere integral
Iwasawa family give a compact adelic parabolic cover. -/
theorem hasCompactParabolicCover_of_local_integral [IsAffine G.X.left]
    (P : GroupScheme (Spec (CommRingCat.of F))) [IsAffine P.X.left] (p : P ⟶ G)
    (hlocal : ∀ i : Place F, ∃ Ω : Set (PlaceGroupPoints F G i), IsCompact Ω ∧
      Set.range (P.affinePointsTarget p (placeCompletion F i)) * Ω = Set.univ)
    (K : ∀ v : FinitePlace F, Subgroup (FinitePlaceGroupPoints F G v))
    (hK : IntegralIwasawaFamily.IsIntegralIwasawaFamily F G P p K) :
    HasCompactParabolicCover F G P p := by
  classical
  obtain ⟨hlocalK, habsorb, hintegral⟩ := hK
  let K₀ := extendFinite F G K
  have hint : IsUniformlyIntegral F G K₀ := hintegral
  let good : ∀ i : Place F, Set (PlaceGroupPoints F G i) → Prop := fun i Ω =>
    IsCompact Ω ∧ Set.range (P.affinePointsTarget p (placeCompletion F i)) * Ω = Set.univ
  have hae : ∀ᶠ i in cofinite, good i (K₀ i : Set (PlaceGroupPoints F G i)) :=
    eventually_place_of_finite F (hlocalK.mono fun v hv => ⟨hv.1, hv.2.2⟩)
  let Ω := CoordinateCompactPatching.patchFamily good hlocal
    (fun i => (K₀ i : Set (PlaceGroupPoints F G i)))
  have hΩ (i : Place F) : good i (Ω i) :=
    CoordinateCompactPatching.good_patchFamily good hlocal _ i
  have hΩeq : ∀ᶠ i in cofinite, Ω i = K₀ i :=
    CoordinateCompactPatching.patchFamily_eventually_eq good hlocal _ hae
  let L : ∀ i : Place F, Subgroup (PlaceGroupPoints F G i) := fun i =>
    if good i (K₀ i : Set (PlaceGroupPoints F G i)) then K₀ i else ⊤
  have hLeq : ∀ᶠ i in cofinite, L i = K₀ i :=
    hae.mono fun i hi => ite_eq_left hi
  have hΩL (i : Place F) : Ω i ⊆ L i := by
    by_cases hi : good i (K₀ i : Set (PlaceGroupPoints F G i))
    · have h1 : Ω i = K₀ i := CoordinateCompactPatching.patchFamily_eq_of_good good hlocal _ i hi
      have h2 : L i = K₀ i := ite_eq_left hi
      rw [h1, h2]
    · have h2 : L i = ⊤ := ite_eq_right hi
      rw [h2]
      exact fun _ _ => Subgroup.mem_top _
  have hgood (a : AdelicGroupPoints F G) : ∀ᶠ i in cofinite, atPlace F G i a ∈ Ω i := by
    filter_upwards [hΩeq, eventually_atPlace_mem_of_finite F G (K := K₀) habsorb a]
      with i heq hi
    rw [heq]
    exact hi
  obtain ⟨Ω', hc, -, hcov⟩ := CoordinateCompactAssembly.exists_isCompact_range_mul_eq_univ
    (hint.of_eventuallyEq hLeq).compactProductLift (fun _ _ h => ext_atPlace F G h)
    (map F P G p : AdelicGroupPoints F P →* AdelicGroupPoints F G)
    (fun i => (atPlace F P i : AdelicGroupPoints F P →* PlaceGroupPoints F P i))
    (fun i => P.affinePointsTarget p (placeCompletion F i))
    Ω hΩL (fun i => (hΩ i).1) (fun i b => atPlace_map F P p i b) hgood
    (fun q hq => exists_atPlace_eq_of_eventually_one F P q hq) (fun i => (hΩ i).2)
  exact ⟨Ω', hc, hcov⟩

/-- **Compact parabolic covers.** For every connected reductive group over a
number field and every parabolic subgroup `p : P ⟶ G`, some compact set `Ω` of
adelic points satisfies `P(𝔸) · Ω = G(𝔸)`. No finite-place Iwasawa
decomposition is used: at the finitely many exceptional finite places the
compactness of `P(F_v) \ G(F_v)` supplies the local compact set. -/
theorem hasCompactParabolicCover (hG : IsConnectedReductive G)
    {P : GroupScheme (Spec (CommRingCat.of F))} (p : P ⟶ G) (hp : IsParabolicSubgroup p) :
    HasCompactParabolicCover F G P p := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  let : IsAffine P.X.left := isAffine_of_isAffineHom p.hom.hom.left
  obtain ⟨K, hK⟩ := IntegralIwasawaFamily.existenceStatement F G hG P p hp
  apply hasCompactParabolicCover_of_local_integral F G P p ?_ K hK
  rintro (w | v)
  · obtain ⟨L, hcompact, -, hcover⟩ :=
      InfinitePlaceGroupPoints.parabolicIwasawaStatement F G hG P p hp w
    exact ⟨(L : Set (InfinitePlaceGroupPoints F G w)), hcompact, hcover⟩
  · exact FinitePlaceGroupPoints.exists_isCompact_parabolic_cover F G hG p hp v

/-- The inverse compact set covers with the parabolic factor on the right. -/
theorem HasCompactParabolicCover.exists_mul_range_eq_univ [IsAffine G.X.left]
    {P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G}
    (h : HasCompactParabolicCover F G P p) :
    ∃ Ω : Set (AdelicGroupPoints F G), IsCompact Ω ∧
      Ω * Set.range (map F P G p) = Set.univ := by
  obtain ⟨Ω, hc, hcov⟩ := h
  refine ⟨Ω⁻¹, hc.inv, Set.eq_univ_of_forall fun g => ?_⟩
  have hg : g⁻¹ ∈ Set.range (map F P G p) * Ω := by
    rw [hcov]
    exact Set.mem_univ _
  obtain ⟨_, ⟨y, rfl⟩, w, hw, hyw⟩ := hg
  refine ⟨w⁻¹, by simpa using hw, map F P G p y⁻¹, ⟨y⁻¹, rfl⟩, ?_⟩
  beta_reduce at hyw ⊢
  rw [map_inv, ← mul_inv_rev, hyw, inv_inv]

/-- Adelic maps of a composite compose. -/
private theorem map_comp_apply_aux {H K : GroupScheme (Spec (CommRingCat.of F))}
    (f : H ⟶ K) (g : K ⟶ G) (x : AdelicGroupPoints F H) :
    map F H G (f ≫ g) x = map F K G g (map F H K f x) := by
  simp only [map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom,
    Category.assoc]

/-- **Norm-one refinement.** If a split component of `G` factors through the
parabolic `p`, the compact set can be chosen inside the norm-one subgroup:
project the compact set of `hasCompactParabolicCover` to its norm-one factor;
the split-component factor is absorbed into the parabolic. -/
theorem hasCompactNormOneParabolicCover_of_splitComponent [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {P : GroupScheme (Spec (CommRingCat.of F))} (p : P ⟶ G) (hp : IsParabolicSubgroup p)
    {Z : CommGroupScheme (Spec (CommRingCat.of F))} (a : Z.toGrp ⟶ P)
    (ha : IsSplitComponent (a ≫ p)) :
    HasCompactNormOneParabolicCover F G P p := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨Ω₀, hc, hcov⟩ := hasCompactParabolicCover F G hG p hp
  let e := PositiveRealTorus.splitComponentNormOneDecomposition
    centralSplitTorusCharacter F G hG Z (a ≫ p) ha
  refine ⟨(fun z => ((e.symm z).2 : AdelicGroupPoints F G)) '' Ω₀,
    hc.image (continuous_subtype_val.comp (continuous_snd.comp e.symm.continuous)), ?_, ?_⟩
  · rintro _ ⟨z, -, rfl⟩
    exact (e.symm z).2.2
  · apply Set.eq_univ_of_forall
    intro g
    have hg : g ∈ Set.range (map F P G p) * Ω₀ := by
      rw [hcov]
      exact Set.mem_univ _
    obtain ⟨_, ⟨y, rfl⟩, w, hw, hyw⟩ := hg
    have hw' : map F Z.toGrp G (a ≫ p) ((e.symm w).1 : AdelicGroupPoints F Z.toGrp) *
        ((e.symm w).2 : AdelicGroupPoints F G) = w :=
      e.apply_symm_apply w
    refine ⟨map F P G p (y * map F Z.toGrp P a ((e.symm w).1 : AdelicGroupPoints F Z.toGrp)),
      ⟨_, rfl⟩, ((e.symm w).2 : AdelicGroupPoints F G), ⟨w, hw, rfl⟩, ?_⟩
    beta_reduce at hyw ⊢
    rw [map_mul, mul_assoc, ← map_comp_apply_aux, hw', hyw]

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T)
  (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

/-- For an actual Siegel setup, the canonical minimal standard parabolic has a
compact norm-one cover: a compact `Ω ⊆ G(𝔸)¹` with `P_∅(𝔸) · Ω = G(𝔸)`. -/
theorem IsSiegelAlgebraicSetup.hasCompactNormOneParabolicCover
    (hG : IsConnectedReductive G) (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j) :
    HasCompactNormOneParabolicCover F G (Standard.parabolicScheme i ν ∅)
      (Standard.parabolicHom i ν ∅) := by
  obtain ⟨-, -, hmin, -, -, -, -, -, Z₀, z, hz, -⟩ := hS
  apply hasCompactNormOneParabolicCover_of_splitComponent F G hG _ hmin.1
    (CommGroupScheme.groupHom z ≫ torusToStandardParabolic F G T i ν)
  rw [Category.assoc, torusToStandardParabolic_comp]
  exact hz

end Langlands.Global.AdelicSiegelFactors
