import Langlands.Geometry.Building.IwahoriWeylStatement
import Langlands.Geometry.Building.ChamberFiltration
import Langlands.GroupScheme.Rational.SimpleRootParabolicFactorization
import Langlands.GroupScheme.Rational.RelativeTitsSystemStatement
import Langlands.GroupScheme.Rational.RootRankOneFactorizationStatement
import Langlands.GroupScheme.Rational.MinimalStandardDynamicComparison
import Langlands.GroupScheme.Rational.RootSubgroupPositive
import Langlands.GroupScheme.Rational.ReflectionNegation
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Rational.RootSubgroupRealizationProof

/-! # The chamber Iwasawa decomposition from the relative Tits system

For a chamber `C` of the apartment and a generic cocharacter `ν`, KP Theorem 5.3.3 states
`G(F) = U(F) N(F) P_C`. This module derives it from three algebraic inputs on the actual
rational points: the relative Tits system `(G(F), P_∅(F), N(F), S)` (Borel–Tits 5.15–5.16), the
factorization `b = b' u` of `P_∅(F)` along a simple root (`HasSimpleRootParabolicFactorization`)
and the rank-one factorization (KP 2.11.17). The set `X = P(ν)(F) N(F) P_C` contains `1` and is
stable under left multiplication by `P_∅(F) = P(ν)(F)` and by every representative of every
simple reflection, hence is `G(F)` (`Langlands.Group.IsTitsSystem.mem_of_stable`). Stability under
a simple reflection uses KP Lemma 5.3.1 at a chamber, proved here from axiom V 5 and the
constancy of the root filtrations on a chamber. Finally `P(ν)(F) = U(F) Z(F)` by the dynamic
limit and `Z_G(ν) = Z_G(S)`. None of the three algebraic inputs is proved here.
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Group.IsTitsSystem

variable {G : Type u} [Group G] {B N : Subgroup G} {W : Type v} [Group W] {π : N →* W}
  {S : Set W}

/-- The elements `g` with `g * x ∈ X ↔ x ∈ X` for all `x`, as a subgroup. -/
def leftStabilizer (X : Set G) : Subgroup G where
  carrier := {g | ∀ x, g * x ∈ X ↔ x ∈ X}
  one_mem' := fun x => by rw [one_mul]
  mul_mem' := fun {g h} hg hh x => by
    rw [mul_assoc]
    exact (hg (h * x)).trans (hh x)
  inv_mem' := fun {g} hg x => by
    rw [← hg (g⁻¹ * x), mul_inv_cancel_left]

/-- In a Tits system, a set containing `1`, stable under left multiplication by `B` and by
every representative of every simple reflection, is the whole group. -/
theorem mem_of_stable (h : IsTitsSystem B N π S) {X : Set G} (h1 : (1 : G) ∈ X)
    (hB : ∀ b ∈ B, ∀ x ∈ X, b * x ∈ X)
    (hS : ∀ s ∈ S, ∀ n : N, π n = s → ∀ x ∈ X, (n : G) * x ∈ X) (g : G) : g ∈ X := by
  have hBH : B ≤ leftStabilizer X := fun b hb x =>
    ⟨fun hx => by simpa using hB b⁻¹ (B.inv_mem hb) _ hx, hB b hb x⟩
  have hSH : ∀ s ∈ S, ∀ n : N, π n = s → (n : G) ∈ leftStabilizer X := by
    intro s hs n hn x
    refine ⟨fun hx => ?_, hS s hs n hn x⟩
    have hinv : π n⁻¹ = s := by
      rw [map_inv, hn]
      exact inv_eq_of_mul_eq_one_left (h.mul_self s hs)
    simpa using hS s hs n⁻¹ hinv _ hx
  have hNH : ∀ n : N, (n : G) ∈ leftStabilizer X := by
    intro n
    have hw : π n ∈ Subgroup.closure S := by
      rw [h.closure_eq]
      exact Subgroup.mem_top _
    suffices hsuff : ∀ w ∈ Subgroup.closure S, ∀ n : N, π n = w → (n : G) ∈ leftStabilizer X from
      hsuff _ hw n rfl
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem s hs => exact hSH s hs
    | one =>
      intro n hn
      have hk : n ∈ π.ker := hn
      rw [h.ker_eq, Subgroup.mem_subgroupOf] at hk
      exact hBH hk
    | mul w₁ w₂ _ _ ih₁ ih₂ =>
      intro n hn
      obtain ⟨n₁, rfl⟩ := h.surjective w₁
      have h2 : π (n₁⁻¹ * n) = w₂ := by rw [map_mul, hn, map_inv, inv_mul_cancel_left]
      have hm := (leftStabilizer X).mul_mem (ih₁ n₁ rfl) (ih₂ _ h2)
      simpa using hm
    | inv w _ ih =>
      intro n hn
      have hm := (leftStabilizer X).inv_mem (ih n⁻¹ (by rw [map_inv, hn, inv_inv]))
      simpa using hm
  have hH : leftStabilizer X = ⊤ := by
    rw [eq_top_iff, ← h.sup_eq]
    exact sup_le hBH fun g hg => hNH ⟨g, hg⟩
  have hg : g ∈ leftStabilizer X := hH ▸ Subgroup.mem_top g
  simpa using (hg 1).2 h1

end Langlands.Group.IsTitsSystem

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- KP Lemma 5.3.1 for the first opposite factor, at a chamber. -/
theorem oppositeFactor_mem_parahoric
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    {c : characterLattice P.S} (hc : c ∈ relativeRoots P.i) (hnc : -c ∈ relativeRoots P.i)
    {u u' u'' : rationalPoints G} (hu : u ∈ rootGroupPoints P.i c) (hu1 : u ≠ 1)
    (huC : u ∉ P.parahoric C) (hu' : u' ∈ rootGroupPoints P.i (-c))
    (hu'' : u'' ∈ rootGroupPoints P.i (-c)) (hm : u' * u * u'' ∈ normalizerPoints P.i) :
    u' ∈ P.parahoric C := by
  obtain ⟨x, hx0, hxC⟩ := id hC
  have hx : x ∈ C := hxC ▸ AffineRootSystem.mem_facet_self _ x
  have hAS4 := hD.mem_or_two_smul_mem
  have h1 := (P.apartment.rootFixer_eq_filtration_of_isFacet hAS4 hC.isFacet hx hc).1
  have h2 := (P.apartment.rootFixer_eq_filtration_of_isFacet hAS4 hC.isFacet hx hnc).1
  have hnot : ¬ ((0 : ℝ) : WithTop ℝ) ≤ x.val c u := by
    intro h
    apply huC
    have hfix : u ∈ P.apartment.rootFixer c C := by
      rw [h1]
      exact ⟨hu, h⟩
    exact P.rootFixer_le_parahoric ⟨c, hc⟩ C hfix
  have hV5 := x.isValuation.opposite c hc u hu hu1 u' hu' u'' hu'' hm
  have hfix : u' ∈ P.apartment.rootFixer (-c) C := by
    rw [h2]
    refine ⟨hu', ?_⟩
    have hb : x.val c u ≠ ⊤ := fun h => hnot (h ▸ le_top)
    obtain ⟨b, hb'⟩ := WithTop.ne_top_iff_exists.1 hb
    have ha : x.val (-c) u' ≠ ⊤ := by
      intro h
      rw [h, WithTop.top_add] at hV5
      exact WithTop.top_ne_zero hV5
    obtain ⟨a, ha'⟩ := WithTop.ne_top_iff_exists.1 ha
    rw [← ha', ← hb', ← WithTop.coe_add] at hV5
    have hab : a + b = 0 := by exact_mod_cast hV5
    rw [← hb'] at hnot
    have hb0 : b < 0 := by
      have := not_le.1 hnot
      exact_mod_cast this
    rw [← ha']
    exact_mod_cast (by linarith : (0 : ℝ) ≤ a)
  exact P.rootFixer_le_parahoric ⟨-c, hnc⟩ C hfix

/-- KP Lemma 5.3.1 at a chamber: if a nonidentity root point is not in the chamber Iwahori,
both opposite factors of a normalizing factorization are. -/
theorem oppositeFactors_mem_parahoric
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    {c : characterLattice P.S} (hc : c ∈ relativeRoots P.i) (hnc : -c ∈ relativeRoots P.i)
    {u u' u'' : rationalPoints G} (hu : u ∈ rootGroupPoints P.i c) (hu1 : u ≠ 1)
    (huC : u ∉ P.parahoric C) (hu' : u' ∈ rootGroupPoints P.i (-c))
    (hu'' : u'' ∈ rootGroupPoints P.i (-c)) (hm : u' * u * u'' ∈ normalizerPoints P.i) :
    u' ∈ P.parahoric C ∧ u'' ∈ P.parahoric C := by
  refine ⟨P.oppositeFactor_mem_parahoric hD hC hc hnc hu hu1 huC hu' hu'' hm, ?_⟩
  have hinvC : u⁻¹ ∉ P.parahoric C := fun h => huC (by simpa using (P.parahoric C).inv_mem h)
  have hminv : u''⁻¹ * u⁻¹ * u'⁻¹ ∈ normalizerPoints P.i := by
    have := (normalizerPoints P.i).inv_mem hm
    simpa [mul_assoc] using this
  have h := P.oppositeFactor_mem_parahoric hD hC hc hnc ((rootGroupPoints P.i c).inv_mem hu)
    (inv_ne_one.2 hu1) hinvC ((rootGroupPoints P.i (-c)).inv_mem hu'')
    ((rootGroupPoints P.i (-c)).inv_mem hu') hminv
  simpa using (P.parahoric C).inv_mem h

/-- A root point of a root positive on `ν` lies in the dynamic parabolic `P(ν)(F)`. -/
theorem rootGroupPoints_le_dynamicParabolic {ν : cocharacterLattice P.S}
    {d : characterLattice P.S} (hd : 0 < latticePairing P.S d ν) :
    rootGroupPoints P.i d ≤
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ P.i)).carrier (Over.mk (𝟙 _)) :=
  fun _ hv => Dynamic.unipotent_le_parabolic _ _
    (RelativeRoot.subgroup_le_dynamicUnipotent P.i ν hd _ hv)

/-- For `n ∈ N(F)` and a root point `u ∈ U_c(F)`, `n * u ∈ P(ν)(F) N(F) P_C`. If `n · c` is
positive on `ν` then `n u n⁻¹ ∈ P(ν)(F)`; otherwise either `u ∈ P_C`, or the rank-one
factorization `u' u u'' = m ∈ N(F)` has both opposite factors in `P_C` and
`n u = (n u'⁻¹ n⁻¹) (n m) u''⁻¹`. -/
theorem normalizer_mul_rootGroup_mem
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    {ν : cocharacterLattice P.S} (hν : IsGenericCocharacter P.i ν)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (n : normalizerPoints P.i) {c : characterLattice P.S} (hc : c ∈ relativeRoots P.i)
    {u : rationalPoints G} (hu : u ∈ rootGroupPoints P.i c) :
    ∃ b ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ P.i)).carrier (Over.mk (𝟙 _)),
      ∃ n' : normalizerPoints P.i, ∃ p ∈ P.parahoric C,
        (n : rationalPoints G) * u = b * (n' : rationalPoints G) * p := by
  have hd : weylAction P.i n c ∈ relativeRoots P.i := weylAction_mapsTo_relativeRoots P.i n hc
  rcases lt_or_gt_of_ne (hν _ hd) with hneg | hpos
  · by_cases huC : u ∈ P.parahoric C
    · exact ⟨1, one_mem _, n, u, huC, by rw [one_mul]⟩
    have hu1 : u ≠ 1 := fun h => huC (h ▸ one_mem _)
    obtain ⟨⟨u', u''⟩, hp, -⟩ := (hrank c hc u hu hu1).1
    obtain ⟨-, -, hrefl, -⟩ := (hrank c hc u hu hu1).2 _ hp
    have hnc : -c ∈ relativeRoots P.i :=
      IsRelativeReflection.neg_mem_relativeRoots P.i hrefl P.isMaximalSplitTorus.isSplitSubtorus.1
    obtain ⟨hu', hu'', hm⟩ := hp
    obtain ⟨-, hu''C⟩ := P.oppositeFactors_mem_parahoric hD hC hc hnc hu hu1 huC hu' hu'' hm
    have hconj := conj_mem_rootGroupPoints n ((rootGroupPoints P.i (-c)).inv_mem hu')
    rw [map_neg] at hconj
    have hpos : 0 < latticePairing P.S (-weylAction P.i n c) ν := by
      rw [map_neg, LinearMap.neg_apply]
      omega
    refine ⟨(n : rationalPoints G) * u'⁻¹ * (n : rationalPoints G)⁻¹,
      P.rootGroupPoints_le_dynamicParabolic hpos hconj, n * ⟨u' * u * u'', hm⟩, u''⁻¹,
      (P.parahoric C).inv_mem hu''C, ?_⟩
    simp only [Subgroup.coe_mul, mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one]
  · exact ⟨(n : rationalPoints G) * u * (n : rationalPoints G)⁻¹,
      P.rootGroupPoints_le_dynamicParabolic hpos (conj_mem_rootGroupPoints n hu), n, 1,
      one_mem _, by group⟩

/-- Left multiplication by a representative `n₀` of a simple relative reflection maps
`P(ν)(F) N(F) P_C` into itself. Write `b = b' u` with `u` in the simple root group and
`n₀ b' n₀⁻¹ ∈ P(ν)(F)`; then `n₀ b n p = (n₀ b' n₀⁻¹) (n₀ n) (n⁻¹ u n) p`. -/
theorem simpleReflection_mul_mem
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    {ν : cocharacterLattice P.S} (hν : IsGenericCocharacter P.i ν)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hF : HasSimpleRootParabolicFactorization P.i ν)
    (hB : standardParabolicPoints P.i ν ∅ =
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ P.i)).carrier (Over.mk (𝟙 _)))
    {s : relativeWeylGroup P.i} (hs : s ∈ simpleRelativeReflections P.i ν)
    (n₀ : normalizerPoints P.i)
    (hn₀ : QuotientGroup.mk' ((centralizerPoints P.i).subgroupOf (normalizerPoints P.i)) n₀ = s)
    {b : rationalPoints G}
    (hb : b ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ P.i)).carrier (Over.mk (𝟙 _)))
    (n : normalizerPoints P.i) {p : rationalPoints G} (hp : p ∈ P.parahoric C) :
    ∃ b' ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ P.i)).carrier (Over.mk (𝟙 _)),
      ∃ n' : normalizerPoints P.i, ∃ p' ∈ P.parahoric C,
        (n₀ : rationalPoints G) * (b * (n : rationalPoints G) * p) =
          b' * (n' : rationalPoints G) * p' := by
  obtain ⟨a, ha, has⟩ := hs
  obtain ⟨b', hb', u, hu, rfl⟩ := hF a ha s has b (hB ▸ hb)
  have hconj := conj_mem_rootGroupPoints n⁻¹ (a := a) hu
  have ha' : weylAction P.i n⁻¹ a ∈ relativeRoots P.i :=
    weylAction_mapsTo_relativeRoots P.i n⁻¹ has.mem_relativeRoots
  obtain ⟨b₂, hb₂, n₂, p₂, hp₂, heq⟩ :=
    P.normalizer_mul_rootGroup_mem hD hC hν hrank (n₀ * n) ha' hconj
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at heq
  refine ⟨(n₀ : rationalPoints G) * b' * (n₀ : rationalPoints G)⁻¹ * b₂,
    mul_mem (hB ▸ hb' n₀ hn₀) hb₂, n₂, p₂ * p, mul_mem hp₂ hp, ?_⟩
  calc (n₀ : rationalPoints G) * (b' * u * (n : rationalPoints G) * p)
      = (n₀ : rationalPoints G) * b' * (n₀ : rationalPoints G)⁻¹ *
          ((n₀ : rationalPoints G) * (n : rationalPoints G) *
            ((n : rationalPoints G)⁻¹ * u * (n : rationalPoints G))) * p := by group
    _ = _ := by rw [heq]; group

/-- `G(F) = P(ν)(F) N(F) P_C` from the relative Tits system, the simple-root factorization of
`P_∅(F)` and the rank-one factorization. -/
theorem exists_dynamicParabolic_normalizer_parahoric
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    {ν : cocharacterLattice P.S} (hν : IsGenericCocharacter P.i ν)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hF : HasSimpleRootParabolicFactorization P.i ν) (hTits : HasRelativeTitsSystem P.i ν)
    (hB : standardParabolicPoints P.i ν ∅ =
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ P.i)).carrier (Over.mk (𝟙 _)))
    (g : rationalPoints G) :
    ∃ b ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ P.i)).carrier (Over.mk (𝟙 _)),
      ∃ n : normalizerPoints P.i, ∃ p ∈ P.parahoric C,
        g = b * (n : rationalPoints G) * p := by
  refine hTits.isTitsSystem.mem_of_stable
    (X := {g | ∃ b ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ P.i)).carrier
      (Over.mk (𝟙 _)), ∃ n : normalizerPoints P.i, ∃ p ∈ P.parahoric C,
        g = b * (n : rationalPoints G) * p}) ?_ ?_ ?_ g
  · exact ⟨1, one_mem _, 1, 1, one_mem _, by simp⟩
  · rintro b₀ hb₀ x ⟨b, hb, n, p, hp, rfl⟩
    exact ⟨b₀ * b, mul_mem (hB ▸ hb₀) hb, n, p, hp, by group⟩
  · rintro s hs n₀ hn₀ x ⟨b, hb, n, p, hp, rfl⟩
    obtain ⟨b', hb', n', p', hp', h⟩ :=
      P.simpleReflection_mul_mem hD hC hν hrank hF hB hs n₀ hn₀ hb n hp
    exact ⟨b', hb', n', p', hp', h⟩

/-- **KP Theorem 5.3.3 for one datum, from the relative Tits system.** Given the relative Tits
system of `(S, ν)`, the simple-root factorization of `P_∅(F)` and the rank-one factorization,
`G(F) = U(F) N(F) P_C`, where `U` is the unipotent radical of the minimal parabolic. -/
theorem iwasawaDecomposition_of_relativeTitsSystem
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    {ν : cocharacterLattice P.S} (hν : IsGenericCocharacter P.i ν)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hF : HasSimpleRootParabolicFactorization P.i ν) (hTits : HasRelativeTitsSystem P.i ν) :
    P.IwasawaDecomposition C ν := by
  have hG := P.isConnectedReductive
  have hi := P.isMaximalSplitTorus
  have hB : standardParabolicPoints P.i ν ∅ =
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ P.i)).carrier (Over.mk (𝟙 _)) := by
    rw [standardParabolicPoints, standardParabolic_empty_eq_dynamic_of_generic P.i ν hG hi hν]
  have hU : standardUnipotentPoints P.i ν ∅ =
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ P.i)).carrier (Over.mk (𝟙 _)) := by
    rw [standardUnipotentPoints, standardUnipotent_empty_eq_dynamic P.i ν hG hi]
  have hZ := genericCentralizer F G hG P.S P.i hi ν hν
  intro g
  obtain ⟨b, hb, n, p, hp, rfl⟩ :=
    P.exists_dynamicParabolic_normalizer_parahoric hD hC hν hrank hF hTits hB g
  have hl : Dynamic.limit (CommGroupScheme.groupHom ν ≫ P.i) ⟨b, hb⟩ ∈ centralizerPoints P.i := by
    rw [← torusCentralizer_carrier_base, ← hZ]
    exact Dynamic.limit_mem_centralizer _ ⟨b, hb⟩
  refine ⟨b * (Dynamic.limit (CommGroupScheme.groupHom ν ≫ P.i) ⟨b, hb⟩)⁻¹,
    hU ▸ Dynamic.mul_inv_limit_mem_unipotent _ ⟨b, hb⟩,
    ⟨_, centralizerPoints_le_normalizerPoints P.i hl⟩ * n, p, hp, ?_⟩
  simp only [Subgroup.coe_mul, mul_assoc, inv_mul_cancel_left]

end Langlands.Geometry.Building.ParahoricBuildingData

namespace Langlands.Geometry.Building

/-- **KP Theorem 5.3.3 from the algebraic structure statements.** The relative Tits system, the
rank-one factorization, the relative root system, the standard parabolic endpoints and the
ordered product of root subgroups give the chamber Iwasawa decomposition. -/
theorem iwasawaDecompositionStatement_of_statements
    (hTits : RelativeTitsSystemStatement.{u}) (hrank : RootRankOneFactorizationStatement.{u})
    (hroot : RelativeRootSystemStatement.{u}) (hE : StandardParabolicEndpointsStatement.{u})
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u}) :
    IwasawaDecompositionStatement.{u} := by
  intro F _ _ _ _ G _ P _ _ hD C ν hC hν
  have hG := P.isConnectedReductive
  have hi := P.isMaximalSplitTorus
  exact P.iwasawaDecomposition_of_relativeTitsSystem hD hC hν (hrank F G hG P.S P.i hi)
    (hasSimpleRootParabolicFactorization_of_statements hroot hE genericCentralizer hprod
      F G hG P.S P.i hi ν hν)
    (hTits F G hG P.S P.i hi ν hν)

/-- **KP Theorem 5.3.3 from the structural statements alone**, with the relative Tits system
supplied by `relativeTitsSystemStatement_of_structuralStatements` and the proved
`genericCentralizer` and `RelativeRoot.rootSubgroupRealization`. -/
theorem iwasawaDecompositionStatement_of_structuralStatements
    (hcox : RelativeWeylCoxeterStatement.{u}) (hE : StandardParabolicEndpointsStatement.{u})
    (hBr : RationalBruhatStatement.{u}) (hrank : RootRankOneFactorizationStatement.{u})
    (hroot : RelativeRootSystemStatement.{u})
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    (hVec : RelativeRoot.RootSubgroupVectorStatement.{u}) :
    IwasawaDecompositionStatement.{u} :=
  iwasawaDecompositionStatement_of_statements
    (relativeTitsSystemStatement_of_structuralStatements hcox hE hBr hrank hroot
      genericCentralizer hprod RelativeRoot.rootSubgroupRealization hVec)
    hrank hroot hE hprod

/-- The chamber Iwasawa decomposition retains the relative Tits system, the rank-one
factorization, the relative root system, the standard parabolic endpoints and the ordered
product of root subgroups as explicit premises. -/
def IwasawaDecompositionReductionStatement : Prop :=
  RelativeTitsSystemStatement.{u} → RootRankOneFactorizationStatement.{u} →
    RelativeRootSystemStatement.{u} → StandardParabolicEndpointsStatement.{u} →
      RelativeRoot.DynamicRootOrderedProductStatement.{u} → IwasawaDecompositionStatement.{u}

theorem iwasawaDecompositionReduction : IwasawaDecompositionReductionStatement.{u} :=
  fun hTits hrank hroot hE hprod =>
    iwasawaDecompositionStatement_of_statements hTits hrank hroot hE hprod

end Langlands.Geometry.Building
