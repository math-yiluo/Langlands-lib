import Langlands.Representation.Intertwining.PQIntertwiningCompositionReduction
import Langlands.GroupScheme.Rational.DynamicUnipotentIntersectionRoots
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof
import Langlands.GroupScheme.Rational.ParabolicRootRadicals
import Langlands.GroupScheme.Rational.ParabolicOppositeNonnegCone
import Langlands.GroupScheme.Rational.StandardLeviStandardFamiliesProof
import Langlands.GroupScheme.Rational.CentralRootRestriction
import Langlands.GroupScheme.Rational.RootRayDecomposition
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Dynamic.OppositeParabolicUniquenessProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.Representation.Exponents.LeviJacquetContragredientStructure
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Plancherel.StandardIntertwiningOppositeCharts

/-! # The product decomposition `V₁₃ = V₁₂ V₂₃` behind Renard VII.3.5 (i) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology Filter Pointwise
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

section Generic

/-- If `X ⊆ Y₁ ∪ Y₂` with `Y₁`, `Y₂` finite and disjoint and `|Y₁| + |Y₂| = |X|`, then
`Y₁ ∪ Y₂ ⊆ X`. -/
theorem union_subset_of_ncard_add_eq {α : Type*} {X Y₁ Y₂ : Set α} (hY₁ : Y₁.Finite)
    (hY₂ : Y₂.Finite) (hcover : X ⊆ Y₁ ∪ Y₂) (hdisj : Disjoint Y₁ Y₂)
    (hcard : Y₁.ncard + Y₂.ncard = X.ncard) : Y₁ ∪ Y₂ ⊆ X := by
  have hu : (Y₁ ∪ Y₂).ncard = X.ncard := by rw [Set.ncard_union_eq hdisj hY₁ hY₂, hcard]
  exact (Set.eq_of_subset_of_ncard_le hcover hu.le (hY₁.union hY₂)).symm.subset

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]

/-- Restriction of a multiplication chart `A ∩ C × B ≃ₜ C` to `K ∩ C`, when `K ∩ A ≤ C` and
`B ≤ K`: multiplication `(K ∩ A) × B → K ∩ C` is a homeomorphism. -/
def infChartHomeomorph {K A B C : Subgroup Γ} (e : A.subgroupOf C × B ≃ₜ C)
    (he : ∀ x, (e x : Γ) = ((x.1 : C) : Γ) * (x.2 : Γ))
    (hKA : K ⊓ A ≤ C) (hBK : B ≤ K) :
    (K ⊓ A : Subgroup Γ) × B ≃ₜ (K ⊓ C : Subgroup Γ) where
  toFun x := ⟨e (⟨⟨x.1, hKA x.1.2⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp x.1.2).2⟩,
      x.2), Subgroup.mem_inf.mpr ⟨by
        rw [he]
        exact K.mul_mem (Subgroup.mem_inf.mp x.1.2).1 (hBK x.2.2), (e _).2⟩⟩
  invFun y :=
    (⟨((e.symm ⟨y, (Subgroup.mem_inf.mp y.2).2⟩).1 : C), Subgroup.mem_inf.mpr ⟨by
        have h := he (e.symm ⟨y, (Subgroup.mem_inf.mp y.2).2⟩)
        rw [Homeomorph.apply_symm_apply] at h
        have h' : (((e.symm ⟨y, (Subgroup.mem_inf.mp y.2).2⟩).1 : C) : Γ) =
            (y : Γ) * ((e.symm ⟨y, (Subgroup.mem_inf.mp y.2).2⟩).2 : Γ)⁻¹ := by
          rw [eq_mul_inv_iff_mul_eq]
          exact h.symm
        rw [h']
        exact K.mul_mem (Subgroup.mem_inf.mp y.2).1
          (K.inv_mem (hBK (e.symm ⟨y, (Subgroup.mem_inf.mp y.2).2⟩).2.2)),
      Subgroup.mem_subgroupOf.mp (e.symm ⟨y, (Subgroup.mem_inf.mp y.2).2⟩).1.2⟩⟩,
      (e.symm ⟨y, (Subgroup.mem_inf.mp y.2).2⟩).2)
  left_inv x := by
    have h : e.symm ⟨(e (⟨⟨x.1, hKA x.1.2⟩,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp x.1.2).2⟩, x.2) : Γ), (e _).2⟩ =
        (⟨⟨x.1, hKA x.1.2⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp x.1.2).2⟩, x.2) :=
      e.symm_apply_apply _
    ext
    · simp only [h]
    · simp only [h]
  right_inv y := by
    apply Subtype.ext
    change ((e (e.symm ⟨y, (Subgroup.mem_inf.mp y.2).2⟩) : C) : Γ) = y
    rw [Homeomorph.apply_symm_apply]
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine continuous_subtype_val.comp (e.continuous.comp ?_)
    exact Continuous.prodMk (((continuous_subtype_val.comp continuous_fst).subtype_mk _).subtype_mk _)
      continuous_snd
  continuous_invFun := by
    have hy : Continuous fun y : (K ⊓ C : Subgroup Γ) =>
        e.symm ⟨y, (Subgroup.mem_inf.mp y.2).2⟩ :=
      e.symm.continuous.comp (continuous_subtype_val.subtype_mk _)
    refine Continuous.prodMk ?_ (continuous_snd.comp hy)
    exact ((continuous_subtype_val.comp (continuous_subtype_val.comp
      (continuous_fst.comp hy))).subtype_mk _)

theorem infChartHomeomorph_apply {K A B C : Subgroup Γ} (e : A.subgroupOf C × B ≃ₜ C)
    (he : ∀ x, (e x : Γ) = ((x.1 : C) : Γ) * (x.2 : Γ))
    (hKA : K ⊓ A ≤ C) (hBK : B ≤ K) (x : (K ⊓ A : Subgroup Γ) × B) :
    (infChartHomeomorph e he hKA hBK x : Γ) = (x.1 : Γ) * (x.2 : Γ) :=
  he _

/-- The existence form of `infChartHomeomorph`, for subgroups given up to equality. -/
theorem exists_mul_homeomorph_of_chart {K A B C V₁ V₂ V₃ : Subgroup Γ}
    (e : A.subgroupOf C × B ≃ₜ C) (he : ∀ x, (e x : Γ) = ((x.1 : C) : Γ) * (x.2 : Γ))
    (hKA : K ⊓ A ≤ C) (hBK : B ≤ K) (h₁ : V₁ = K ⊓ A) (h₂ : V₂ = B) (h₃ : V₃ = K ⊓ C) :
    ∃ f : V₁ × V₂ ≃ₜ V₃, ∀ x, (f x : Γ) = (x.1 : Γ) * (x.2 : Γ) := by
  subst h₁ h₂ h₃
  exact ⟨infChartHomeomorph e he hKA hBK, infChartHomeomorph_apply e he hKA hBK⟩

end Generic

open GroupScheme

section Pairing

variable {k : Type u} [Field k] {A : CommGroupScheme (Spec (CommRingCat.of k))}

theorem latticePairing_neg_right (β : characterLattice A) (ν : cocharacterLattice A) :
    latticePairing A β (-ν) = -latticePairing A β ν :=
  map_neg _ _

theorem latticePairing_nsmul_left (β : characterLattice A) (n : ℕ) (ν : cocharacterLattice A) :
    latticePairing A (n • β) ν = (n : ℤ) * latticePairing A β ν := by
  simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]

theorem nat_mul_pos_iff {n : ℕ} (hn : 0 < n) (x : ℤ) : 0 < (n : ℤ) * x ↔ 0 < x := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  constructor
  · intro h
    by_contra h'
    have h'' := not_lt.mp h'
    nlinarith
  · intro h
    exact mul_pos hn' h

theorem nat_mul_neg_iff {n : ℕ} (hn : 0 < n) (x : ℤ) : (n : ℤ) * x < 0 ↔ x < 0 := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  constructor
  · intro h
    by_contra h'
    have h'' := not_lt.mp h'
    nlinarith
  · intro h
    nlinarith

end Pairing

/-- Cocharacter data for one represented parabolic `P = MN` and an opposite `P̄ = MN̄` with
Levi `m₀ : M ⟶ G`, read on a split component `a` of `M`: a cocharacter `λ` of `A` with
`roots(N) = {λ > 0}`, `roots(N̄) = {λ < 0}`, `N(F) = U(λ)(F)`, `N̄(F) = U(-λ)(F)`,
`M = Z(λ)`, and `⟨β, λ⟩ ≠ 0` for every root `β`. -/
theorem exists_oppositePair_cocharacter
    {k : Type u} [Field k] {G M P N Pb Nb : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] (hG : IsConnectedReductive G)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a) {m₀ : M ⟶ G}
    {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} (hp : IsParabolicSubgroup p)
    (hl : IsRationalLeviSubgroup l) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    {pb : Pb ⟶ G} {lb : M ⟶ Pb} {rb : Nb ⟶ Pb} (hpb : IsParabolicSubgroup pb)
    (hlb : IsRationalLeviSubgroup lb) (hrb : LeviSubgroup.IsGeometricUnipotentRadical rb)
    (hm : l ≫ p = m₀) (hmb : lb ≫ pb = m₀)
    (hpts : pointImage p ⊓ pointImage pb = pointImage m₀) :
    ∃ lam : cocharacterLattice A,
      RelativeRoot.subgroupRelativeRoots (a ≫ m₀) (SubgroupFunctor.range (r ≫ p)) =
          positiveRelativeRoots (a ≫ m₀) lam ∧
      RelativeRoot.subgroupRelativeRoots (a ≫ m₀) (SubgroupFunctor.range (rb ≫ pb)) =
          positiveRelativeRoots (a ≫ m₀) (-lam) ∧
      pointImage (r ≫ p) =
          (Dynamic.unipotent (CommGroupScheme.groupHom lam ≫ a ≫ m₀)).carrier
            (Over.mk (𝟙 _)) ∧
      pointImage (rb ≫ pb) =
          (Dynamic.unipotent (CommGroupScheme.groupHom (-lam) ≫ a ≫ m₀)).carrier
            (Over.mk (𝟙 _)) ∧
      SubgroupFunctor.range m₀ =
          Dynamic.centralizer (CommGroupScheme.groupHom lam ≫ a ≫ m₀) ∧
      ∀ β ∈ relativeRoots (a ≫ m₀), latticePairing A β lam ≠ 0 := by
  subst hm
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨R⟩ := parabolicRootPresentationExistence k G hG P M A p l a hp hl ha
  obtain ⟨S⟩ := parabolicRootPresentationExistence k G hG Pb M A pb lb a hpb hlb ha
  have hpoints : (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)) ⊓
      (SubgroupFunctor.range pb).carrier (Over.mk (𝟙 _)) =
      (SubgroupFunctor.range (l ≫ p)).carrier (Over.mk (𝟙 _)) := by
    simpa only [pointImage_eq_range_carrier] using hpts
  have hsigns := R.opposite_componentRoot_signs S hG hmb hpoints
  refine ⟨R.splitComponentCocharacter, R.subgroupRelativeRoots_radical hr, ?_, ?_, ?_,
    R.levi_eq_splitComponentCocharacter, ?_⟩
  · have h := S.subgroupRelativeRoots_radical hrb
    rw [hmb] at h
    rw [h]
    ext β
    simp only [positiveRelativeRoots, Set.mem_ofPred_eq, latticePairing_neg_right, neg_pos]
    exact ⟨fun h => ⟨h.1, (hsigns β h.1).2.mp h.2⟩, fun h => ⟨h.1, (hsigns β h.1).2.mpr h.2⟩⟩
  · rw [pointImage_eq_range_carrier, R.range_comp_radical_eq hr]
  · rw [groupHom_neg_comp_eq_oppositeCocharacter]
    exact pointImage_opposite_radical_eq_dynamic parabolicDynamic
      oppositeDynamicParabolicUniqueness hG _ l R.parabolic_eq_splitComponentCocharacter
      R.levi_eq_splitComponentCocharacter hpb hlb hrb hmb hpts
  · intro β hβ hzero
    have : IsAffineHom M.X.hom := hl.isConnectedReductive.isAffineHom
    have : Smooth M.X.hom := hl.isConnectedReductive.smooth
    have := (hl.isClosedSubgroup.comp hp.isClosedSubgroup).mono
    have hfac := relativeRoots_centralizer_factor dynamicLie (a ≫ l ≫ p) a (l ≫ p) rfl
      R.splitComponentCocharacter
      ⟨Over.mono_of_mono_left _, R.levi_eq_splitComponentCocharacter⟩
    have hβa : β ∈ relativeRoots a := by
      rw [hfac]
      exact ⟨hβ, hzero⟩
    have hc : IsCentral (CommGroupScheme.groupHom (𝟙 A) ≫ a) := by
      change IsCentral (𝟙 A.toGrp ≫ a)
      rw [Category.id_comp]
      exact ha.1.2
    have hz := root_restrict_eq_zero_of_isCentral a (𝟙 A) ha.1.1.1 hc hβa
    exact (mem_relativeRoots.mp hβa).1 (by simpa using hz)

/-- The product decomposition behind Renard VII.3.5 (i) (printed p.239): under the root-distance
hypothesis `d(P₁, P₃) = d(P₁, P₂) + d(P₂, P₃)`, multiplication
`(N̄₁ ∩ N₂)(F) × (N̄₂ ∩ N₃)(F) → (N̄₁ ∩ N₃)(F)` is a homeomorphism. -/
theorem pqCompositionProduct : PQCompositionProductStatement.{u} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ M P₁ N₁ P₂ N₂ P₃ N₃ Pb₁ Nb₁ Pb₂ Nb₂ Pb₃ Nb₃ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
      p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ p₃ l₃ r₃ hp₃ hl₃ hr₃ hmul₃
      pb₁ lb₁ rb₁ hpb₁ hlb₁ hrb₁ hmulb₁ pb₂ lb₂ rb₂ hpb₂ hlb₂ hrb₂ hmulb₂
      pb₃ lb₃ rb₃ hpb₃ hlb₃ hrb₃ hmulb₃ h21 h31 hb1 hb2 hb3 ho1 ho2 ho3 A a ha rootsIn d hd hd1
    V₁₂ V₂₃ V₁₃
  have : Smooth G.X.hom := hG.smooth
  have hS : IsSplitTorus A.toGrp := ha.1.1.1
  obtain ⟨lam₁, hR₁, hRb₁, hN₁, hNb₁, hZ₁, h0₁⟩ :=
    exists_oppositePair_cocharacter hG ha hp₁ hl₁ hr₁ hpb₁ hlb₁ hrb₁ rfl hb1 ho1
  obtain ⟨lam₂, hR₂, hRb₂, hN₂, hNb₂, hZ₂, h0₂⟩ :=
    exists_oppositePair_cocharacter hG ha hp₂ hl₂ hr₂ hpb₂ hlb₂ hrb₂ h21 hb2 ho2
  obtain ⟨lam₃, hR₃, hRb₃, hN₃, hNb₃, hZ₃, h0₃⟩ :=
    exists_oppositePair_cocharacter hG ha hp₃ hl₃ hr₃ hpb₃ hlb₃ hrb₃ h31 hb3 ho3
  -- The root-distance hypothesis in terms of the three cocharacters.
  dsimp only [d, rootsIn] at hd
  rw [hR₁, hR₂, hRb₂, hRb₃] at hd
  set I := RelativeRoot.indivisibleRoots (a ≫ l₁ ≫ p₁) with hI
  have hfin : (relativeRoots (a ≫ l₁ ≫ p₁)).Finite := hS.finite_relativeRoots _
  have hcover : (positiveRelativeRoots (a ≫ l₁ ≫ p₁) lam₁ ∩ I) ∩
      (positiveRelativeRoots (a ≫ l₁ ≫ p₁) (-lam₃) ∩ I) ⊆
      ((positiveRelativeRoots (a ≫ l₁ ≫ p₁) lam₁ ∩ I) ∩
        (positiveRelativeRoots (a ≫ l₁ ≫ p₁) (-lam₂) ∩ I)) ∪
      ((positiveRelativeRoots (a ≫ l₁ ≫ p₁) lam₂ ∩ I) ∩
        (positiveRelativeRoots (a ≫ l₁ ≫ p₁) (-lam₃) ∩ I)) := by
    rintro β ⟨⟨⟨hβ, h1⟩, hβI⟩, ⟨-, h3⟩, -⟩
    rcases lt_trichotomy (latticePairing A β lam₂) 0 with h2 | h2 | h2
    · left
      refine ⟨⟨⟨hβ, h1⟩, hβI⟩, ⟨hβ, ?_⟩, hβI⟩
      rw [latticePairing_neg_right]
      exact neg_pos.mpr h2
    · exact absurd h2 (h0₂ β hβ)
    · right
      exact ⟨⟨⟨hβ, h2⟩, hβI⟩, ⟨hβ, h3⟩, hβI⟩
  have hdisj : Disjoint ((positiveRelativeRoots (a ≫ l₁ ≫ p₁) lam₁ ∩ I) ∩
        (positiveRelativeRoots (a ≫ l₁ ≫ p₁) (-lam₂) ∩ I))
      ((positiveRelativeRoots (a ≫ l₁ ≫ p₁) lam₂ ∩ I) ∩
        (positiveRelativeRoots (a ≫ l₁ ≫ p₁) (-lam₃) ∩ I)) := by
    refine Set.disjoint_left.mpr fun β h h' => ?_
    have hneg := h.2.1.2
    have hpos := h'.1.1.2
    rw [latticePairing_neg_right] at hneg
    linarith
  have hsub := union_subset_of_ncard_add_eq (hfin.subset fun _ h => h.1.1.1)
    (hfin.subset fun _ h => h.1.1.1) hcover hdisj hd
  -- `V₁₂ ≤ N₃`: a root positive on `λ₂` and on `-λ₁` is positive on `λ₃`.
  have hKA := RelativeRoot.dynamicUnipotent_inf_le_of_positiveRoots hG.smooth hG.connectedSpace
    hS (a ≫ l₁ ≫ p₁) (-lam₁) lam₂ lam₃ (by
      intro β hβ h1
      by_contra hneg
      have h3 : latticePairing A β lam₃ < 0 := lt_of_le_of_ne (not_lt.mp hneg) (h0₃ β hβ.1)
      obtain ⟨α, ⟨hαI, hα2⟩, n, -, hn, rfl⟩ :=
        RelativeRoot.exists_indivisiblePositiveRoot_ray (a ≫ l₁ ≫ p₁) lam₂ hβ.1 hβ.2
      rw [latticePairing_nsmul_left, nat_mul_neg_iff hn] at h3
      rw [latticePairing_neg_right, latticePairing_nsmul_left, neg_pos, nat_mul_neg_iff hn] at h1
      have hαX := hsub (Or.inr ⟨⟨⟨hαI.1, hα2⟩, hαI⟩,
        ⟨hαI.1, by rw [latticePairing_neg_right]; linarith⟩, hαI⟩)
      have := hαX.1.1.2
      linarith)
  -- `V₂₃ ≤ N̄₁`: a root positive on `λ₃` and on `-λ₂` is positive on `-λ₁`.
  have hBK := RelativeRoot.dynamicUnipotent_inf_le_of_positiveRoots hG.smooth hG.connectedSpace
    hS (a ≫ l₁ ≫ p₁) (-lam₂) lam₃ (-lam₁) (by
      intro β hβ h2
      rw [latticePairing_neg_right, neg_pos] at h2 ⊢
      by_contra hneg
      have h1 : 0 < latticePairing A β lam₁ :=
        lt_of_le_of_ne (not_lt.mp hneg) (Ne.symm (h0₁ β hβ.1))
      obtain ⟨α, ⟨hαI, hα3⟩, n, -, hn, rfl⟩ :=
        RelativeRoot.exists_indivisiblePositiveRoot_ray (a ≫ l₁ ≫ p₁) lam₃ hβ.1 hβ.2
      rw [latticePairing_nsmul_left, nat_mul_pos_iff hn] at h1
      rw [latticePairing_nsmul_left, nat_mul_neg_iff hn] at h2
      have hαX := hsub (Or.inl ⟨⟨⟨hαI.1, h1⟩, hαI⟩,
        ⟨hαI.1, by rw [latticePairing_neg_right]; linarith⟩, hαI⟩)
      have := hαX.2.1.2
      rw [latticePairing_neg_right] at this
      linarith)
  -- The chart `N₃(F) = (N₂ ∩ N₃)(F) × (N̄₂ ∩ N₃)(F)`.
  have hZ : (Dynamic.centralizer (CommGroupScheme.groupHom lam₃ ≫ a ≫ l₁ ≫ p₁)).carrier
        (Over.mk (𝟙 _)) =
      (Dynamic.centralizer (CommGroupScheme.groupHom lam₂ ≫ a ≫ l₁ ≫ p₁)).carrier
        (Over.mk (𝟙 _)) := by
    rw [← hZ₃, ← hZ₂]
  rw [groupHom_neg_comp_eq_oppositeCocharacter (a ≫ l₁ ≫ p₁) lam₂] at hBK
  refine exists_mul_homeomorph_of_chart
    (Plancherel.StandardIntertwining.OppositeCharts.secondChart hZ) (fun _ => rfl) hKA hBK
    ?_ ?_ ?_
  · change pointImage (rb₁ ≫ pb₁) ⊓ pointImage (r₂ ≫ p₂) = _
    rw [hNb₁, hN₂]
  · change pointImage (rb₂ ≫ pb₂) ⊓ pointImage (r₃ ≫ p₃) = _
    rw [hNb₂, hN₃, groupHom_neg_comp_eq_oppositeCocharacter]
    rfl
  · change pointImage (rb₁ ≫ pb₁) ⊓ pointImage (r₃ ≫ p₃) = _
    rw [hNb₁, hN₃]

end Langlands.Aubert.General.RepresentedParabolic
