import Langlands.Geometry.Building.KPLocalMoyPrasadIntersectionCell
import Langlands.Geometry.Building.ApartmentFacetClosureFixing
import Langlands.GroupScheme.Rational.CocharacterCentralizer
import Langlands.GroupScheme.Rational.RootFactorPairReflection
import Langlands.GroupScheme.Rational.SemigroupCommutatorReduction
import Langlands.LinearAlgebra.RootFaceReflection

/-!
# Levi decomposition of the groups `G(K)_{x,r}` at positive depth

For a real cocharacter `ν`, a positive-depth product cover of `G(K)_{x,r}` along a generic
integral cocharacter refining the signs of `ν` regroups into
`U_{Φ⁻(ν),x,r} · M_{ν,x,r} · U_{Φ⁺(ν),x,r}`, whose factors are unique in
`U⁻(ν) × M_ν × U⁺(ν)`. This gives the Iwahori factorization and the Levi intersection at
positive depth.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal commutatorElement Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building

section Signs

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] (i : S.toGrp ⟶ G)

/-- Every real cocharacter has an integral cocharacter with the same signs on the roots. -/
theorem exists_cocharacter_sign_eq (hfin : (relativeRoots i).Finite) (ν : V S) :
    ∃ lam : cocharacterLattice S, ∀ b ∈ relativeRoots i,
      (0 < latticePairing S b lam ↔ 0 < eval S b ν) ∧
        (latticePairing S b lam < 0 ↔ eval S b ν < 0) := by
  classical
  obtain ⟨lam, hlam⟩ := Langlands.LinearAlgebra.RootFaceCone.exists_int_sign_realization
    (hfin.toFinset ∪ hfin.toFinset.image Neg.neg) (fun b => latticePairing S b)
    (fun b => eval S b) (fun b t n => eval_tmul S b t n) ν
  refine ⟨lam, fun b hb => ⟨hlam b (Finset.mem_union_left _ (hfin.mem_toFinset.2 hb)), ?_⟩⟩
  have h := hlam (-b) (Finset.mem_union_right _
    (Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 hb)))
  simp only [map_neg, LinearMap.neg_apply, eval_neg_char, neg_pos] at h
  exact h

/-- Every integral cocharacter is refined by a generic one: roots positive (negative) on
`lam` stay positive (negative). -/
theorem exists_genericCocharacter_refining [LocallyOfFiniteType G.X.hom]
    (hT : IsSplitTorus S.toGrp) (lam : cocharacterLattice S) :
    ∃ mu : cocharacterLattice S, IsGenericCocharacter i mu ∧ ∀ b ∈ relativeRoots i,
      (0 < latticePairing S b lam → 0 < latticePairing S b mu) ∧
        (latticePairing S b lam < 0 → latticePairing S b mu < 0) := by
  classical
  have hfin := hT.finite_relativeRoots i
  obtain ⟨ν₀, hν₀⟩ := hT.exists_genericCocharacter i
  set M : ℤ := 1 + ∑ b ∈ hfin.toFinset, |latticePairing S b ν₀| with hMdef
  have hM : ∀ b ∈ relativeRoots i, |latticePairing S b ν₀| < M := by
    intro b hb
    have h := Finset.single_le_sum (f := fun b => |latticePairing S b ν₀|)
      (fun _ _ => abs_nonneg _) (hfin.mem_toFinset.2 hb)
    omega
  have hpair : ∀ b, latticePairing S b (M • lam + ν₀) =
      M * latticePairing S b lam + latticePairing S b ν₀ := by
    intro b
    rw [map_add, map_zsmul, smul_eq_mul]
  refine ⟨M • lam + ν₀, fun b hb => ?_, fun b hb => ⟨fun hp => ?_, fun hn => ?_⟩⟩
  · rw [hpair]
    have hq := abs_lt.1 (hM b hb)
    rcases lt_trichotomy (latticePairing S b lam) 0 with hp | hp | hp
    · nlinarith
    · rw [hp, mul_zero, zero_add]
      exact hν₀ b hb
    · nlinarith
  · rw [hpair]
    have hq := abs_lt.1 (hM b hb)
    nlinarith
  · rw [hpair]
    have hq := abs_lt.1 (hM b hb)
    nlinarith

end Signs

section Levi

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

omit [IsAffineHom G.X.hom] in
/-- A root group of a root with zero pairing lies in the centralizer of the cocharacter. -/
theorem rootGroupPoints_le_dynamicCentralizer {a : characterLattice S}
    (ha : latticePairing S a ν = 0) :
    rootGroupPoints i a ≤
      (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) :=
  fun _ hg => RelativeRoot.kernelCentralizer_le_dynamicCentralizer_of_pairing_eq_zero i a ν ha _
    (RelativeRoot.subgroup_le_kernelCentralizer i a _ hg)

/-- Uniqueness of the factors in `U(-ν) × Z_G(ν) × U(ν)`, for any subgroups of the three
factors. -/
theorem leviTripleProduct_injective (Uminus M Uplus : Subgroup (rationalPoints G))
    (hminus : Uminus ≤
      (Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ i)).carrier (Over.mk (𝟙 _)))
    (hM : M ≤ (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)))
    (hplus : Uplus ≤
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _))) :
    Function.Injective (fun p : Uminus × M × Uplus =>
      (p.1 : rationalPoints G) * (p.2.1 : rationalPoints G) * (p.2.2 : rationalPoints G)) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let χ := CommGroupScheme.groupHom ν ≫ i
  let χminus := Dynamic.oppositeCocharacter χ
  let X : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 _)
  have hz (z : M) : (z : rationalPoints G) ∈ (Dynamic.centralizer χ).carrier X := hM z.property
  have hm (v : Uminus) : (v : rationalPoints G) ∈ (Dynamic.unipotent χminus).carrier X := by
    have h := hminus v.property
    rw [groupHom_neg_comp_eq_oppositeCocharacter i ν] at h
    exact h
  let f : Uminus × M × Uplus →
      (Dynamic.unipotent χminus).carrier X × (Dynamic.parabolic χ).carrier X :=
    fun p => (⟨p.1, hm p.1⟩,
      ⟨(p.2.1 : rationalPoints G) * p.2.2,
        Subgroup.mul_mem _ (Dynamic.centralizer_le_parabolic χ X (hz p.2.1))
          (Dynamic.unipotent_le_parabolic χ X (hplus p.2.2.property))⟩)
  intro p q hpq
  have hpairs : f p = f q :=
    hasInjectiveOppositeCellMultiplication_of_isAffine i ν X
      (by simpa only [f, mul_assoc] using hpq)
  have hv : (p.1 : rationalPoints G) = q.1 :=
    congrArg (fun r : (Dynamic.unipotent χminus).carrier X ×
      (Dynamic.parabolic χ).carrier X => (r.1 : rationalPoints G)) hpairs
  have hzu : (p.2.1 : rationalPoints G) * (p.2.2 : rationalPoints G) =
      (q.2.1 : rationalPoints G) * (q.2.2 : rationalPoints G) :=
    congrArg (fun r : (Dynamic.unipotent χminus).carrier X ×
      (Dynamic.parabolic χ).carrier X => (r.2 : rationalPoints G)) hpairs
  have hlimp : Dynamic.HasLimit χ ((p.2.1 : rationalPoints G) * (p.2.2 : rationalPoints G))
      (p.2.1 : rationalPoints G) := by
    simpa only [mul_one] using
      (Dynamic.hasLimit_of_mem_centralizer χ (hz p.2.1)).mul χ (hplus p.2.2.property)
  have hlimq : Dynamic.HasLimit χ ((p.2.1 : rationalPoints G) * (p.2.2 : rationalPoints G))
      (q.2.1 : rationalPoints G) := by
    rw [hzu]
    simpa only [mul_one] using
      (Dynamic.hasLimit_of_mem_centralizer χ (hz q.2.1)).mul χ (hplus q.2.2.property)
  have hzj : (p.2.1 : rationalPoints G) = q.2.1 := hlimp.unique χ hlimq
  have hu : (p.2.2 : rationalPoints G) = q.2.2 := by
    rw [hzj] at hzu
    exact mul_left_cancel hzu
  exact Prod.ext (Subtype.ext hv) (Prod.ext (Subtype.ext hzj) (Subtype.ext hu))

end Levi

end Langlands.Geometry.Building

namespace Langlands.Geometry.Building.MaximalUnramified.BuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
  (B : BuildingData F H) (hZ : IsTorus B.centralizer.Z)

/-- The relative roots of `B` form a finite set. -/
theorem finite_relativeRoots : (relativeRoots B.i).Finite := by
  have : Smooth H.X.hom := B.isConnectedReductive.smooth
  exact B.isMaximalSplitTorus.1.1.finite_relativeRoots B.i

/-- A generic integral cocharacter exists. -/
theorem exists_genericCocharacter : ∃ mu : cocharacterLattice B.S, IsGenericCocharacter B.i mu := by
  have : Smooth H.X.hom := B.isConnectedReductive.smooth
  exact B.isMaximalSplitTorus.1.1.exists_genericCocharacter B.i

/-- For a real cocharacter `ν` there are an integral `lam` with the signs of `ν` on the roots
and a generic integral `mu` refining these signs. -/
theorem exists_sign_and_generic (ν : V B.S) :
    ∃ lam mu : cocharacterLattice B.S, IsGenericCocharacter B.i mu ∧ ∀ b ∈ relativeRoots B.i,
      (0 < latticePairing B.S b lam ↔ 0 < eval B.S b ν) ∧
        (latticePairing B.S b lam < 0 ↔ eval B.S b ν < 0) ∧
          (0 < eval B.S b ν → 0 < latticePairing B.S b mu) ∧
            (eval B.S b ν < 0 → latticePairing B.S b mu < 0) := by
  have : Smooth H.X.hom := B.isConnectedReductive.smooth
  obtain ⟨lam, hlam⟩ := exists_cocharacter_sign_eq B.i B.finite_relativeRoots ν
  obtain ⟨mu, hmu, href⟩ :=
    exists_genericCocharacter_refining B.i B.isMaximalSplitTorus.1.1 lam
  refine ⟨lam, mu, hmu, fun b hb => ⟨(hlam b hb).1, (hlam b hb).2, fun h => ?_, fun h => ?_⟩⟩
  · exact (href b hb).1 ((hlam b hb).1.2 h)
  · exact (href b hb).2 ((hlam b hb).2.2 h)

/-- The filtration span is monotone in the set of roots. -/
theorem rootFiltrationSpan_mono (x : B.Apartment) {Ψ Ψ' : Set (characterLattice B.S)}
    (h : Ψ ⊆ Ψ') (r : ℝ) : B.rootFiltrationSpan x Ψ r ≤ B.rootFiltrationSpan x Ψ' r :=
  biSup_mono fun _ hb => h hb

/-- The root-group span is monotone in the set of roots. -/
theorem rootGroupSpan_mono {Ψ Ψ' : Set (characterLattice B.S)} (h : Ψ ⊆ Ψ') :
    B.rootGroupSpan Ψ ≤ B.rootGroupSpan Ψ' :=
  biSup_mono fun _ hb => h hb

theorem rootFiltrationSpan_union (x : B.Apartment) (Ψ Ψ' : Set (characterLattice B.S))
    (r : ℝ) : B.rootFiltrationSpan x (Ψ ∪ Ψ') r =
      B.rootFiltrationSpan x Ψ r ⊔ B.rootFiltrationSpan x Ψ' r :=
  iSup_union

/-- The filtration span of a set of roots lies in `G(K)_{x,r}`. -/
theorem rootFiltrationSpan_le_moyPrasad (x : B.Apartment) {Ψ : Set (characterLattice B.S)}
    (hΨ : Ψ ⊆ relativeRoots B.i) (r : ℝ≥0) :
    B.rootFiltrationSpan x Ψ r ≤ B.moyPrasad hZ x r :=
  iSup₂_le fun b hb => B.filtration_le_moyPrasad hZ x ⟨b, hΨ hb⟩ r

/-- Two roots with `⟨b, ν⟩ = 0 ≠ ⟨c, ν⟩` are not negatively proportional. -/
theorem nonopposite_of_eval (ν : V B.S) {b c : characterLattice B.S}
    (hb : eval B.S b ν = 0) (hc : eval B.S c ν ≠ 0) :
    ∀ t : ℝ, 0 < t → ((1 : ℝ) ⊗ₜ[ℤ] c : Vstar B.S) ≠ -(t • (1 : ℝ) ⊗ₜ[ℤ] b) := by
  intro t _ heq
  have h := congrArg (fun χ => pair B.S χ ν) heq
  rw [eval_eq_pair] at hb hc
  simp only [map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply, hb, smul_zero,
    neg_zero] at h
  exact hc h

/-- If the commutators `[U_b, U_c]`, `b ∈ Ψ₀`, `c ∈ Ψ`, only produce roots of `Ψ`, then
`U_{Ψ₀,x,r}` normalizes `U_{Ψ,x,r}` for `r ≥ 0`. -/
theorem rootFiltrationSpan_le_normalizer (x : B.Apartment) {r : ℝ} (hr : 0 ≤ r)
    {Ψ₀ Ψ : Set (characterLattice B.S)} (hΨ₀ : Ψ₀ ⊆ relativeRoots B.i)
    (hΨ : Ψ ⊆ relativeRoots B.i)
    (hnon : ∀ b ∈ Ψ₀, ∀ c ∈ Ψ, ∀ t : ℝ, 0 < t →
      ((1 : ℝ) ⊗ₜ[ℤ] c : Vstar B.S) ≠ -(t • (1 : ℝ) ⊗ₜ[ℤ] b))
    (hclosed : ∀ b ∈ Ψ₀, ∀ c ∈ Ψ, ∀ p q : ℕ, 0 < p → 0 < q →
      p • b + q • c ∈ relativeRoots B.i → p • b + q • c ∈ Ψ) :
    B.rootFiltrationSpan x Ψ₀ r ≤
      Subgroup.normalizer (B.rootFiltrationSpan x Ψ r : Set (rationalPoints H)) := by
  rw [rootFiltrationSpan_eq_iSup_subtype B x Ψ r, Subgroup.iSup_eq_closure]
  refine iSup₂_le fun b hb => ?_
  apply Langlands.GroupScheme.RelativeRoot.subgroup_le_normalizer_closure_of_commutators
  intro g hg z hz
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hz
  rw [← Subgroup.iSup_eq_closure]
  have hmem := B.apartment.filtration_commutator_le x (hΨ₀ hb) (hΨ c.2) (hnon b hb c c.2) r r
    (Subgroup.commutator_mem_commutator hg hc)
  refine (show (⨆ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
      (_ : p • b + q • (c : characterLattice B.S) ∈ relativeRoots B.i),
        B.apartment.filtration x (p • b + q • (c : characterLattice B.S)) (p * r + q * r)) ≤
      ⨆ c : Ψ, B.filtration x c r from ?_) hmem
  refine iSup_le fun p => iSup_le fun q => iSup_le fun hp => iSup_le fun hq =>
    iSup_le fun hroot => ?_
  have hdepth : r ≤ (p : ℝ) * r + (q : ℝ) * r := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have h1 := mul_le_mul_of_nonneg_right hq1 hr
    have h2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) p) hr
    linarith
  exact le_iSup_of_le (⟨p • b + q • c, hclosed b hb c c.2 p q hp hq hroot⟩ : Ψ)
    (B.apartment.filtration_antitone x _ hdepth)

/-- The roots with zero pairing normalize the filtration span of the roots with positive
pairing. -/
theorem zeroPairing_le_normalizer_positive (x : B.Apartment) {r : ℝ} (hr : 0 ≤ r) (ν : V B.S)
    {Ψ₀ : Set (characterLattice B.S)} (hΨ₀ : Ψ₀ ⊆ B.zeroPairingRoots ν) :
    B.rootFiltrationSpan x Ψ₀ r ≤
      Subgroup.normalizer
        (B.rootFiltrationSpan x (B.positivePairingRoots ν) r : Set (rationalPoints H)) := by
  apply B.rootFiltrationSpan_le_normalizer x hr (fun b hb => (hΨ₀ hb).1) (fun c hc => hc.1)
  · exact fun b hb c hc => B.nonopposite_of_eval ν (hΨ₀ hb).2 hc.2.ne'
  · intro b hb c hc p q _ hq hroot
    refine ⟨hroot, ?_⟩
    rw [eval_add_char, eval_nsmul_char, eval_nsmul_char, (hΨ₀ hb).2, mul_zero, zero_add]
    exact mul_pos (by exact_mod_cast hq) hc.2

/-- The roots with zero pairing normalize the filtration span of the roots with negative
pairing. -/
theorem zeroPairing_le_normalizer_negative (x : B.Apartment) {r : ℝ} (hr : 0 ≤ r) (ν : V B.S)
    {Ψ₀ : Set (characterLattice B.S)} (hΨ₀ : Ψ₀ ⊆ B.zeroPairingRoots ν) :
    B.rootFiltrationSpan x Ψ₀ r ≤
      Subgroup.normalizer
        (B.rootFiltrationSpan x (B.negativePairingRoots ν) r : Set (rationalPoints H)) := by
  apply B.rootFiltrationSpan_le_normalizer x hr (fun b hb => (hΨ₀ hb).1) (fun c hc => hc.1)
  · exact fun b hb c hc => B.nonopposite_of_eval ν (hΨ₀ hb).2 hc.2.ne
  · intro b hb c hc p q _ hq hroot
    refine ⟨hroot, ?_⟩
    rw [eval_add_char, eval_nsmul_char, eval_nsmul_char, (hΨ₀ hb).2, mul_zero, zero_add]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast hq) hc.2

/-- **Regrouping the product cover.** If `mu` refines the signs of `ν` and
`g = u · j(z) · v` with `u ∈ U_{Φ⁺(-mu),x,r}`, `z ∈ Z(K)_r` and `v ∈ U_{Φ⁺(mu),x,r}`, then
`g = n' · m · n` with `n' ∈ U_{Φ⁻(ν),x,r}`, `m ∈ j(Z(K)_r) ⊔ U_{Φ⁰(ν),x,r}` and
`n ∈ U_{Φ⁺(ν),x,r}`. -/
theorem exists_levi_mul_of_mul (x : B.Apartment) (r : ℝ≥0) (ν : V B.S)
    (mu : cocharacterLattice B.S)
    (hpos : ∀ b ∈ relativeRoots B.i, 0 < eval B.S b ν → 0 < latticePairing B.S b mu)
    (hneg : ∀ b ∈ relativeRoots B.i, eval B.S b ν < 0 → latticePairing B.S b mu < 0)
    {u v : rationalPoints H} {z : rationalPoints B.centralizer.Z}
    (hu : u ∈ B.rootFiltrationSpan x (positiveRelativeRoots B.i (-mu)) r)
    (hz : z ∈ B.centralizerTorusFiltration hZ r)
    (hv : v ∈ B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) r) :
    ∃ n' ∈ B.rootFiltrationSpan x (B.negativePairingRoots ν) r,
      ∃ m ∈ B.centralizerTorusImage hZ r ⊔ B.rootFiltrationSpan x (B.zeroPairingRoots ν) r,
        ∃ n ∈ B.rootFiltrationSpan x (B.positivePairingRoots ν) r,
          u * rationalPoints.map B.centralizer.j z * v = n' * m * n := by
  set Ψp := B.zeroPairingRoots ν ∩ positiveRelativeRoots B.i mu with hΨp
  set Ψn := B.zeroPairingRoots ν ∩ positiveRelativeRoots B.i (-mu) with hΨn
  have hsplitp : positiveRelativeRoots B.i mu = Ψp ∪ B.positivePairingRoots ν := by
    ext b
    constructor
    · intro hb
      rcases lt_trichotomy (eval B.S b ν) 0 with h | h | h
      · exact absurd hb.2 (not_lt.2 (hneg b hb.1 h).le)
      · exact Or.inl ⟨⟨hb.1, h⟩, hb⟩
      · exact Or.inr ⟨hb.1, h⟩
    · rintro (hb | hb)
      · exact hb.2
      · exact ⟨hb.1, hpos b hb.1 hb.2⟩
  have hsplitn : positiveRelativeRoots B.i (-mu) = B.negativePairingRoots ν ∪ Ψn := by
    ext b
    constructor
    · intro hb
      have hb2 : latticePairing B.S b mu < 0 := by
        have := hb.2
        rw [map_neg] at this
        omega
      rcases lt_trichotomy (eval B.S b ν) 0 with h | h | h
      · exact Or.inl ⟨hb.1, h⟩
      · exact Or.inr ⟨⟨hb.1, h⟩, hb⟩
      · exact absurd hb2 (not_lt.2 (hpos b hb.1 h).le)
    · rintro (hb | hb)
      · refine ⟨hb.1, ?_⟩
        rw [map_neg]
        have := hneg b hb.1 hb.2
        omega
      · exact hb.2
  have hr : (0 : ℝ) ≤ r := r.coe_nonneg
  have hv' : v ∈ ((B.rootFiltrationSpan x Ψp r ⊔
      B.rootFiltrationSpan x (B.positivePairingRoots ν) r : Subgroup (rationalPoints H)) :
        Set (rationalPoints H)) := by
    rw [← rootFiltrationSpan_union, ← hsplitp]
    exact hv
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (B.zeroPairing_le_normalizer_positive x hr ν Set.inter_subset_left)] at hv'
  obtain ⟨h, hh, n, hn, rfl⟩ := hv'
  have hu' : u ∈ ((B.rootFiltrationSpan x (B.negativePairingRoots ν) r ⊔
      B.rootFiltrationSpan x Ψn r : Subgroup (rationalPoints H)) :
        Set (rationalPoints H)) := by
    rw [← rootFiltrationSpan_union, ← hsplitn]
    exact hu
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (B.zeroPairing_le_normalizer_negative x hr ν Set.inter_subset_left)] at hu'
  obtain ⟨n', hn', h', hh', rfl⟩ := hu'
  refine ⟨n', hn', h' * rationalPoints.map B.centralizer.j z * h, ?_, n, hn, ?_⟩
  · refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
    · exact Subgroup.mem_sup_right
        (B.rootFiltrationSpan_mono x Set.inter_subset_left r hh')
    · exact Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ hz)
    · exact Subgroup.mem_sup_right
        (B.rootFiltrationSpan_mono x Set.inter_subset_left r hh)
  · simp only [mul_assoc]

/-- `M_ν` lies in the centralizer of an integral cocharacter `lam` vanishing on the roots
`b` with `⟨b, ν⟩ = 0`. -/
theorem pairingLeviSpan_le_dynamicCentralizer (ν : V B.S) (lam : cocharacterLattice B.S)
    (hlam : ∀ b ∈ B.zeroPairingRoots ν, latticePairing B.S b lam = 0) :
    B.pairingLeviSpan ν ≤
      (Dynamic.centralizer (CommGroupScheme.groupHom lam ≫ B.i)).carrier (Over.mk (𝟙 _)) := by
  unfold pairingLeviSpan rootGroupSpan
  refine sup_le ?_ (iSup₂_le fun b hb => ?_)
  · rintro _ ⟨z, rfl⟩
    have hz : rationalPoints.map B.centralizer.j z ∈
        (torusCentralizer B.i).carrier (Over.mk (𝟙 _)) := by
      rw [torusCentralizer_carrier_base]
      exact map_mem_centralizerPoints B.centralizer.isRepresentedBy z
    exact torusCentralizer_le_dynamicCentralizer B.i (CommGroupScheme.groupHom lam)
      (Over.mk (𝟙 _)) hz
  · intro g hg
    have hg' : g ∈ rootGroupPoints B.i b := hg
    have h0 : latticePairing B.S b lam = 0 := hlam b hb
    have hc := rootGroupPoints_le_dynamicCentralizer B.i lam h0 hg'
    exact hc

/-- **Uniqueness in the Levi decomposition.** If `lam` has the signs of `ν` on the roots,
the factors of `v' · m · v` with `v' ∈ U_{Φ⁻(ν)}`, `m ∈ M_ν` and `v ∈ U_{Φ⁺(ν)}` are
unique. -/
theorem levi_eq_of_mul_eq_mul (ν : V B.S) (lam : cocharacterLattice B.S)
    (hlam : ∀ b ∈ relativeRoots B.i,
      (0 < latticePairing B.S b lam ↔ 0 < eval B.S b ν) ∧
        (latticePairing B.S b lam < 0 ↔ eval B.S b ν < 0))
    {u u' m m' v v' : rationalPoints H}
    (hu : u ∈ B.rootGroupSpan (B.negativePairingRoots ν))
    (hu' : u' ∈ B.rootGroupSpan (B.negativePairingRoots ν))
    (hm : m ∈ B.pairingLeviSpan ν) (hm' : m' ∈ B.pairingLeviSpan ν)
    (hv : v ∈ B.rootGroupSpan (B.positivePairingRoots ν))
    (hv' : v' ∈ B.rootGroupSpan (B.positivePairingRoots ν))
    (h : u * m * v = u' * m' * v') :
    u = u' ∧ m = m' ∧ v = v' := by
  have hminus := B.rootGroupSpan_le_dynamicUnipotent (-lam)
    (Ψ := B.negativePairingRoots ν) fun b hb => by
      rw [map_neg]
      have := (hlam b hb.1).2.2 hb.2
      omega
  have hplus := B.rootGroupSpan_le_dynamicUnipotent lam
    (Ψ := B.positivePairingRoots ν) fun b hb => (hlam b hb.1).1.2 hb.2
  have hM := B.pairingLeviSpan_le_dynamicCentralizer ν lam fun b hb => by
    have h1 := (hlam b hb.1).1
    have h2 := (hlam b hb.1).2
    rw [hb.2] at h1 h2
    simp only [lt_self_iff_false, iff_false, not_lt] at h1 h2
    omega
  have hinj := leviTripleProduct_injective B.i lam _ _ _ hminus hM hplus
  have heq := @hinj (⟨u, hu⟩, ⟨m, hm⟩, ⟨v, hv⟩) (⟨u', hu'⟩, ⟨m', hm'⟩, ⟨v', hv'⟩) h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at heq
  exact heq

/-- Elementwise form of the sign product cover of `LocalMoyPrasadPositiveProductStatement`. -/
theorem exists_mul_of_productCover (x : B.Apartment) (r : ℝ≥0) (mu : cocharacterLattice B.S)
    (hPC : (B.moyPrasad hZ x r : Set (rationalPoints H)) =
      (B.rootFiltrationSpan x (positiveRelativeRoots B.i (-mu)) r :
          Set (rationalPoints H)) *
        (B.centralizerTorusImage hZ r : Set (rationalPoints H)) *
          (B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) r : Set (rationalPoints H)))
    {g : rationalPoints H} (hg : g ∈ B.moyPrasad hZ x r) :
    ∃ u ∈ B.rootFiltrationSpan x (positiveRelativeRoots B.i (-mu)) r,
      ∃ z ∈ B.centralizerTorusFiltration hZ r,
        ∃ v ∈ B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) r,
          g = u * rationalPoints.map B.centralizer.j z * v := by
  have hg' : g ∈ (B.moyPrasad hZ x r : Set (rationalPoints H)) := hg
  rw [hPC] at hg'
  obtain ⟨_, ⟨u, hu, w, hw, rfl⟩, v, hv, rfl⟩ := hg'
  obtain ⟨z, hz, rfl⟩ := hw
  exact ⟨u, hu, z, hz, v, hv, rfl⟩

/-- `j(Z(K)_r) ⊔ U_{Φ⁰(ν),x,r}` lies in `M_ν`. -/
theorem leviFiltration_le_pairingLeviSpan (x : B.Apartment) (r : ℝ≥0) (ν : V B.S) :
    B.centralizerTorusImage hZ r ⊔ B.rootFiltrationSpan x (B.zeroPairingRoots ν) r ≤
      B.pairingLeviSpan ν :=
  sup_le_sup (Subgroup.map_le_range _ _) (B.rootFiltrationSpan_le_rootGroupSpan x _ r)

/-- `j(Z(K)_r) ⊔ U_{Φ⁰(ν),x,r}` lies in `G(K)_{x,r}`. -/
theorem leviFiltration_le_moyPrasad (x : B.Apartment) (r : ℝ≥0) (ν : V B.S) :
    B.centralizerTorusImage hZ r ⊔ B.rootFiltrationSpan x (B.zeroPairingRoots ν) r ≤
      B.moyPrasad hZ x r :=
  sup_le (B.centralizerTorusImage_le_moyPrasad hZ x r)
    (B.rootFiltrationSpan_le_moyPrasad hZ x (fun _ hb => hb.1) r)

/-- The regrouped decomposition of an element of `G(K)_{x,r}`, `r > 0`, from the sign
product cover of `LocalMoyPrasadPositiveProductStatement`. -/
theorem exists_levi_mul_of_productCover
    (hPC : ∀ (x : B.Apartment) (r : ℝ≥0), 0 < r → ∀ mu : cocharacterLattice B.S,
      IsGenericCocharacter B.i mu →
        (B.moyPrasad hZ x r : Set (rationalPoints H)) =
          (B.rootFiltrationSpan x (positiveRelativeRoots B.i (-mu)) r :
              Set (rationalPoints H)) *
            (B.centralizerTorusImage hZ r : Set (rationalPoints H)) *
              (B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) r :
                Set (rationalPoints H)))
    (ν : V B.S) (x : B.Apartment) {r : ℝ≥0} (hr : 0 < r) :
    ∃ lam : cocharacterLattice B.S, (∀ b ∈ relativeRoots B.i,
      (0 < latticePairing B.S b lam ↔ 0 < eval B.S b ν) ∧
        (latticePairing B.S b lam < 0 ↔ eval B.S b ν < 0)) ∧
      ∀ g ∈ B.moyPrasad hZ x r,
        ∃ n' ∈ B.rootFiltrationSpan x (B.negativePairingRoots ν) r,
          ∃ m ∈ B.centralizerTorusImage hZ r ⊔ B.rootFiltrationSpan x (B.zeroPairingRoots ν) r,
            ∃ n ∈ B.rootFiltrationSpan x (B.positivePairingRoots ν) r, g = n' * m * n := by
  obtain ⟨lam, mu, hmu, hsign⟩ := B.exists_sign_and_generic ν
  refine ⟨lam, fun b hb => ⟨(hsign b hb).1, (hsign b hb).2.1⟩, fun g hg => ?_⟩
  obtain ⟨u, hu, z, hz, v, hv, rfl⟩ :=
    B.exists_mul_of_productCover hZ x r mu (hPC x r hr mu hmu) hg
  exact B.exists_levi_mul_of_mul hZ x r ν mu (fun b hb => (hsign b hb).2.2.1)
    (fun b hb => (hsign b hb).2.2.2) hu hz hv

/-- **Clause 5 (Iwahori factorization), from the sign product cover.** -/
theorem iwahoriFactorization_of_productCover
    (hPC : ∀ (x : B.Apartment) (r : ℝ≥0), 0 < r → ∀ mu : cocharacterLattice B.S,
      IsGenericCocharacter B.i mu →
        (B.moyPrasad hZ x r : Set (rationalPoints H)) =
          (B.rootFiltrationSpan x (positiveRelativeRoots B.i (-mu)) r :
              Set (rationalPoints H)) *
            (B.centralizerTorusImage hZ r : Set (rationalPoints H)) *
              (B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) r :
                Set (rationalPoints H))) :
    LocalMoyPrasadIwahoriFactorization B hZ := by
  intro ν x r hr v' hv' m hm v hv hg
  obtain ⟨lam, hlam, hdec⟩ := B.exists_levi_mul_of_productCover hZ hPC ν x hr
  obtain ⟨n', hn', m₀, hm₀, n, hn, heq⟩ := hdec _ hg
  have h := B.levi_eq_of_mul_eq_mul ν lam hlam hv'
    (B.rootFiltrationSpan_le_rootGroupSpan x _ r hn') hm
    (B.leviFiltration_le_pairingLeviSpan hZ x r ν hm₀) hv
    (B.rootFiltrationSpan_le_rootGroupSpan x _ r hn) heq
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨B.rootFiltrationSpan_le_moyPrasad hZ x (fun _ hb => hb.1) r hn',
    B.leviFiltration_le_moyPrasad hZ x r ν hm₀,
    B.rootFiltrationSpan_le_moyPrasad hZ x (fun _ hb => hb.1) r hn⟩

/-- **Clause 6 at positive depth, from the sign product cover.** -/
theorem leviIntersection_of_productCover
    (hPC : ∀ (x : B.Apartment) (r : ℝ≥0), 0 < r → ∀ mu : cocharacterLattice B.S,
      IsGenericCocharacter B.i mu →
        (B.moyPrasad hZ x r : Set (rationalPoints H)) =
          (B.rootFiltrationSpan x (positiveRelativeRoots B.i (-mu)) r :
              Set (rationalPoints H)) *
            (B.centralizerTorusImage hZ r : Set (rationalPoints H)) *
              (B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) r :
                Set (rationalPoints H)))
    (ν : V B.S) (x : B.Apartment) {r : ℝ≥0} (hr : 0 < r) :
    B.pairingLeviSpan ν ⊓ B.moyPrasad hZ x r =
      B.centralizerTorusImage hZ r ⊔ B.rootFiltrationSpan x (B.zeroPairingRoots ν) r := by
  apply le_antisymm
  · rintro g ⟨hgM, hg⟩
    obtain ⟨lam, hlam, hdec⟩ := B.exists_levi_mul_of_productCover hZ hPC ν x hr
    obtain ⟨n', hn', m₀, hm₀, n, hn, heq⟩ := hdec _ hg
    have h := B.levi_eq_of_mul_eq_mul ν lam hlam (Subgroup.one_mem _)
      (B.rootFiltrationSpan_le_rootGroupSpan x _ r hn') hgM
      (B.leviFiltration_le_pairingLeviSpan hZ x r ν hm₀) (Subgroup.one_mem _)
      (B.rootFiltrationSpan_le_rootGroupSpan x _ r hn)
      (by rw [one_mul, mul_one]; exact heq)
    rw [h.2.1]
    exact hm₀
  · exact le_inf (B.leviFiltration_le_pairingLeviSpan hZ x r ν)
      (B.leviFiltration_le_moyPrasad hZ x r ν)

/-- **Clause 7 at positive depth, from the sign product cover.** -/
theorem comap_moyPrasad_eq_of_productCover
    (hPC : ∀ (x : B.Apartment) (r : ℝ≥0), 0 < r → ∀ mu : cocharacterLattice B.S,
      IsGenericCocharacter B.i mu →
        (B.moyPrasad hZ x r : Set (rationalPoints H)) =
          (B.rootFiltrationSpan x (positiveRelativeRoots B.i (-mu)) r :
              Set (rationalPoints H)) *
            (B.centralizerTorusImage hZ r : Set (rationalPoints H)) *
              (B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) r :
                Set (rationalPoints H)))
    (x : B.Apartment) {r : ℝ≥0} (hr : 0 < r) :
    (B.moyPrasad hZ x r).comap (rationalPoints.map B.centralizer.j) =
      B.centralizerTorusFiltration hZ r := by
  obtain ⟨mu, hmu⟩ := B.exists_genericCocharacter
  exact B.comap_moyPrasad_eq_of_cover hZ x r mu fun g hg =>
    B.exists_mul_of_productCover hZ x r mu (hPC x r hr mu hmu) hg

/-- **Clause 8, from the sign product cover.** -/
theorem separated_of_productCover
    (hPC : ∀ (x : B.Apartment) (r : ℝ≥0), 0 < r → ∀ mu : cocharacterLattice B.S,
      IsGenericCocharacter B.i mu →
        (B.moyPrasad hZ x r : Set (rationalPoints H)) =
          (B.rootFiltrationSpan x (positiveRelativeRoots B.i (-mu)) r :
              Set (rationalPoints H)) *
            (B.centralizerTorusImage hZ r : Set (rationalPoints H)) *
              (B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) r :
                Set (rationalPoints H))) :
    LocalMoyPrasadSeparated B hZ := by
  intro x
  obtain ⟨mu, hmu⟩ := B.exists_genericCocharacter
  exact B.iInf_moyPrasad_eq_bot_of_cover hZ x mu fun r hr g hg =>
    B.exists_mul_of_productCover hZ x r mu (hPC x r hr mu hmu) hg

end Langlands.Geometry.Building.MaximalUnramified.BuildingData
