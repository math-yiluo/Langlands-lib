import Langlands.Geometry.Building.GenericPointSharpExchange
import Langlands.Geometry.Building.ChamberSharpCore
import Langlands.GroupScheme.Absolute.RegularPerturbation
import Langlands.GroupScheme.Reductive.RankOneRootReducednessAssembly
import Langlands.GroupScheme.Reductive.TitsKernelIndexData
import Langlands.GroupScheme.Rational.CocharacterCentralizerPointDetection
import Langlands.GroupScheme.Rational.BruhatPointReduction
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.SplitTorusRationalDetection
import Langlands.GroupScheme.Dynamic.OppositeIntersection
import Langlands.GroupScheme.Dynamic.Decomposition
import Langlands.GroupScheme.Dynamic.Uniqueness
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.Geometry.Building.KPBuilding
import Langlands.GroupScheme.Rational.StandardParabolicOrderFromRoots

/-! # Levi sharp transport for apartment data over an infinite field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Pointwise commutatorElement
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

/-! ### Torus points, normalizers and centralizers -/

section TorusPoints

variable {B : Scheme.{u}} {T : CommGroupScheme B} {G : GroupScheme B}

/-- Conjugation by a point normalizing `i` preserves the base points of the image of `i`. -/
theorem conj_mem_range_of_mem_normalizerPoints (i : T.toGrp ⟶ G)
    {n r : Over.mk (𝟙 B) ⟶ G.X} (hn : n ∈ normalizerPoints i)
    (hr : r ∈ (SubgroupFunctor.range i).carrier (Over.mk (𝟙 B))) :
    n * r * n⁻¹ ∈ (SubgroupFunctor.range i).carrier (Over.mk (𝟙 B)) := by
  obtain ⟨σ, hσ⟩ := hn
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hr
  refine SubgroupFunctor.mem_range.mpr ⟨y ≫ (CommGroupScheme.groupHom σ.hom).hom.hom, ?_⟩
  have h := congrArg (fun φ : T.toGrp ⟶ G => y ≫ φ.hom.hom) hσ
  simp only [Grp.comp_hom_hom] at h
  rw [← Category.assoc, comp_innerIso_hom, constantPoint_self, ← Category.assoc] at h
  exact h.symm

/-- Base points of the image of a torus lie in every dynamic centralizer of a cocharacter of
that torus. -/
theorem range_le_dynamicCentralizer (i : T.toGrp ⟶ G) (χ : (Gm B).toGrp ⟶ T.toGrp) :
    (SubgroupFunctor.range i).carrier (Over.mk (𝟙 B)) ≤
      (Dynamic.centralizer (χ ≫ i)).carrier (Over.mk (𝟙 B)) :=
  fun _ hr => (range_le_torusCentralizer i).trans (torusCentralizer_le_dynamicCentralizer i χ)
    _ hr

/-- Points centralizing a torus lie in every dynamic centralizer of a cocharacter of it. -/
theorem centralizerPoints_le_dynamicCentralizer (i : T.toGrp ⟶ G)
    (χ : (Gm B).toGrp ⟶ T.toGrp) :
    centralizerPoints i ≤ (Dynamic.centralizer (χ ≫ i)).carrier (Over.mk (𝟙 B)) := by
  intro g hg
  rw [← torusCentralizer_carrier_base i] at hg
  exact torusCentralizer_le_dynamicCentralizer i χ _ hg

/-- A point centralizing a torus commutes with the image of every base point of the torus. -/
theorem commute_of_mem_centralizerPoints (i : T.toGrp ⟶ G) {g : Over.mk (𝟙 B) ⟶ G.X}
    (hg : g ∈ centralizerPoints i) (t : Over.mk (𝟙 B) ⟶ T.X) :
    Commute g (t ≫ i.hom.hom) := by
  rw [← torusCentralizer_carrier_base] at hg
  simpa only [Category.id_comp] using hg _ (𝟙 _) t

end TorusPoints

section RationalCentralizer

variable {k : Type u} [Field k] {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Over an infinite field, a rational point commuting with the rational points of a split
torus centralizes the torus. -/
theorem mem_centralizerPoints_of_forall_commute [Infinite k] [IsAffine G.X.left]
    (hA : IsSplitTorus A.toGrp) (j : A.toGrp ⟶ G) {g : rationalPoints G}
    (hg : ∀ t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X, Commute g (t ≫ j.hom.hom)) :
    g ∈ centralizerPoints j := by
  rw [mem_centralizerPoints]
  apply Grp.hom_ext
  apply hA.hom_ext_kpoints
  intro t
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom, constantPoint_self,
    (hg t).eq, mul_inv_cancel_right]

variable {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The rational root group of a root trivial on a subtorus centralizes that subtorus. -/
theorem rootGroupPoints_le_centralizerPoints_of_comp_eq_zero (i : S.toGrp ⟶ G) (f : A ⟶ S)
    {b : characterLattice S} (hb : f ≫ b = 0) :
    rootGroupPoints i b ≤ centralizerPoints (CommGroupScheme.groupHom f ≫ i) := by
  intro u hu
  obtain ⟨e, he, _⟩ := hu
  have hker := RelativeRoot.mem_kernelCentralizer_of_isOrbitExtension i b he
  rw [← torusCentralizer_carrier_base, mem_torusCentralizer]
  intro V a t
  let s := t ≫ (CommGroupScheme.groupHom f).hom.hom
  have hs : s ≫ (CommGroupScheme.groupHom b).hom.hom = 1 := by
    dsimp only [s]
    rw [← comp_groupHom_comp, hb, comp_groupHom_zero]
  let c : V ⟶ (RelativeRoot.characterKernel b).X :=
    (kernelPointsEquiv (CommGroupScheme.groupHom b) V).symm ⟨s, hs⟩
  have hc : c ≫ (RelativeRoot.characterKernelι b).hom.hom = s :=
    congrArg Subtype.val
      ((kernelPointsEquiv (CommGroupScheme.groupHom b) V).apply_symm_apply ⟨s, hs⟩)
  have h := (RelativeRoot.mem_kernelCentralizer i b).mp hker V a c
  simpa only [Grp.comp_hom_hom, ← Category.assoc, hc] using h

end RationalCentralizer

/-! ### Cocharacters avoiding finitely many characters -/

section Avoid

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Finitely many characters, each nonzero on some cocharacter, are simultaneously nonzero on
one cocharacter. -/
theorem exists_forall_latticePairing_ne_zero (s : Finset (characterLattice T))
    (hs : ∀ a ∈ s, ∃ ξ, latticePairing T a ξ ≠ 0) :
    ∃ ν : cocharacterLattice T, ∀ a ∈ s, latticePairing T a ν ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun a ha => by simp at ha⟩
  | @insert a s ha ih =>
    obtain ⟨ν, hν⟩ := ih fun b hb => hs b (Finset.mem_insert_of_mem hb)
    obtain ⟨ξ, hξ⟩ := hs a (Finset.mem_insert_self a s)
    let m : ℤ := 1 + ∑ c ∈ insert a s, |latticePairing T c ν|
    refine ⟨ν + m • ξ, fun b hb hzero => ?_⟩
    have hle : |latticePairing T b ν| ≤ ∑ c ∈ insert a s, |latticePairing T c ν| :=
      Finset.single_le_sum (f := fun c => |latticePairing T c ν|) (fun c _ => abs_nonneg _) hb
    have hpos : |latticePairing T b ν| < m := by
      change |latticePairing T b ν| < 1 + ∑ c ∈ insert a s, |latticePairing T c ν|
      linarith
    rw [map_add, map_zsmul, smul_eq_mul] at hzero
    by_cases hbξ : latticePairing T b ξ = 0
    · rw [hbξ, mul_zero, add_zero] at hzero
      have hba : b ≠ a := by
        rintro rfl
        exact hξ hbξ
      exact hν b (Finset.mem_of_mem_insert_of_ne hb hba) hzero
    · have h1 : 1 ≤ |latticePairing T b ξ| := Int.one_le_abs hbξ
      have hm0 : 0 < m := lt_of_le_of_lt (abs_nonneg _) hpos
      have h2 : |latticePairing T b ν| = m * |latticePairing T b ξ| := by
        rw [eq_neg_of_add_eq_zero_left hzero, abs_neg, abs_mul, abs_of_pos hm0]
      nlinarith

/-- Perturbing a large multiple of `lam` by `mu'` keeps the strict sign of every character of
a finite set on `lam`, and agrees with `mu'` on the characters vanishing on `lam`. -/
theorem exists_latticePairing_refine (s : Finset (characterLattice T))
    (lam mu' : cocharacterLattice T) :
    ∃ mu : cocharacterLattice T, ∀ a ∈ s,
      (0 < latticePairing T a lam → 0 < latticePairing T a mu) ∧
      (latticePairing T a lam < 0 → latticePairing T a mu < 0) ∧
      (latticePairing T a lam = 0 → latticePairing T a mu = latticePairing T a mu') := by
  let m : ℤ := 1 + ∑ c ∈ s, |latticePairing T c mu'|
  refine ⟨m • lam + mu', fun a ha => ?_⟩
  have hle : |latticePairing T a mu'| ≤ ∑ c ∈ s, |latticePairing T c mu'| :=
    Finset.single_le_sum (f := fun c => |latticePairing T c mu'|) (fun c _ => abs_nonneg _) ha
  have hm : |latticePairing T a mu'| < m := by
    change |latticePairing T a mu'| < 1 + ∑ c ∈ s, |latticePairing T c mu'|
    linarith
  have habs := abs_lt.mp hm
  simp only [map_add, map_zsmul, smul_eq_mul]
  refine ⟨fun h => ?_, fun h => ?_, fun h => by rw [h, mul_zero, zero_add]⟩
  · have h1 : (1 : ℤ) ≤ latticePairing T a lam := h
    nlinarith
  · have h1 : latticePairing T a lam ≤ -1 := by omega
    nlinarith

end Avoid

namespace RootGroupFamily

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] {i : S.toGrp ⟶ G}
  {U : characterLattice S → Subgroup (rationalPoints G)}

/-- A root subgroup whose root is nonnegative on `ν` normalizes the span of the roots positive
on `ν` (commutator relations). -/
theorem le_normalizer_span_positiveRelativeRoots (hcomm : HasCommutatorRelations i U)
    (ν : cocharacterLattice S) {c : characterLattice S} (hc : c ∈ relativeRoots i)
    (hcν : 0 ≤ latticePairing S c ν) :
    U c ≤ Subgroup.normalizer
      ((span U (positiveRelativeRoots i ν) : Subgroup (rationalPoints G)) :
        Set (rationalPoints G)) := by
  refine le_normalizer_iSup_of_commutator_le fun b => ?_
  obtain ⟨hb, hbν⟩ := b.2
  have hnon : ∀ t : ℝ, 0 < t →
      ((1 : ℝ) ⊗ₜ[ℤ] (b : characterLattice S) : Vstar S) ≠ -(t • (1 : ℝ) ⊗ₜ[ℤ] c) := by
    intro t ht heq
    have h1 := congrArg (fun χ => pair S χ ((1 : ℝ) ⊗ₜ[ℤ] ν)) heq
    simp only [map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul,
      ← eval_eq_pair, eval_tmul, one_mul] at h1
    have hb' : (0 : ℝ) < (latticePairing S b ν : ℝ) := by exact_mod_cast hbν
    have hc' : (0 : ℝ) ≤ (latticePairing S c ν : ℝ) := by exact_mod_cast hcν
    nlinarith
  refine (hcomm hc hb hnon).trans ?_
  refine iSup_le fun p => iSup_le fun q => iSup_le fun hp => iSup_le fun hq =>
    iSup_le fun he => ?_
  refine le_span ⟨he, ?_⟩
  simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  nlinarith

end RootGroupFamily

/-! ### The Levi product decomposition of a point sharp fixer -/

namespace KPApartmentData

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}
  [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- **Levi product decomposition of a point sharp fixer.** For any cocharacter `lam` of the
maximal split torus, `G(k)^♯_x ⊆ X(Φ_{lam<0}) X(Φ_{lam=0}) X(Φ_{lam>0}) H_x`, where `X(P)` is
generated by the depth-zero root groups `U_{b,x,0}` with `b ∈ P` and `H_x` is the
`N(k)`-stabilizer part of `G(k)^♯_x`. -/
theorem sharpFixer_subset_leviProduct (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (x : D.Apartment) (lam : cocharacterLattice S) :
    (D.sharpFixer {x} : Set (rationalPoints G)) ⊆
      ((⨆ b : positiveRelativeRoots i (-lam), D.filtration x b 0 :
          Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
        ((⨆ b : zeroRelativeRoots i lam, D.filtration x b 0 :
          Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
        ((⨆ b : positiveRelativeRoots i lam, D.filtration x b 0 :
          Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
        (D.sharpNormalizerStabilizer x : Set (rationalPoints G)) := by
  classical
  have hT : IsSplitTorus S.toGrp := hi.1.1
  have : Smooth G.X.hom := hG.smooth
  have hfin := IsSplitTorus.finite_relativeRoots (i := i) hT
  obtain ⟨mu', hmu'⟩ := exists_forall_latticePairing_ne_zero hfin.toFinset fun a ha => by
    obtain ⟨ξ, hξ⟩ := hT.exists_latticePairing_pos
      (mem_relativeRoots.mp (hfin.mem_toFinset.mp ha)).1
    exact ⟨ξ, hξ.ne'⟩
  obtain ⟨mu, hmu⟩ := exists_latticePairing_refine hfin.toFinset lam mu'
  have hgen : IsGenericCocharacter i mu := by
    intro a ha
    have ha' := hfin.mem_toFinset.mpr ha
    obtain ⟨hpos, hneg, hzero⟩ := hmu a ha'
    rcases lt_trichotomy (latticePairing S a lam) 0 with h | h | h
    · exact (hneg h).ne
    · rw [hzero h]
      exact hmu' a ha'
    · exact (hpos h).ne'
  have hcomm := D.rootFixer_hasCommutatorRelations (Set.finite_singleton x)
    (Set.singleton_nonempty x)
  simp only [rootFixer_singleton] at hcomm
  set Nm : Subgroup (rationalPoints G) :=
    ⨆ b : positiveRelativeRoots i (-lam), D.filtration x b 0 with hNm
  set Z : Subgroup (rationalPoints G) :=
    ⨆ b : zeroRelativeRoots i lam, D.filtration x b 0 with hZ
  set Np : Subgroup (rationalPoints G) :=
    ⨆ b : positiveRelativeRoots i lam, D.filtration x b 0 with hNp
  have hZm : Z ≤ Subgroup.normalizer (Nm : Set (rationalPoints G)) :=
    iSup_le fun b => RootGroupFamily.le_normalizer_span_positiveRelativeRoots hcomm (-lam)
      b.2.1 (by rw [map_neg, b.2.2, neg_zero])
  have hZp : Z ≤ Subgroup.normalizer (Np : Set (rationalPoints G)) :=
    iSup_le fun b => RootGroupFamily.le_normalizer_span_positiveRelativeRoots hcomm lam
      b.2.1 b.2.2.ge
  have hminus : (⨆ b : positiveRelativeRoots i (-mu), D.chamberRootGroup x false b :
      Subgroup (rationalPoints G)) ≤ Nm ⊔ Z := by
    refine iSup_le fun b => ?_
    obtain ⟨hb, hbmu⟩ := b.2
    rw [map_neg, neg_pos] at hbmu
    obtain ⟨hpos, -, -⟩ := hmu b (hfin.mem_toFinset.mpr hb)
    change D.filtration x b 0 ≤ Nm ⊔ Z
    rcases lt_trichotomy (latticePairing S b lam) 0 with h | h | h
    · exact le_sup_of_le_left (le_iSup_of_le (⟨b, hb, by rwa [map_neg, neg_pos]⟩ :
        positiveRelativeRoots i (-lam)) le_rfl)
    · exact le_sup_of_le_right (le_iSup_of_le (⟨b, hb, h⟩ : zeroRelativeRoots i lam) le_rfl)
    · exact absurd (hpos h) (not_lt.mpr hbmu.le)
  have hplus : (⨆ b : positiveRelativeRoots i mu, D.chamberRootGroup x false b :
      Subgroup (rationalPoints G)) ≤ Z ⊔ Np := by
    refine iSup_le fun b => ?_
    obtain ⟨hb, hbmu⟩ := b.2
    obtain ⟨-, hneg, -⟩ := hmu b (hfin.mem_toFinset.mpr hb)
    change D.filtration x b 0 ≤ Z ⊔ Np
    rcases lt_trichotomy (latticePairing S b lam) 0 with h | h | h
    · exact absurd (hneg h) (not_lt.mpr hbmu.le)
    · exact le_sup_of_le_left (le_iSup_of_le (⟨b, hb, h⟩ : zeroRelativeRoots i lam) le_rfl)
    · exact le_sup_of_le_right (le_iSup_of_le (⟨b, hb, h⟩ : positiveRelativeRoots i lam) le_rfl)
  intro g hg
  obtain ⟨vw, ⟨v, hv, w, hw, rfl⟩, n, hn, rfl⟩ :=
    D.sharpFixer_subset_mul_sharpNormalizerStabilizer hG hi x mu hgen hg
  have hv' : v ∈ (Nm : Set (rationalPoints G)) * Z := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left Nm Z hZm]
    exact hminus hv
  have hw' : w ∈ (Z : Set (rationalPoints G)) * Np := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right Z Np hZp]
    exact hplus hw
  obtain ⟨v₁, hv₁, z₁, hz₁, rfl⟩ := hv'
  obtain ⟨z₂, hz₂, w₁, hw₁, rfl⟩ := hw'
  refine ⟨v₁ * (z₁ * z₂) * w₁, ⟨v₁ * (z₁ * z₂), ⟨v₁, hv₁, z₁ * z₂, Z.mul_mem hz₁ hz₂, rfl⟩,
    w₁, hw₁, rfl⟩, n, hn, ?_⟩
  simp only [mul_assoc]

/-- **Levi sharp transport over an infinite field.** Let `A` be a split torus mapping into the
maximal split torus `S` by `f`, with composite embedding `j = f ≫ i`, and let `n` normalize
`j`. If `n` carries the apartment point `x` to a point of the same apartment in the reduced
building, then some `h` in the depth-zero root groups `U_{b,x,0}` with `f ≫ b = 0` (the Levi
`Z_G(A)`) centralizes `A` and makes `n * h` normalize `S`. -/
theorem exists_leviSharp_transport [Infinite k] (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) {A : CommGroupScheme (Spec (CommRingCat.of k))}
    (hA : IsSplitTorus A.toGrp) (f : A ⟶ S) {j : A.toGrp ⟶ G}
    (hj : CommGroupScheme.groupHom f ≫ i = j) {n : rationalPoints G}
    (hn : n ∈ normalizerPoints j) (x y : D.Apartment)
    (hxy : D.apartmentMap y = n • D.apartmentMap x) :
    ∃ h : rationalPoints G, h ∈ centralizerPoints j ∧
      h ∈ (⨆ (b : characterLattice S) (_ : b ∈ relativeRoots i) (_ : f ≫ b = 0),
        D.filtration x b 0) ∧
      n * h ∈ normalizerPoints i := by
  classical
  subst hj
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hT : IsSplitTorus S.toGrp := hi.1.1
  have : Smooth G.X.hom := hG.smooth
  have hfin := IsSplitTorus.finite_relativeRoots (i := i) hT
  -- Unfold the quotient relation: `n⁻¹ m` fixes `x` for some `m ∈ N(k)`.
  obtain ⟨m, -, hm⟩ :=
    (ApartmentQuotient.mk_eq_mk_iff D.sharpFixerFamily (n * 1) 1 x y).mp hxy.symm
  have hg : n⁻¹ * (m : rationalPoints G) ∈ D.sharpFixer {x} := by
    simp only [mul_one] at hm
    exact hm
  -- A cocharacter of `A` that is nonzero on every root not trivial on `A`.
  obtain ⟨lam, hlam⟩ := exists_forall_latticePairing_ne_zero
    ((hfin.toFinset.filter fun c => f ≫ c ≠ 0).image fun c => f ≫ c) fun a ha => by
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨ξ, hξ⟩ := hA.exists_latticePairing_pos (Finset.mem_filter.mp hc).2
      exact ⟨ξ, hξ.ne'⟩
  set lamS : cocharacterLattice S := lam ≫ f with hlamS
  have hzero : ∀ c ∈ relativeRoots i, latticePairing S c lamS = 0 → f ≫ c = 0 := by
    intro c hc h0
    by_contra hfc
    apply hlam (f ≫ c) (Finset.mem_image.mpr
      ⟨c, Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hc, hfc⟩, rfl⟩)
    rw [latticePairing_precomp]
    exact h0
  set χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G :=
    CommGroupScheme.groupHom lamS ≫ i with hχ
  have hχA : CommGroupScheme.groupHom lam ≫ (CommGroupScheme.groupHom f ≫ i) = χ := by
    rw [← Category.assoc]
    rfl
  -- The Levi product decomposition of `n⁻¹ m`.
  obtain ⟨_, ⟨_, ⟨v, hv, z, hz, rfl⟩, w, hw, rfl⟩, n', hn', hdec⟩ :=
    D.sharpFixer_subset_leviProduct hG hi x lamS hg
  obtain ⟨-, hn'N, -⟩ := mem_sharpNormalizerStabilizer.mp hn'
  set m₁ : rationalPoints G := (m : rationalPoints G) * n'⁻¹ with hm₁def
  have hm₁ : m₁ ∈ normalizerPoints i := mul_mem m.2 (inv_mem hn'N)
  have hg₀ : v * z * w = n⁻¹ * m₁ := by
    rw [hm₁def, ← mul_assoc, ← hdec, mul_inv_cancel_right]
  -- Memberships of the three factors.
  have hvU : v ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom (-lamS) ≫ i)).carrier (Over.mk (𝟙 _)) :=
    (D.positiveChamberRootGroups_le_sharpUnipotentPoints x (-lamS) hv).1
  have hwU : w ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) :=
    (D.positiveChamberRootGroups_le_sharpUnipotentPoints x lamS hw).1
  have hzC : z ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) := by
    refine (iSup_le fun b : zeroRelativeRoots i lamS => ?_ :
      _ ≤ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _))) hz
    exact (D.filtration_le_rootGroupPoints x b 0).trans
      (RelativeRoot.subgroup_le_dynamicCentralizer_of_pairing_eq_zero i b lamS b.2.2 _)
  have hzA : z ∈ centralizerPoints (CommGroupScheme.groupHom f ≫ i) := by
    refine (iSup_le fun b : zeroRelativeRoots i lamS => ?_ :
      _ ≤ centralizerPoints (CommGroupScheme.groupHom f ≫ i)) hz
    exact (D.filtration_le_rootGroupPoints x b 0).trans
      (rootGroupPoints_le_centralizerPoints_of_comp_eq_zero i f (hzero b b.2.1 b.2.2))
  have hzL : z ∈ (⨆ (b : characterLattice S) (_ : b ∈ relativeRoots i) (_ : f ≫ b = 0),
      D.filtration x b 0) := by
    have hle : (⨆ b : zeroRelativeRoots i lamS, D.filtration x b 0 :
        Subgroup (rationalPoints G)) ≤
        ⨆ (b : characterLattice S) (_ : b ∈ relativeRoots i) (_ : f ≫ b = 0),
          D.filtration x b 0 :=
      iSup_le fun b => le_iSup_of_le (b : characterLattice S) (le_iSup_of_le b.2.1
        (le_iSup_of_le (hzero b b.2.1 b.2.2) le_rfl))
    exact hle hz
  -- Facts about torus points.
  have hrange : ∀ t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X,
      t ≫ (CommGroupScheme.groupHom f ≫ i).hom.hom ∈
        (SubgroupFunctor.range i).carrier (Over.mk (𝟙 _)) := fun t =>
    SubgroupFunctor.mem_range.mpr ⟨t ≫ (CommGroupScheme.groupHom f).hom.hom, by
      rw [Grp.comp_hom_hom, Category.assoc]⟩
  have hrangeZ : ∀ {r}, r ∈ (SubgroupFunctor.range i).carrier (Over.mk (𝟙 _)) →
      r ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) := fun hr =>
    range_le_dynamicCentralizer i (CommGroupScheme.groupHom lamS) hr
  have hrangeC : ∀ {r}, r ∈ (SubgroupFunctor.range i).carrier (Over.mk (𝟙 _)) →
      r ∈ centralizerPoints i := fun hr => by
    rw [← torusCentralizer_carrier_base i]
    exact range_le_torusCentralizer i _ hr
  have hP : ∀ {p}, p ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) →
      p ∈ (Dynamic.parabolic χ).carrier (Over.mk (𝟙 _)) := fun hp =>
    Dynamic.centralizer_le_parabolic χ _ hp
  have huniq : ∀ (U : Over (Spec (CommRingCat.of k))) (g l l' : U ⟶ G.X),
      Dynamic.HasLimit χ g l → Dynamic.HasLimit χ g l' → l = l' :=
    fun _ _ _ _ h h' => h.unique _ h'
  -- Conjugating `v z w = n⁻¹ m₁` by a point `s` of `A` multiplies it by a point of `S`.
  have hτ : ∀ t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X,
      (v * z * w)⁻¹ * (t ≫ (CommGroupScheme.groupHom f ≫ i).hom.hom) * (v * z * w) *
          (t ≫ (CommGroupScheme.groupHom f ≫ i).hom.hom)⁻¹ ∈
        (SubgroupFunctor.range i).carrier (Over.mk (𝟙 _)) := by
    intro t
    have hst := hrange t
    set s := t ≫ (CommGroupScheme.groupHom f ≫ i).hom.hom with hs
    have h1 := conj_mem_range_of_mem_normalizerPoints _ hn
      (SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩)
    obtain ⟨t', ht'⟩ := SubgroupFunctor.mem_range.mp h1
    have h2 : n * s * n⁻¹ ∈ (SubgroupFunctor.range i).carrier (Over.mk (𝟙 _)) := by
      rw [← ht']
      exact hrange t'
    have h3 := conj_mem_range_of_mem_normalizerPoints i (inv_mem hm₁) h2
    rw [hg₀]
    convert mul_mem h3 (inv_mem hst) using 1
    group
  -- The factor `v` is trivial.
  have hv1 : v = 1 := by
    have hcomm : ∀ t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X,
        Commute v (t ≫ (CommGroupScheme.groupHom f ≫ i).hom.hom) := by
      intro t
      have hτt := hτ t
      have hsr := hrange t
      set s := t ≫ (CommGroupScheme.groupHom f ≫ i).hom.hom with hs
      set τ := (v * z * w)⁻¹ * s * (v * z * w) * s⁻¹ with hτdef
      have he : v⁻¹ * (s * v * s⁻¹) = (z * w) * τ * (s * (z * w) * s⁻¹)⁻¹ := by
        rw [hτdef]
        group
      have heU : v⁻¹ * (s * v * s⁻¹) ∈ (Dynamic.unipotent
          (Dynamic.oppositeCocharacter χ)).carrier (Over.mk (𝟙 _)) := by
        rw [hχ, ← groupHom_neg_comp_eq_oppositeCocharacter]
        exact mul_mem (inv_mem hvU)
          (centralizer_conj_mem_dynamicUnipotent (-lamS) (hrangeC hsr) hvU)
      have heP : v⁻¹ * (s * v * s⁻¹) ∈ (Dynamic.parabolic χ).carrier (Over.mk (𝟙 _)) := by
        rw [he]
        have hzwP : z * w ∈ (Dynamic.parabolic χ).carrier (Over.mk (𝟙 _)) :=
          mul_mem (hP hzC) (Dynamic.unipotent_le_parabolic χ _ hwU)
        have hsP := hP (hrangeZ hsr)
        exact mul_mem (mul_mem hzwP (hP (hrangeZ hτt)))
          (inv_mem (mul_mem (mul_mem hsP hzwP) (inv_mem hsP)))
      have h1 := Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic χ heU heP
      have h2 : s * v * s⁻¹ = v := (inv_mul_eq_one.mp h1).symm
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    have hvA := mem_centralizerPoints_of_forall_commute hA _ hcomm
    have hvP := centralizerPoints_le_dynamicParabolic _ (CommGroupScheme.groupHom lam) hvA
    rw [hχA] at hvP
    have hvU' : v ∈ (Dynamic.unipotent
        (Dynamic.oppositeCocharacter χ)).carrier (Over.mk (𝟙 _)) := by
      rw [hχ, ← groupHom_neg_comp_eq_oppositeCocharacter]
      exact hvU
    exact Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic χ hvU' hvP
  subst hv1
  -- The factor `w` is trivial.
  have hw1 : w = 1 := by
    have hcomm : ∀ t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X,
        Commute w (t ≫ (CommGroupScheme.groupHom f ≫ i).hom.hom) := by
      intro t
      have hτt := hτ t
      have hsr := hrange t
      have hzs := commute_of_mem_centralizerPoints _ hzA t
      set s := t ≫ (CommGroupScheme.groupHom f ≫ i).hom.hom with hs
      have hτeq : (1 * z * w)⁻¹ * s * (1 * z * w) * s⁻¹ = w⁻¹ * (s * w * s⁻¹) := by
        have hzz : z⁻¹ * s * z = s := by
          rw [mul_assoc, ← hzs.eq, inv_mul_cancel_left]
        calc (1 * z * w)⁻¹ * s * (1 * z * w) * s⁻¹ = w⁻¹ * (z⁻¹ * s * z) * w * s⁻¹ := by
              group
          _ = w⁻¹ * (s * w * s⁻¹) := by
              rw [hzz]
              group
      rw [hτeq] at hτt
      have hU : w⁻¹ * (s * w * s⁻¹) ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) :=
        mul_mem (inv_mem hwU) (centralizer_conj_mem_dynamicUnipotent lamS (hrangeC hsr) hwU)
      have h1 := Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent χ huniq (hrangeZ hτt) hU
      have h2 : s * w * s⁻¹ = w := (inv_mul_eq_one.mp h1).symm
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    have hwA := mem_centralizerPoints_of_forall_commute hA _ hcomm
    have hwZ := centralizerPoints_le_dynamicCentralizer _ (CommGroupScheme.groupHom lam) hwA
    rw [hχA] at hwZ
    exact Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent χ huniq hwZ hwU
  subst hw1
  refine ⟨z, hzA, hzL, ?_⟩
  have hz' : z = n⁻¹ * m₁ := by
    simpa only [one_mul, mul_one] using hg₀
  rw [hz', mul_inv_cancel_left]
  exact hm₁

end KPApartmentData

end Langlands.Geometry.Building
