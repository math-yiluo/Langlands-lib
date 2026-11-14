import Langlands.Geometry.Building.KPLocalMoyPrasadDepthZeroStatement
import Langlands.Geometry.Building.RealTorusSpace
import Langlands.Geometry.Building.LeviSharpTransport
import Langlands.Geometry.Building.UnramifiedNormIwahoriZeroFixer
import Langlands.Geometry.Building.UnramifiedZeroNormalizerComparison
import Langlands.Geometry.Building.UnramifiedSimplyConnectedNormalizerAffineWeylProof
import Langlands.Geometry.Building.AffineWeylPointStabilizer
import Langlands.Geometry.Building.KPZeroDatumExistence
import Langlands.Geometry.Building.GenericApartmentFixer
import Langlands.Geometry.Building.IntegerValuationOneStabilizerBounded
import Langlands.Geometry.Building.GenericPointSharpExchange
import Langlands.Geometry.Building.IntegerValuationNormalizerSharpReduction
import Langlands.Geometry.Building.KPLocalMoyPrasadBlockExchange
import Langlands.Geometry.Building.KPCentralizerCompatibility
import Langlands.Geometry.Building.RootFixerExchange
import Langlands.Geometry.Building.GenericZeroFixerNormalizerReduction
import Langlands.Geometry.Building.GenericApartmentInjection
import Langlands.Geometry.Building.IntegerValuationSharpCoverImage
import Langlands.Geometry.Building.IntegerAffineRootLocalFiniteness
import Langlands.LocalField.ValuativeInfinite

/-!
# Proof of the depth-zero intersections of `G(K)_{x,0}` over `K = F^ur`

This module proves `MaximalUnramified.LocalMoyPrasadDepthZeroStatement` (the depth-zero cases of
Kaletha–Prasad Proposition 7.3.12 and Lemma 8.5.19 for the actual group `G(K)_{x,0}`), as
`MaximalUnramified.localMoyPrasadDepthZero`. The paired Markdown describes the proof.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj NNReal Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.LocalGalois.Separable

/-! ### Integral approximation of a real cocharacter -/

namespace Langlands.Geometry.Building.DepthZeroApprox

/-- Finitely many nonzero reals are simultaneously nonzero under one `ℚ`-linear functional. -/
theorem exists_ratFunctional_ne_zero (s : Finset ℝ) (hs : ∀ a ∈ s, a ≠ 0) :
    ∃ ψ : ℝ →ₗ[ℚ] ℚ, ∀ a ∈ s, ψ a ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun a ha => by simp at ha⟩
  | @insert a s ha ih =>
    obtain ⟨ψ, hψ⟩ := ih fun b hb => hs b (Finset.mem_insert_of_mem hb)
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℚ (hs a (Finset.mem_insert_self a s))
    obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset ((insert a s).image fun c => -(ψ c) / φ c)
    refine ⟨ψ + q • φ, fun c hc hzero => ?_⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hzero
    by_cases hφc : φ c = 0
    · rw [hφc, mul_zero, add_zero] at hzero
      have hca : c ≠ a := by
        rintro rfl
        exact hφ hφc
      exact hψ c (Finset.mem_of_mem_insert_of_ne hc hca) hzero
    · apply hq
      refine Finset.mem_image.2 ⟨c, hc, ?_⟩
      field_simp
      linarith

variable {k : Type u} [Field k] (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- Applying a `ℚ`-linear functional `ψ : ℝ → ℚ` to the coefficients of a real cocharacter and
clearing denominators gives an integral cocharacter whose pairings are a fixed nonzero integer
multiple of the images under `ψ` of the real pairings. -/
theorem exists_latticePairing_eq_mul (ψ : ℝ →ₗ[ℚ] ℚ) (ν : V T) :
    ∃ (lam : cocharacterLattice T) (d : ℤ), d ≠ 0 ∧
      ∀ χ : characterLattice T, ((latticePairing T χ lam : ℤ) : ℚ) = d * ψ (eval T χ ν) := by
  induction ν using TensorProduct.inductionOn with
  | tmul r ξ =>
    refine ⟨(ψ r).num • ξ, (ψ r).den, by exact_mod_cast (ψ r).den_nz, fun χ => ?_⟩
    have hψ : ∀ n : ℤ, ψ ((n : ℝ) * r) = (n : ℚ) * ψ r := fun n => by
      rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]
    rw [eval_tmul, map_zsmul, smul_eq_mul, mul_comm r, hψ, Int.cast_mul]
    have h := Rat.mul_den_eq_num (ψ r)
    rw [← h]
    push_cast
    ring
  | add ν₁ ν₂ h₁ h₂ =>
    obtain ⟨lam₁, d₁, hd₁, h₁⟩ := h₁
    obtain ⟨lam₂, d₂, hd₂, h₂⟩ := h₂
    refine ⟨d₂ • lam₁ + d₁ • lam₂, d₁ * d₂, mul_ne_zero hd₁ hd₂, fun χ => ?_⟩
    rw [map_add, map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul, Int.cast_add, Int.cast_mul,
      Int.cast_mul, h₁, h₂, map_add, map_add]
    push_cast
    ring

/-- For finitely many characters there is an integral cocharacter vanishing on exactly the
characters of the set on which a given real cocharacter vanishes. -/
theorem exists_latticePairing_eq_zero_iff (s : Finset (characterLattice T)) (ν : V T) :
    ∃ lam : cocharacterLattice T, ∀ χ ∈ s,
      (latticePairing T χ lam = 0 ↔ eval T χ ν = 0) := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_ratFunctional_ne_zero
    ((s.image fun χ => eval T χ ν).filter fun a => a ≠ 0) (fun a ha => (Finset.mem_filter.1 ha).2)
  obtain ⟨lam, d, hd, hlam⟩ := exists_latticePairing_eq_mul T ψ ν
  refine ⟨lam, fun χ hχ => ⟨fun h0 => ?_, fun h0 => ?_⟩⟩
  · by_contra hne
    have hmem : eval T χ ν ∈ (s.image fun χ => eval T χ ν).filter fun a => a ≠ 0 :=
      Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hχ, hne⟩
    have h := hlam χ
    rw [h0, Int.cast_zero, eq_comm, mul_eq_zero] at h
    rcases h with h | h
    · exact hd (by exact_mod_cast h)
    · exact hψ _ hmem h
  · have h := hlam χ
    rw [h0, map_zero, mul_zero] at h
    exact_mod_cast h

/-- A composite `ν ≫ χ` vanishes exactly when the lattice pairing does. -/
theorem comp_eq_zero_iff_latticePairing_eq_zero (χ : characterLattice T)
    (ν : cocharacterLattice T) : ν ≫ χ = 0 ↔ latticePairing T χ ν = 0 := by
  rw [latticePairing_apply]
  exact (AddEquiv.map_eq_zero_iff (gmEndEquiv k)).symm

/-- For finitely many characters there is an integral cocharacter `lam` with `lam ≫ χ = 0`
exactly for the characters `χ` of the set with `⟨χ, ν⟩ = 0`. -/
theorem exists_comp_eq_zero_iff (s : Finset (characterLattice T)) (ν : V T) :
    ∃ lam : cocharacterLattice T, ∀ χ ∈ s, (lam ≫ χ = 0 ↔ eval T χ ν = 0) := by
  obtain ⟨lam, hlam⟩ := exists_latticePairing_eq_zero_iff T s ν
  exact ⟨lam, fun χ hχ =>
    (comp_eq_zero_iff_latticePairing_eq_zero T χ lam).trans (hlam χ hχ)⟩

end Langlands.Geometry.Building.DepthZeroApprox

namespace Langlands.Geometry.Building.MaximalUnramified.BuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
  (B : BuildingData F H) (hZ : IsTorus B.centralizer.Z)

/-! ### Clause (a): the positive unipotent intersection -/

/-- At depth zero the sharp filtration is the sharp fixer of the point. -/
theorem sharpFiltration_zero_eq_sharpFixer (x : B.Apartment) :
    B.apartment.sharpFiltration x (fun _ => ((0 : ℝ≥0) : ℝ)) = B.sharpFixer {x} := by
  rw [B.apartment.sharpFiltration_eq_iSup]
  simp only [NNReal.coe_zero, KPApartmentData.sharpFixer, KPApartmentData.rootFixer_singleton]

/-- `G(K)_{x,0}` fixes the image of `x` in the reduced building. -/
theorem moyPrasad_zero_le_fixer (x : B.Apartment) :
    B.moyPrasad hZ x 0 ≤ B.fixer (B.apartmentMap x) := by
  rw [moyPrasad_eq_sup, sharpFiltration_zero_eq_sharpFixer]
  refine sup_le ?_ (B.sharpFixer_le_fixer x)
  rintro _ ⟨z, hz, rfl⟩
  have hz' : z ∈ characterValuationKernel (MaximalUnramified.valuation F) B.centralizer.Z := by
    have h := B.centralizerTorusFiltration_le_characterValuationKernel hZ 0 hz
    rw [mem_characterValuationKernel] at h ⊢
    intro χ
    exact (MaximalUnramified.valuation_isEquiv F).eq_one_iff_eq_one.mpr (h χ)
  exact B.oneStabilizer_le_fixer _ (B.map_mem_oneStabilizer hz' x)

/-- The positive depth-zero root-group span at `x` lies in the root filtration span. -/
theorem positiveZeroRootGroups_le_rootFiltrationSpan (x : B.Apartment)
    (mu : cocharacterLattice B.S) :
    B.positiveZeroRootGroups x mu ≤ B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) 0 := by
  refine iSup_le fun b => ?_
  exact le_iSup₂_of_le (f := fun c (_ : c ∈ positiveRelativeRoots B.i mu) =>
        B.filtration x c 0) b.1 b.2 le_rfl

/-- `U_{b,x,0} ≤ U_b(K)`, spanned over a set of roots. -/
theorem rootFiltrationSpan_zero_le_rootGroupSpan (x : B.Apartment)
    (Ψ : Set (characterLattice B.S)) :
    B.rootFiltrationSpan x Ψ 0 ≤ B.rootGroupSpan Ψ :=
  iSup₂_mono fun b _ => B.filtration_le_rootGroup x b 0

/-- The depth-zero root filtrations of relative roots lie in `G(K)_{x,0}`. -/
theorem rootFiltrationSpan_zero_le_moyPrasad (x : B.Apartment) (Ψ : Set (characterLattice B.S))
    (hΨ : Ψ ⊆ relativeRoots B.i) :
    B.rootFiltrationSpan x Ψ 0 ≤ B.moyPrasad hZ x 0 := by
  refine iSup₂_le fun b hb => ?_
  have h0 := B.filtration_le_moyPrasad hZ x ⟨b, hΨ hb⟩ 0
  rwa [NNReal.coe_zero] at h0

/-- Clause (a): for a generic integral cocharacter `mu`,
`⟨U_b(K) : b ∈ Φ⁺(mu)⟩ ∩ G(K)_{x,0} = ⟨U_{b,x,0} : b ∈ Φ⁺(mu)⟩`. -/
theorem rootGroupSpan_inf_moyPrasad_zero (x : B.Apartment) (mu : cocharacterLattice B.S)
    (hmu : IsGenericCocharacter B.i mu) :
    B.rootGroupSpan (positiveRelativeRoots B.i mu) ⊓ B.moyPrasad hZ x 0 =
      B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) 0 := by
  apply le_antisymm
  · rintro g ⟨hgU, hgM⟩
    have hU : g ∈ (Dynamic.unipotent
        (CommGroupScheme.groupHom mu ≫ B.i)).carrier (Over.mk (𝟙 _)) := by
      refine (iSup₂_le fun b hb => ?_ : B.rootGroupSpan (positiveRelativeRoots B.i mu) ≤ _) hgU
      exact RelativeRoot.subgroup_le_dynamicUnipotent B.i mu hb.2 (Over.mk (𝟙 _))
    have hfix := B.moyPrasad_zero_le_fixer hZ x hgM
    have h : g ∈ B.positiveZeroRootGroups x mu :=
      B.apartment.mem_positiveRootGroups_of_mem_unipotent_of_smul_apartmentMap_eq
        B.isConnectedReductive B.isMaximalSplitTorus x mu hmu hU hfix
    exact B.positiveZeroRootGroups_le_rootFiltrationSpan x mu h
  · exact le_inf (B.rootFiltrationSpan_zero_le_rootGroupSpan x _)
      (B.rootFiltrationSpan_zero_le_moyPrasad hZ x _ fun _ hb => hb.1)

/-! ### Clause (b): auxiliary facts on Levi subgroups and the depth-zero group -/

/-- An integral cocharacter vanishing on exactly the relative roots on which `ν` vanishes. -/
theorem exists_cocharacter_comp_eq_zero_iff (ν : V B.S) :
    ∃ lam : cocharacterLattice B.S, ∀ b ∈ relativeRoots B.i,
      (lam ≫ b = 0 ↔ eval B.S b ν = 0) := by
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : Smooth H.X.hom := B.isConnectedReductive.smooth
  have hfin := IsSplitTorus.finite_relativeRoots (i := B.i) B.isMaximalSplitTorus.1.1
  obtain ⟨lam, hlam⟩ := DepthZeroApprox.exists_comp_eq_zero_iff B.S hfin.toFinset ν
  exact ⟨lam, fun b hb => hlam b (hfin.mem_toFinset.2 hb)⟩

/-- The relative roots killed by `lam` coincide with `Φ₀(ν)`. -/
theorem zeroPairingRoots_eq_setOf (ν : V B.S) (lam : cocharacterLattice B.S)
    (hlam : ∀ b ∈ relativeRoots B.i, (lam ≫ b = 0 ↔ eval B.S b ν = 0)) :
    B.zeroPairingRoots ν = {b | b ∈ relativeRoots B.i ∧ lam ≫ b = 0} := by
  ext b
  exact ⟨fun h => ⟨h.1, (hlam b h.1).2 h.2⟩, fun h => ⟨h.1, (hlam b h.1).1 h.2⟩⟩

/-- A depth-zero filtration subgroup of a root of `Ψ` lies in the span over `Ψ`. -/
theorem filtration_le_rootFiltrationSpan (x : B.Apartment) {Ψ : Set (characterLattice B.S)}
    {b : characterLattice B.S} (hb : b ∈ Ψ) (r : ℝ) :
    B.filtration x b r ≤ B.rootFiltrationSpan x Ψ r :=
  le_iSup₂_of_le (f := fun c (_ : c ∈ Ψ) => B.filtration x c r) b hb le_rfl

/-- The depth-zero root filtration span of relative roots lies in the point sharp fixer. -/
theorem rootFiltrationSpan_le_sharpFixer (x : B.Apartment) (Ψ : Set (characterLattice B.S))
    (hΨ : Ψ ⊆ relativeRoots B.i) :
    B.rootFiltrationSpan x Ψ 0 ≤ B.sharpFixer {x} := by
  refine iSup₂_le fun b hb => ?_
  have h := B.apartment.rootFixer_le_sharpFixer ⟨b, hΨ hb⟩ {x}
  rwa [KPApartmentData.rootFixer_singleton] at h

/-- The triple supremum produced by Levi sharp transport is the root filtration span. -/
theorem iSup_comp_eq_zero_le_rootFiltrationSpan (x : B.Apartment)
    (lam : cocharacterLattice B.S) :
    (⨆ (b : characterLattice B.S) (_ : b ∈ relativeRoots B.i) (_ : lam ≫ b = 0),
        B.apartment.filtration x b 0) ≤
      B.rootFiltrationSpan x {b | b ∈ relativeRoots B.i ∧ lam ≫ b = 0} 0 :=
  iSup_le fun _ => iSup_le fun hb => iSup_le fun h0 =>
    B.filtration_le_rootFiltrationSpan x (Ψ := {b | b ∈ relativeRoots B.i ∧ lam ≫ b = 0})
      ⟨hb, h0⟩ 0

/-- Centralizing `S` implies centralizing every subtorus mapped into it. -/
theorem centralizerPoints_le_centralizerPoints_comp
    {A : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} (f : A ⟶ B.S) :
    centralizerPoints B.i ≤ centralizerPoints (CommGroupScheme.groupHom f ≫ B.i) := by
  intro g hg
  rw [mem_centralizerPoints] at hg ⊢
  rw [Category.assoc, hg]

/-- `j(Z(K))` centralizes `S`. -/
theorem range_le_centralizerPoints :
    (rationalPoints.map B.centralizer.j).range ≤ centralizerPoints B.i := by
  rintro _ ⟨z, rfl⟩
  exact _root_.Langlands.Geometry.Building.map_mem_centralizerPoints
    B.centralizer.isRepresentedBy z

/-- The root groups of `Φ₀(ν)` centralize the image of `lam` when `lam` kills `Φ₀(ν)`. -/
theorem rootGroupSpan_zeroPairingRoots_le_centralizerPoints (ν : V B.S)
    (lam : cocharacterLattice B.S) (hlam : ∀ b ∈ B.zeroPairingRoots ν, lam ≫ b = 0) :
    B.rootGroupSpan (B.zeroPairingRoots ν) ≤
      centralizerPoints (CommGroupScheme.groupHom lam ≫ B.i) := by
  refine iSup₂_le fun b hb => ?_
  exact rootGroupPoints_le_centralizerPoints_of_comp_eq_zero B.i lam (hlam b hb)

/-- `M_ν(K)` centralizes the image of `lam` when `lam` kills `Φ₀(ν)`. -/
theorem pairingLeviSpan_le_centralizerPoints (ν : V B.S) (lam : cocharacterLattice B.S)
    (hlam : ∀ b ∈ B.zeroPairingRoots ν, lam ≫ b = 0) :
    B.pairingLeviSpan ν ≤ centralizerPoints (CommGroupScheme.groupHom lam ≫ B.i) :=
  sup_le ((B.range_le_centralizerPoints).trans
      (B.centralizerPoints_le_centralizerPoints_comp lam))
    (B.rootGroupSpan_zeroPairingRoots_le_centralizerPoints ν lam hlam)

/-- The point sharp fixer is generated by the depth-zero root filtrations. -/
theorem sharpFixer_singleton_eq_iSup (x : B.Apartment) :
    B.sharpFixer {x} = ⨆ b : relativeRoots B.i, B.filtration x b 0 := by
  rw [← B.sharpFiltration_zero_eq_sharpFixer x, B.apartment.sharpFiltration_eq_iSup]
  rfl

/-- `j(Z(K)_0)` normalizes the point sharp fixer. -/
theorem centralizerTorusImage_zero_le_normalizer_sharpFixer (x : B.Apartment) :
    B.centralizerTorusImage hZ 0 ≤
      Subgroup.normalizer (B.sharpFixer {x} : Set (rationalPoints H)) := by
  rw [B.sharpFixer_singleton_eq_iSup x]
  exact le_trans
    (le_iInf fun b : relativeRoots B.i => B.image_le_normalizer_filtration hZ x 0 b.1 0)
    (Subgroup.iInf_normalizer_le_normalizer_iSup _)

/-- `G(K)_{x,0} = j(Z(K)_0) · G(K)^♯_x` as sets. -/
theorem coe_moyPrasad_zero (x : B.Apartment) :
    (B.moyPrasad hZ x 0 : Set (rationalPoints H)) =
      (B.centralizerTorusImage hZ 0 : Set (rationalPoints H)) * B.sharpFixer {x} := by
  rw [moyPrasad_eq_sup, B.sharpFiltration_zero_eq_sharpFixer x]
  exact Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (B.centralizerTorusImage_zero_le_normalizer_sharpFixer hZ x)

/-- A normalizer point centralizing the image of `lam` fixes `lam` under its Weyl action. -/
theorem comp_normalizingAut_hom_eq (lam : cocharacterLattice B.S) (n : normalizerPoints B.i)
    (hn : (n : rationalPoints H) ∈ centralizerPoints (CommGroupScheme.groupHom lam ≫ B.i)) :
    lam ≫ (normalizingAut B.i n).hom = lam := by
  have hσ := isNormalizingPoint_normalizingAut B.i n
  rw [mem_centralizerPoints, Category.assoc] at hn
  rw [hσ] at hn
  have h' : (CommGroupScheme.groupHom lam ≫
        CommGroupScheme.groupHom (normalizingAut B.i n).hom).hom.hom.left ≫
        B.i.hom.hom.left =
      (CommGroupScheme.groupHom lam).hom.hom.left ≫ B.i.hom.hom.left :=
    congrArg (fun f => f.hom.hom.left) ((Category.assoc _ _ _).trans hn)
  have h'' := (cancel_mono _).1 h'
  change Additive.ofMul (CommGroupScheme.groupHom lam ≫
      CommGroupScheme.groupHom (normalizingAut B.i n).hom) =
    Additive.ofMul (CommGroupScheme.groupHom lam)
  congr 1
  apply Grp.hom_ext
  exact Over.OverMorphism.ext h''

/-! ### Clause (b): normalizer points in the sharp fixer centralizing `lam` -/

/-- An affine-root reflection vanishing at `x` and at `lam +ᵥ x` lifts to the normalizer
inside the depth-zero root filtration span at `x` of the relative roots killed by `lam`. -/
theorem exists_rootFiltrationSpan_normalizer_eq_affineReflection (x : B.Apartment)
    (lam : cocharacterLattice B.S) {ψ : B.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ B.affineRoots)
    (hx : ψ x = 0)
    (hlx : ψ ((Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] lam) : TranslationSpace B.i) +ᵥ x) = 0)
    {w : TranslationSpace B.i} (hw : AffineRootSystem.IsCoroot B.affineRoots ψ w) :
    ∃ m : normalizerPoints B.i, (m : rationalPoints H) ∈
        B.rootFiltrationSpan x {b | b ∈ relativeRoots B.i ∧ lam ≫ b = 0} 0 ∧
      B.apartment.normalizerAffineEquiv m = AffineRootSystem.affineReflection ψ hw.1 := by
  have hψ' := B.apartment.affineRoots_subset_extendedAffineRoots hψ
  rw [← B.reflectionAffineRoots_eq] at hψ'
  obtain ⟨α, u, hu, hu1, rfl⟩ := hψ'
  obtain ⟨p, hp⟩ := B.hasOppositeFactorPairs α α.property u hu hu1
  have hflip : weylAction B.i (B.reflectionElement hp) α = -(α : characterLattice B.S) :=
    hp.weylAction_eq_neg B.i B.isMaximalSplitTorus.isSplitSubtorus.1 α.property.1 hu hu1
  have hneg : -(α : characterLattice B.S) ∈ relativeRoots B.i :=
    hflip ▸ weylAction_mapsTo_relativeRoots B.i (B.reflectionElement hp) α.property
  have hval0 : x.val α u = 0 := by
    rw [← B.coe_reflectionFunctional_apply hu hu1 x, hx, WithTop.coe_zero]
  have hval1 : ((Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] lam) : TranslationSpace B.i) +ᵥ x).val
      α u = 0 := by
    rw [← B.coe_reflectionFunctional_apply hu hu1 _, hlx, WithTop.coe_zero]
  have hpair : latticePairing B.S (α : characterLattice B.S) lam = 0 := by
    rw [KPApartmentData.val_mk_vadd_apply, hval0, zero_add, eval_tmul, one_mul] at hval1
    exact_mod_cast hval1
  have hlam : lam ≫ (α : characterLattice B.S) = 0 :=
    (DepthZeroApprox.comp_eq_zero_iff_latticePairing_eq_zero B.S _ lam).2 hpair
  have hlamneg : lam ≫ (-(α : characterLattice B.S)) = 0 := by
    rw [Preadditive.comp_neg, hlam, neg_zero]
  have hfix : u ∈ B.apartment.rootFixer α {x} := by
    refine B.apartment.mem_rootFixer.2 ⟨hu, fun y hy => ⟨hu, ?_⟩⟩
    rw [Set.mem_singleton_iff.1 hy]
    simp only [hval0, WithTop.coe_zero, le_refl]
  have hp1 : p.1 ∈ B.apartment.rootFixer (-(α : characterLattice B.S)) {x} := by
    refine B.apartment.mem_rootFixer.2 ⟨hp.1, fun y hy => ⟨hp.1, ?_⟩⟩
    rw [Set.mem_singleton_iff.1 hy]
    have h5 := x.isValuation.opposite α α.property u hu hu1 p.1 hp.1 p.2 hp.2.1 hp.2.2
    rw [hval0, add_zero] at h5
    simp only [h5, WithTop.coe_zero, le_refl]
  have hp2 : p.2 ∈ B.apartment.rootFixer (-(α : characterLattice B.S)) {x} := by
    refine B.apartment.mem_rootFixer.2 ⟨hp.2.1, fun y hy => ⟨hp.2.1, ?_⟩⟩
    rw [Set.mem_singleton_iff.1 hy]
    have h5 := x.isValuation.opposite_snd α.property hu hu1 hp.1 hp.2.1 hp.2.2
    rw [hval0, add_zero] at h5
    simp only [h5, WithTop.coe_zero, le_refl]
  rw [KPApartmentData.rootFixer_singleton] at hfix hp1 hp2
  have hfix' := B.filtration_le_rootFiltrationSpan x
    (Ψ := {b | b ∈ relativeRoots B.i ∧ lam ≫ b = 0}) ⟨α.property, hlam⟩ 0 hfix
  have hp1' := B.filtration_le_rootFiltrationSpan x
    (Ψ := {b | b ∈ relativeRoots B.i ∧ lam ≫ b = 0}) ⟨hneg, hlamneg⟩ 0 hp1
  have hp2' := B.filtration_le_rootFiltrationSpan x
    (Ψ := {b | b ∈ relativeRoots B.i ∧ lam ≫ b = 0}) ⟨hneg, hlamneg⟩ 0 hp2
  refine ⟨B.reflectionElement hp, ?_, ?_⟩
  · rw [B.coe_reflectionElement]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hp1' hfix') hp2'
  · have heq := B.reflectionCoroot_eq_of_isCoroot hu hu1 hp hw
    simpa only [heq] using B.normalizerAffineEquiv_reflectionElement hu hu1 hp

/-- A normalizer point centralizing the image of `lam` fixes the translation by `lam`. -/
theorem translationAction_tmul_eq_of_mem_centralizerPoints (lam : cocharacterLattice B.S)
    (n : normalizerPoints B.i)
    (hnc : (n : rationalPoints H) ∈ centralizerPoints (CommGroupScheme.groupHom lam ≫ B.i)) :
    translationAction B.i n
        (Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] lam) : TranslationSpace B.i) =
      Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] lam) := by
  rw [translationAction_mk]
  change Submodule.Quotient.mk (normalizerAction B.i n ((1 : ℝ) ⊗ₜ[ℤ] lam)) = _
  rw [normalizerAction_tmul, B.comp_normalizingAut_hom_eq lam n hnc]

/-- A normalizer point fixing `x` and centralizing the image of `lam` fixes `lam +ᵥ x`. -/
theorem normalizerAffineEquiv_vadd_eq_of_mem_centralizerPoints (x : B.apartment.Apartment)
    (lam : cocharacterLattice B.S) (n : normalizerPoints B.i)
    (hfx : B.apartment.normalizerAffineEquiv n x = x)
    (hnc : (n : rationalPoints H) ∈ centralizerPoints (CommGroupScheme.groupHom lam ≫ B.i)) :
    B.apartment.normalizerAffineEquiv n
        ((Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] lam) : TranslationSpace B.i) +ᵥ x) =
      (Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] lam) : TranslationSpace B.i) +ᵥ x := by
  rw [KPApartmentData.normalizerAffineEquiv_apply, KPApartmentData.smul_vadd,
    ← KPApartmentData.normalizerAffineEquiv_apply, hfx,
    B.translationAction_tmul_eq_of_mem_centralizerPoints lam n hnc]

/-- An affine-Weyl normalizer point fixing `x` and `lam +ᵥ x` acts on the apartment like an
element of the depth-zero root filtration span at `x` of the roots killed by `lam`. -/
theorem exists_rootFiltrationSpan_normalizerAffineEquiv_eq (x : B.apartment.Apartment)
    (lam : cocharacterLattice B.S) (n : normalizerPoints B.i)
    (hnW : B.apartment.normalizerAffineEquiv n ∈
      AffineRootSystem.affineWeylGroup B.affineRoots)
    (hfx : B.apartment.normalizerAffineEquiv n x = x)
    (hfv : B.apartment.normalizerAffineEquiv n
        ((Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] lam) : TranslationSpace B.i) +ᵥ x) =
      (Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] lam) : TranslationSpace B.i) +ᵥ x) :
    ∃ m : normalizerPoints B.i, (m : rationalPoints H) ∈
        B.rootFiltrationSpan x {b | b ∈ relativeRoots B.i ∧ lam ≫ b = 0} 0 ∧
      B.apartment.normalizerAffineEquiv m = B.apartment.normalizerAffineEquiv n := by
  classical
  have hΨ := B.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs
    B.hasOppositeFactorPairs
  obtain ⟨z, hzfix, hzgen⟩ := AffineRootSystem.exists_generic_point hΨ
    {x, (Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] lam) : TranslationSpace B.i) +ᵥ x}
    (Finset.insert_nonempty _ _)
  have haz : B.apartment.normalizerAffineEquiv n z = z := by
    refine hzfix _ fun y hy => ?_
    rcases Finset.mem_insert.1 hy with hy | hy
    · rw [hy]
      exact hfx
    · rw [Finset.mem_singleton.1 hy]
      exact hfv
  have hcl := AffineRootSystem.mem_closure_pointReflections_of_apply_eq hΨ
    ⟨B.apartment.normalizerAffineEquiv n, hnW⟩ haz
  have hle : Subgroup.closure (AffineRootSystem.pointReflections B.affineRoots z) ≤
      ((B.rootFiltrationSpan x {b | b ∈ relativeRoots B.i ∧ lam ≫ b = 0} 0).subgroupOf
        (normalizerPoints B.i)).map B.apartment.normalizerAffineEquiv := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨ψ, hψ, hψz, w, hw, rfl⟩
    obtain ⟨m, hm, hmeq⟩ := B.exists_rootFiltrationSpan_normalizer_eq_affineReflection x lam hψ
      (hzgen ψ hψ hψz x (Finset.mem_insert_self _ _))
      (hzgen ψ hψ hψz _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) hw
    exact ⟨m, Subgroup.mem_subgroupOf.2 hm, hmeq⟩
  obtain ⟨m, hm, hmeq⟩ := hle hcl
  exact ⟨m, hm, hmeq⟩

/-- Two depth-zero normalizer points acting identically on the apartment differ by an element
of `j(Z(K)_0)`. -/
theorem mem_centralizerTorusImage_of_normalizerAffineEquiv_eq (m n : normalizerPoints B.i)
    (hm : (m : rationalPoints H) ∈
      (UnramifiedZeroDatum.ofConnectedReductive H B.isConnectedReductive).zeroPoints)
    (hn : (n : rationalPoints H) ∈
      (UnramifiedZeroDatum.ofConnectedReductive H B.isConnectedReductive).zeroPoints)
    (hmn : B.apartment.normalizerAffineEquiv m = B.apartment.normalizerAffineEquiv n) :
    (m : rationalPoints H)⁻¹ * n ∈ B.centralizerTorusImage hZ 0 := by
  rw [← (UnramifiedZeroDatum.ofConnectedReductive H
    B.isConnectedReductive).wholeApartmentZeroFixer_eq_centralizerTorusImage B hZ]
  refine Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hm) hn, ?_⟩
  refine (B.apartment.mem_pointwiseFixer_image_iff).2 fun y _ => ?_
  have h1 : B.apartment.normalizerAffineEquiv (m⁻¹ * n) y = y := by
    rw [map_mul, map_inv, hmn, inv_mul_cancel]
    rfl
  have h2 := congrArg B.apartment.apartmentMap h1
  rw [KPApartmentData.normalizerAffineEquiv_apply, KPApartmentData.apartmentMap_smul] at h2
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h2

/-- A normalizer point in the sharp fixer of `x` centralizing the image of `lam` lies in the
join of `j(Z(K)_0)` with the depth-zero root filtrations at `x` of the roots killed by `lam`. -/
theorem normalizer_mem_of_mem_centralizerPoints (x : B.Apartment)
    (lam : cocharacterLattice B.S) (n : normalizerPoints B.i)
    (hnx : (n : rationalPoints H) ∈ B.sharpFixer {x})
    (hnc : (n : rationalPoints H) ∈ centralizerPoints (CommGroupScheme.groupHom lam ≫ B.i)) :
    (n : rationalPoints H) ∈ B.centralizerTorusImage hZ 0 ⊔
      B.rootFiltrationSpan x {b | b ∈ relativeRoots B.i ∧ lam ≫ b = 0} 0 := by
  have hn0 := (UnramifiedZeroDatum.ofConnectedReductive H
    B.isConnectedReductive).sharpFixer_le_zeroPoints B {x} hnx
  have hnW := (UnramifiedZeroDatum.ofConnectedReductive H
    B.isConnectedReductive).normalizer_mem_affineWeylGroup_of_mem_zeroPoints B
    MaximalUnramified.simplyConnectedNormalizerAffineWeyl n hn0
  have hfx : B.apartment.normalizerAffineEquiv n x = x :=
    (KPApartmentData.normalizerAffineEquiv_apply n x).trans
      (B.apartment.normalizer_smul_eq_self_of_mem_sharpFixer
        B.isConnectedReductive B.isMaximalSplitTorus x n hnx)
  obtain ⟨m, hmS, hmn⟩ := B.exists_rootFiltrationSpan_normalizerAffineEquiv_eq x lam n hnW hfx
    (B.normalizerAffineEquiv_vadd_eq_of_mem_centralizerPoints x lam n hfx hnc)
  have hm0 := (UnramifiedZeroDatum.ofConnectedReductive H
    B.isConnectedReductive).sharpFixer_le_zeroPoints B {x}
      (B.rootFiltrationSpan_le_sharpFixer x _ (fun _ hb => hb.1) hmS)
  have hk := B.mem_centralizerTorusImage_of_normalizerAffineEquiv_eq hZ m n hm0 hn0 hmn
  have h : (m : rationalPoints H) * ((m : rationalPoints H)⁻¹ * n) ∈
      B.centralizerTorusImage hZ 0 ⊔
        B.rootFiltrationSpan x {b | b ∈ relativeRoots B.i ∧ lam ≫ b = 0} 0 :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_right hmS) (Subgroup.mem_sup_left hk)
  rwa [mul_inv_cancel_left] at h

/-! ### Clause (b) -/

/-- `j(Z(K)_0)` centralizes the image of every cocharacter of `S`. -/
theorem centralizerTorusImage_le_centralizerPoints (lam : cocharacterLattice B.S) (r : ℝ≥0) :
    B.centralizerTorusImage hZ r ≤
      centralizerPoints (CommGroupScheme.groupHom lam ≫ B.i) :=
  ((Subgroup.map_le_range _ _).trans B.range_le_centralizerPoints).trans
    (B.centralizerPoints_le_centralizerPoints_comp lam)

/-- An element of `G(K)_{x,0}` centralizing the image of `lam` lies in the join of
`j(Z(K)_0)` with the depth-zero root filtrations at `x` of the roots killed by `lam`. -/
theorem mem_sup_of_mem_centralizerPoints_of_mem_moyPrasad (x : B.Apartment)
    (lam : cocharacterLattice B.S) {g : rationalPoints H}
    (hgc : g ∈ centralizerPoints (CommGroupScheme.groupHom lam ≫ B.i))
    (hgM : g ∈ B.moyPrasad hZ x 0) :
    g ∈ B.centralizerTorusImage hZ 0 ⊔
      B.rootFiltrationSpan x {b | b ∈ relativeRoots B.i ∧ lam ≫ b = 0} 0 := by
  have hgM' : g ∈ (B.moyPrasad hZ x 0 : Set (rationalPoints H)) := hgM
  rw [B.coe_moyPrasad_zero hZ x] at hgM'
  obtain ⟨z, hz, s, hs, rfl⟩ := Set.mem_mul.1 hgM'
  have hz' : z ∈ B.centralizerTorusImage hZ 0 := hz
  have hs' : s ∈ B.sharpFixer {x} := hs
  have hzc := B.centralizerTorusImage_le_centralizerPoints hZ lam 0 hz'
  have hsc : s ∈ centralizerPoints (CommGroupScheme.groupHom lam ≫ B.i) := by
    have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ hzc) hgc
    rwa [inv_mul_cancel_left] at h
  have hsn : s ∈ normalizerPoints (CommGroupScheme.groupHom lam ≫ B.i) :=
    centralizerPoints_le_normalizerPoints (CommGroupScheme.groupHom lam ≫ B.i) hsc
  have hxy : B.apartment.apartmentMap x = s • B.apartment.apartmentMap x :=
    (B.apartment.mem_reducedFixer.1 (B.apartment.sharpFixer_le_reducedFixer x hs')).symm
  have : Infinite F := LocalField.infinite_of_isNonarchimedeanLocalField F
  have : Infinite (UnramifiedClosure F) :=
    Infinite.of_injective (algebraMap F (UnramifiedClosure F))
      (algebraMap F (UnramifiedClosure F)).injective
  obtain ⟨h, hhc, hhF, hsh⟩ := B.apartment.exists_leviSharp_transport
    B.isConnectedReductive B.isMaximalSplitTorus
    (isSplitTorus_gm (S := Spec (CommRingCat.of (UnramifiedClosure F)))) lam rfl hsn x x hxy
  have hhS : h ∈ B.rootFiltrationSpan x {b | b ∈ relativeRoots B.i ∧ lam ≫ b = 0} 0 :=
    B.iSup_comp_eq_zero_le_rootFiltrationSpan x lam hhF
  have hshx : s * h ∈ B.sharpFixer {x} :=
    Subgroup.mul_mem _ hs' (B.rootFiltrationSpan_le_sharpFixer x _ (fun _ hb => hb.1) hhS)
  have hshc : s * h ∈ centralizerPoints (CommGroupScheme.groupHom lam ≫ B.i) :=
    Subgroup.mul_mem _ hsc hhc
  have hn := B.normalizer_mem_of_mem_centralizerPoints hZ x lam ⟨s * h, hsh⟩ hshx hshc
  have hfin : z * (s * h) * h⁻¹ ∈ B.centralizerTorusImage hZ 0 ⊔
      B.rootFiltrationSpan x {b | b ∈ relativeRoots B.i ∧ lam ≫ b = 0} 0 :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hz') hn)
      (Subgroup.inv_mem _ (Subgroup.mem_sup_right hhS))
  rwa [← mul_assoc z s h, mul_inv_cancel_right] at hfin

/-- Clause (b): `M_ν(K) ∩ G(K)_{x,0} ⊆ j(Z(K)_0) · ⟨U_{b,x,0} : ⟨b, ν⟩ = 0⟩`. -/
theorem pairingLeviSpan_inf_moyPrasad_zero_le (x : B.Apartment) (ν : V B.S) :
    B.pairingLeviSpan ν ⊓ B.moyPrasad hZ x 0 ≤
      B.centralizerTorusImage hZ 0 ⊔ B.rootFiltrationSpan x (B.zeroPairingRoots ν) 0 := by
  obtain ⟨lam, hlam⟩ := B.exists_cocharacter_comp_eq_zero_iff ν
  rintro g ⟨hgL, hgM⟩
  have hgc := B.pairingLeviSpan_le_centralizerPoints ν lam
    (fun b hb => (hlam b hb.1).2 hb.2) hgL
  have h := B.mem_sup_of_mem_centralizerPoints_of_mem_moyPrasad hZ x lam hgc hgM
  rwa [← B.zeroPairingRoots_eq_setOf ν lam hlam] at h

end Langlands.Geometry.Building.MaximalUnramified.BuildingData

namespace Langlands.Geometry.Building.MaximalUnramified

/-- **KP Proposition 7.3.12 and Lemma 8.5.19 at depth zero over `K = F^ur`.** -/
theorem localMoyPrasadDepthZero : LocalMoyPrasadDepthZeroStatement.{u} := by
  intro F _ _ _ _ H _ B hZ
  exact ⟨fun x mu hmu => B.rootGroupSpan_inf_moyPrasad_zero hZ x mu hmu,
    fun x ν => B.pairingLeviSpan_inf_moyPrasad_zero_le hZ x ν⟩

end Langlands.Geometry.Building.MaximalUnramified
