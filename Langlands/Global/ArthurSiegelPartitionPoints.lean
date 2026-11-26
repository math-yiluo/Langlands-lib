import Langlands.Global.ArthurSiegelSetsIwasawaStatement
import Langlands.Global.ArthurParabolicSpacesStatement
import Langlands.Global.AdelicEisensteinParabolicRangeTransport
import Langlands.Global.AdelicStandardLeviHeightRestriction
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof
import Langlands.GroupScheme.Absolute.ParabolicTransport

/-! # Rational points and heights for standard parabolic subgroups

Facts on the objects of `Langlands.Global.ArthurTruncation` used in the proof of Arthur's
partition lemma (Arthur 1978, Lemma 6.4):

* `parabolicRationalImage_mono`: `P_1(F) ⊆ P(F)` for standard `P_1 ⊆ P`;
* `rationalSubgroup_le_parabolicRationalImage`: `G(F) = P(F)` for `Δ_0^P = Δ_0`;
* `height_sub_mem_span`: for `γ ∈ P(F)`, `H_0(γy) − H_0(y)` lies in `𝔞_0^P`, the span of the
  coroots of `Δ_0^P` (from the comparison `ParabolicSpacesComparisonStatement` and the product
  formula);
* `height_siegel_product` identifies `H_0(nmak)` with `H_0(a)`. The corresponding
  Siegel-set membership statement is `exists_height_eq_of_mem_siegelSet`. Both are in
  `Langlands.Global.ArthurSiegelPartitionProof`. -/

noncomputable section

set_option linter.unusedSectionVars false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints
  ArthurParabolicSpaces AdelicSiegelFactors

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T}

section Points

omit [Mono i.hom.hom.left] in
theorem mem_parabolicRationalImage_iff (J : Set (characterLattice T))
    (x : AdelicGroupPoints F G) :
    x ∈ parabolicRationalImage (Standard.parabolicHom i ν J) ↔
      x ∈ rationalImage F (Standard.parabolicHom i ν J) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hy
    rw [rationalImage_eq_map]
    exact ⟨z, hz, hzy⟩
  · intro hx
    have hx' := hx
    rw [rationalImage_eq_map] at hx'
    obtain ⟨z, hz, hzx⟩ := hx'
    have hmem : x ∈ rationalSubgroup F G := rationalImage_le_rationalSubgroup _ hx
    exact ⟨⟨x, hmem⟩, ⟨z, hz, hzx⟩, rfl⟩

omit [Mono i.hom.hom.left] in
/-- `P_1(F) ⊆ P(F)` for standard parabolic subgroups `P_1 ⊆ P`. -/
theorem parabolicRationalImage_mono (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {J K : Set (characterLattice T)} (hJK : J ⊆ K)
    (hK : K ⊆ simpleRelativeRoots i ν) :
    parabolicRationalImage (Standard.parabolicHom i ν J) ≤
      parabolicRationalImage (Standard.parabolicHom i ν K) := by
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have hle : standardParabolic i ν J ≤ standardParabolic i ν K :=
    ((standardParabolicOrder F G hG T i hi ν hν).1 J K (hJK.trans hK) hK).1.mp hJK
  intro x hx
  rw [mem_parabolicRationalImage_iff] at hx ⊢
  refine rationalImage_le_of_range_le _ _ ?_ hx
  rw [(Standard.isRepresentedBy_parabolicHom i ν J).2,
    (Standard.isRepresentedBy_parabolicHom i ν K).2]
  exact hle

omit [Mono i.hom.hom.left] in
/-- `G(F) = P(F)` for the standard parabolic subgroup with `Δ_0^P = Δ_0`. -/
theorem rationalSubgroup_le_parabolicRationalImage (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) :
    rationalSubgroup F G ≤
      parabolicRationalImage (Standard.parabolicHom i ν (simpleRelativeRoots i ν)) := by
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have htop : standardParabolic i ν (simpleRelativeRoots i ν) = ⊤ :=
    (standardParabolicEndpoints F G hG T i hi ν hν).2.2.1
  intro x hx
  rw [mem_parabolicRationalImage_iff]
  obtain ⟨y, rfl⟩ := hx
  have hrange : SubgroupFunctor.range (𝟙 G) ≤
      SubgroupFunctor.range (Standard.parabolicHom i ν (simpleRelativeRoots i ν)) := by
    rw [(Standard.isRepresentedBy_parabolicHom i ν _).2, htop]
    intro U x _
    exact Subgroup.mem_top x
  refine rationalImage_le_of_range_le _ _ hrange ⟨y, ?_⟩
  simp [map_apply]

end Points

section Heights

variable [LocallyOfFiniteType G.X.hom] {K : Subgroup (AdelicGroupPoints F G)}

omit [NumberField F] [Mono i.hom.hom.left] [LocallyOfFiniteType G.X.hom] in
/-- The inclusion `P_0 ⊆ P` of standard parabolic subgroups, as a factorization of the closed
representatives. -/
theorem exists_parabolicFactor (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {S : Set (characterLattice T)}
    (hS : S ⊆ simpleRelativeRoots i ν) :
    ∃ f : Standard.parabolicScheme i ν ∅ ⟶ Standard.parabolicScheme i ν S,
      f ≫ Standard.parabolicHom i ν S = Standard.parabolicHom i ν ∅ := by
  have hle : standardParabolic i ν ∅ ≤ standardParabolic i ν S :=
    ((standardParabolicOrder F G hG T i hi ν hν).1 ∅ S (Set.empty_subset _) hS).1.mp
      (Set.empty_subset S)
  have := (Standard.isRepresentedBy_parabolicHom i ν ∅).1
  have := (Standard.isRepresentedBy_parabolicHom i ν S).1
  refine SubgroupFunctor.exists_factor_of_range_le ?_
  rw [(Standard.isRepresentedBy_parabolicHom i ν ∅).2,
    (Standard.isRepresentedBy_parabolicHom i ν S).2]
  exact hle

omit [Mono i.hom.hom.left] [LocallyOfFiniteType G.X.hom] in
/-- A compact subgroup with `P_0(𝔸)K = G(𝔸)` satisfies `P(𝔸)K = G(𝔸)` for every standard `P`. -/
theorem isIwasawaCompact_standard (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    {S : Set (characterLattice T)} (hS : S ⊆ simpleRelativeRoots i ν) :
    IsIwasawaCompact (Standard.parabolicHom i ν S) K := by
  obtain ⟨f, hf⟩ := exists_parabolicFactor hG hi hν hS
  refine ⟨hK.isCompact, Set.eq_univ_of_forall fun g => ?_⟩
  obtain ⟨q, k, hk, rfl⟩ := hK.exists_eq g
  refine ⟨map F _ G (Standard.parabolicHom i ν S) (map F _ _ f q), ⟨_, rfl⟩, k, hk, ?_⟩
  rw [← map_comp_apply_of_hom, hf]

omit [Mono i.hom.hom.left] [LocallyOfFiniteType G.X.hom] in
/-- The height `H_P` of a standard parabolic subgroup is the image of `H_P0` under the map
induced by the inclusion `P_0 ⊆ P`. -/
theorem height_standard_eq (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    {S : Set (characterLattice T)}
    (f : Standard.parabolicScheme i ν ∅ ⟶ Standard.parabolicScheme i ν S)
    (hf : f ≫ Standard.parabolicHom i ν S = Standard.parabolicHom i ν ∅)
    (hKS : IsIwasawaCompact (Standard.parabolicHom i ν S) K) (g : AdelicGroupPoints F G) :
    hKS.height g = realCharacterDualMap F _ _ f (hK.height g) := by
  obtain ⟨q, k, hk, rfl⟩ := hK.exists_eq g
  rw [hK.height_eq hk rfl, ← characterLog_map]
  have hq : map F _ G (Standard.parabolicHom i ν ∅) q =
      map F _ G (Standard.parabolicHom i ν S) (map F _ _ f q) := by
    rw [← map_comp_apply_of_hom, hf]
  rw [hq, hKS.height_eq hk rfl]

omit [NumberField F] [Mono i.hom.hom.left] [LocallyOfFiniteType G.X.hom] in
theorem torusToParabolic_comp_factor
    {S : Set (characterLattice T)}
    (f : Standard.parabolicScheme i ν ∅ ⟶ Standard.parabolicScheme i ν S)
    (hf : f ≫ Standard.parabolicHom i ν S = Standard.parabolicHom i ν ∅) :
    torusToParabolic F i ν ∅ ≫ f = torusToParabolic F i ν S := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  refine (cancel_mono (Standard.parabolicHom i ν S).hom.hom.left).mp ?_
  have h : (torusToParabolic F i ν ∅ ≫ f) ≫ Standard.parabolicHom i ν S =
      torusToParabolic F i ν S ≫ Standard.parabolicHom i ν S := by
    rw [Category.assoc, hf, torusToParabolic_comp, torusToParabolic_comp]
  exact congrArg (fun z : T.toGrp ⟶ G => z.hom.hom.left) h

/-- **`H_P` from `H_0`.** For a standard parabolic subgroup `P` with `Δ_0^P = S`, the map
`𝔞_0 → Hom(X(P), ℝ)` dual to restriction sends `H_0(g)` to the height `H_P(g)` of `K`. -/
theorem toCharacterDual_height (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)) {S : Set (characterLattice T)}
    (hS : S ⊆ simpleRelativeRoots i ν) (g : AdelicGroupPoints F G) :
    toCharacterDual F i ν S (height hi hK hρ g) = (isIwasawaCompact_standard hG hi hν hK hS).height g := by
  obtain ⟨f, hf⟩ := exists_parabolicFactor hG hi hν hS
  rw [height_standard_eq hK f hf (isIwasawaCompact_standard hG hi hν hK hS) g]
  apply AddMonoidHom.ext
  intro χ
  change pair T (restrictToTorus F i ν S ((1 : ℝ) ⊗ₜ[ℤ] χ)) (height hi hK hρ g) =
    hK.height g (characterRestrict f χ)
  have hres : restrictToTorus F i ν S ((1 : ℝ) ⊗ₜ[ℤ] χ) =
      restrictToTorus F i ν ∅ ((1 : ℝ) ⊗ₜ[ℤ] characterRestrict f χ) := by
    change rationalCharacterRestrictReal (torusToParabolic F i ν S) ((1 : ℝ) ⊗ₜ[ℤ] χ) =
      rationalCharacterRestrictReal (torusToParabolic F i ν ∅)
        ((1 : ℝ) ⊗ₜ[ℤ] characterRestrict f χ)
    rw [rationalCharacterRestrictReal_tmul, rationalCharacterRestrictReal_tmul,
      ← torusToParabolic_comp_factor f hf]
    rw [characterRestrict_comp]
    rfl
  rw [hres]
  change pair T (restrictToTorus F i ν ∅ ((1 : ℝ) ⊗ₜ[ℤ] characterRestrict f χ))
    (toA0 hi.isSplitSubtorus.1 hρ (hK.height g)) = _
  rw [pair_toA0, realParameterPairing_tmul, one_mul]

/-- **Invariance of `H_P` under `P(F)`.** For `γ ∈ P(F)`, `H_0(γy) − H_0(y)` lies in `𝔞_0^P`,
the span of the coroots of `Δ_0^P` (product formula, and the comparison
`ParabolicSpacesComparisonStatement` identifying the kernel of `𝔞_0 → Hom(X(P), ℝ)`). -/
theorem height_sub_mem_span
    (hcomp : ParabolicSpacesComparisonStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)) {S : Set (characterLattice T)}
    (hS : S ⊆ simpleRelativeRoots i ν) {r : AdelicGroupPoints F G}
    (hr : r ∈ parabolicRationalImage (Standard.parabolicHom i ν S))
    (y : AdelicGroupPoints F G) :
    height hi hK hρ (r * y) - height hi hK hρ y ∈ Submodule.span ℝ (D.realCorootsOf S) := by
  have hker := (hcomp F G hG T i hi ν hν D S hS).2.2.2.1
  rw [← hker, LinearMap.mem_ker, map_sub, toCharacterDual_height hG hi hν hK hρ hS,
    toCharacterDual_height hG hi hν hK hρ hS, sub_eq_zero]
  rw [mem_parabolicRationalImage_iff, rationalImage_eq_map] at hr
  obtain ⟨z, ⟨w, rfl⟩, rfl⟩ := hr
  exact (isIwasawaCompact_standard hG hi hν hK hS).height_rational_mul w y

end Heights

end Langlands.Global.ArthurTruncation
