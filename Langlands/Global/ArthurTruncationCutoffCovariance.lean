import Langlands.Global.ArthurSiegelSetsIwasawaStatement
import Langlands.Global.ArthurParabolicSpacesProof
import Langlands.Global.AdelicEisensteinParabolicRangeTransport
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof

/-! # Rational translations of Arthur's cutoff -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.Global.ArthurTruncation.Idempotence

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints
  ArthurParabolicSpaces

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T}

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

omit [Mono i.hom.hom.left] [LocallyOfFiniteType G.X.hom] in
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

omit [LocallyOfFiniteType G.X.hom] in
/-- **Invariance of `H_P` under `P(F)`.** For `γ ∈ P(F)`, `H_0(γy) − H_0(y)` lies in `𝔞_0^P`,
the span of the coroots of `Δ_0^P` (product formula, and the comparison
`ParabolicSpacesComparisonStatement` identifying the kernel of `𝔞_0 → Hom(X(P), ℝ)`). -/
theorem height_sub_mem_span
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)) {S : Set (characterLattice T)}
    (hS : S ⊆ simpleRelativeRoots i ν) {r : AdelicGroupPoints F G}
    (hr : r ∈ parabolicRationalImage (Standard.parabolicHom i ν S))
    (y : AdelicGroupPoints F G) :
    height hi hK hρ (r * y) - height hi hK hρ y ∈ Submodule.span ℝ (D.realCorootsOf S) := by
  have hker := (parabolicSpacesComparison F G hG T i hi ν hν D S hS).2.2.2.1
  rw [← hker, LinearMap.mem_ker, map_sub, toCharacterDual_height hG hi hν hK hρ hS,
    toCharacterDual_height hG hi hν hK hρ hS, sub_eq_zero]
  rw [mem_parabolicRationalImage_iff, rationalImage_eq_map] at hr
  obtain ⟨z, ⟨w, rfl⟩, rfl⟩ := hr
  exact (isIwasawaCompact_standard hG hi hν hK hS).height_rational_mul w y

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
/-- The full fundamental weights outside `S` vanish on the coroot span of `S`. -/
theorem fullWeight_eq_zero_of_mem_corootSpan
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
    {S : Set (characterLattice T)} (hS : S ⊆ simpleRelativeRoots i ν)
    {β : characterLattice T} (hβ : β ∈ simpleRelativeRoots i ν \ S)
    {H : V T} (hH : H ∈ Submodule.span ℝ (D.realCorootsOf S)) :
    ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) β H = 0 := by
  classical
  refine (Submodule.span_le.mpr ?_ :
    Submodule.span ℝ (D.realCorootsOf S) ≤
      (ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) β).ker) hH
  rintro _ ⟨α, hα, rfl⟩
  apply LinearMap.mem_ker.mpr
  rw [ArthurRelative.weight_coroot hG hi D hν
    Set.Subset.rfl hβ.1 α (hS hα), ite_eq_right]
  exact fun he => hβ.2 (he.symm ▸ hα)

omit [LocallyOfFiniteType G.X.hom] in
/-- The cutoff attached to `P` is constant on left `P(F)`-orbits. -/
theorem tauHat_parabolicRational_mul
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅))
    {S : Set (characterLattice T)} (hS : S ⊆ simpleRelativeRoots i ν)
    {r : AdelicGroupPoints F G}
    (hr : r ∈ parabolicRationalImage (Standard.parabolicHom i ν S))
    (y : AdelicGroupPoints F G) (Tp : V T) :
    ArthurRelative.tauHat hG hi ν D S (simpleRelativeRoots i ν)
        (height hi hK hρ (r * y) - Tp) =
      ArthurRelative.tauHat hG hi ν D S (simpleRelativeRoots i ν)
        (height hi hK hρ y - Tp) := by
  classical
  simp only [ArthurRelative.tauHat_eq hG hi D (ν := ν) S Set.Subset.rfl]
  refine if_congr ?_ rfl rfl
  refine forall_congr' fun β => forall_congr' fun hβ => ?_
  have h := fullWeight_eq_zero_of_mem_corootSpan hG hi hν D hS hβ
    (height_sub_mem_span hG hi hν D hK hρ hS hr y)
  rw [map_sub, sub_eq_zero] at h
  simp only [map_sub, h]

end Heights

end Langlands.Global.ArthurTruncation.Idempotence
