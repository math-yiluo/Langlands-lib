import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.BaseKummer
import Langlands.GaloisCohomology.Global.Finiteness

/-!
# Tate's base case in degrees zero and one

Let `K` be a number field, `S` a finite set of finite places containing the places above the
prime `ℓ`, `L ⊆ K_S` finite Galois over `K` with `μ_ℓ ⊆ L` and `[L : K]` prime to `ℓ`, `P ⊆ G_S` the
subgroup fixing `L`, and `M` a `G_S`-module killed by `ℓ` on which `P` acts trivially. With
`d = baseTwistFun` the additive function `X ↦ dim (X ⊗ Hom(μ_ℓ, M))^{Gal(L/K)}` and
`Aᵢ = Hⁱ(P, 𝒪_Sˣ)`:

* `dim H⁰(G_S, M) = d(A₀[ℓ])` (`baseCase_finrank_zero`) and
  `dim H¹(G_S, M) = d(A₀/ℓ) + d(A₁[ℓ])` (`baseCase_finrank_one`), from the coprime twist and the
  Kummer sequence;
* `d(A₀/ℓ) - d(A₀[ℓ]) = d(𝔽_ℓ[S_L]) + d(𝔽_ℓ[∞_L]) - d(𝔽_ℓ)` (`baseCase_units`), from the `S`-units of
  `L` as a Galois lattice, and `d(A₁/ℓ) = d(A₁[ℓ])` since `A₁` is finite (`baseCase_picard`).

Together: `dim H⁰ - dim H¹ = d(𝔽_ℓ) - d(𝔽_ℓ[S_L]) - d(𝔽_ℓ[∞_L]) - d(A₁/ℓ)`
(`baseCase_finrank_zero_sub_finrank_one`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  Langlands.GaloisCohomology.Local

universe u

noncomputable section

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] {ℓ : ℕ} [Fact ℓ.Prime]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
  {L : Type u} [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) [IsGalois K L]
  [(GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal]
  (hcop : Nat.Coprime (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)).index ℓ)
  (hζ : ∃ ζ : L, IsPrimitiveRoot ζ ℓ)
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
  (hMℓ : ∀ m : M, ℓ • m = 0)
  (hMP : ∀ g ∈ (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)), M.ρ g = 1)

attribute [local instance 2000] IsSepClosure.isGalois

/-- The subgroup fixing `L` is compact. -/
instance compactSpace_fixingOpenSubgroup :
    CompactSpace (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)) :=
  compactSpace_openSubgroup _

omit [Finite S] [IsGalois K L] [(GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal] [IsSmoothRep M] [Finite M] in
include hMP in
theorem res_apply_eq_of_trivial (g : (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S))) (m : M) : M.ρ g m = m := by
  rw [hMP g g.2]
  rfl

omit [Finite S] [Fact ℓ.Prime] in
include hcop in
theorem coprime_card_gal : Nat.Coprime (Nat.card (L ≃ₐ[K] L)) ℓ := by
  rw [card_gal_eq_index hL]
  exact hcop

/-- The module `Hom(μ_ℓ, M)` over `ULift (ZMod ℓ)` is finite-dimensional. -/
instance moduleFinite_homRep_roots :
    Module.Finite (ULift.{u} (ZMod ℓ))
      (homRep (zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
        (nsmul_galRootsOfUnity_eq_zero ℓ)) (zmodRepOfTorsion ℓ M hMℓ)) := by
  have : Finite (zmodRepOfTorsion ℓ M hMℓ) := inferInstanceAs (Finite M)
  have : Finite (zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
      (nsmul_galRootsOfUnity_eq_zero ℓ)) :=
    inferInstanceAs (Finite (Additive (rootsOfUnity ℓ (maximalUnramifiedOutside K Ω S))))
  have : Module.Finite (ULift.{u} (ZMod ℓ)) (zmodRepOfTorsion ℓ M hMℓ) := Module.Finite.of_finite
  have : Module.Finite (ULift.{u} (ZMod ℓ))
      (zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
        (nsmul_galRootsOfUnity_eq_zero ℓ)) := Module.Finite.of_finite
  exact inferInstanceAs (Module.Finite (ULift.{u} (ZMod ℓ))
    (zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
      (nsmul_galRootsOfUnity_eq_zero ℓ) →ₗ[ULift.{u} (ZMod ℓ)] zmodRepOfTorsion ℓ M hMℓ))

/-- The additive function `X ↦ dim (X ⊗ Hom(μ_ℓ, M))^{Gal(L/K)}` of the base case. -/
def baseTwistFun : AdditiveFunction.{u} ℓ (L ≃ₐ[K] L) :=
  twistFun (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL) (quotientGalEquiv hL) ℓ
    (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ) M (nsmul_galRootsOfUnity_eq_zero ℓ) hMℓ
    (rootsOfUnity_res_trivial hL hζ) (res_apply_eq_of_trivial hL M hMP) (coprime_card_gal hL hcop)

omit [Finite S] [IsGalois K L] [(GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal] in
include hcop in
/-- The index of `P` is invertible in `𝔽_ℓ`. -/
theorem index_ne_zero_zmod :
    (((GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).index : ℕ) : ULift.{u} (ZMod ℓ)) ≠ 0 := by
  intro h0
  have h0' : (((GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).index : ℕ) : ZMod ℓ) = 0 := congrArg ULift.down h0
  rw [ZMod.natCast_eq_zero_iff] at h0'
  exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : ℓ.Prime)).1 hcop.symm h0'

omit [Finite S] in
include hS in
/-- The Kummer sequence `0 → μ_ℓ → 𝒪_Sˣ → 𝒪_Sˣ → 0` of `G_S`. -/
theorem baseKummer_shortExact :
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
    (sUnitsKummerSequence S (maximalUnramifiedOutside K Ω S) ℓ).ShortExact :=
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  sUnitsKummerSequence_shortExact (Ω := Ω) S ℓ (PoitouTate.Internal.natCast_notMem_of_notMem ℓ hS)

omit [IsGalois K L] [(GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal] in
/-- `A₀` is finitely generated: it is the group of `S`-units of `L`. -/
theorem moduleFinite_cohomology_zero_res_maximalSUnits :
    Module.Finite ℤ (cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 0) := by
  classical
  have hfin := finite_finitePlacesAbove (L := L) (Set.toFinite S)
  let T : Finset (HeightOneSpectrum (𝓞 L)) := hfin.toFinset
  have hsub : Langlands.Global.Arithmetic.SUnitIndex.sUnits L T = sUnitsOf S L := by
    ext x
    rw [mem_sUnitsOf_iff_mem_unit]
    change x ∈ ((T : Set (HeightOneSpectrum (𝓞 L)))).unit L ↔ _
    rw [show ((T : Set (HeightOneSpectrum (𝓞 L)))) = finitePlacesAbove L S from
        Set.Finite.coe_toFinset hfin]
  have e : Additive (Langlands.Global.Arithmetic.SUnitIndex.sUnits L T) ≃+
      cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 0 :=
    (MulEquiv.subgroupCongr hsub).toAdditive.trans (sUnitsOfEquivCohomologyZero hL)
  exact Module.Finite.equiv e.toIntLinearEquiv

include hS in
/-- **Degree zero.** `dim H⁰(G_S, M) = d(A₀[ℓ])`. -/
theorem baseCase_finrank_zero :
    haveI := moduleFinite_cohomology_zero_res_maximalSUnits hL
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    haveI := finite_torsN_of_moduleFinite (A := cohomology (Rep.res
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 0) ℓ
    (Module.finrank (ULift.{u} (ZMod ℓ)) (cohomology (zmodRepOfTorsion ℓ M hMℓ) 0) : ℤ) =
      (letI := conjAction (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (quotientGalEquiv hL)
          (maximalSUnitsModule K Ω S) 0;
        (baseTwistFun hL hcop hζ M hMℓ hMP).toFun
          (TorsN (cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
            Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 0) ℓ)
          (torsNRep (L ≃ₐ[K] L) _ ℓ)) := by
  have := moduleFinite_cohomology_zero_res_maximalSUnits hL
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have := finite_cohomology_res_rootsOfUnityModule (Ω := Ω) S (Fact.out : ℓ.Prime) hS
    (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL) 0 (by norm_num)
  let P := (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S))
  let T := rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ
  have htw := finrank_cohomology_eq_twistFun (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
    (quotientGalEquiv hL) ℓ T M (nsmul_galRootsOfUnity_eq_zero ℓ) hMℓ (rootsOfUnity_res_trivial hL hζ)
    (res_apply_eq_of_trivial hL M hMP) (finrank_zmodRepOfTorsion_rootsOfUnity hS)
    (index_ne_zero_zmod hL hcop) (coprime_card_gal hL hcop) 0
  rw [htw]
  let := conjAction P (quotientGalEquiv hL) T 0
  have := finite_torsN_of_moduleFinite (A := cohomology (Rep.res P.subtype
    (maximalSUnitsModule K Ω S)) 0) ℓ
  have : Finite (TorsN (cohomology (Rep.res P.subtype T) 0) ℓ) :=
    Finite.of_injective _ Subtype.val_injective
  have hK := baseKummer_shortExact (Ω := Ω) (ℓ := ℓ) hS
  exact toFun_eq_torsN_zero (T := T) (O := maximalSUnitsModule K Ω S)
    (f := rootsOfUnityToSUnits (F := K) S (maximalUnramifiedOutside K Ω S) ℓ) P (quotientGalEquiv hL) hK _ _
    (torsNEquivOfNsmul ℓ (nsmul_cohomology_eq_zero (Rep.res P.subtype T)
      (fun a => nsmul_galRootsOfUnity_eq_zero (K := K) (Ksep := maximalUnramifiedOutside K Ω S) ℓ a) 0))
    (fun g x => by
      change (cohomologyConjRep T P 0 ((quotientGalEquiv hL).symm
        (quotientGalEquiv hL (QuotientGroup.mk g))) x.1) = _
      rw [MulEquiv.symm_apply_apply, cohomologyConjRep_mk]
      rfl)

include hS in
/-- **Degree one.** `dim H¹(G_S, M) = d(A₀/ℓ) + d(A₁[ℓ])`. -/
theorem baseCase_finrank_one :
    haveI := moduleFinite_cohomology_zero_res_maximalSUnits hL
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    haveI := finite_modN_of_moduleFinite (A := cohomology (Rep.res
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 0) ℓ
    haveI := finite_cohomology_one_res_maximalSUnits hL
    (Module.finrank (ULift.{u} (ZMod ℓ)) (cohomology (zmodRepOfTorsion ℓ M hMℓ) 1) : ℤ) =
      (letI := conjAction (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (quotientGalEquiv hL)
          (maximalSUnitsModule K Ω S) 0;
        (baseTwistFun hL hcop hζ M hMℓ hMP).toFun
          (ModN (cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
            Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 0) ℓ)
          (modNRep (L ≃ₐ[K] L) _ ℓ)) +
      (letI := conjAction (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (quotientGalEquiv hL)
          (maximalSUnitsModule K Ω S) 1;
        (baseTwistFun hL hcop hζ M hMℓ hMP).toFun
          (TorsN (cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
            Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 1) ℓ)
          (torsNRep (L ≃ₐ[K] L) _ ℓ)) := by
  have := moduleFinite_cohomology_zero_res_maximalSUnits hL
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have := finite_cohomology_one_res_maximalSUnits hL
  have := finite_cohomology_res_rootsOfUnityModule (Ω := Ω) S (Fact.out : ℓ.Prime) hS
    (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL) 1 (by norm_num)
  let P := (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S))
  let T := rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ
  have := finite_modN_of_moduleFinite (A := cohomology (Rep.res P.subtype
    (maximalSUnitsModule K Ω S)) 0) ℓ
  have htw := finrank_cohomology_eq_twistFun (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
    (quotientGalEquiv hL) ℓ T M (nsmul_galRootsOfUnity_eq_zero ℓ) hMℓ (rootsOfUnity_res_trivial hL hζ)
    (res_apply_eq_of_trivial hL M hMP) (finrank_zmodRepOfTorsion_rootsOfUnity hS)
    (index_ne_zero_zmod hL hcop) (coprime_card_gal hL hcop) 1
  rw [htw]
  let := conjAction P (quotientGalEquiv hL) T 1
  have : Finite (TorsN (cohomology (Rep.res P.subtype T) 1) ℓ) :=
    Finite.of_injective _ Subtype.val_injective
  have hK := baseKummer_shortExact (Ω := Ω) (ℓ := ℓ) hS
  exact toFun_eq_modN_add_torsN (T := T) (O := maximalSUnitsModule K Ω S)
    (f := rootsOfUnityToSUnits (F := K) S (maximalUnramifiedOutside K Ω S) ℓ) P (quotientGalEquiv hL) hK
    _ 0 _
    (torsNEquivOfNsmul ℓ (nsmul_cohomology_eq_zero (Rep.res P.subtype T)
      (fun a => nsmul_galRootsOfUnity_eq_zero (K := K) (Ksep := maximalUnramifiedOutside K Ω S) ℓ a) 1))
    (fun g x => by
      change (cohomologyConjRep T P 1 ((quotientGalEquiv hL).symm
        (quotientGalEquiv hL (QuotientGroup.mk g))) x.1) = _
      rw [MulEquiv.symm_apply_apply, cohomologyConjRep_mk]
      rfl)

omit [Finite M] [IsSmoothRep M] in
/-- **The `S`-units.** `d(A₀/ℓ) - d(A₀[ℓ]) = d(𝔽_ℓ[S_L]) + d(𝔽_ℓ[∞_L]) - d(𝔽_ℓ)` for every additive
function `d`. -/
theorem baseCase_units (d : AdditiveFunction.{u} ℓ (L ≃ₐ[K] L)) :
    haveI := moduleFinite_cohomology_zero_res_maximalSUnits hL
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    haveI := finite_modN_of_moduleFinite (A := cohomology (Rep.res
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 0) ℓ
    haveI := finite_torsN_of_moduleFinite (A := cohomology (Rep.res
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 0) ℓ
    haveI : Finite (finitePlacesAbove L S) :=
      (finite_finitePlacesAbove (L := L) (Set.toFinite S)).to_subtype
    (letI := conjAction (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (quotientGalEquiv hL)
          (maximalSUnitsModule K Ω S) 0;
        d.toFun
          (ModN (cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
            Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 0) ℓ)
          (modNRep (L ≃ₐ[K] L) _ ℓ) -
        d.toFun
          (TorsN (cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
            Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 0) ℓ)
          (torsNRep (L ≃ₐ[K] L) _ ℓ)) =
      d.toFun (finitePlacesAbove L S → ZMod ℓ)
          (funPermRep (ZMod ℓ) (L ≃ₐ[K] L) (finitePlacesAbove L S)) +
        d.toFun (InfinitePlace L → ZMod ℓ) (funPermRep (ZMod ℓ) (L ≃ₐ[K] L) (InfinitePlace L)) -
          d.one := by
  have := moduleFinite_cohomology_zero_res_maximalSUnits hL
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  let P := (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S))
  let := conjAction P (quotientGalEquiv hL) (maximalSUnitsModule K Ω S) 0
  have := finite_modN_of_moduleFinite (A := cohomology (Rep.res P.subtype
    (maximalSUnitsModule K Ω S)) 0) ℓ
  have := finite_torsN_of_moduleFinite (A := cohomology (Rep.res P.subtype
    (maximalSUnitsModule K Ω S)) 0) ℓ
  rw [← d.g_eq]
  let := sUnitsOfAction (K := K) (L := L) S
  have : Module.Finite ℤ (cohomology (Rep.res P.subtype (maximalSUnitsModule K Ω S)) 0) :=
    moduleFinite_cohomology_zero_res_maximalSUnits hL
  have hg := d.g_congr (sUnitsOfEquivCohomologyZero hL).symm (fun γ x => by
    obtain ⟨σ, rfl⟩ := galRestrict_surjective hL γ
    apply (sUnitsOfEquivCohomologyZero hL).injective
    rw [AddEquiv.apply_symm_apply, sUnitsOfEquivCohomologyZero_smul, AddEquiv.apply_symm_apply,
      ← quotientGalEquiv_mk, conjAction_smul])
  rw [hg]
  exact g_sUnitsOf S d

omit [IsSmoothRep M] [Finite M] [IsGalois K L] [Finite S] [Fact ℓ.Prime] in
/-- **The `S`-class group.** `A₁` is finite, so `d(A₁/ℓ) = d(A₁[ℓ])`. -/
theorem baseCase_picard [IsGalois K L] (d : AdditiveFunction.{u} ℓ (L ≃ₐ[K] L)) :
    haveI := finite_cohomology_one_res_maximalSUnits hL
    (letI := conjAction (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (quotientGalEquiv hL)
          (maximalSUnitsModule K Ω S) 1;
        d.toFun
          (ModN (cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
            Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 1) ℓ)
          (modNRep (L ≃ₐ[K] L) _ ℓ)) =
      (letI := conjAction (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (quotientGalEquiv hL)
          (maximalSUnitsModule K Ω S) 1;
        d.toFun
          (TorsN (cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
            Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 1) ℓ)
          (torsNRep (L ≃ₐ[K] L) _ ℓ)) := by
  have := finite_cohomology_one_res_maximalSUnits hL
  let := conjAction (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (quotientGalEquiv hL) (maximalSUnitsModule K Ω S) 1
  have h := d.g_eq_zero_of_finite (cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 1)
  rw [d.g_eq] at h
  exact sub_eq_zero.1 h

end

end Langlands.GaloisCohomology
