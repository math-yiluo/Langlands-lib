/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
public import WeilConjectures.NumberTheory.Padics.IntegersModPow

/-!

# The condensed rings `(𝒪_E ⧸ ℓⁿ)̲` and the reductions `𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲`

Let `ℓ` be a prime and `E ⊆ ℚ̄_ℓ` a subfield with ring of integers `𝒪_E`. The discrete rings
`𝒪_E ⧸ ℓⁿ = PadicAlgCl.integersModPow ℓ E n` give condensed rings
```
(𝒪_E ⧸ ℓⁿ)̲(S) := C(S, 𝒪_E ⧸ ℓⁿ),
```
(`Profinite.integersModPowRingObj`), and the reduction `𝒪_E → 𝒪_E ⧸ ℓⁿ`, which is continuous
(`PadicAlgCl.continuous_integersModPowMk`), induces by postcomposition a morphism of condensed
rings `𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲` (`Profinite.padicIntegersRingObjToIntegersModPow`).

For `E` finite over `ℚ_ℓ`, the ring `𝒪_E ⧸ ℓⁿ` is finite (`PadicAlgCl.finite_integersModPow`):
it is the image of the compact space `𝒪_E` under a continuous map to a discrete space.

The sequence `0 ⟶ 𝒪̲_E --ℓⁿ--> 𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲ ⟶ 0` of condensed abelian groups is short exact
(`Profinite.shortExact_padicIntegersRingObjToIntegersModPow`); this is checked on sections.

## Main definitions

* `Profinite.integersModPowRingObj`: the condensed ring `(𝒪_E ⧸ ℓⁿ)̲`, as a commutative ring
  object of condensed abelian groups.
* `Profinite.padicIntegersRingObjToIntegersModPow`: the reduction `𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲`, a
  morphism of ring objects.

-/

@[expose] public section

universe u

open CategoryTheory MonObj

namespace PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- `ℓⁿ = 0` in `𝒪_E ⧸ ℓⁿ`. -/
lemma natCast_pow_eq_zero_integersModPow (n : ℕ) : (ℓ : integersModPow ℓ E n) ^ n = 0 := by
  rw [← map_natCast (integersModPowMk ℓ E n), ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)

/-- For `E` finite over `ℚ_ℓ`, the ring `𝒪_E ⧸ ℓⁿ` is finite: it is the image of the compact
space `𝒪_E` under the continuous reduction map to a discrete space. -/
instance finite_integersModPow [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] (n : ℕ) : Finite (integersModPow ℓ E n) := by
  let := normedFieldOfAlgebra ℓ E
  have := compactSpace_integers ℓ E
  rw [← Set.finite_univ_iff, ← (integersModPowMk_surjective ℓ E n).range_eq]
  exact (isCompact_range (continuous_integersModPowMk ℓ E n)).finite_of_discrete

end PadicAlgCl

namespace Profinite

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] (n : ℕ)

/-- The condensed ring `(𝒪_E ⧸ ℓⁿ)̲`, with sections `C(S, 𝒪_E ⧸ ℓⁿ)` for the discrete topology,
as a ring object of condensed abelian groups. -/
noncomputable abbrev integersModPowRingObj : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  continuousMapRingObj (PadicAlgCl.integersModPow ℓ E n)

/-- The condensed ring `(𝒪_E ⧸ ℓⁿ)̲` is a commutative ring object of condensed abelian groups. -/
instance isCommMonObj_integersModPowRingObj : IsCommMonObj (integersModPowRingObj.{u} ℓ E n) :=
  isCommMonObj_continuousMapRingObj (PadicAlgCl.integersModPow ℓ E n)

/-- The reduction `𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲`, a morphism of condensed rings: postcomposition with the
continuous reduction map `𝒪_E → 𝒪_E ⧸ ℓⁿ`. -/
noncomputable def padicIntegersCondensedRingToIntegersModPow :
    padicIntegersCondensedRing.{u} ℓ E ⟶
      continuousMapRingSheaf (PadicAlgCl.integersModPow ℓ E n) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheafMap (PadicAlgCl.integersModPowMk ℓ E n)
    (PadicAlgCl.continuous_integersModPowMk ℓ E n)

/-- The reduction `𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲` of ring objects of condensed abelian groups: the abelian
sheaf morphism underlying `Profinite.padicIntegersCondensedRingToIntegersModPow`. -/
noncomputable def padicIntegersRingObjToIntegersModPow :
    padicIntegersRingObj.{u} ℓ E ⟶ integersModPowRingObj ℓ E n :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (padicIntegersCondensedRingToIntegersModPow ℓ E n)

instance : IsMonHom (padicIntegersRingObjToIntegersModPow.{u} ℓ E n) :=
  inferInstanceAs (IsMonHom
    ((sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (padicIntegersCondensedRingToIntegersModPow.{u} ℓ E n)))

/-- On sections over a profinite set `S`, the reduction `𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲` is
postcomposition with the reduction map. -/
lemma padicIntegersRingObjToIntegersModPow_hom_app_apply (S : Profinite.{u}ᵒᵖ) :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    ∀ a : ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E),
      (padicIntegersRingObjToIntegersModPow ℓ E n).hom.app S a =
        ULift.up ((⟨PadicAlgCl.integersModPowMk ℓ E n,
          PadicAlgCl.continuous_integersModPowMk ℓ E n⟩ :
            C(PadicAlgCl.integers ℓ E, PadicAlgCl.integersModPow ℓ E n)).comp a.down) :=
  fun _ ↦ rfl

/-- On sections over a profinite set `S`, the multiplication by an integer `k` on `𝒪̲_E` is the
multiplication by `k` on continuous maps. -/
lemma zsmul_id_padicIntegersRingObj_hom_app_apply (k : ℤ) (S : Profinite.{u}ᵒᵖ) :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    ∀ a : ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E),
      (k • 𝟙 (padicIntegersRingObj.{u} ℓ E)).hom.app S a = ULift.up (k • a.down) := by
  intro a
  have h : (k • 𝟙 (padicIntegersRingObj.{u} ℓ E)).hom.app S = k • 𝟙 _ :=
    ((sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙
      (evaluation _ _).obj S).map_zsmul (f := 𝟙 _) (r := k)).trans (by simp)
  rw [h]
  rfl

/-- `ℓⁿ` vanishes in `(𝒪_E ⧸ ℓⁿ)̲`: the multiplication by `ℓⁿ` on `𝒪̲_E` followed by the reduction
is zero. -/
lemma zsmul_id_comp_padicIntegersRingObjToIntegersModPow :
    ((ℓ : ℤ) ^ n • 𝟙 (padicIntegersRingObj.{u} ℓ E)) ≫
      padicIntegersRingObjToIntegersModPow ℓ E n = 0 := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ext S a
  refine ULift.ext (ContinuousMap.ext fun s ↦ ?_)
  have h1 := zsmul_id_padicIntegersRingObj_hom_app_apply ℓ E ((ℓ : ℤ) ^ n) S a
  have h2 := padicIntegersRingObjToIntegersModPow_hom_app_apply ℓ E n S
  have h3 : (((ℓ : ℤ) ^ n • 𝟙 (padicIntegersRingObj.{u} ℓ E)) ≫
      padicIntegersRingObjToIntegersModPow ℓ E n).hom.app S a =
      (padicIntegersRingObjToIntegersModPow ℓ E n).hom.app S
        (((ℓ : ℤ) ^ n • 𝟙 (padicIntegersRingObj.{u} ℓ E)).hom.app S a) := rfl
  rw [h3, h1, h2]
  simp [zsmul_eq_mul, PadicAlgCl.natCast_pow_eq_zero_integersModPow]

/-- **`0 ⟶ 𝒪̲_E --ℓⁿ--> 𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲ ⟶ 0` is short exact**, checked on sections over each
profinite set `S`: multiplication by `ℓⁿ` is injective on `C(S, 𝒪_E)`, a continuous map
`S → 𝒪_E` with values in `ℓⁿ 𝒪_E` is `ℓⁿ` times a continuous map (multiplication by `ℓⁿ` is an
embedding), and a continuous map `S → 𝒪_E ⧸ ℓⁿ` lifts along any section of the reduction, the
target being discrete. -/
lemma shortExact_padicIntegersRingObjToIntegersModPow :
    (ShortComplex.mk _ _ (zsmul_id_comp_padicIntegersRingObjToIntegersModPow.{u} ℓ E n)
      ).ShortExact := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let T := ShortComplex.mk _ _ (zsmul_id_comp_padicIntegersRingObjToIntegersModPow.{u} ℓ E n)
  have hl : ((ℓ : PadicAlgCl.integers ℓ E) ^ n) ≠ 0 := by
    refine pow_ne_zero n fun h ↦ PadicAlgCl.natCast_ne_zero_of_algebra (l := ℓ) (E := E) ?_
    simpa using congrArg Subtype.val h
  have hf (S : Profinite.{u}ᵒᵖ) (a : ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E)) :
      (T.f.hom.app S a).down = (ℓ : PadicAlgCl.integers ℓ E) ^ n • a.down := by
    refine (congrArg ULift.down (zsmul_id_padicIntegersRingObj_hom_app_apply ℓ E _ S a)).trans ?_
    ext s
    simp [zsmul_eq_mul]
  have hg (S : Profinite.{u}ᵒᵖ) (a : ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E)) (s) :
      (T.g.hom.app S a).down s = PadicAlgCl.integersModPowMk ℓ E n (a.down s) := rfl
  have hpre : (T.map (sheafToPresheaf _ _)).Exact := by
    rw [ShortComplex.exact_iff_isZero_homology]
    refine Functor.isZero _ fun S ↦ ?_
    have h : ((T.map (sheafToPresheaf _ _)).map ((evaluation _ _).obj S)).Exact := by
      rw [ShortComplex.ab_exact_iff]
      intro a ha
      have hz (s : S.unop) : PadicAlgCl.integersModPowMk ℓ E n (a.down s) = 0 :=
        (hg S a s).symm.trans (congrArg (fun z : ULift.{u + 1} C(S.unop,
          PadicAlgCl.integersModPow ℓ E n) ↦ z.down s) ha)
      choose b hb using fun s ↦ PadicAlgCl.exists_natCast_pow_mul_eq ℓ E n (a.down s) (hz s)
      have hbc : Continuous b := by
        refine (PadicAlgCl.isEmbedding_natCast_pow_mul ℓ E n).continuous_iff.2 ?_
        simpa only [Function.comp_def, hb] using a.down.continuous
      exact ⟨ULift.up ⟨b, hbc⟩, ULift.ext ((hf S _).trans (ContinuousMap.ext fun s ↦ by
        simpa using hb s))⟩
    rw [ShortComplex.exact_iff_isZero_homology] at h
    exact h.of_iso ((T.map (sheafToPresheaf _ _)).mapHomologyIso ((evaluation _ _).obj S)).symm
  have hmono (S : Profinite.{u}ᵒᵖ) : Mono (((sheafToPresheaf _ _).map T.f).app S) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b hab
    have h := (hf S a).symm.trans ((congrArg ULift.down hab).trans (hf S b))
    exact ULift.ext (ContinuousMap.ext fun s ↦ mul_left_cancel₀ hl (by
      simpa using congrArg (fun z : C(S.unop, PadicAlgCl.integers ℓ E) ↦ z s) h))
  have hepi (S : Profinite.{u}ᵒᵖ) : Epi (((sheafToPresheaf _ _).map T.g).app S) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro c
    refine ⟨ULift.up ⟨Function.surjInv (PadicAlgCl.integersModPowMk_surjective ℓ E n) ∘ c.down,
      continuous_of_discreteTopology.comp c.down.continuous⟩,
      ULift.ext (ContinuousMap.ext fun s ↦ ?_)⟩
    exact (hg S _ s).trans (Function.surjInv_eq _ _)
  have : Mono T.f := (sheafToPresheaf _ _).mono_of_mono_map (NatTrans.mono_of_mono_app _)
  have : Epi T.g := (sheafToPresheaf _ _).epi_of_epi_map (NatTrans.epi_of_epi_app _)
  refine ⟨?_⟩
  exact (ShortComplex.exact_iff_of_iso
    (T.mapNatIso (asIso (sheafificationAdjunction _ _).counit))).1
    (hpre.map (presheafToSheaf _ _))

end Profinite
