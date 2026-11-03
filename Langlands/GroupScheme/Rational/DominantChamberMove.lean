import Langlands.GroupScheme.Rational.RelativeReflectionProperties
import Langlands.GroupScheme.Rational.StandardLeviRootTransport
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsStatement

/-! # Moving a cocharacter into the closed dominant chamber by a normalizing point -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

section Chamber

variable (i : T.toGrp ⟶ G)

section Normalizing

variable [Mono i.hom.hom.left]

/-- The torus automorphism of a product of normalizing points is the composite of
the automorphisms of the factors, the right factor acting first. -/
theorem normalizingAut_mul (n m : normalizerPoints i) :
    normalizingAut i (n * m) = normalizingAut i m ≪≫ normalizingAut i n :=
  (isNormalizingPoint_normalizingAut i (n * m)).unique i
    ((isNormalizingPoint_normalizingAut i n).mul (isNormalizingPoint_normalizingAut i m))

/-- The cocharacter action of a product of normalizing points is the composite action. -/
theorem cocharacterAut_normalizingAut_mul (n m : normalizerPoints i)
    (ξ : cocharacterLattice T) :
    cocharacterAut (normalizingAut i (n * m)) ξ =
      cocharacterAut (normalizingAut i n) (cocharacterAut (normalizingAut i m) ξ) := by
  simp only [normalizingAut_mul, cocharacterAut_apply, Iso.trans_hom, Category.assoc]

/-- The cocharacter action of a normalizing point is contragredient to its Weyl action
on characters, for the actual integral lattice pairing. -/
theorem latticePairing_cocharacterAut_normalizingAut (n : normalizerPoints i)
    (χ : characterLattice T) (ζ : cocharacterLattice T) :
    latticePairing T χ (cocharacterAut (normalizingAut i n) ζ) =
      latticePairing T (weylAction i n⁻¹ χ) ζ := by
  have hχ : characterAut (normalizingAut i n) (weylAction i n⁻¹ χ) = χ := by
    change weylAction i n (weylAction i n⁻¹ χ) = χ
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [← latticePairing_characterAut_cocharacterAut (normalizingAut i n)
    (weylAction i n⁻¹ χ) ζ, hχ]

end Normalizing

variable [IsAffineHom G.X.hom]

/-- The sum of the positive relative roots of `ν` (the classical `2ρ`), as a finitary
sum over the actual set `positiveRelativeRoots i ν`. -/
def positiveRootSum (ν : cocharacterLattice T) : characterLattice T :=
  ∑ᶠ α ∈ positiveRelativeRoots i ν, α

theorem positiveRootSum_eq_sum {ν : cocharacterLattice T}
    (hfin : (positiveRelativeRoots i ν).Finite) :
    positiveRootSum i ν = ∑ α ∈ hfin.toFinset, α :=
  finsum_mem_eq_finite_toFinset_sum _ hfin

open RelativeRootSystem

/-- Evaluation of a cocharacter on the rationalization of a character in the root span. -/
theorem corootFunctional_mk (ζ : cocharacterLattice T) (χ : characterLattice T)
    (hχ : toRat χ ∈ relativeRootSpan i) :
    corootFunctional i ζ ⟨toRat χ, hχ⟩ = (latticePairing T χ ζ : ℚ) := by
  simp [corootFunctional, toRat, zsmul_eq_mul]

variable [Mono i.hom.hom.left]

/-- The pairing formula for a normalizing point acting by a reflection in `α` on the
rational root span: `⟨s χ, ζ⟩ = ⟨χ, ζ⟩ - c(χ) ⟨α, ζ⟩`. -/
theorem latticePairing_weylAction_of_reflection {α : characterLattice T}
    (hα : α ∈ relativeRoots i) {c : Module.Dual ℚ (relativeRootSpan i)}
    (hc : c ⟨toRat α, toRat_mem_ratSpan hα⟩ = 2) {m : normalizerPoints i}
    (hw : relativeWeylAction i (QuotientGroup.mk m) = Module.reflection hc)
    {χ : characterLattice T} (hχ : toRat χ ∈ relativeRootSpan i) (ζ : cocharacterLattice T) :
    (latticePairing T (weylAction i m χ) ζ : ℚ) =
      latticePairing T χ ζ - c ⟨toRat χ, hχ⟩ * latticePairing T α ζ := by
  have hmem : toRat (weylAction i m χ) ∈ relativeRootSpan i := by
    have h := (relativeWeylAction i (QuotientGroup.mk m) ⟨toRat χ, hχ⟩).2
    rwa [coe_relativeWeylAction_mk_apply, ratAut_toRat] at h
  have hvec : relativeWeylAction i (QuotientGroup.mk m) ⟨toRat χ, hχ⟩ =
      ⟨toRat (weylAction i m χ), hmem⟩ := by
    apply Subtype.ext
    rw [coe_relativeWeylAction_mk_apply, ratAut_toRat]
  have hαval : corootFunctional i ζ ⟨toRat α, toRat_mem_ratSpan hα⟩ =
      (latticePairing T α ζ : ℚ) :=
    corootFunctional_rootVector i ζ ⟨α, hα⟩
  have key := congrArg (corootFunctional i ζ) hvec
  rw [hw, Module.reflection_apply, map_sub, map_smul, corootFunctional_mk, corootFunctional_mk,
    hαval, smul_eq_mul] at key
  exact key.symm

/-- **Moving a cocharacter into the closed dominant chamber.** If the actual relative
roots form the published root system, every cocharacter of the split torus is moved by a
normalizing rational point to one pairing nonnegatively with every positive relative root
of `ν`. No genericity of `ν` is needed. The point maximizes the pairing with the sum of
the positive roots; a reflection in a positive root pairing negatively would increase it. -/
theorem HasRelativeRootSystem.exists_normalizerPoint_dominant
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (ν ξ : cocharacterLattice T) :
    ∃ n : normalizerPoints i, ∀ α ∈ positiveRelativeRoots i ν,
      0 ≤ latticePairing T α (cocharacterAut (normalizingAut i n) ξ) := by
  classical
  have hΦ := hroot.finite_relativeRoots i hT
  have hfin := hroot.finite_positiveRelativeRoots i hT ν
  have := hΦ.to_subtype
  set A := hfin.toFinset with hA
  have hmemA : ∀ {β : characterLattice T}, β ∈ A ↔ β ∈ positiveRelativeRoots i ν :=
    fun {_} => hfin.mem_toFinset
  set ρ : characterLattice T := positiveRootSum i ν with hρdef
  have hρ : ρ = ∑ β ∈ A, β := positiveRootSum_eq_sum i hfin
  have hpair_sum : ∀ (f : characterLattice T ≃ₗ[ℤ] characterLattice T)
      (ζ : cocharacterLattice T),
      latticePairing T (f ρ) ζ = ∑ β ∈ A, latticePairing T (f β) ζ := by
    intro f ζ
    rw [hρ, map_sum, map_sum, LinearMap.sum_apply]
  set F : normalizerPoints i → ℤ :=
    fun n => latticePairing T ρ (cocharacterAut (normalizingAut i n) ξ) with hFdef
  -- the values of `F` are sums of pairings of `ξ` with actual relative roots
  have hrange : (Set.range F).Finite := by
    let H : (A → relativeRoots i) → ℤ :=
      fun g => ∑ β ∈ A.attach, latticePairing T (g β : characterLattice T) ξ
    refine (Set.finite_range H).subset ?_
    rintro _ ⟨n, rfl⟩
    refine ⟨fun β => ⟨weylAction i n⁻¹ β,
      weylAction_mapsTo_relativeRoots i n⁻¹ (hmemA.mp β.2).1⟩, ?_⟩
    simp only [H, hFdef, latticePairing_cocharacterAut_normalizingAut]
    rw [Finset.sum_attach A (fun β => latticePairing T (weylAction i n⁻¹ β) ξ)]
    have := hpair_sum (weylAction i n⁻¹) ξ
    exact this.symm
  obtain ⟨_, ⟨n₀, rfl⟩, hmax⟩ :=
    Set.exists_max_image (Set.range F) id hrange (Set.range_nonempty F)
  refine ⟨n₀, fun α hα => ?_⟩
  set η := cocharacterAut (normalizingAut i n₀) ξ with hη
  by_contra hneg
  replace hneg := lt_of_not_ge hneg
  obtain ⟨w, hαr, c, hc, hw⟩ := hroot.exists_isRelativeReflection hα.1
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective w
  have hρmem : toRat ρ ∈ relativeRootSpan i := by
    rw [hρ, map_sum]
    exact Submodule.sum_mem _ fun β hβ => toRat_mem_ratSpan (hmemA.mp hβ).1
  have hαν : 0 < latticePairing T α ν := hα.2
  -- the reflection negates `α`
  have hmα : latticePairing T (weylAction i m α) ν = -latticePairing T α ν := by
    have h := latticePairing_weylAction_of_reflection i hαr hc hw (toRat_mem_ratSpan hαr) ν
    rw [hc] at h
    exact_mod_cast (by linarith : (latticePairing T (weylAction i m α) ν : ℚ) =
      -(latticePairing T α ν : ℚ))
  -- comparison of the sums over the positive roots and over their images
  have hlt : ∑ β ∈ A, latticePairing T (weylAction i m β) ν <
      ∑ β ∈ A, latticePairing T β ν := by
    have himage : ∑ β ∈ A, latticePairing T (weylAction i m β) ν =
        ∑ γ ∈ A.image (weylAction i m), latticePairing T γ ν :=
      (Finset.sum_image (f := fun γ => latticePairing T γ ν)
        fun x _ y _ h => (weylAction i m).injective h).symm
    rw [himage, ← Finset.sum_filter_add_sum_filter_not (A.image (weylAction i m)) (· ∈ A)]
    have hle : ∑ γ ∈ (A.image (weylAction i m)).filter (· ∈ A), latticePairing T γ ν ≤
        ∑ β ∈ A, latticePairing T β ν :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun γ hγ => (Finset.mem_filter.mp hγ).2)
        fun γ hγ _ => (hmemA.mp hγ).2.le
    have hneg' : ∑ γ ∈ (A.image (weylAction i m)).filter (· ∉ A), latticePairing T γ ν < 0 := by
      have h0 : ∑ γ ∈ (A.image (weylAction i m)).filter (· ∉ A), latticePairing T γ ν <
          ∑ γ ∈ (A.image (weylAction i m)).filter (· ∉ A), (0 : ℤ) := by
        apply Finset.sum_lt_sum
        · intro γ hγ
          obtain ⟨hγB, hγA⟩ := Finset.mem_filter.mp hγ
          obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp hγB
          have hroot' : weylAction i m β ∈ relativeRoots i :=
            weylAction_mapsTo_relativeRoots i m (hmemA.mp hβ).1
          by_contra hpos
          exact hγA (hmemA.mpr ⟨hroot', lt_of_not_ge hpos⟩)
        · refine ⟨weylAction i m α, Finset.mem_filter.mpr
            ⟨Finset.mem_image_of_mem _ (hmemA.mpr hα), ?_⟩, ?_⟩
          · intro hgα
            have := (hmemA.mp hgα).2
            rw [hmα] at this
            linarith
          · rw [hmα]
            linarith
      simpa using h0
    linarith
  -- hence the reflection coefficient of `ρ` is positive
  have hcpos : 0 < c ⟨toRat ρ, hρmem⟩ := by
    have h := latticePairing_weylAction_of_reflection i hαr hc hw hρmem ν
    have hsum := hpair_sum (weylAction i m) ν
    have hsum1 := hpair_sum (LinearEquiv.refl ℤ _) ν
    simp only [LinearEquiv.refl_apply] at hsum1
    have hlt' : (latticePairing T (weylAction i m ρ) ν : ℚ) < latticePairing T ρ ν := by
      rw [hsum, hsum1]
      exact_mod_cast hlt
    have hανq : (0 : ℚ) < latticePairing T α ν := by exact_mod_cast hαν
    have hprod : 0 < c ⟨toRat ρ, hρmem⟩ * latticePairing T α ν := by linarith
    exact pos_of_mul_pos_left hprod hανq.le
  -- and the reflected point has a strictly larger value of `F`
  have hbig : F n₀ < F (m⁻¹ * n₀) := by
    have hval : F (m⁻¹ * n₀) = latticePairing T (weylAction i m ρ) η := by
      simp only [hFdef]
      rw [cocharacterAut_normalizingAut_mul, latticePairing_cocharacterAut_normalizingAut,
        inv_inv]
    have h := latticePairing_weylAction_of_reflection i hαr hc hw hρmem η
    have hηq : (latticePairing T α η : ℚ) < 0 := by exact_mod_cast hneg
    have hmul : 0 < c ⟨toRat ρ, hρmem⟩ * -(latticePairing T α η : ℚ) :=
      mul_pos hcpos (neg_pos.mpr hηq)
    have : (F n₀ : ℚ) < F (m⁻¹ * n₀) := by
      rw [hval, h]
      simp only [hFdef]
      linarith
    exact_mod_cast this
  exact absurd (hmax _ ⟨m⁻¹ * n₀, rfl⟩) (not_le.mpr hbig)

/-- With the parabolic direction of the root-sign criterion, a generic `ν` and the
chamber move, every cocharacter of the torus is conjugated by a normalizing rational point
to one whose dynamic parabolic contains that of `ν`, on every test scheme. -/
theorem HasRelativeRootSystem.exists_normalizerPoint_parabolic_le
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    (hsign : ∀ η : cocharacterLattice T,
      (∀ α ∈ relativeRoots i, 0 ≤ latticePairing T α ν → 0 ≤ latticePairing T α η) →
        Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
          Dynamic.parabolic (CommGroupScheme.groupHom η ≫ i))
    (ξ : cocharacterLattice T) :
    ∃ n : normalizerPoints i,
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
        Dynamic.parabolic ((CommGroupScheme.groupHom ξ ≫ i) ≫
          (G.innerIso (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)).hom) := by
  obtain ⟨n, hn⟩ := hroot.exists_normalizerPoint_dominant i hT ν ξ
  refine ⟨n, ?_⟩
  rw [← groupHom_cocharacterAut_comp]
  exact hsign _ fun α hα hαν => hn α ⟨hα, lt_of_le_of_ne hαν (Ne.symm (hν α hα))⟩

end Chamber

/-- Statement-level form: from the published relative root system and root-sign
statements, for a connected reductive `G`, a maximal split torus `i` and a generic `ν`,
every cocharacter of the torus is conjugated by a normalizing rational point to one whose
dynamic parabolic contains `P(ν)`. -/
theorem exists_normalizerPoint_parabolic_le_of_statements
    (hroot : RelativeRootSystemStatement.{u}) (hsign : RelativeRootSignInclusionsStatement.{u})
    (hG : IsConnectedReductive G) {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    {ν : cocharacterLattice T} :
    letI := hG.isAffineHom
    IsGenericCocharacter i ν → ∀ ξ : cocharacterLattice T,
      ∃ n : normalizerPoints i,
        Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
          Dynamic.parabolic ((CommGroupScheme.groupHom ξ ≫ i) ≫
            (G.innerIso (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)).hom) := by
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν ξ
  exact (hroot k G hG T i hi).exists_normalizerPoint_parabolic_le i hi.isSplitSubtorus.1 hν
    (fun η hη => ((hsign k G hG T i hi ν η).1).mpr hη) ξ

end Langlands.GroupScheme
