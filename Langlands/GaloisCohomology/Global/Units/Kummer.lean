import Langlands.GaloisCohomology.Global.Units.Picard

/-!
# The Kummer sequence of the `S`-units

For `n` invertible outside `S` and `Ω` separably closed, `0 → μ_n → 𝒪_Sˣ → 𝒪_Sˣ → 0`
(multiplication by `n`) is a short exact sequence of `G_S`-modules (`sUnitsKummerSequence_shortExact`),
because the `n`-th roots of `S`-units of `K_S` lie in `K_S`. Its cohomology gives the exact sequence
`0 → 𝒪_{F,S}ˣ / n → H¹(G_S, μ_n) → Pic(𝒪_S)[n] → 0`: the Kummer map `kummerSUnitsHom` has kernel the
`n`-th powers (`kummerSUnitsHom_eq_zero_iff`), its image is the kernel of `kummerPicHom`
(`kummerPicHom_eq_zero_iff`), and the image of `kummerPicHom` is the `n`-torsion of `Pic(𝒪_S)`
(`mem_range_kummerPicHom_iff`). Finally the `S`-units do not change when `F` is replaced by a finite
extension `L` and `S` by the places of `L` above it (`sUnitsOf_finitePlacesAbove_eq`).
-/

namespace Langlands.GaloisCohomology

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum CategoryTheory
open Langlands.Galois Langlands.ProfiniteCohomology

universe u

noncomputable section

section Sequence

variable {F : Type u} [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 F)))
variable (E : Type u) [Field E] [Algebra F E] (n : ℕ) [NeZero n]

/-- The Kummer sequence `0 → μ_n → 𝒪_{E,S}ˣ → 𝒪_{E,S}ˣ` (multiplication by `n`). -/
noncomputable def sUnitsKummerSequence : ShortComplex (Rep.{u} (ULift.{u} ℤ) Gal(E/F)) :=
  ShortComplex.mk (rootsOfUnityToSUnits S E n) (n • 𝟙 (sUnitsModule S E)) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    change ((((Additive.toMul (α := rootsOfUnity n E) x : rootsOfUnity n E) : Eˣ) ^ n : Eˣ) : E) = 1
    rw [(mem_rootsOfUnity n _).1 (Additive.toMul (α := rootsOfUnity n E) x).2, Units.val_one])

/-- The second map of the Kummer sequence is multiplication by `n`. -/
theorem sUnitsKummerSequence_g : (sUnitsKummerSequence S E n).g = n • 𝟙 (sUnitsModule S E) :=
  rfl

end Sequence

section ShortExact

variable {F : Type u} [Field F] [NumberField F] {Ω : Type u} [Field Ω] [Algebra F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F))) [IsGalois F Ω] [IsSepClosed Ω]

/-- For `n` invertible outside `S` and `Ω` separably closed, `0 → μ_n → 𝒪_Sˣ → 𝒪_Sˣ → 0` is exact over `G_S`. -/
theorem sUnitsKummerSequence_shortExact (n : ℕ) [NeZero n]
    (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    (sUnitsKummerSequence S (maximalUnramifiedOutside F Ω S) n).ShortExact where
  exact := by
    apply shortComplex_exact_of_forall_exists
    intro x hx
    let x' : Additive (maximalSUnits F Ω S) := x
    have hx2 : n • x' = 0 :=
      (nsmul_id_hom_apply (sUnitsModule S (maximalUnramifiedOutside F Ω S)) n x).symm.trans hx
    have hx' : (Additive.toMul x' : maximalSUnits F Ω S) ^ n = 1 := by
      rw [← toMul_nsmul, hx2]
      rfl
    have hmem : ((Additive.toMul x' : maximalSUnits F Ω S) : (maximalUnramifiedOutside F Ω S)ˣ) ∈
        rootsOfUnity n (maximalUnramifiedOutside F Ω S) := by
      rw [mem_rootsOfUnity, ← Subgroup.coe_pow, hx']
      rfl
    exact ⟨Additive.ofMul ⟨_, hmem⟩, rfl⟩
  mono_f := (Rep.mono_iff_injective _).2 fun a b h =>
    Additive.toMul.injective (Subtype.ext (congrArg
      (fun z : Additive (maximalSUnits F Ω S) => ((Additive.toMul z : maximalSUnits F Ω S) :
        (maximalUnramifiedOutside F Ω S)ˣ)) h))
  epi_g := (Rep.epi_iff_surjective _).2 fun y => by
    obtain ⟨β, hβ, hβn⟩ := exists_pow_eq_of_mem_maximalSUnits S (NeZero.ne n) hnS
      (Additive.toMul y : maximalSUnits F Ω S).2
    refine ⟨Additive.ofMul ⟨β, hβ⟩, ?_⟩
    refine (nsmul_id_hom_apply (sUnitsModule S (maximalUnramifiedOutside F Ω S)) n _).trans ?_
    apply Additive.toMul.injective
    apply Subtype.ext
    change β ^ n = _
    exact hβn

end ShortExact

section KummerPic

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
  [IsSepClosed Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F))) (n : ℕ) [NeZero n]
  (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 F) ∉ v.asIdeal)

/-- Smoothness of the terms of the Kummer sequence. -/
instance isSmoothRep_sUnitsKummerSequence_X₁ :
    IsSmoothRep (sUnitsKummerSequence S (maximalUnramifiedOutside F Ω S) n).X₁ :=
  inferInstanceAs (IsSmoothRep (rootsOfUnityModule F (maximalUnramifiedOutside F Ω S) n))

/-- Smoothness of the terms of the Kummer sequence. -/
instance isSmoothRep_sUnitsKummerSequence_X₂ :
    IsSmoothRep (sUnitsKummerSequence S (maximalUnramifiedOutside F Ω S) n).X₂ :=
  inferInstanceAs (IsSmoothRep (sUnitsModule S (maximalUnramifiedOutside F Ω S)))

/-- Smoothness of the terms of the Kummer sequence. -/
instance isSmoothRep_sUnitsKummerSequence_X₃ :
    IsSmoothRep (sUnitsKummerSequence S (maximalUnramifiedOutside F Ω S) n).X₃ :=
  inferInstanceAs (IsSmoothRep (sUnitsModule S (maximalUnramifiedOutside F Ω S)))

omit [IsGalois F Ω] [IsSepClosed Ω] [NeZero n] in
/-- Multiplication by `n` on invariants. -/
theorem invariantsFunctor_map_nsmul_apply
    (w : (sUnitsModule S (maximalUnramifiedOutside F Ω S)).ρ.invariants) :
    ((Rep.invariantsFunctor (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside F Ω S)).map
      (n • 𝟙 (sUnitsModule S (maximalUnramifiedOutside F Ω S)))).hom w = n • w := by
  apply Subtype.ext
  change (n • 𝟙 (sUnitsModule S (maximalUnramifiedOutside F Ω S))).hom w.1 = _
  rw [nsmul_id_hom_apply]
  rfl

include hnS

/-- The Kummer map `𝒪_{F,S}ˣ → H¹(G_S, μ_n)` (the connecting map of the Kummer sequence). -/
noncomputable def kummerSUnitsHom :
    Additive (S.unit F) →+ cohomology (rootsOfUnityModule F (maximalUnramifiedOutside F Ω S) n) 1 :=
  ((δ (sUnitsKummerSequence_shortExact (Ω := Ω) S n hnS) 0 1 rfl).hom.toAddMonoidHom.comp
    (zeroIso (sUnitsKummerSequence S (maximalUnramifiedOutside F Ω S) n).X₃).inv.hom.toAddMonoidHom).comp
    (sUnitsToInvariants S (maximalUnramifiedOutside F Ω S))

/-- The map `H¹(G_S, μ_n) → H¹(G_S, 𝒪_Sˣ) → Pic(𝒪_S)`. -/
noncomputable def kummerPicHom :
    cohomology (rootsOfUnityModule F (maximalUnramifiedOutside F Ω S) n) 1 →+ SPicardGroup S :=
  (cohomologyOneSUnitsToSPicard (Ω := Ω) S).comp
    (coeffMap (sUnitsKummerSequence S (maximalUnramifiedOutside F Ω S) n).f 1).hom.toAddMonoidHom

/-- The kernel of the Kummer map is `n`-th powers: `𝒪_{F,S}ˣ / n ↪ H¹(G_S, μ_n)`. -/
theorem kummerSUnitsHom_eq_zero_iff (a : Additive (S.unit F)) :
    kummerSUnitsHom (Ω := Ω) S n hnS a = 0 ↔ ∃ b, n • b = a := by
  refine (δ_zeroIso_inv_eq_zero_iff (sUnitsKummerSequence_shortExact (Ω := Ω) S n hnS) _).trans ?_
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨b, rfl⟩ := sUnitsToInvariants_surjective S (maximalUnramifiedOutside F Ω S) w
    refine ⟨b, sUnitsToInvariants_injective S (maximalUnramifiedOutside F Ω S) ?_⟩
    rw [map_nsmul]
    refine Eq.trans ?_ hw
    exact (invariantsFunctor_map_nsmul_apply (Ω := Ω) S n _).symm
  · rintro ⟨b, rfl⟩
    refine ⟨sUnitsToInvariants S (maximalUnramifiedOutside F Ω S) b, ?_⟩
    exact (invariantsFunctor_map_nsmul_apply (Ω := Ω) S n _).trans (map_nsmul _ _ _).symm

/-- Exactness at `H¹(G_S, μ_n)`: the kernel of `kummerPicHom` is the image of the Kummer map. -/
theorem kummerPicHom_eq_zero_iff (y : cohomology (rootsOfUnityModule F (maximalUnramifiedOutside F Ω S) n) 1) :
    kummerPicHom (Ω := Ω) S n y = 0 ↔ ∃ a, kummerSUnitsHom (Ω := Ω) S n hnS a = y := by
  have hK := sUnitsKummerSequence_shortExact (Ω := Ω) S n hnS
  constructor
  · intro hy
    have h0 : (coeffMap (sUnitsKummerSequence S (maximalUnramifiedOutside F Ω S) n).f 1).hom y = 0 :=
      cohomologyOneSUnitsToSPicard_injective S (hy.trans (map_zero _).symm)
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hK 0 1 rfl) y h0
    obtain ⟨b, hb⟩ := sUnitsToInvariants_surjective S (maximalUnramifiedOutside F Ω S)
      ((zeroIso (sUnitsKummerSequence S (maximalUnramifiedOutside F Ω S) n).X₃).hom.hom z)
    refine ⟨b, ?_⟩
    change (δ hK 0 1 rfl).hom ((zeroIso _).inv.hom (sUnitsToInvariants S _ b)) = y
    rw [hb, zeroIso_inv_hom_apply]
    exact hz
  · rintro ⟨a, rfl⟩
    have h0 := congrArg (fun φ => φ.hom ((zeroIso (sUnitsKummerSequence S (maximalUnramifiedOutside F Ω S) n).X₃).inv.hom
      (sUnitsToInvariants S (maximalUnramifiedOutside F Ω S) a))) (δ_comp hK 0 1 rfl)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at h0
    exact (congrArg (cohomologyOneSUnitsToSPicard (Ω := Ω) S) h0).trans (map_zero _)

/-- The image of `kummerPicHom` is the `n`-torsion of `Pic(𝒪_S)`. -/
theorem mem_range_kummerPicHom_iff (c : SPicardGroup S) :
    (∃ y, kummerPicHom (Ω := Ω) S n y = c) ↔ n • c = 0 := by
  have hK := sUnitsKummerSequence_shortExact (Ω := Ω) S n hnS
  have hg : ∀ h : cohomology (sUnitsModule S (maximalUnramifiedOutside F Ω S)) 1,
      (coeffMap (sUnitsKummerSequence S (maximalUnramifiedOutside F Ω S) n).g 1).hom h = n • h :=
    fun h => cohomologyMap_nsmul_id_apply (sUnitsModule S (maximalUnramifiedOutside F Ω S)) n 1 h
  constructor
  · rintro ⟨y, rfl⟩
    have h1 := cohomologyMap_g_cohomologyMap_f_apply (S := sUnitsKummerSequence S (maximalUnramifiedOutside F Ω S) n) 1 y
    have h1' := (hg _).symm.trans h1
    have h2 := congrArg (cohomologyOneSUnitsToSPicard (Ω := Ω) S) h1'
    exact (map_nsmul (cohomologyOneSUnitsToSPicard (Ω := Ω) S) n _).symm.trans (h2.trans (map_zero _))
  · intro hc
    obtain ⟨h, rfl⟩ := exists_cohomologyOneSUnitsToSPicard_eq (Ω := Ω) S (NeZero.ne n) hnS c hc
    have hh : n • h = 0 := cohomologyOneSUnitsToSPicard_injective S (by rw [map_nsmul, hc, map_zero])
    obtain ⟨y, hy⟩ := exists_cohomologyMap_f_eq hK 1 h ((hg h).trans hh)
    exact ⟨y, congrArg (cohomologyOneSUnitsToSPicard (Ω := Ω) S) hy⟩

end KummerPic

section BaseChange

variable {F L E : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field E]
  [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

/-- Integrality over the `S`-integers of `F` is integrality over the `S_L`-integers of `L`. -/
theorem isIntegral_integer_iff_finitePlacesAbove (x : E) :
    IsIntegral (S.integer F) x ↔
      IsIntegral ((finitePlacesAbove L S : Set (HeightOneSpectrum (𝓞 L))).integer L) x := by
  constructor
  · intro hx
    let f : S.integer F →+* (finitePlacesAbove L S : Set (HeightOneSpectrum (𝓞 L))).integer L :=
      ((algebraMap F L).comp (S.integer F).val.toRingHom).codRestrict _
        fun r w hw => valuation_algebraMap_integer_le_one S hw r
    exact IsIntegral.map_of_comp_eq f (RingHom.id E) (by
      ext r
      exact (IsScalarTower.algebraMap_apply F L E (r : F)).symm) hx
  · intro hx
    let C := integralClosure (S.integer F) E
    let f : (finitePlacesAbove L S : Set (HeightOneSpectrum (𝓞 L))).integer L →+* C :=
      ((algebraMap L E).comp
        ((finitePlacesAbove L S : Set (HeightOneSpectrum (𝓞 L))).integer L).val.toRingHom).codRestrict
        C.toSubring fun c => by
          have hc : IsIntegral (S.integer F) (c : L) :=
            isIntegral_integer_of_valuation_le_one S fun w hw => c.2 w hw
          exact hc.map ((IsScalarTower.toAlgHom F L E).restrictScalars (S.integer F))
    have hxC : IsIntegral C (RingHom.id E x) := IsIntegral.map_of_comp_eq f (RingHom.id E)
      (by ext c; rfl) hx
    have hmem : x ∈ integralClosure C E := hxC
    rw [integralClosure_idem, Algebra.mem_bot] at hmem
    obtain ⟨c, rfl⟩ := hmem
    exact c.2

/-- The `S_L`-units over `L` are the `S`-units over `F`. -/
theorem sUnitsOf_finitePlacesAbove_eq :
    sUnitsOf (finitePlacesAbove L S : Set (HeightOneSpectrum (𝓞 L))) E = sUnitsOf S E := by
  ext x
  rw [mem_sUnitsOf, mem_sUnitsOf, isIntegral_integer_iff_finitePlacesAbove (L := L) S,
    isIntegral_integer_iff_finitePlacesAbove (L := L) S]

end BaseChange

end

end Langlands.GaloisCohomology
