import Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.Main

/-!
# The Kummer sequence of the `S`-units with compact support

Let `K` be a number field, `S` a finite set of finite places, `n ≥ 1` invertible outside `S`, and
`E = 𝒪_{K_S,S}ˣ` the `S`-units of `K_S`. The Kummer sequence `0 → μ_n → E → E → 0` of `G_S`
(`sUnitsKummerSequence`) and the local Kummer sequences `0 → μ_n → K̄_vˣ → K̄_vˣ → 0` at the places
`v ∈ S` (`localKummerSequence`, with `μ_n(K_S)` embedded by `ι`) form a short exact sequence of
coefficients with local terms; its connecting map with compact support is

  `kummerCompactδ : H_c¹(G_S, E; (K̄_vˣ)_{v ∈ S}) → H_c²(G_S, μ_n)`,

the target being the cohomology with compact support of `μ_n` with the restricted local modules.
For `n = ℓᵏ` with `S` containing the places above `ℓ`, and `n` odd or `K` totally complex, it is
surjective (`surjective_kummerCompactδ`): the map `H_c²(G_S, μ_n) → H_c²(G_S, E)` is zero, because a
class of `H²(G_S, μ_n)` vanishing at the places of `S` has zero image in `H²(G_S, E)` (its Brauer
class vanishes everywhere, and `H²(G_S, E)(ℓ) → Br(K)` is injective), and
`H¹(K_v, K̄_vˣ) = 0` (Hilbert 90).
-/

namespace Langlands.GaloisCohomology.PoitouTate.Internal

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

section LocalMaps

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The coefficient map `K_Sˣ → K̄_vˣ` of `ι` at a finite place `v`, a morphism of modules of
`G_{K_v}`. -/
def maximalUnitsLocalHom (v : HeightOneSpectrum (𝓞 K)) :
    localModule ι (unitsModule K (maximalUnramifiedOutside K Ω S)) v ⟶
      unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) :=
  Rep.ofHom ⟨(uliftIntLinearMap (MonoidHom.toAdditive
      (Units.map (((ι.finite v).comp (maximalUnramifiedOutside K Ω S).val :
        maximalUnramifiedOutside K Ω S →ₐ[K] AlgebraicClosure (v.adicCompletion K)) :
          maximalUnramifiedOutside K Ω S →* AlgebraicClosure (v.adicCompletion K)))) :
      Additive (maximalUnramifiedOutside K Ω S)ˣ →ₗ[ULift.{u} ℤ]
        Additive (AlgebraicClosure (v.adicCompletion K))ˣ), fun σ => by
    ext x
    exact Units.ext (localizationHom_apply ι S v σ
      ((Additive.toMul (show Additive (maximalUnramifiedOutside K Ω S)ˣ from x) :
        (maximalUnramifiedOutside K Ω S)ˣ) : maximalUnramifiedOutside K Ω S))⟩

theorem maximalUnitsLocalHom_hom_apply (v : HeightOneSpectrum (𝓞 K))
    (x : Additive (maximalUnramifiedOutside K Ω S)ˣ) :
    (((Additive.toMul ((maximalUnitsLocalHom ι S v).hom x) :
        (AlgebraicClosure (v.adicCompletion K))ˣ)) : AlgebraicClosure (v.adicCompletion K)) =
      ι.finite v (((Additive.toMul x : (maximalUnramifiedOutside K Ω S)ˣ) :
        maximalUnramifiedOutside K Ω S) : Ω) :=
  rfl

/-- The coefficient map `𝒪_{K_S,S}ˣ → K̄_vˣ` of `ι` at a finite place `v`. -/
def sUnitsLocalHom (v : HeightOneSpectrum (𝓞 K)) :
    localModule ι (maximalSUnitsModule K Ω S) v ⟶
      unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) :=
  Rep.ofHom ⟨(uliftIntLinearMap (MonoidHom.toAdditive
      ((Units.map (((ι.finite v).comp (maximalUnramifiedOutside K Ω S).val :
        maximalUnramifiedOutside K Ω S →ₐ[K] AlgebraicClosure (v.adicCompletion K)) :
          maximalUnramifiedOutside K Ω S →* AlgebraicClosure (v.adicCompletion K))).comp
        (maximalSUnits K Ω S).subtype)) :
      Additive (maximalSUnits K Ω S) →ₗ[ULift.{u} ℤ]
        Additive (AlgebraicClosure (v.adicCompletion K))ˣ), fun σ => by
    ext x
    exact Units.ext (localizationHom_apply ι S v σ
      (((Additive.toMul (show Additive (maximalSUnits K Ω S) from x) : maximalSUnits K Ω S) :
        (maximalUnramifiedOutside K Ω S)ˣ) : maximalUnramifiedOutside K Ω S))⟩

theorem sUnitsLocalHom_hom_apply (v : HeightOneSpectrum (𝓞 K))
    (x : Additive (maximalSUnits K Ω S)) :
    (((Additive.toMul ((sUnitsLocalHom ι S v).hom x) :
        (AlgebraicClosure (v.adicCompletion K))ˣ)) : AlgebraicClosure (v.adicCompletion K)) =
      ι.finite v ((((Additive.toMul x : maximalSUnits K Ω S) : (maximalUnramifiedOutside K Ω S)ˣ) :
        maximalUnramifiedOutside K Ω S) : Ω) :=
  rfl

end LocalMaps

section Kummer

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) [NeZero n]

instance isSmoothRep_localKummerSequence_X₁ (v : HeightOneSpectrum (𝓞 K)) :
    IsSmoothRep (localKummerSequence ι S n v).X₁ :=
  inferInstanceAs (IsSmoothRep (localModule ι (dualizingModule K Ω S n) v))

instance isSmoothRep_localKummerSequence_X₂ (v : HeightOneSpectrum (𝓞 K)) :
    IsSmoothRep (localKummerSequence ι S n v).X₂ :=
  inferInstanceAs (IsSmoothRep
    (unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))))

instance isSmoothRep_localKummerSequence_X₃ (v : HeightOneSpectrum (𝓞 K)) :
    IsSmoothRep (localKummerSequence ι S n v).X₃ :=
  inferInstanceAs (IsSmoothRep
    (unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))))

/-- The Kummer sequence of the `S`-units, restricted to `G_{K_v}`, maps to the local Kummer
sequence: the identity on `μ_n` and `sUnitsLocalHom` on the units. -/
def kummerLocalMap (v : S) :
    (sUnitsKummerSequence S (maximalUnramifiedOutside K Ω S) n).map
        (Rep.resFunctor (localFamily ι S v : _ →* GaloisGroupUnramifiedOutside K Ω S)) ⟶
      localKummerSequence ι S n v.1 where
  τ₁ := 𝟙 (localModule ι (dualizingModule K Ω S n) v.1)
  τ₂ := sUnitsLocalHom ι S v.1
  τ₃ := sUnitsLocalHom ι S v.1
  comm₁₂ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Units.ext
    rfl
  comm₂₃ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change (n • 𝟙 (unitsModule (v.1.adicCompletion K)
        (AlgebraicClosure (v.1.adicCompletion K)))).hom ((sUnitsLocalHom ι S v.1).hom x) =
      (sUnitsLocalHom ι S v.1).hom (n • x)
    rw [nsmul_id_hom_apply]
    exact (map_nsmul (sUnitsLocalHom ι S v.1).hom n
      (show localModule ι (maximalSUnitsModule K Ω S) v.1 from x)).symm

theorem kummerLocalMap_τ₁ (v : S) :
    (kummerLocalMap ι S n v).τ₁ = 𝟙 (localModule ι (dualizingModule K Ω S n) v.1) :=
  rfl

theorem kummerLocalMap_τ₃ (v : S) :
    (kummerLocalMap ι S n v).τ₃ = sUnitsLocalHom ι S v.1 :=
  rfl

variable {S}

omit [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [NeZero n] in
theorem natCast_notMem_of_notMem (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    ∀ v ∉ S, ((n : ℕ) : 𝓞 K) ∉ v.asIdeal := fun v hv h => hv (hS v h)

variable (S) in
/-- The cohomology with compact support of the `S`-units, with the local modules `K̄_vˣ`. -/
abbrev unitsCompact (m : ℕ) : ModuleCat.{u} (ULift.{u} ℤ) :=
  compactSupportCohomology (localFamily ι S) (maximalSUnitsModule K Ω S)
    (fun v => unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K)))
    (fun v => sUnitsLocalHom ι S v.1) m

/-- **The Kummer connecting map with compact support**
`H_c¹(G_S, 𝒪_Sˣ; (K̄_vˣ)_v) → H_c²(G_S, μ_n)`. -/
def kummerCompactδ (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    unitsCompact ι S 1 ⟶ compactSupportCohomologyRes (localFamily ι S) (dualizingModule K Ω S n) 2 :=
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  compactSupportδ (localFamily ι S) (kummerLocalMap ι S n)
    (sUnitsKummerSequence_shortExact (Ω := Ω) S n (natCast_notMem_of_notMem n hS))
    (fun v => localKummerSequence_shortExact ι S n hS v.1) 1

end Kummer

section Surjective

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) {S : Set (HeightOneSpectrum (𝓞 K))} (n : ℕ) [NeZero n]

section Naturality

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι' : Type u} {H : ι' → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]
  {Aᵥ Bᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsSmoothRep (Aᵥ v)] [∀ v, IsSmoothRep (Bᵥ v)]
  {a : ∀ v, Rep.res (φ v : H v →* G) A ⟶ Aᵥ v} {b : ∀ v, Rep.res (φ v : H v →* G) B ⟶ Bᵥ v}

/-- `H_c → H` is natural in the coefficients. -/
theorem compactSupportMap_compactToGlobal (g : A ⟶ B) (gᵥ : ∀ v, Aᵥ v ⟶ Bᵥ v)
    (hg : ∀ v, a v ≫ gᵥ v = (Rep.resFunctor (φ v : H v →* G)).map g ≫ b v) (m : ℕ) :
    compactSupportMap φ g gᵥ hg m ≫ GaloisCohomology.compactToGlobal φ B Bᵥ b m =
      GaloisCohomology.compactToGlobal φ A Aᵥ a m ≫ coeffMap g m := by
  rw [coeffMap_def]
  refine (HomologicalComplex.homologyMap_comp _ _ m).symm.trans ?_
  refine Eq.trans ?_ (HomologicalComplex.homologyMap_comp _ _ m)
  exact congrArg (HomologicalComplex.homologyMap · m) (mappingCoconeNat.map_fst _ _ _)

end Naturality

variable {n}

omit [IsSepClosure K Ω] [NeZero n] in
/-- An `n`-torsion class of the Brauer group of a real or complex place is zero when `n` is odd or
`K` is totally complex. -/
theorem eq_zero_realBrauerGroup_of_nsmul (hK : Odd n ∨ IsTotallyComplex K) (w : InfinitePlace K)
    (b : RealBrauerGroup w) (hb : n • b = 0) : b = 0 := by
  rcases hK with h | h
  · exact eq_zero_of_coprime_nsmul_eq_zero (ℓ := n) (k := 1) (Nat.coprime_two_left.2 h)
      (two_nsmul_realBrauerGroup w b) (by rw [pow_one]; exact hb)
  · have := subsingleton_realBrauerGroup_of_isComplex w (h.isComplex w)
    exact Subsingleton.elim _ _

/-- A class of `H²(G_S, μ_n)` vanishing at the places of `S` maps to zero in `H²(G_S, 𝒪_Sˣ)`. -/
theorem coeffMap_rootsOfUnityToSUnits_eq_zero (hn : IsPrimePow n)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hK : Odd n ∨ IsTotallyComplex K) (x : cohomology (dualizingModule K Ω S n) 2)
    (hx : x ∈ ptSha (localFamily ι S) (dualizingModule K Ω S n) 2) :
    (coeffMap (rootsOfUnityToSUnits S (maximalUnramifiedOutside K Ω S) n) 2).hom x = 0 := by
  obtain ⟨ℓ, k, hℓ, hk, hnk⟩ := (isPrimePow_nat_iff n).1 hn
  have hℓS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S := fun v hv =>
    hS v (by
      rw [← hnk, Nat.cast_pow]
      exact v.asIdeal.pow_mem_of_mem hv k hk)
  have hnx : n • x = 0 := nsmul_cohomology_eq_zero _ (nsmul_dualizingModule S n) 2 x
  refine eq_zero_of_maximalSUnitsInflation_eq_zero S hℓ hℓS _ (k := k) ?_ ?_
  · rw [hnk, ← map_nsmul, hnx, map_zero]
  · rw [← brauerClass_eq_maximalSUnitsInflation]
    refine eq_zero_of_brauerLocalization_eq_zero' ι _ (fun v => ?_) (fun w => ?_)
    · by_cases hv : v ∈ S
      · have h0 : localization ι (dualizingModule K Ω S n) v 2 x = 0 :=
          ptRes_eq_zero_of_mem_ptSha (localFamily ι S) (dualizingModule K Ω S n) hx ⟨v, hv⟩
        rw [brauerLocalization_brauerClass, h0, map_zero]
      · exact brauerLocalization_brauerClass_eq_zero ι S n hv x
    · refine eq_zero_realBrauerGroup_of_nsmul hK w _ ?_
      rw [← map_nsmul, ← map_nsmul, hnx, map_zero, map_zero]

theorem subsingleton_cohomology_one_localUnits (v : HeightOneSpectrum (𝓞 K)) :
    Subsingleton (cohomology (unitsModule (v.adicCompletion K)
      (AlgebraicClosure (v.adicCompletion K))) 1) :=
  subsingleton_cohomology_one_unitsModule (K := v.adicCompletion K)
    (L := AlgebraicClosure (v.adicCompletion K))

/-- `μ_n → 𝒪_Sˣ` induces zero on `H_c²`. -/
theorem compactSupportMap_rootsOfUnityToSUnits_eq_zero (hn : IsPrimePow n)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hK : Odd n ∨ IsTotallyComplex K)
    (y : compactSupportCohomologyRes (localFamily ι S) (dualizingModule K Ω S n) 2) :
    (compactSupportMap (localFamily ι S) (sUnitsKummerSequence S (maximalUnramifiedOutside K Ω S) n).f
      (fun v => (localKummerSequence ι S n v.1).f) (fun v => (kummerLocalMap ι S n v).comm₁₂) 2).hom y
      = 0 := by
  set z := (compactSupportMap (localFamily ι S)
    (sUnitsKummerSequence S (maximalUnramifiedOutside K Ω S) n).f
    (fun v => (localKummerSequence ι S n v.1).f) (fun v => (kummerLocalMap ι S n v).comm₁₂) 2).hom y
    with hz
  have e : (GaloisCohomology.compactToGlobal (localFamily ι S) (maximalSUnitsModule K Ω S)
      (fun v => unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K)))
      (fun v => sUnitsLocalHom ι S v.1) 2).hom z =
      (coeffMap (rootsOfUnityToSUnits S (maximalUnramifiedOutside K Ω S) n) 2).hom
        ((ptCompactToGlobal (localFamily ι S) (dualizingModule K Ω S n) 2).hom y) :=
    congrArg (fun F => F.hom y) (compactSupportMap_compactToGlobal (localFamily ι S)
      (sUnitsKummerSequence S (maximalUnramifiedOutside K Ω S) n).f
      (fun v => (localKummerSequence ι S n v.1).f) (fun v => (kummerLocalMap ι S n v).comm₁₂) 2)
  have hglob : (GaloisCohomology.compactToGlobal (localFamily ι S) (maximalSUnitsModule K Ω S)
      (fun v => unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K)))
      (fun v => sUnitsLocalHom ι S v.1) 2).hom z = 0 :=
    e.trans (coeffMap_rootsOfUnityToSUnits_eq_zero ι hn hS hK _
      (ptCompactToGlobal_mem_ptSha (localFamily ι S) (dualizingModule K Ω S n) y))
  obtain ⟨ξ, hξ⟩ := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (compactSupportCohomology_exact_compact (localFamily ι S) (maximalSUnitsModule K Ω S)
      (fun v => unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K)))
      (fun v => sUnitsLocalHom ι S v.1) 1) hglob
  have hξ0 : ξ = 0 := funext fun v => (subsingleton_cohomology_one_localUnits v.1).elim _ _
  rw [← hξ, hξ0, map_zero]
  rfl

/-- **The Kummer connecting map with compact support is surjective** for `n = ℓᵏ`, the places above
`ℓ` in `S`, `n` odd or `K` totally complex. -/
theorem surjective_kummerCompactδ (hn : IsPrimePow n)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hK : Odd n ∨ IsTotallyComplex K) : Function.Surjective (kummerCompactδ ι n hS).hom := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hex := compactSupportCohomology_exact₁ (localFamily ι S) (kummerLocalMap ι S n)
    (sUnitsKummerSequence_shortExact (Ω := Ω) S n (natCast_notMem_of_notMem n hS))
    (fun v => localKummerSequence_shortExact ι S n hS v.1) 1
  intro y
  exact (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1 hex
    (compactSupportMap_rootsOfUnityToSUnits_eq_zero ι hn hS hK y)

end Surjective

end

end Langlands.GaloisCohomology.PoitouTate.Internal
