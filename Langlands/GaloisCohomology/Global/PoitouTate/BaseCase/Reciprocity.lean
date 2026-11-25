import Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.CupUnits
import Langlands.GaloisCohomology.Local.CupSymbol
import Langlands.GaloisCohomology.Global.Units.CapitulationPrincipalIdeal

/-!
# The trace of the Kummer classes with compact support

With the notation of `Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.CupUnits`, this file
computes the trace `finiteTrace (δ_c(e) ∪ χ)` of the cup product of the Kummer class with compact
support of the class `e` of a datum `(t, (a_v)_{v ∈ S})` with a character `χ ∈ H¹(G_S, ℤ/n)`, by the
reciprocity law of the Brauer group of `K` (`finiteTrace_kummerCompactδ_unitsData`):

  `finiteTrace (δ_c(e) ∪ χ) = Σ_{v ∈ S} inv_v (δχ_v ∪ a_v) - Σ_{v ∉ S} ord_v(t) · inv_v (δχ_v ∪ π_v)`,

`χ_v` the restriction of `χ` to the local Galois group at `v`, `π_v ∈ Kˣ` an element of order one at
`v`, and `δχ_v ∪ a` the cup symbol `characterCup` of local class field theory.

**Proof.** By `exists_compactCupRes_kummerCompactδ_unitsData` the image of `δ_c(e) ∪ χ` in
`H_c³(G_S, 𝒪_Sˣ)` is `localToCompact (W|_{K_v} + δχ_v ∪ a_v)_v` with `W ≡ t ^ {c_χ}` modulo `𝒪_Sˣ`.
Writing `δ_c(e) ∪ χ = localToCompact (ξ_v)_v` (the localization `H²(G_S, μ_n) → ⊕ H²(K_v, μ_n)`
followed by `localToCompact` is onto `H_c³` as `H³(G_S, μ_n) = 0`), the family
`(ξ_v - W|_{K_v} - δχ_v ∪ a_v)_v` is the localization of a class `y ∈ H²(G_S, 𝒪_Sˣ)`; so `B = W + y` is
a class of `H²(G_S, K_Sˣ)` with localizations `ξ_v - δχ_v ∪ a_v` at `v ∈ S`. Its invariants add up to
zero (`localInvariant_finite_support_and_sum_eq_zero`). Outside `S`, `y` does not contribute
(`brauerLocalization_maximalSUnitsInflation_eq_zero`), and the divisor class of `W - ord_v(t) (π_v ∪ δχ)`
vanishes at `v` (the divisor of `W(g, h)` is `c_χ(g, h) div(t)`), so its localization at `v` is zero
(`brauerLocalization_maximalUnitsInflation_eq_zero_iff`); the localization of `π_v ∪ δχ` is the cup
symbol `δχ_v ∪ π_v` (`brauerLocalization_bockUnitsClass`). The real invariants vanish: they are
killed by `2` and, with all other terms, by `n`, when `n` is odd, and there are no real places when
`K` is totally complex.
-/

namespace Langlands.GaloisCohomology.PoitouTate.Internal

open CategoryTheory Limits MonoidalCategory Langlands.ProfiniteCohomology Langlands.Galois NumberField
  IsDedekindDomain Langlands.ClassFieldTheory.Local

universe u

noncomputable section

section Generic

/-- A finite sum over a set `S` and the places outside `S` weighted by a finitely supported function:
the sum of a function given on `S` by `G` and outside `S` by `D • c`. -/
theorem finsum_eq_sum_add_finsuppSum {X M : Type*} [AddCommGroup M] (S : Set X) [Fintype S]
    (F : X → M) (G : S → M) (D : {v // v ∉ S} →₀ ℤ) (c : {v // v ∉ S} → M)
    (hS : ∀ v : S, F v = G v) (hSc : ∀ v : {v // v ∉ S}, F v = D v • c v) :
    ∑ᶠ v, F v = ∑ v : S, G v + D.sum fun v m => m • c v := by
  classical
  set F₁ : X → M := fun v => if h : v ∈ S then G ⟨v, h⟩ else 0 with hF₁
  set F₂ : X → M := fun v => if h : v ∈ S then 0 else D ⟨v, h⟩ • c ⟨v, h⟩ with hF₂
  have hF : F = F₁ + F₂ := by
    funext v
    by_cases h : v ∈ S
    · simp only [hF₁, hF₂, Pi.add_apply, dite_eq_left h, add_zero]
      exact hS ⟨v, h⟩
    · simp only [hF₁, hF₂, Pi.add_apply, dite_eq_right h, zero_add]
      exact hSc ⟨v, h⟩
  have h1 : Function.support F₁ ⊆ (S.toFinset : Set X) := by
    intro v hv
    by_contra h'
    rw [Finset.mem_coe, Set.mem_toFinset] at h'
    exact hv (dite_eq_right h')
  have h2 : Function.support F₂ ⊆ (D.support.map (Function.Embedding.subtype _) : Set X) := by
    intro v hv
    by_cases h : v ∈ S
    · exact absurd (dite_eq_left h) hv
    · have hD : D ⟨v, h⟩ ≠ 0 := fun h0 => hv (by
        change (if h : v ∈ S then 0 else D ⟨v, h⟩ • c ⟨v, h⟩) = 0
        rw [dite_eq_right h, h0, zero_smul])
      exact Finset.mem_map.2 ⟨⟨v, h⟩, Finsupp.mem_support_iff.2 hD, rfl⟩
  rw [hF]
  change ∑ᶠ v, (F₁ v + F₂ v) = _
  rw [finsum_add_distrib ((Finset.finite_toSet _).subset h1) ((Finset.finite_toSet _).subset h2),
    finsum_eq_sum_of_support_subset _ h1, finsum_eq_sum_of_support_subset _ h2, Finset.sum_map]
  congr 1
  · rw [Finset.sum_subtype S.toFinset (fun x => Set.mem_toFinset) F₁]
    exact Finset.sum_congr rfl fun v _ => dite_eq_left v.2
  · exact Finset.sum_congr rfl fun v _ => dite_eq_right v.2

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {I : Type u} {H : I → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)

/-- A family of local classes whose image in `H_c^{m+1}(G, B)` is the image of a family of local
classes of `A` under a map `g : A ⟶ B` differs from it by the localization of a global class. -/
theorem exists_map_eq_sub {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]
    {Bᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsSmoothRep (Bᵥ v)]
    {b : ∀ v, Rep.res (φ v : H v →* G) B ⟶ Bᵥ v} (g : A ⟶ B)
    (gᵥ : ∀ v, Rep.res (φ v : H v →* G) A ⟶ Bᵥ v)
    (hg : ∀ v, 𝟙 _ ≫ gᵥ v = (Rep.resFunctor (φ v : H v →* G)).map g ≫ b v) (m : ℕ)
    (ξ : ∀ v, cohomology (Rep.res (φ v : H v →* G) A) m) (η : ∀ v, cohomology (Bᵥ v) m)
    (h : (compactSupportMap φ g gᵥ hg (m + 1)).hom ((GaloisCohomology.localToCompact φ A
      (fun v => Rep.res (φ v : H v →* G) A) (fun _ => 𝟙 _) m).hom ξ) =
      (GaloisCohomology.localToCompact φ B Bᵥ b m).hom η) :
    ∃ y : cohomology B m, ∀ v, (map (φ v) (b v) m).hom y = (coeffMap (gᵥ v) m).hom (ξ v) - η v := by
  have e := congrArg (fun F => F.hom ξ) (localToCompact_compactSupportMap φ g gᵥ hg m)
  have h0 : (GaloisCohomology.localToCompact φ B Bᵥ b m).hom
      ((fun v => (coeffMap (gᵥ v) m).hom (ξ v)) - η) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact e.symm.trans h
  obtain ⟨y, hy⟩ := ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (compactSupportCohomology_exact_local φ B Bᵥ b m) _).1 h0
  exact ⟨y, fun v => congrFun hy v⟩

end Generic

section LocalCharacter

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) {n : ℕ}

theorem zmodCocycleHom_one {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (z : cocycles (zmodRep.{u} G n) 1) : zmodCocycleHom z 1 = 0 := by
  have h := zmodCocycleHom_mul z 1 1
  rw [mul_one] at h
  exact (add_eq_left.1 h.symm)

/-- The restriction of a character `z ∈ H¹(G_S, ℤ/n)` (a cocycle) to the local Galois group at a
finite place `v`, with values in `ℚ/ℤ`. -/
def localCharacter (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1)
    (v : HeightOneSpectrum (𝓞 K)) :
    Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K) →* Multiplicative RationalModIntegers where
  toFun σ := Multiplicative.ofAdd (QZ.toRationalModIntegers
    (zmodToQZ n (zmodCocycleHom z (localizationHom ι S v σ))))
  map_one' := by
    rw [map_one, zmodCocycleHom_one, map_zero, map_zero, ofAdd_zero]
  map_mul' σ τ := by
    rw [map_mul, zmodCocycleHom_mul, map_add, map_add, ofAdd_add]

theorem toAdd_localCharacter (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1)
    (v : HeightOneSpectrum (𝓞 K)) (σ : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)) :
    (localCharacter ι S z v σ).toAdd =
      QZ.toRationalModIntegers (zmodToQZ n (zmodCocycleHom z (localizationHom ι S v σ))) :=
  rfl

theorem isOpen_ker_localCharacter
    (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1)
    (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen ((localCharacter ι S z v).ker : Set Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)) := by
  have hlc : IsLocallyConstant (localCharacter ι S z v) :=
    ((isLocallyConstant_zmodCocycleHom z).comp_continuous (localizationHom ι S v).continuous).comp
      (fun c : ZMod n => Multiplicative.ofAdd (QZ.toRationalModIntegers (zmodToQZ n c)))
  exact hlc.isOpen_fiber 1

theorem charCocycle_localCharacter [NeZero n]
    (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1)
    (v : HeightOneSpectrum (𝓞 K)) (g h : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)) :
    GroupCoh.charCocycle (charAdd (Local.characterToQZ (localCharacter ι S z v)
      (isOpen_ker_localCharacter ι S z v))) (g, h) =
      bockInt (zmodCocycleHom z) (localizationHom ι S v g) (localizationHom ι S v h) :=
  charCocycle_eq_bockInt (fun g => zmodCocycleHom z (localizationHom ι S v g)) _ (fun _ => rfl) g h

/-- The cup symbol `inv_v (δχ_v ∪ a)` of a unit `a ∈ K_vˣ` with the restriction of the character `z`. -/
def cupSymbol (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1)
    (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) : RationalModIntegers :=
  finiteInvariant v (Local.characterCup (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
    (localCharacter ι S z v) (isOpen_ker_localCharacter ι S z v) a)

end LocalCharacter

section Localization

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The localization at `v` of the Brauer class of a class of `H²(G_S, K_Sˣ)`. -/
theorem brauerLocalization_maximalUnitsInflation (v : HeightOneSpectrum (𝓞 K))
    (x : cohomology (unitsModule K (maximalUnramifiedOutside K Ω S)) 2) :
    brauerLocalization ι v 2 (maximalUnitsInflation K Ω S 2 x) =
      (map (localizationHom ι S v) (maximalUnitsLocalHom ι S v) 2).hom x := by
  rw [maximalUnitsInflation_apply, brauerLocalization, LinearMap.toAddMonoidHom_coe, map_map_apply]
  have hφ : (GaloisGroupUnramifiedOutside.quotientMap K Ω S).comp
      (decompositionHom (v.adicCompletion K) (ι.finite v)) = localizationHom ι S v :=
    ContinuousMonoidHom.ext fun σ => (localizationHom_eq_quotientMap ι S v σ).symm
  rw [map_congr _ (maximalUnitsLocalHom ι S v) hφ ?_ 2]
  intro a
  rfl

/-- On the image of the `S`-units, the localization is the one of `sUnitsLocalHom`. -/
theorem map_maximalUnitsLocalHom_coeffMap (v : HeightOneSpectrum (𝓞 K))
    (y : cohomology (maximalSUnitsModule K Ω S) 2) :
    (map (localizationHom ι S v) (maximalUnitsLocalHom ι S v) 2).hom
        ((coeffMap (sUnitsToUnits S (maximalUnramifiedOutside K Ω S)) 2).hom y) =
      (map (localizationHom ι S v) (sUnitsLocalHom ι S v) 2).hom y := by
  rw [map_coeffMap_hom_apply]
  exact congrArg (fun F => F.hom y) (map_congr (A := maximalSUnitsModule K Ω S)
    (B := unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)))
    ((Rep.resFunctor (localizationHom ι S v : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)
        →* GaloisGroupUnramifiedOutside K Ω S)).map
      (sUnitsToUnits S (maximalUnramifiedOutside K Ω S)) ≫ maximalUnitsLocalHom ι S v)
    (sUnitsLocalHom ι S v) rfl (fun _ => rfl) 2)

end Localization

section BockClass

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) {n : ℕ} [NeZero n]

variable (Ω) in
/-- The class `π ∪ δχ ∈ H²(G_S, K_Sˣ)` of a unit `π ∈ Kˣ` and the Bockstein of a character `z`. -/
def bockUnitsClass (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1) (π : Kˣ) :
    cohomology (unitsModule K (maximalUnramifiedOutside K Ω S)) 2 :=
  cupPairing (intMulPairing (GaloisGroupUnramifiedOutside K Ω S)
      (unitsModule K (maximalUnramifiedOutside K Ω S))) (show 2 + 0 = 2 from rfl)
    ((δ (bockSeq_shortExact (GaloisGroupUnramifiedOutside K Ω S) n (NeZero.ne n)) 1 2 rfl).hom
      (cohomologyπ _ 1 z))
    ((zeroIso _).inv.hom (unitsToInvariants K (maximalUnramifiedOutside K Ω S) (Additive.ofMul π)))

theorem maximalUnitsLocalHom_unitsToInvariants (v : HeightOneSpectrum (𝓞 K)) (π : Kˣ) :
    (maximalUnitsLocalHom ι S v).hom
        (unitsToInvariants K (maximalUnramifiedOutside K Ω S) (Additive.ofMul π) :
          unitsModule K (maximalUnramifiedOutside K Ω S)) =
      baseUnit (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
        (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) π) :=
  Additive.toMul.injective (Units.ext (((ι.finite v).commutes (π : K)).trans
    (IsScalarTower.algebraMap_apply K (v.adicCompletion K)
      (AlgebraicClosure (v.adicCompletion K)) (π : K))))

/-- **The localization of `π ∪ δχ` is the cup symbol** `δχ_v ∪ π` of local class field theory. -/
theorem brauerLocalization_bockUnitsClass
    (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1)
    (v : HeightOneSpectrum (𝓞 K)) (π : Kˣ) :
    brauerLocalization ι v 2 (maximalUnitsInflation K Ω S 2 (bockUnitsClass Ω S z π)) =
      Local.characterCup (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
        (localCharacter ι S z v) (isOpen_ker_localCharacter ι S z v)
        (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) π) := by
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupPairing_δ_bockSeq (NeZero.ne n)
    (unitsModule K (maximalUnramifiedOutside K Ω S)) z
    (unitsToInvariants K (maximalUnramifiedOutside K Ω S) (Additive.ofMul π))
  rw [bockUnitsClass, ← hw, brauerLocalization_maximalUnitsInflation, map_cohomologyπ,
    Local.characterCup]
  congr 1
  apply cocycles_ext
  funext σ
  rw [cochainOf_cocycleι_cocyclesMap, Local.cochainOf_cocycleι_characterCupCocycle]
  have hσ : (⇑(localizationHom ι S v) ∘ σ) = ![localizationHom ι S v (σ 0), localizationHom ι S v (σ 1)] := by
    funext i
    fin_cases i <;> rfl
  change (maximalUnitsLocalHom ι S v).hom (cochainOf (unitsModule K (maximalUnramifiedOutside K Ω S))
    (cocycleι (unitsModule K (maximalUnramifiedOutside K Ω S)) 2 w)
    (⇑(localizationHom ι S v) ∘ σ)) = _
  rw [hσ, hwc, map_zsmul, maximalUnitsLocalHom_unitsToInvariants,
    charCocycle_eq_bockInt (fun g => zmodCocycleHom z (localizationHom ι S v g))
      (charAdd (Local.characterToQZ (localCharacter ι S z v) (isOpen_ker_localCharacter ι S z v)))
      (fun g => rfl)]
  rfl

omit [IsSepClosure K Ω] [NumberField K] [NeZero n] in
theorem intActPairingRes_tmul_ρ {L G : Type u} [Group L] [Group G] (A : Rep.{u} (ULift.{u} ℤ) L)
    (ψ : L →* G) (a : A) (g : L) (m : ℤ) :
    (intActPairingRes A ψ).hom (a ⊗ₜ[ULift.{u} ℤ]
      ((Rep.res ψ (intRepTriv G)).ρ g (ULift.up m : Rep.res ψ (intRepTriv G))) :
        (A ⊗ Rep.res ψ (intRepTriv G) : Rep _ _)) = m • a :=
  intActPairingRes_tmul A ψ a m

/-- The cup product of a class of degree `0` with a `2`-cocycle with values in `ℤ` (with trivial
action), along the action pairing. -/
theorem cupPairing_zeroIso_inv_intActPairingRes {L G : Type u} [Group L] [TopologicalSpace L]
    [IsTopologicalGroup L] [Group G] (A : Rep.{u} (ULift.{u} ℤ) L) [IsSmoothRep A] (ψ : L →* G)
    [IsSmoothRep (Rep.res ψ (intRepTriv G))] (a : A.ρ.invariants)
    (y : cocycles (Rep.res ψ (intRepTriv G)) 2) (w : cocycles A 2)
    (hw : ∀ σ : Fin 2 → L, cochainOf A (cocycleι A 2 w) σ =
      (cochainOf _ (cocycleι _ 2 y) σ).down • (a : A)) :
    cupPairing (intActPairingRes A ψ) (show 0 + 2 = 2 from rfl) ((zeroIso A).inv.hom a)
      (cohomologyπ _ 2 y) = cohomologyπ A 2 w := by
  obtain ⟨z0, hz0, hz0c⟩ := exists_cocycle_zeroIso_inv A a
  rw [← hz0, cupPairing_cohomologyπ]
  congr 1
  apply cocycles_ext
  funext σ
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hz0c, hw]
  have h0 : Fin.partialProd σ ⟨0, by omega⟩ = 1 := Fin.partialProd_zero σ
  have hσ : (fun j : Fin 2 => σ ⟨0 + j, by omega⟩) = σ := by
    funext j
    congr 1
    ext
    simp
  rw [h0, map_one, Module.End.one_apply, hσ]
  exact intActPairingRes_tmul A ψ _ _

/-- `localUnitsCup` is the cup symbol of local class field theory. -/
theorem localUnitsCup_eq_characterCup (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1)
    (v : S) (a : Additive (v.1.adicCompletion K)ˣ) :
    localUnitsCup ι S v a ((δ (bockSeq_shortExact (GaloisGroupUnramifiedOutside K Ω S) n
        (NeZero.ne n)) 1 2 rfl).hom (cohomologyπ _ 1 z)) =
      Local.characterCup (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K))
        (localCharacter ι S z v.1) (isOpen_ker_localCharacter ι S z v.1) (Additive.toMul a) := by
  have : IsSmoothRep (Rep.res (localFamilyHom ι S v) (intRepTriv (GaloisGroupUnramifiedOutside K Ω S))) :=
    isSmoothRep_res (localFamily ι S v) _
  obtain ⟨x₁, hx₁π, hx₁v⟩ := exists_cocycle_δ_bockSeq (NeZero.ne n) z
  obtain ⟨y₁, hy₁, hy₁c⟩ : ∃ y₁ : cocycles (Rep.res (localFamilyHom ι S v)
      (intRepTriv (GaloisGroupUnramifiedOutside K Ω S))) 2,
      (map (localFamily ι S v) (𝟙 _) 2).hom (cohomologyπ _ 2 x₁) = cohomologyπ _ 2 y₁ ∧
      ∀ τ : Fin 2 → Gal(AlgebraicClosure (v.1.adicCompletion K)/v.1.adicCompletion K),
        (cochainOf _ (cocycleι _ 2 y₁) τ).down = bockInt (zmodCocycleHom z)
          (localizationHom ι S v.1 (τ 0)) (localizationHom ι S v.1 (τ 1)) := by
    refine ⟨cocyclesMap (localFamily ι S v) (𝟙 _) 2 x₁, map_cohomologyπ _ _ x₁, fun τ => ?_⟩
    rw [cochainOf_cocycleι_cocyclesMap]
    have hτ : (⇑(localFamily ι S v) ∘ τ) =
        ![localizationHom ι S v.1 (τ 0), localizationHom ι S v.1 (τ 1)] := by
      funext i
      fin_cases i <;> rfl
    change (cochainOf (intRepTriv (GaloisGroupUnramifiedOutside K Ω S))
      (cocycleι (intRepTriv (GaloisGroupUnramifiedOutside K Ω S)) 2 x₁)
        (⇑(localFamily ι S v) ∘ τ)).down = _
    rw [hτ]
    exact hx₁v _ _
  rw [localUnitsCup, ← hx₁π, hy₁, Local.characterCup]
  refine cupPairing_zeroIso_inv_intActPairingRes _ _ _ _ _ fun σ => ?_
  rw [Local.cochainOf_cocycleι_characterCupCocycle, charCocycle_localCharacter, hy₁c]
  rfl

end BockClass

section DivisorCriterion

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) {n : ℕ} [NeZero n]

/-- The order at `v ∉ S` of a unit of `K`, read on `K_S`, is minus its order. -/
theorem sOrder_algebraMap {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) (x : Kˣ) :
    sOrder S ι v (Units.map (algebraMap K (maximalUnramifiedOutside K Ω S) : K →* _) x) =
      -ordAt v x := by
  have h2 : ordAbove S v ((⟨_, map_algebraMap_mem_sInvariantSubgroup (Ω := Ω) S x⟩ :
      sInvariantSubgroup Ω S) : (maximalUnramifiedOutside K Ω S)ˣ) = ordAt v x :=
    congrArg (fun D : SDivisor S => D ⟨v, hv⟩) (divAbove_algebraMap (Ω := Ω) S x)
  rw [ordAbove_eq_neg_sOrder ι hv (map_algebraMap_mem_sInvariantSubgroup (Ω := Ω) S x)] at h2
  omega

/-- The order cocycle at `v ∉ S` of a `2`-cocycle of `G_S` in `K_Sˣ`: the value at `σ` of the
`v`-component of its divisor cocycle is the order at `v` of its value at the localization of `σ`. -/
theorem cochainOf_orderCocycle {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    (c : cocycles (unitsModule K (maximalUnramifiedOutside K Ω S)) 2)
    (σ : Fin 2 → Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)) :
    (cochainOf _ (cocycleι _ 2 (cocyclesMap (outsideLocalizationHom S ι ⟨v, hv⟩)
      (divisorEval (outsideLocalizationHom S ι) (ULift.{u} ℤ) ⟨v, hv⟩) 2
        (HomologicalComplex.cyclesMap (coeffCochainsMap (unitsToSDivisor S ι)) 2 c))) σ) =
      ULift.up (sOrder S ι v (Additive.toMul (cochainOf _ (cocycleι _ 2 c)
        (⇑(localizationHom ι S v) ∘ σ)) : (maximalUnramifiedOutside K Ω S)ˣ)) := by
  rw [cochainOf_cocycleι_cocyclesMap]
  beta_reduce
  rw [cochainOf_cocycleι_cyclesMap, divisorEval_hom_apply]
  change ULift.up (sOrder S ι v (galUnitsHom K _ 1 _)) = _
  rw [map_one]
  rfl

/-- The order at `v ∉ S` of an element congruent to `t ^ m` modulo the `S`-units. -/
theorem sOrder_eq_mul_of_mem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    (t x : (maximalUnramifiedOutside K Ω S)ˣ) (m : ℤ) (hx : x * (t ^ m)⁻¹ ∈ maximalSUnits K Ω S) :
    sOrder S ι v x = m * sOrder S ι v t := by
  calc sOrder S ι v x = sOrder S ι v ((x * (t ^ m)⁻¹) * t ^ m) := by rw [inv_mul_cancel_right]
    _ = m * sOrder S ι v t := by
      rw [sOrder_mul ι hv, sOrder_eq_zero_of_mem ι hv hx, sOrder_zpow ι hv, zero_add]

omit [IsSepClosure K Ω] [NumberField K] [NeZero n] in
theorem cochainOf_zsmul {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : Rep.{u} (ULift.{u} ℤ) G} [IsSmoothRep A] {p : ℕ} (m : ℤ) (x : cocycles A p) :
    cochainOf A (cocycleι A p (m • x)) = m • cochainOf A (cocycleι A p x) := by
  rw [map_zsmul]
  exact map_zsmul (AddMonoidHom.mk' (cochainOf A) (fun a b => cochainOf_add a b)) m _

omit [IsSepClosure K Ω] [NumberField K] [NeZero n] in
theorem eq_zsmul_of_comp_sub_zsmul_eq_zero {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (f : A →+ B) (g : B →+ C) (a b : A) (m : ℤ) (h : g (f (a - m • b)) = 0) :
    g (f a) = m • g (f b) := by
  rwa [map_sub, map_zsmul, map_sub, map_zsmul, sub_eq_zero] at h

omit [NeZero n] in
/-- The divisor cocycle at `v ∉ S` of a cocycle `W` congruent to `t ^ {c_χ}` is `ord_v(t)` times the
one of a cocycle `π_v ^ {c_χ}` of `π_v ∪ δχ`. -/
theorem cocyclesMap_divisorEval_eq_zsmul {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    (t : sInvariantSubgroup Ω S)
    (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1)
    (W : cocycles (unitsModule K (maximalUnramifiedOutside K Ω S)) 2)
    (hW : ∀ g h, (Additive.toMul (cochainOf _ (cocycleι _ 2 W) ![g, h]) :
        (maximalUnramifiedOutside K Ω S)ˣ) *
        ((t : (maximalUnramifiedOutside K Ω S)ˣ) ^ bockInt (zmodCocycleHom z) g h)⁻¹ ∈
          maximalSUnits K Ω S)
    (w : cocycles (unitsModule K (maximalUnramifiedOutside K Ω S)) 2)
    (hwc : ∀ g h, cochainOf _ (cocycleι _ 2 w) ![g, h] = bockInt (zmodCocycleHom z) g h •
      ((unitsToInvariants K (maximalUnramifiedOutside K Ω S) (Additive.ofMul (globalUniformizer v)) :
        (unitsModule K (maximalUnramifiedOutside K Ω S)).ρ.invariants) :
          unitsModule K (maximalUnramifiedOutside K Ω S))) :
    cocyclesMap (outsideLocalizationHom S ι ⟨v, hv⟩)
      (divisorEval (outsideLocalizationHom S ι) (ULift.{u} ℤ) ⟨v, hv⟩) 2
        (HomologicalComplex.cyclesMap (coeffCochainsMap (unitsToSDivisor S ι)) 2 W) =
      ordAbove S v (t : (maximalUnramifiedOutside K Ω S)ˣ) •
        cocyclesMap (outsideLocalizationHom S ι ⟨v, hv⟩)
          (divisorEval (outsideLocalizationHom S ι) (ULift.{u} ℤ) ⟨v, hv⟩) 2
            (HomologicalComplex.cyclesMap (coeffCochainsMap (unitsToSDivisor S ι)) 2 w) := by
  have hDt : sOrder S ι v (t : (maximalUnramifiedOutside K Ω S)ˣ) =
      -ordAbove S v (t : (maximalUnramifiedOutside K Ω S)ˣ) := by
    rw [ordAbove_eq_neg_sOrder ι hv t.2, neg_neg]
  apply cocycles_ext
  rw [cochainOf_zsmul]
  funext σ
  rw [Pi.smul_apply, cochainOf_orderCocycle ι S hv, cochainOf_orderCocycle ι S hv]
  have hσ : (⇑(localizationHom ι S v) ∘ σ) =
      ![localizationHom ι S v (σ 0), localizationHom ι S v (σ 1)] := by
    funext i
    fin_cases i <;> rfl
  rw [hσ, sOrder_eq_mul_of_mem ι S hv _ _ _ (hW _ _), hDt]
  have hπ : (Additive.toMul (cochainOf _ (cocycleι _ 2 w)
      ![localizationHom ι S v (σ 0), localizationHom ι S v (σ 1)]) :
        (maximalUnramifiedOutside K Ω S)ˣ) =
      Units.map (algebraMap K (maximalUnramifiedOutside K Ω S) : K →* _) (globalUniformizer v) ^
        bockInt (zmodCocycleHom z) (localizationHom ι S v (σ 0)) (localizationHom ι S v (σ 1)) := by
    rw [hwc]
    rfl
  rw [hπ, sOrder_zpow ι hv, sOrder_algebraMap ι S hv, ordAt_globalUniformizer]
  apply ULift.ext
  change _ = ordAbove S v (t : (maximalUnramifiedOutside K Ω S)ˣ) • (_ : ℤ)
  rw [smul_eq_mul]
  ring

/-- **The localization outside `S` of a cocycle congruent to `t ^ {c_χ}`**: it is `ord_v(t)` times
the localization of `π_v ∪ δχ`, for `π_v` the global uniformizer at `v`. -/
theorem brauerLocalization_eq_ordAbove_smul {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    (t : sInvariantSubgroup Ω S)
    (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1)
    (W : cocycles (unitsModule K (maximalUnramifiedOutside K Ω S)) 2)
    (hW : ∀ g h, (Additive.toMul (cochainOf _ (cocycleι _ 2 W) ![g, h]) :
        (maximalUnramifiedOutside K Ω S)ˣ) *
        ((t : (maximalUnramifiedOutside K Ω S)ˣ) ^ bockInt (zmodCocycleHom z) g h)⁻¹ ∈
          maximalSUnits K Ω S) :
    brauerLocalization ι v 2 (maximalUnitsInflation K Ω S 2 (cohomologyπ _ 2 W)) =
      ordAbove S v (t : (maximalUnramifiedOutside K Ω S)ˣ) •
        brauerLocalization ι v 2 (maximalUnitsInflation K Ω S 2
          (bockUnitsClass Ω S z (globalUniformizer v))) := by
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupPairing_δ_bockSeq (NeZero.ne n)
    (unitsModule K (maximalUnramifiedOutside K Ω S)) z
    (unitsToInvariants K (maximalUnramifiedOutside K Ω S) (Additive.ofMul (globalUniformizer v)))
  have hc := cocyclesMap_divisorEval_eq_zsmul ι S hv t z W hW w hwc
  have h0 := (brauerLocalization_maximalUnitsInflation_eq_zero_iff S ι ⟨v, hv⟩
    (cohomologyπ _ 2 W - ordAbove S v (t : (maximalUnramifiedOutside K Ω S)ˣ) •
      cohomologyπ _ 2 w)).2 (by
      rw [map_sub, map_zsmul, map_sub, map_zsmul, sub_eq_zero, cohomologyMap_cohomologyπ,
        cohomologyMap_cohomologyπ, map_cohomologyπ, map_cohomologyπ]
      exact (congrArg (fun c => cohomologyπ _ 2 c) hc).trans (map_zsmul _ _ _))
  rw [bockUnitsClass, ← hw]
  exact eq_zsmul_of_comp_sub_zsmul_eq_zero _ _ _ _ _ h0

end DivisorCriterion

section TraceFormula

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- The cup symbols of a character of `G_S` with values in `ℤ/n` are killed by `n`. -/
theorem nsmul_cupSymbol (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1)
    (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) : n • cupSymbol ι S z v a = 0 := by
  have h1 : localCharacter ι S z v ^ n = 1 := by
    ext σ
    apply Multiplicative.toAdd.injective
    rw [MonoidHom.pow_apply, toAdd_pow, toAdd_localCharacter, MonoidHom.one_apply, toAdd_one,
      ← map_nsmul, ← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero, map_zero]
  have hn : IsOpen ((localCharacter ι S z v ^ n).ker :
      Set Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)) := by
    rw [h1, MonoidHom.ker_one]
    exact isOpen_univ
  have h1' : IsOpen ((1 : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K) →*
      Multiplicative RationalModIntegers).ker :
        Set Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)) := h1 ▸ hn
  rw [cupSymbol, ← map_nsmul, ← Local.characterCup_pow_left _ _ _ _ n hn,
    Local.characterCup_congr _ _ h1 hn h1', Local.characterCup_one_left, map_zero]

omit [NeZero n] in
/-- The invariants of the classes of `H²(K_v, μ_n)` are killed by `n`. -/
theorem nsmul_finiteInvariant_coeffMap (v : HeightOneSpectrum (𝓞 K))
    (x : cohomology (localModule ι (dualizingModule K Ω S n) v) 2) :
    n • finiteInvariant v ((coeffMap (rootsOfUnityLocalHom ι S n v) 2).hom x) = 0 := by
  rw [← map_nsmul, ← map_nsmul, nsmul_cohomology_eq_zero (localModule ι (dualizingModule K Ω S n) v)
    (fun d => nsmul_dualizingModule S n d) 2 x, map_zero, map_zero]

/-- The real invariants are killed by `2`. -/
theorem two_nsmul_realLocalInvariant (w : InfinitePlace K) (X : cohomology (unitsModule K Ω) 2) :
    2 • realLocalInvariant ι w X = 0 := by
  rw [realLocalInvariant, ← realInvariantHom_apply, ← map_nsmul, two_nsmul_realBrauerGroup, map_zero]

omit [NeZero n] in
/-- For `n` odd or `K` totally complex, the real invariants of a Brauer class whose finite
invariants add up to an element killed by `n` add up to zero. -/
theorem sum_realLocalInvariant_eq_zero (hK : Odd n ∨ IsTotallyComplex K)
    (X : cohomology (unitsModule K Ω) 2) (hX : n • ∑ᶠ v, localInvariant ι v X = 0) :
    ∑ w, realLocalInvariant ι w X = 0 := by
  rcases hK with ho | hc
  · have hsum := (localInvariant_finite_support_and_sum_eq_zero ι X).2
    have h2 : 2 • ∑ w, realLocalInvariant ι w X = 0 := by
      rw [Finset.smul_sum]
      exact Finset.sum_eq_zero fun w _ => two_nsmul_realLocalInvariant ι w X
    have hn : n ^ 1 • ∑ w, realLocalInvariant ι w X = 0 := by
      rw [pow_one, eq_neg_of_add_eq_zero_right hsum, smul_neg, hX, neg_zero]
    exact eq_zero_of_coprime_nsmul_eq_zero (Nat.coprime_two_left.2 ho) h2 hn
  · exact Finset.sum_eq_zero fun w _ => by
      have := subsingleton_realBrauerGroup_of_isComplex w (hc.isComplex w)
      exact (realLocalInvariant_eq_zero_iff ι w X).2 (Subsingleton.elim _ _)

/-- The localization at `v ∈ S` of `y + [W]`, for `y` with prescribed localizations. -/
theorem brauerLocalization_add_of_mem (v : S)
    (y : cohomology (maximalSUnitsModule K Ω S) 2)
    (W : cocycles (unitsModule K (maximalUnramifiedOutside K Ω S)) 2)
    (x c : cohomology (unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K))) 2)
    (hy : (map (localFamily ι S v) (sUnitsLocalHom ι S v.1) 2).hom y =
      x - ((map (localFamily ι S v) (maximalUnitsLocalHom ι S v.1) 2).hom (cohomologyπ _ 2 W) + c)) :
    brauerLocalization ι v.1 2 (maximalUnitsInflation K Ω S 2
      ((coeffMap (sUnitsToUnits S (maximalUnramifiedOutside K Ω S)) 2).hom y +
        cohomologyπ _ 2 W)) = x - c := by
  rw [brauerLocalization_maximalUnitsInflation, map_add, map_maximalUnitsLocalHom_coeffMap]
  change (map (localFamily ι S v) (sUnitsLocalHom ι S v.1) 2).hom y +
    (map (localFamily ι S v) (maximalUnitsLocalHom ι S v.1) 2).hom (cohomologyπ _ 2 W) = _
  rw [hy]
  abel

/-- The localization at `v ∉ S` of `y + [W]`, for `W ≡ t ^ {c_χ}`: `ord_v(t)` times the cup
symbol of `π_v`. -/
theorem brauerLocalization_add_of_not_mem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    (y : cohomology (maximalSUnitsModule K Ω S) 2) (t : sInvariantSubgroup Ω S)
    (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1)
    (W : cocycles (unitsModule K (maximalUnramifiedOutside K Ω S)) 2)
    (hW : ∀ g h, (Additive.toMul (cochainOf _ (cocycleι _ 2 W) ![g, h]) :
        (maximalUnramifiedOutside K Ω S)ˣ) *
        ((t : (maximalUnramifiedOutside K Ω S)ˣ) ^ bockInt (zmodCocycleHom z) g h)⁻¹ ∈
          maximalSUnits K Ω S) :
    brauerLocalization ι v 2 (maximalUnitsInflation K Ω S 2
      ((coeffMap (sUnitsToUnits S (maximalUnramifiedOutside K Ω S)) 2).hom y +
        cohomologyπ _ 2 W)) =
      ordAbove S v (t : (maximalUnramifiedOutside K Ω S)ˣ) •
        Local.characterCup (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
          (localCharacter ι S z v) (isOpen_ker_localCharacter ι S z v)
          (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K)
            (globalUniformizer v)) := by
  rw [map_add, map_add, ← maximalSUnitsInflation_apply,
    brauerLocalization_maximalSUnitsInflation_eq_zero S ι hv, zero_add,
    brauerLocalization_eq_ordAbove_smul ι S hv t z W hW, brauerLocalization_bockUnitsClass]

/-- **The sum formula for `y + [W]`.** For classes `ξ_v ∈ H²(K_v, μ_n)`, a cocycle `W ≡ t ^ {c_χ}` and
`y ∈ H²(G_S, 𝒪_Sˣ)` with localizations `ξ_v - W|_{K_v} - δχ_v ∪ a_v` at the places of `S`, the sum
of the invariants of the `ξ_v` is `Σ_{v ∈ S} inv_v (δχ_v ∪ a_v) - Σ_{v ∉ S} ord_v(t) inv_v (δχ_v ∪ π_v)`. -/
theorem sum_finiteInvariant_eq_of_localization [Finite S] (hK : Odd n ∨ IsTotallyComplex K)
    (d : UnitsDatum Ω S) (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1)
    (ξ : ∀ v : S, cohomology (localModule ι (dualizingModule K Ω S n) v.1) 2)
    (y : cohomology (maximalSUnitsModule K Ω S) 2)
    (W : cocycles (unitsModule K (maximalUnramifiedOutside K Ω S)) 2)
    (hW : ∀ g h, (Additive.toMul (cochainOf _ (cocycleι _ 2 W) ![g, h]) :
        (maximalUnramifiedOutside K Ω S)ˣ) *
        (((Additive.toMul d.1 : sInvariantSubgroup Ω S) : (maximalUnramifiedOutside K Ω S)ˣ) ^
          bockInt (zmodCocycleHom z) g h)⁻¹ ∈ maximalSUnits K Ω S)
    (hy : ∀ v : S, (map (localFamily ι S v) (sUnitsLocalHom ι S v.1) 2).hom y =
      (coeffMap (rootsOfUnityLocalHom ι S n v.1) 2).hom (ξ v) -
        ((map (localFamily ι S v) (maximalUnitsLocalHom ι S v.1) 2).hom (cohomologyπ _ 2 W) +
          localUnitsCup ι S v (d.2 v)
            ((δ (bockSeq_shortExact (GaloisGroupUnramifiedOutside K Ω S) n (NeZero.ne n)) 1 2
              rfl).hom (cohomologyπ _ 1 z)))) :
    letI : Fintype S := Fintype.ofFinite S
    ∑ v : S, finiteInvariant v.1 ((coeffMap (rootsOfUnityLocalHom ι S n v.1) 2).hom (ξ v)) =
      ∑ v : S, cupSymbol ι S z v.1 (Additive.toMul (d.2 v)) -
        (divAbove S d.1).sum fun v m => m • cupSymbol ι S z v.1
          (Units.map (algebraMap K (v.1.adicCompletion K) : K →* v.1.adicCompletion K)
            (globalUniformizer v.1)) := by
  let _ : Fintype S := Fintype.ofFinite S
  set X := maximalUnitsInflation K Ω S 2
    ((coeffMap (sUnitsToUnits S (maximalUnramifiedOutside K Ω S)) 2).hom y + cohomologyπ _ 2 W)
    with hX
  have hfin := finsum_eq_sum_add_finsuppSum S (fun v => localInvariant ι v X)
    (fun v => finiteInvariant v.1 ((coeffMap (rootsOfUnityLocalHom ι S n v.1) 2).hom (ξ v)) -
      cupSymbol ι S z v.1 (Additive.toMul (d.2 v))) (divAbove S d.1)
    (fun v => cupSymbol ι S z v.1
      (Units.map (algebraMap K (v.1.adicCompletion K) : K →* v.1.adicCompletion K)
        (globalUniformizer v.1)))
    (fun v => by
      rw [localInvariant_apply, hX, brauerLocalization_add_of_mem ι S v y W _ _ (hy v),
        localUnitsCup_eq_characterCup, map_sub (finiteInvariant v.1)]
      rfl)
    (fun v => by
      rw [localInvariant_apply, hX, brauerLocalization_add_of_not_mem ι S v.2 y _ z W hW,
        map_zsmul (finiteInvariant v.1)]
      rfl)
  have hreal := sum_realLocalInvariant_eq_zero ι hK X (by
    rw [hfin, smul_add, Finset.smul_sum, Finsupp.smul_sum]
    refine (congrArg₂ (· + ·) (Finset.sum_eq_zero fun v _ => ?_)
      (Finset.sum_eq_zero fun v _ => ?_)).trans (add_zero 0)
    · rw [smul_sub, nsmul_finiteInvariant_coeffMap, nsmul_cupSymbol, sub_zero]
    · change n • (_ • _) = _
      rw [smul_comm, nsmul_cupSymbol, smul_zero])
  have hsum := (localInvariant_finite_support_and_sum_eq_zero ι X).2
  rw [hfin, hreal, add_zero, Finset.sum_sub_distrib] at hsum
  rw [eq_sub_iff_add_eq, ← sub_eq_zero, ← hsum]
  abel

/-- **The trace of the Kummer class with compact support of a datum against a character.** For a
datum `d = (t, (a_v)_{v ∈ S})` and a character `z` of `G_S` with values in `ℤ/n`,

  `finiteTrace (δ_c(e(d)) ∪ χ) = Σ_{v ∈ S} inv_v (δχ_v ∪ a_v) - Σ_{v ∉ S} ord_v(t) · inv_v (δχ_v ∪ π_v)`

(read in `ℚ/ℤ`), `π_v = globalUniformizer v`. -/
theorem finiteTrace_kummerCompactδ_unitsData [Finite S] (hn : IsPrimePow n)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hK : Odd n ∨ IsTotallyComplex K) (d : UnitsDatum Ω S)
    (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1) :
    letI : Fintype S := Fintype.ofFinite S
    QZ.toRationalModIntegers (zmodToQZ n (finiteTrace ι S n hK
      (compactCupRes (localFamily ι S)
        (zmodMulPairingRight n (dualizingModule K Ω S n) (nsmul_dualizingModule S n))
        (show 2 + 1 = 3 from rfl) ((kummerCompactδ ι n hS).hom (unitsData S ι d))
        (cohomologyπ _ 1 z)))) =
      ∑ v : S, cupSymbol ι S z v.1 (Additive.toMul (d.2 v)) -
        (divAbove S d.1).sum fun v m => m • cupSymbol ι S z v.1
          (Units.map (algebraMap K (v.1.adicCompletion K) : K →* v.1.adicCompletion K)
            (globalUniformizer v.1)) := by
  let _ : Fintype S := Fintype.ofFinite S
  obtain ⟨ξ, hξ⟩ := surjective_ptLocalToCompact_two ι S n hK hS (compactCupRes (localFamily ι S)
    (zmodMulPairingRight n (dualizingModule K Ω S n) (nsmul_dualizingModule S n))
    (show 2 + 1 = 3 from rfl) ((kummerCompactδ ι n hS).hom (unitsData S ι d)) (cohomologyπ _ 1 z))
  obtain ⟨W, hW, hcup⟩ := exists_compactCupRes_kummerCompactδ_unitsData ι S n hn hS d z
  rw [← hξ] at hcup
  obtain ⟨y, hy⟩ := exists_map_eq_sub (localFamily ι S) (A := dualizingModule K Ω S n)
    (B := maximalSUnitsModule K Ω S) (sUnitsKummerSequence S (maximalUnramifiedOutside K Ω S) n).f
    (fun v => (localKummerSequence ι S n v.1).f) (fun v => (kummerLocalMap ι S n v).comm₁₂) 2 ξ _
    hcup
  rw [← hξ, isFiniteTrace_finiteTrace ι S n hK ξ, map_sum]
  refine (Finset.sum_congr rfl fun v _ => ?_).trans
    (sum_finiteInvariant_eq_of_localization ι S hK d z ξ y W hW hy)
  rw [invariantAt_apply, AddEquiv.apply_symm_apply]

end TraceFormula

end

end Langlands.GaloisCohomology.PoitouTate.Internal
