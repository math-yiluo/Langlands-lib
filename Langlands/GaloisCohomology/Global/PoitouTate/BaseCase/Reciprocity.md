# The trace of the Kummer classes with compact support

`Langlands/GaloisCohomology/Global/PoitouTate/BaseCase/Reciprocity.lean`, namespace `Langlands.GaloisCohomology.PoitouTate.Internal`.

With the notation of `Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.CupUnits`, this file
computes the trace `finiteTrace (δ_c(e(d)) ∪ χ)` of the cup product of the Kummer class with compact
support of the class `e(d)` of a datum `d = (t, (a_v)_{v ∈ S})` with a character
`χ ∈ H¹(G_S, ℤ/n)` (a `1`-cocycle `z`), by the reciprocity law of the Brauer group of `K`
(`finiteTrace_kummerCompactδ_unitsData`): in `ℚ/ℤ`,

  `finiteTrace (δ_c(e(d)) ∪ χ) = Σ_{v ∈ S} cupSymbol z v a_v - Σ_{v ∉ S} ord_v(t) · cupSymbol z v π_v`,

the second sum being `(divAbove S t).sum`, `π_v` the image in `K_v` of `globalUniformizer v` and

  `cupSymbol ι S z v a = finiteInvariant v (δχ_v ∪ a)`

the invariant of the cup symbol `Local.characterCup` of the restriction `localCharacter ι S z v` of
`χ` to `G_{K_v}` with `a ∈ K_vˣ`.

**Main statements.**
* `brauerLocalization_bockUnitsClass`: the localization at `v` of the class `π ∪ δχ ∈ H²(G_S, K_Sˣ)`
  (`bockUnitsClass`, for `π ∈ Kˣ`) is the cup symbol `δχ_v ∪ π`; `localUnitsCup_eq_characterCup`:
  the local cup products of `CupUnits` are the cup symbols.
* `brauerLocalization_eq_ordAbove_smul` (the places outside `S`): for `v ∉ S` and a `2`-cocycle `W`
  congruent to `t ^ {c_χ}` modulo the `S`-units, the localization at `v` of the Brauer class of `W`
  is `ord_v(t)` times that of `π_v ∪ δχ`: the divisor class of `W - ord_v(t)(π_v ∪ δχ)` vanishes at
  `v` (`cocyclesMap_divisorEval_eq_zsmul`), which is the criterion
  `brauerLocalization_maximalUnitsInflation_eq_zero_iff`.
* `sum_realLocalInvariant_eq_zero`: for `n` odd or `K` totally complex, the real invariants of a
  Brauer class whose finite invariants add up to an element killed by `n` add up to zero.
* `finiteTrace_kummerCompactδ_unitsData`: the formula above.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.Internal.finsum_eq_sum_add_finsuppSum.{u_1, u_2} {X : Type u_1} {M : Type u_2}
  [AddCommGroup M] (S : Set X) [Fintype ↑S] (F : X → M) (G : ↑S → M) (D : { v // v ∉ S } →₀ ℤ) (c : { v // v ∉ S } → M)
  (hS : ∀ (v : ↑S), F ↑v = G v) (hSc : ∀ (v : { v // v ∉ S }), F ↑v = D v • c v) :
  ∑ᶠ (v : X), F v = ∑ v, G v + D.sum fun v m => m • c v
Langlands.GaloisCohomology.PoitouTate.Internal.exists_map_eq_sub.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {I : Type u} {H : I → Type u} [(v : I) → Group (H v)]
  [(v : I) → TopologicalSpace (H v)] [∀ (v : I), IsTopologicalGroup (H v)] (φ : (v : I) → H v →ₜ* G)
  {A B : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A] [Langlands.IsSmoothRep B] {Bᵥ : (v : I) → Rep.{u, u, u} k (H v)}
  [∀ (v : I), Langlands.IsSmoothRep (Bᵥ v)] {b : (v : I) → Rep.res (↑(φ v)) B ⟶ Bᵥ v} (g : A ⟶ B)
  (gᵥ : (v : I) → Rep.res (↑(φ v)) A ⟶ Bᵥ v)
  (hg :
    ∀ (v : I),
      CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.id (Rep.res (↑(φ v)) A)) (gᵥ v) =
        CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑(φ v)).map g) (b v))
  (m : ℕ) (ξ : (v : I) → ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(φ v)) A) m))
  (η : (v : I) → ↑(Langlands.ProfiniteCohomology.cohomology (Bᵥ v) m))
  (h :
    (ModuleCat.Hom.hom (Langlands.GaloisCohomology.compactSupportMap φ g gᵥ hg (m + 1)))
        ((ModuleCat.Hom.hom
            (Langlands.GaloisCohomology.localToCompact φ A (fun v => Rep.res (↑(φ v)) A)
              (fun x => CategoryTheory.CategoryStruct.id (Rep.res (↑(φ x)) A)) m))
          ξ) =
      (ModuleCat.Hom.hom (Langlands.GaloisCohomology.localToCompact φ B Bᵥ b m)) η) :
  ∃ y,
    ∀ (v : I),
      (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.map (φ v) (b v) m)) y =
        (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.coeffMap (gᵥ v) m)) (ξ v) - η v
Langlands.GaloisCohomology.PoitouTate.Internal.zmodCocycleHom_one.{u} {n : ℕ} {G : Type u} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (z : ↑(Langlands.ProfiniteCohomology.cocycles (Langlands.ProfiniteCohomology.zmodRep G n) 1)) :
  Langlands.ProfiniteCohomology.zmodCocycleHom z 1 = 0
Langlands.GaloisCohomology.PoitouTate.Internal.localCharacter.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {n : ℕ}
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Gal(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
          v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) →*
    Multiplicative Langlands.ClassFieldTheory.Local.RationalModIntegers
Langlands.GaloisCohomology.PoitouTate.Internal.toAdd_localCharacter.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {n : ℕ}
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (σ :
    Gal(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
          v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) :
  Multiplicative.toAdd ((Langlands.GaloisCohomology.PoitouTate.Internal.localCharacter ι S z v) σ) =
    Langlands.ProfiniteCohomology.QZ.toRationalModIntegers
      ((Langlands.ProfiniteCohomology.zmodToQZ n)
        (Langlands.ProfiniteCohomology.zmodCocycleHom z ((Langlands.Galois.localizationHom ι S v) σ)))
Langlands.GaloisCohomology.PoitouTate.Internal.isOpen_ker_localCharacter.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {n : ℕ}
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  IsOpen ↑(Langlands.GaloisCohomology.PoitouTate.Internal.localCharacter ι S z v).ker
Langlands.GaloisCohomology.PoitouTate.Internal.charCocycle_localCharacter.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {n : ℕ} [NeZero n]
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (g h :
    Gal(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
          v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) :
  Langlands.ProfiniteCohomology.GroupCoh.charCocycle
      (Langlands.ProfiniteCohomology.charAdd
        (Langlands.GaloisCohomology.Local.characterToQZ
          (Langlands.GaloisCohomology.PoitouTate.Internal.localCharacter ι S z v) ⋯))
      (g, h) =
    Langlands.ProfiniteCohomology.bockInt (Langlands.ProfiniteCohomology.zmodCocycleHom z)
      ((Langlands.Galois.localizationHom ι S v) g) ((Langlands.Galois.localizationHom ι S v) h)
Langlands.GaloisCohomology.PoitouTate.Internal.cupSymbol.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {n : ℕ}
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (a : (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)ˣ) : Langlands.ClassFieldTheory.Local.RationalModIntegers
Langlands.GaloisCohomology.PoitouTate.Internal.brauerLocalization_maximalUnitsInflation.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (x :
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2)) :
  (Langlands.GaloisCohomology.brauerLocalization ι v 2) ((Langlands.GaloisCohomology.maximalUnitsInflation K Ω S 2) x) =
    (ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.map (Langlands.Galois.localizationHom ι S v)
          (Langlands.GaloisCohomology.PoitouTate.Internal.maximalUnitsLocalHom ι S v) 2))
      x
Langlands.GaloisCohomology.PoitouTate.Internal.map_maximalUnitsLocalHom_coeffMap.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) 2)) :
  (ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.map (Langlands.Galois.localizationHom ι S v)
          (Langlands.GaloisCohomology.PoitouTate.Internal.maximalUnitsLocalHom ι S v) 2))
      ((ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.coeffMap
            (Langlands.GaloisCohomology.sUnitsToUnits S ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2))
        y) =
    (ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.map (Langlands.Galois.localizationHom ι S v)
          (Langlands.GaloisCohomology.PoitouTate.Internal.sUnitsLocalHom ι S v) 2))
      y
Langlands.GaloisCohomology.PoitouTate.Internal.bockUnitsClass.{u} {K : Type u} (Ω : Type u) [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {n : ℕ} [NeZero n]
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
  (π : Kˣ) :
  ↑(Langlands.ProfiniteCohomology.cohomology
      (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2)
Langlands.GaloisCohomology.PoitouTate.Internal.maximalUnitsLocalHom_unitsToInvariants.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (π : Kˣ) :
  (Rep.Hom.hom (Langlands.GaloisCohomology.PoitouTate.Internal.maximalUnitsLocalHom ι S v))
      ↑((Langlands.GaloisCohomology.unitsToInvariants K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
          (Additive.ofMul π)) =
    Langlands.ClassFieldTheory.Local.baseUnit (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
      ((Units.map ↑(algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))) π)
Langlands.GaloisCohomology.PoitouTate.Internal.brauerLocalization_bockUnitsClass.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {n : ℕ} [NeZero n]
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (π : Kˣ) :
  (Langlands.GaloisCohomology.brauerLocalization ι v 2)
      ((Langlands.GaloisCohomology.maximalUnitsInflation K Ω S 2)
        (Langlands.GaloisCohomology.PoitouTate.Internal.bockUnitsClass Ω S z π)) =
    Langlands.GaloisCohomology.Local.characterCup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
      (Langlands.GaloisCohomology.PoitouTate.Internal.localCharacter ι S z v) ⋯
      ((Units.map ↑(algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))) π)
Langlands.GaloisCohomology.PoitouTate.Internal.intActPairingRes_tmul_ρ.{u} {L G : Type u} [Group L] [Group G]
  (A : Rep.{u, u, u} (ULift.{u, 0} ℤ) L) (ψ : L →* G) (a : ↑A) (g : L) (m : ℤ) :
  (Rep.Hom.hom (Langlands.GaloisCohomology.PoitouTate.Internal.intActPairingRes A ψ))
      (a ⊗ₜ[ULift.{u, 0} ℤ] ((Rep.res ψ (Langlands.ProfiniteCohomology.intRepTriv G)).ρ g) { down := m }) =
    m • a
Langlands.GaloisCohomology.PoitouTate.Internal.cupPairing_zeroIso_inv_intActPairingRes.{u} {L G : Type u} [Group L]
  [TopologicalSpace L] [IsTopologicalGroup L] [Group G] (A : Rep.{u, u, u} (ULift.{u, 0} ℤ) L) [Langlands.IsSmoothRep A]
  (ψ : L →* G) [Langlands.IsSmoothRep (Rep.res ψ (Langlands.ProfiniteCohomology.intRepTriv G))] (a : ↥A.ρ.invariants)
  (y : ↑(Langlands.ProfiniteCohomology.cocycles (Rep.res ψ (Langlands.ProfiniteCohomology.intRepTriv G)) 2))
  (w : ↑(Langlands.ProfiniteCohomology.cocycles A 2))
  (hw :
    ∀ (σ : Fin 2 → L),
      Langlands.ProfiniteCohomology.cochainOf A ((Langlands.ProfiniteCohomology.cocycleι A 2) w) σ =
        (Langlands.ProfiniteCohomology.cochainOf (Rep.res ψ (Langlands.ProfiniteCohomology.intRepTriv G))
              ((Langlands.ProfiniteCohomology.cocycleι (Rep.res ψ (Langlands.ProfiniteCohomology.intRepTriv G)) 2) y)
              σ).down •
          ↑a) :
  ((Langlands.ProfiniteCohomology.cupPairing (Langlands.GaloisCohomology.PoitouTate.Internal.intActPairingRes A ψ) ⋯)
        ((ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.zeroIso A).inv) a))
      ((CategoryTheory.ConcreteCategory.hom
          (Langlands.ProfiniteCohomology.cohomologyπ (Rep.res ψ (Langlands.ProfiniteCohomology.intRepTriv G)) 2))
        y) =
    (CategoryTheory.ConcreteCategory.hom (Langlands.ProfiniteCohomology.cohomologyπ A 2)) w
Langlands.GaloisCohomology.PoitouTate.Internal.localUnitsCup_eq_characterCup.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {n : ℕ} [NeZero n]
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
  (v : ↑S) (a : Additive (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)ˣ) :
  Langlands.GaloisCohomology.PoitouTate.Internal.localUnitsCup ι S v a
      ((ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.δ ⋯ 1 2 ⋯))
        ((CategoryTheory.ConcreteCategory.hom
            (Langlands.ProfiniteCohomology.cohomologyπ
              (Langlands.ProfiniteCohomology.bockSeq (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n).X₃ 1))
          z)) =
    Langlands.GaloisCohomology.Local.characterCup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v))
      (Langlands.GaloisCohomology.PoitouTate.Internal.localCharacter ι S z ↑v) ⋯ (Additive.toMul a)
Langlands.GaloisCohomology.PoitouTate.Internal.sOrder_algebraMap.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} (hv : v ∉ S) (x : Kˣ) :
  Langlands.GaloisCohomology.sOrder S ι v
      ((Units.map ↑(algebraMap K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))) x) =
    -Langlands.GaloisCohomology.ordAt v x
Langlands.GaloisCohomology.PoitouTate.Internal.cochainOf_orderCocycle.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} (hv : v ∉ S)
  (c :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2))
  (σ :
    Fin 2 →
      Gal(AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
            v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) :
  Langlands.ProfiniteCohomology.cochainOf
      (Langlands.GaloisCohomology.trivialModule
        Gal(AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
              ↑⟨v, hv⟩)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑⟨v, hv⟩)
        (ULift.{u, 0} ℤ))
      ((Langlands.ProfiniteCohomology.cocycleι
          (Langlands.GaloisCohomology.trivialModule
            Gal(AlgebraicClosure
                (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
                  ↑⟨v, hv⟩)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑⟨v, hv⟩)
            (ULift.{u, 0} ℤ))
          2)
        ((CategoryTheory.ConcreteCategory.hom
            (Langlands.ProfiniteCohomology.cocyclesMap (Langlands.GaloisCohomology.outsideLocalizationHom S ι ⟨v, hv⟩)
              (Langlands.GaloisCohomology.divisorEval (Langlands.GaloisCohomology.outsideLocalizationHom S ι)
                (ULift.{u, 0} ℤ) ⟨v, hv⟩)
              2))
          ((CategoryTheory.ConcreteCategory.hom
              (HomologicalComplex.cyclesMap
                (Langlands.ProfiniteCohomology.coeffCochainsMap (Langlands.GaloisCohomology.unitsToSDivisor S ι)) 2))
            c)))
      σ =
    {
      down :=
        Langlands.GaloisCohomology.sOrder S ι v
          (Additive.toMul
            (Langlands.ProfiniteCohomology.cochainOf
              (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
              ((Langlands.ProfiniteCohomology.cocycleι
                  (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2)
                c)
              (⇑(Langlands.Galois.localizationHom ι S v) ∘ σ))) }
Langlands.GaloisCohomology.PoitouTate.Internal.sOrder_eq_mul_of_mem.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} (hv : v ∉ S)
  (t x : (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ) (m : ℤ)
  (hx : x * (t ^ m)⁻¹ ∈ Langlands.GaloisCohomology.maximalSUnits K Ω S) :
  Langlands.GaloisCohomology.sOrder S ι v x = m * Langlands.GaloisCohomology.sOrder S ι v t
Langlands.GaloisCohomology.PoitouTate.Internal.cochainOf_zsmul.{u} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {A : Rep.{u, u, u} (ULift.{u, 0} ℤ) G} [Langlands.IsSmoothRep A] {p : ℕ} (m : ℤ)
  (x : ↑(Langlands.ProfiniteCohomology.cocycles A p)) :
  Langlands.ProfiniteCohomology.cochainOf A ((Langlands.ProfiniteCohomology.cocycleι A p) (m • x)) =
    m • Langlands.ProfiniteCohomology.cochainOf A ((Langlands.ProfiniteCohomology.cocycleι A p) x)
Langlands.GaloisCohomology.PoitouTate.Internal.eq_zsmul_of_comp_sub_zsmul_eq_zero.{u_1, u_2, u_3} {A : Type u_1}
  {B : Type u_2} {C : Type u_3} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : A →+ B) (g : B →+ C) (a b : A)
  (m : ℤ) (h : g (f (a - m • b)) = 0) : g (f a) = m • g (f b)
Langlands.GaloisCohomology.PoitouTate.Internal.cocyclesMap_divisorEval_eq_zsmul.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {n : ℕ}
  {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} (hv : v ∉ S)
  (t : ↥(Langlands.GaloisCohomology.sInvariantSubgroup Ω S))
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
  (W :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2))
  (hW :
    ∀ (g h : Gal(↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)/K)),
      Additive.toMul
            (Langlands.ProfiniteCohomology.cochainOf
              (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
              ((Langlands.ProfiniteCohomology.cocycleι
                  (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2)
                W)
              ![g, h]) *
          (↑t ^ Langlands.ProfiniteCohomology.bockInt (Langlands.ProfiniteCohomology.zmodCocycleHom z) g h)⁻¹ ∈
        Langlands.GaloisCohomology.maximalSUnits K Ω S)
  (w :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2))
  (hwc :
    ∀ (g h : Gal(↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)/K)),
      Langlands.ProfiniteCohomology.cochainOf
          (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
          ((Langlands.ProfiniteCohomology.cocycleι
              (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2)
            w)
          ![g, h] =
        Langlands.ProfiniteCohomology.bockInt (Langlands.ProfiniteCohomology.zmodCocycleHom z) g h •
          ↑((Langlands.GaloisCohomology.unitsToInvariants K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
              (Additive.ofMul (Langlands.GaloisCohomology.globalUniformizer v)))) :
  (CategoryTheory.ConcreteCategory.hom
        (Langlands.ProfiniteCohomology.cocyclesMap (Langlands.GaloisCohomology.outsideLocalizationHom S ι ⟨v, hv⟩)
          (Langlands.GaloisCohomology.divisorEval (Langlands.GaloisCohomology.outsideLocalizationHom S ι)
            (ULift.{u, 0} ℤ) ⟨v, hv⟩)
          2))
      ((CategoryTheory.ConcreteCategory.hom
          (HomologicalComplex.cyclesMap
            (Langlands.ProfiniteCohomology.coeffCochainsMap (Langlands.GaloisCohomology.unitsToSDivisor S ι)) 2))
        W) =
    Langlands.GaloisCohomology.ordAbove S v ↑t •
      (CategoryTheory.ConcreteCategory.hom
          (Langlands.ProfiniteCohomology.cocyclesMap (Langlands.GaloisCohomology.outsideLocalizationHom S ι ⟨v, hv⟩)
            (Langlands.GaloisCohomology.divisorEval (Langlands.GaloisCohomology.outsideLocalizationHom S ι)
              (ULift.{u, 0} ℤ) ⟨v, hv⟩)
            2))
        ((CategoryTheory.ConcreteCategory.hom
            (HomologicalComplex.cyclesMap
              (Langlands.ProfiniteCohomology.coeffCochainsMap (Langlands.GaloisCohomology.unitsToSDivisor S ι)) 2))
          w)
Langlands.GaloisCohomology.PoitouTate.Internal.brauerLocalization_eq_ordAbove_smul.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {n : ℕ} [NeZero n]
  {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} (hv : v ∉ S)
  (t : ↥(Langlands.GaloisCohomology.sInvariantSubgroup Ω S))
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
  (W :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2))
  (hW :
    ∀ (g h : Gal(↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)/K)),
      Additive.toMul
            (Langlands.ProfiniteCohomology.cochainOf
              (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
              ((Langlands.ProfiniteCohomology.cocycleι
                  (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2)
                W)
              ![g, h]) *
          (↑t ^ Langlands.ProfiniteCohomology.bockInt (Langlands.ProfiniteCohomology.zmodCocycleHom z) g h)⁻¹ ∈
        Langlands.GaloisCohomology.maximalSUnits K Ω S) :
  (Langlands.GaloisCohomology.brauerLocalization ι v 2)
      ((Langlands.GaloisCohomology.maximalUnitsInflation K Ω S 2)
        ((CategoryTheory.ConcreteCategory.hom
            (Langlands.ProfiniteCohomology.cohomologyπ
              (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2))
          W)) =
    Langlands.GaloisCohomology.ordAbove S v ↑t •
      (Langlands.GaloisCohomology.brauerLocalization ι v 2)
        ((Langlands.GaloisCohomology.maximalUnitsInflation K Ω S 2)
          (Langlands.GaloisCohomology.PoitouTate.Internal.bockUnitsClass Ω S z
            (Langlands.GaloisCohomology.globalUniformizer v)))
Langlands.GaloisCohomology.PoitouTate.Internal.nsmul_cupSymbol.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {n : ℕ}
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (a : (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)ˣ) :
  n • Langlands.GaloisCohomology.PoitouTate.Internal.cupSymbol ι S z v a = 0
Langlands.GaloisCohomology.PoitouTate.Internal.nsmul_finiteInvariant_coeffMap.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {n : ℕ}
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (x :
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) v)
        2)) :
  n •
      (Langlands.GaloisCohomology.finiteInvariant v)
        ((ModuleCat.Hom.hom
            (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityLocalHom ι S n v)
              2))
          x) =
    0
Langlands.GaloisCohomology.PoitouTate.Internal.two_nsmul_realLocalInvariant.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (w : NumberField.InfinitePlace K)
  (X : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)) :
  2 • Langlands.GaloisCohomology.realLocalInvariant ι w X = 0
Langlands.GaloisCohomology.PoitouTate.Internal.sum_realLocalInvariant_eq_zero.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω) {n : ℕ}
  (hK : Odd n ∨ NumberField.IsTotallyComplex K)
  (X : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2))
  (hX :
    n •
        ∑ᶠ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
          (Langlands.GaloisCohomology.localInvariant ι v) X =
      0) :
  ∑ w, Langlands.GaloisCohomology.realLocalInvariant ι w X = 0
Langlands.GaloisCohomology.PoitouTate.Internal.brauerLocalization_add_of_mem.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (v : ↑S)
  (y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) 2))
  (W :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2))
  (x c :
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)))
        2))
  (hy :
    (ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.map (Langlands.GaloisCohomology.PoitouTate.localFamily ι S v)
            (Langlands.GaloisCohomology.PoitouTate.Internal.sUnitsLocalHom ι S ↑v) 2))
        y =
      x -
        ((ModuleCat.Hom.hom
              (Langlands.ProfiniteCohomology.map (Langlands.GaloisCohomology.PoitouTate.localFamily ι S v)
                (Langlands.GaloisCohomology.PoitouTate.Internal.maximalUnitsLocalHom ι S ↑v) 2))
            ((CategoryTheory.ConcreteCategory.hom
                (Langlands.ProfiniteCohomology.cohomologyπ
                  (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2))
              W) +
          c)) :
  (Langlands.GaloisCohomology.brauerLocalization ι (↑v) 2)
      ((Langlands.GaloisCohomology.maximalUnitsInflation K Ω S 2)
        ((ModuleCat.Hom.hom
              (Langlands.ProfiniteCohomology.coeffMap
                (Langlands.GaloisCohomology.sUnitsToUnits S ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2))
            y +
          (CategoryTheory.ConcreteCategory.hom
              (Langlands.ProfiniteCohomology.cohomologyπ
                (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2))
            W)) =
    x - c
Langlands.GaloisCohomology.PoitouTate.Internal.brauerLocalization_add_of_not_mem.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {n : ℕ} [NeZero n]
  {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} (hv : v ∉ S)
  (y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) 2))
  (t : ↥(Langlands.GaloisCohomology.sInvariantSubgroup Ω S))
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
  (W :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2))
  (hW :
    ∀ (g h : Gal(↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)/K)),
      Additive.toMul
            (Langlands.ProfiniteCohomology.cochainOf
              (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
              ((Langlands.ProfiniteCohomology.cocycleι
                  (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2)
                W)
              ![g, h]) *
          (↑t ^ Langlands.ProfiniteCohomology.bockInt (Langlands.ProfiniteCohomology.zmodCocycleHom z) g h)⁻¹ ∈
        Langlands.GaloisCohomology.maximalSUnits K Ω S) :
  (Langlands.GaloisCohomology.brauerLocalization ι v 2)
      ((Langlands.GaloisCohomology.maximalUnitsInflation K Ω S 2)
        ((ModuleCat.Hom.hom
              (Langlands.ProfiniteCohomology.coeffMap
                (Langlands.GaloisCohomology.sUnitsToUnits S ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2))
            y +
          (CategoryTheory.ConcreteCategory.hom
              (Langlands.ProfiniteCohomology.cohomologyπ
                (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2))
            W)) =
    Langlands.GaloisCohomology.ordAbove S v ↑t •
      Langlands.GaloisCohomology.Local.characterCup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
        (Langlands.GaloisCohomology.PoitouTate.Internal.localCharacter ι S z v) ⋯
        ((Units.map ↑(algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))
          (Langlands.GaloisCohomology.globalUniformizer v))
Langlands.GaloisCohomology.PoitouTate.Internal.sum_finiteInvariant_eq_of_localization.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {n : ℕ} [NeZero n] [Finite ↑S]
  (hK : Odd n ∨ NumberField.IsTotallyComplex K) (d : Langlands.GaloisCohomology.PoitouTate.Internal.UnitsDatum Ω S)
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
  (ξ :
    (v : ↑S) →
      ↑(Langlands.ProfiniteCohomology.cohomology
          (Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) ↑v)
          2))
  (y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) 2))
  (W :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2))
  (hW :
    ∀ (g h : Gal(↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)/K)),
      Additive.toMul
            (Langlands.ProfiniteCohomology.cochainOf
              (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
              ((Langlands.ProfiniteCohomology.cocycleι
                  (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2)
                W)
              ![g, h]) *
          (↑(Additive.toMul d.1) ^
              Langlands.ProfiniteCohomology.bockInt (Langlands.ProfiniteCohomology.zmodCocycleHom z) g h)⁻¹ ∈
        Langlands.GaloisCohomology.maximalSUnits K Ω S)
  (hy :
    ∀ (v : ↑S),
      (ModuleCat.Hom.hom
            (Langlands.ProfiniteCohomology.map (Langlands.GaloisCohomology.PoitouTate.localFamily ι S v)
              (Langlands.GaloisCohomology.PoitouTate.Internal.sUnitsLocalHom ι S ↑v) 2))
          y =
        (ModuleCat.Hom.hom
              (Langlands.ProfiniteCohomology.coeffMap
                (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityLocalHom ι S n ↑v) 2))
            (ξ v) -
          ((ModuleCat.Hom.hom
                (Langlands.ProfiniteCohomology.map (Langlands.GaloisCohomology.PoitouTate.localFamily ι S v)
                  (Langlands.GaloisCohomology.PoitouTate.Internal.maximalUnitsLocalHom ι S ↑v) 2))
              ((CategoryTheory.ConcreteCategory.hom
                  (Langlands.ProfiniteCohomology.cohomologyπ
                    (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2))
                W) +
            Langlands.GaloisCohomology.PoitouTate.Internal.localUnitsCup ι S v (d.2 v)
              ((ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.δ ⋯ 1 2 ⋯))
                ((CategoryTheory.ConcreteCategory.hom
                    (Langlands.ProfiniteCohomology.cohomologyπ
                      (Langlands.ProfiniteCohomology.bockSeq (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n).X₃
                      1))
                  z)))) :
  ∑ v,
      (Langlands.GaloisCohomology.finiteInvariant ↑v)
        ((ModuleCat.Hom.hom
            (Langlands.ProfiniteCohomology.coeffMap
              (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityLocalHom ι S n ↑v) 2))
          (ξ v)) =
    ∑ v, Langlands.GaloisCohomology.PoitouTate.Internal.cupSymbol ι S z (↑v) (Additive.toMul (d.2 v)) -
      Finsupp.sum ((Langlands.GaloisCohomology.divAbove S) d.1) fun v m =>
        m •
          Langlands.GaloisCohomology.PoitouTate.Internal.cupSymbol ι S z (↑v)
            ((Units.map ↑(algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)))
              (Langlands.GaloisCohomology.globalUniformizer ↑v))
Langlands.GaloisCohomology.PoitouTate.Internal.finiteTrace_kummerCompactδ_unitsData.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {n : ℕ} [NeZero n] [Finite ↑S]
  (hn : IsPrimePow n)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ NumberField.IsTotallyComplex K) (d : Langlands.GaloisCohomology.PoitouTate.Internal.UnitsDatum Ω S)
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1)) :
  Langlands.ProfiniteCohomology.QZ.toRationalModIntegers
      ((Langlands.ProfiniteCohomology.zmodToQZ n)
        ((Langlands.GaloisCohomology.PoitouTate.finiteTrace ι S n hK)
          (((Langlands.GaloisCohomology.compactCupRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
                (Langlands.GaloisCohomology.zmodMulPairingRight n
                  (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) ⋯)
                ⋯)
              ((ModuleCat.Hom.hom (Langlands.GaloisCohomology.PoitouTate.Internal.kummerCompactδ ι n hS))
                ((Langlands.GaloisCohomology.PoitouTate.Internal.unitsData S ι) d)))
            ((CategoryTheory.ConcreteCategory.hom
                (Langlands.ProfiniteCohomology.cohomologyπ
                  (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
              z)))) =
    ∑ v, Langlands.GaloisCohomology.PoitouTate.Internal.cupSymbol ι S z (↑v) (Additive.toMul (d.2 v)) -
      Finsupp.sum ((Langlands.GaloisCohomology.divAbove S) d.1) fun v m =>
        m •
          Langlands.GaloisCohomology.PoitouTate.Internal.cupSymbol ι S z (↑v)
            ((Units.map ↑(algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)))
              (Langlands.GaloisCohomology.globalUniformizer ↑v))
```

## Outline of the proofs

By `surjective_ptLocalToCompact_two`, `δ_c(e(d)) ∪ χ = localToCompact (ξ_v)_v` with
`ξ_v ∈ H²(K_v, μ_n)`, and `finiteTrace` of it is the sum of the invariants of the `ξ_v`
(`isFiniteTrace_finiteTrace`). By `exists_compactCupRes_kummerCompactδ_unitsData` the image of
`δ_c(e(d)) ∪ χ` in `H_c³(G_S, 𝒪_Sˣ)` is `localToCompact (W|_{K_v} + δχ_v ∪ a_v)_v`; so the family
`(ξ_v - W|_{K_v} - δχ_v ∪ a_v)_v` is the localization of a class `y ∈ H²(G_S, 𝒪_Sˣ)`
(`exists_map_eq_sub`, exactness of `H² → ∏ H² → H_c³`), and `B = y + [W] ∈ H²(G_S, K_Sˣ)` has the
localizations `ξ_v - δχ_v ∪ a_v` at `v ∈ S` (`brauerLocalization_add_of_mem`) and
`ord_v(t) (δχ_v ∪ π_v)` at `v ∉ S` (`brauerLocalization_add_of_not_mem`: `y` contributes nothing
outside `S`, `brauerLocalization_maximalSUnitsInflation_eq_zero`). The invariants of the Brauer
class of `B` add up to zero (`localInvariant_finite_support_and_sum_eq_zero`); the finite part is
`Σ_{v∈S} (inv ξ_v - cupSymbol a_v) + Σ_{v∉S} ord_v(t) cupSymbol π_v`
(`finsum_eq_sum_add_finsuppSum`), killed by `n` (`nsmul_cupSymbol`,
`nsmul_finiteInvariant_coeffMap`), so the real part vanishes (`sum_realLocalInvariant_eq_zero`: it is
killed by `2` and by `n`, or there are no real places), which is the formula
(`sum_finiteInvariant_eq_of_localization`).

## Declarations

In the order of the file:

- `finsum_eq_sum_add_finsuppSum` (theorem): A finite sum over a set `S` and the places outside `S` weighted by a finitely supported function: the sum of a function given on `S` by `G` and outside `S` by `D • c`.
- `exists_map_eq_sub` (theorem): A family of local classes whose image in `H_c^{m+1}(G, B)` is the image of a family of local classes of `A` under a map `g : A ⟶ B` differs from it by the localization of a global class.
- `zmodCocycleHom_one` (theorem).
- `localCharacter` (def): The restriction of a character `z ∈ H¹(G_S, ℤ/n)` (a cocycle) to the local Galois group at a finite place `v`, with values in `ℚ/ℤ`.
- `toAdd_localCharacter` (theorem).
- `isOpen_ker_localCharacter` (theorem).
- `charCocycle_localCharacter` (theorem).
- `cupSymbol` (def): The cup symbol `inv_v (δχ_v ∪ a)` of a unit `a ∈ K_vˣ` with the restriction of the character `z`.
- `brauerLocalization_maximalUnitsInflation` (theorem): The localization at `v` of the Brauer class of a class of `H²(G_S, K_Sˣ)`.
- `map_maximalUnitsLocalHom_coeffMap` (theorem): On the image of the `S`-units, the localization is the one of `sUnitsLocalHom`.
- `bockUnitsClass` (def): The class `π ∪ δχ ∈ H²(G_S, K_Sˣ)` of a unit `π ∈ Kˣ` and the Bockstein of a character `z`.
- `maximalUnitsLocalHom_unitsToInvariants` (theorem).
- `brauerLocalization_bockUnitsClass` (theorem): **The localization of `π ∪ δχ` is the cup symbol** `δχ_v ∪ π` of local class field theory.
- `intActPairingRes_tmul_ρ` (theorem).
- `cupPairing_zeroIso_inv_intActPairingRes` (theorem): The cup product of a class of degree `0` with a `2`-cocycle with values in `ℤ` (with trivial action), along the action pairing.
- `localUnitsCup_eq_characterCup` (theorem): `localUnitsCup` is the cup symbol of local class field theory.
- `sOrder_algebraMap` (theorem): The order at `v ∉ S` of a unit of `K`, read on `K_S`, is minus its order.
- `cochainOf_orderCocycle` (theorem): The order cocycle at `v ∉ S` of a `2`-cocycle of `G_S` in `K_Sˣ`: the value at `σ` of the `v`-component of its divisor cocycle is the order at `v` of its value at the localization of `σ`.
- `sOrder_eq_mul_of_mem` (theorem): The order at `v ∉ S` of an element congruent to `t ^ m` modulo the `S`-units.
- `cochainOf_zsmul` (theorem).
- `eq_zsmul_of_comp_sub_zsmul_eq_zero` (theorem).
- `cocyclesMap_divisorEval_eq_zsmul` (theorem): The divisor cocycle at `v ∉ S` of a cocycle `W` congruent to `t ^ {c_χ}` is `ord_v(t)` times the one of a cocycle `π_v ^ {c_χ}` of `π_v ∪ δχ`.
- `brauerLocalization_eq_ordAbove_smul` (theorem): **The localization outside `S` of a cocycle congruent to `t ^ {c_χ}`**: it is `ord_v(t)` times the localization of `π_v ∪ δχ`, for `π_v` the global uniformizer at `v`.
- `nsmul_cupSymbol` (theorem): The cup symbols of a character of `G_S` with values in `ℤ/n` are killed by `n`.
- `nsmul_finiteInvariant_coeffMap` (theorem): The invariants of the classes of `H²(K_v, μ_n)` are killed by `n`.
- `two_nsmul_realLocalInvariant` (theorem): The real invariants are killed by `2`.
- `sum_realLocalInvariant_eq_zero` (theorem): For `n` odd or `K` totally complex, the real invariants of a Brauer class whose finite invariants add up to an element killed by `n` add up to zero.
- `brauerLocalization_add_of_mem` (theorem): The localization at `v ∈ S` of `y + [W]`, for `y` with prescribed localizations.
- `brauerLocalization_add_of_not_mem` (theorem): The localization at `v ∉ S` of `y + [W]`, for `W ≡ t ^ {c_χ}`: `ord_v(t)` times the cup symbol of `π_v`.
- `sum_finiteInvariant_eq_of_localization` (theorem): **The sum formula for `y + [W]`.** For classes `ξ_v ∈ H²(K_v, μ_n)`, a cocycle `W ≡ t ^ {c_χ}` and `y ∈ H²(G_S, 𝒪_Sˣ)` with localizations `ξ_v - W|_{K_v} - δχ_v ∪ a_v` at the places of `S`, the sum of the invariants of the `ξ_v` is `Σ_{v ∈ S} inv_v (δχ_v ∪ a_v) - Σ_{v ∉ S} ord_v(t) inv_v (δχ_v ∪ π_v)`.
- `finiteTrace_kummerCompactδ_unitsData` (theorem): **The trace of the Kummer class with compact support of a datum against a character.** For a datum `d = (t, (a_v)_{v ∈ S})` and a character `z` of `G_S` with values in `ℤ/n`,  `finiteTrace (δ_c(e(d)) ∪ χ) = Σ_{v ∈ S} inv_v (δχ_v ∪ a_v) - Σ_{v ∉ S} ord_v(t) · inv_v (δχ_v ∪ π_v)`  (read in `ℚ/ℤ`), `π_v = globalUniformizer v`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BasePairing.lean` (`zmodCocycleHom_one`) and file `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseCupLocal.lean` (the vanishing of the real invariants, killed by `2` and by `n`). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's Brauer group of `K` with its sum formula (`localInvariant_finite_support_and_sum_eq_zero`), the divisor criterion outside `S` (`brauerLocalization_maximalUnitsInflation_eq_zero_iff`) and the cup symbol `Local.characterCup` replace the source's `brauerLocal`, `placeInv` and `localInvU`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected printing (Springer, 2013), Chapter VIII, §3, Proposition (8.3.11), p. 458; Chapter VIII, §6, the explicit pairing
  `Σ_{p ∈ S} inv_p[y_p ∪ x_p - z_p]` and Proposition (8.6.8), pp. 487–488.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge, 2006), Chapter II, §2, Remark 2.2, p. 165 (the sum of the local invariants).
