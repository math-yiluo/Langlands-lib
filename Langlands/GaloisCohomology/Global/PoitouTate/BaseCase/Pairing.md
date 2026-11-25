# The pairing of `H_c²(G_S, μ_n)` with the characters of `G_S`

`Langlands/GaloisCohomology/Global/PoitouTate/BaseCase/Pairing.lean`, namespace `Langlands.GaloisCohomology.PoitouTate.Internal (and `Langlands.GaloisCohomology.PoitouTate` for `rootsOfUnityPairingStatement`)`.

For a number field `K`, a finite set `S` of finite places containing the places above `n` (`n` a
prime power, `n` odd or `K` totally complex), this file proves that the pairing

  `H_c²(G_S, μ_n) × H¹(G_S, ℤ/n) → ℤ/n`, `(y, χ) ↦ finiteTrace (y ∪ χ)`

has trivial kernels on both sides: `rootsOfUnityPairingStatement : RootsOfUnityPairingStatement`.

**The comparison with class field theory** (`classPairing_eq_neg`). For a `1`-cocycle `z` with values
in `ℤ/n`, let `χ_z = cocycleCharacter z` be its continuous character and
`ψ_z = continuousCharEquivSIdeleClass Ω (Set.toFinite S) hK χ_z : SIdeleClassGroup S →* ℤ/n` the
character of the `S`-idèle class group attached to it by the Library's reciprocity
(`Langlands.GaloisCohomology.Global.Abelianization`, geometric normalization: a uniformizer at
`v ∉ S` goes to a geometric Frobenius). The pairing `unitsPairing z d = finiteTrace (δ_c(e(d)) ∪ z)`
of the data depends only on the `S`-idèle class of the datum and gives `classPairing z`, and

  `classPairing z c = -(ψ_z c)` for every `c ∈ C_S`,

that is, `finiteTrace (δ_c(e(d)) ∪ z) = -ψ_z(sPresentation(a, -div t))`: the trace pairing is
**minus** the reciprocity character. At a place `v ∉ S`, the pairing at the generator `v` of the
divisors is `χ_z(σ)` for an arithmetic Artin lift `σ` of `π_v` (`unitsPairing_of_divAbove_eq_neg_single`,
`cupSymbol_eq_of_isArithmeticArtinLift`), while `ψ_z` takes the value `χ_z(σ)⁻¹` there
(`continuousCharEquivSIdeleClass_sPresentation_one_single_of_isArithmeticArtinLift`).

**The places of `S`** (`toAdd_continuousCharEquivSIdeleClass_sPresentation_mulSingle`). For `v ∈ S`,
`a ∈ K_vˣ` and an arithmetic Artin lift `σ` of `a`, `ψ_z` takes at the class of the idèle `a` at `v`
the value `-z(σ)`: the pairing of the datum `(1, a e_v)` is the cup symbol `inv_v(δχ_v ∪ a) = χ(σ)`
(`Local.invariant_characterClass_cup`), and `classPairing_eq_neg` changes the sign. So
`continuousCharEquivSIdeleClass` is the geometric normalization of reciprocity at all places.

**Kernels.** `eq_zero_of_forall_finiteTrace_compactCupRes_eq_zero_left` (a character pairing
trivially with `H_c²(G_S, μ_n)` is zero) and `eq_zero_of_forall_finiteTrace_compactCupRes_eq_zero_right`
(a class of `H_c²(G_S, μ_n)` pairing trivially with all characters is zero).

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.Internal.cocycleCharacter.{u} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {n : ℕ}
  (z : ↑(Langlands.ProfiniteCohomology.cocycles (Langlands.ProfiniteCohomology.zmodRep G n) 1)) :
  G →ₜ* Multiplicative (ZMod n)
Langlands.GaloisCohomology.PoitouTate.Internal.cocycleCharacter_apply.{u} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {n : ℕ}
  (z : ↑(Langlands.ProfiniteCohomology.cocycles (Langlands.ProfiniteCohomology.zmodRep G n) 1)) (g : G) :
  (Langlands.GaloisCohomology.PoitouTate.Internal.cocycleCharacter z) g =
    Multiplicative.ofAdd (Langlands.ProfiniteCohomology.zmodCocycleHom z g)
Langlands.GaloisCohomology.PoitouTate.Internal.cocycleOfCharacter.{u} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {n : ℕ} (χ : G →ₜ* Multiplicative (ZMod n)) :
  ↑(Langlands.ProfiniteCohomology.cocycles (Langlands.ProfiniteCohomology.zmodRep G n) 1)
Langlands.GaloisCohomology.PoitouTate.Internal.cocycleCharacter_cocycleOfCharacter.{u} {G : Type u} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ} (χ : G →ₜ* Multiplicative (ZMod n)) :
  Langlands.GaloisCohomology.PoitouTate.Internal.cocycleCharacter
      (Langlands.GaloisCohomology.PoitouTate.Internal.cocycleOfCharacter χ) =
    χ
Langlands.GaloisCohomology.PoitouTate.Internal.eq_zero_of_cocycleCharacter_eq_one.{u} {G : Type u} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}
  (z : ↑(Langlands.ProfiniteCohomology.cocycles (Langlands.ProfiniteCohomology.zmodRep G n) 1))
  (h : Langlands.GaloisCohomology.PoitouTate.Internal.cocycleCharacter z = 1) : z = 0
Langlands.GaloisCohomology.PoitouTate.Internal.finiteIdeleInclusion_mem_of_localUniformizer_mem.{u} {K : Type u}
  [Field K] [NumberField K] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {H : Subgroup (Langlands.Global.Ideles K)} (hU : Langlands.GaloisCohomology.positiveUnitIdelesOutside S ≤ H)
  {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} (hv : v ∉ S)
  (hπ : (Langlands.Global.finiteIdeleInclusion K v) (Langlands.GaloisCohomology.localUniformizer v) ∈ H)
  (a : (Langlands.Global.FiniteCompletion K v)ˣ) : (Langlands.Global.finiteIdeleInclusion K v) a ∈ H
Langlands.GaloisCohomology.PoitouTate.Internal.exists_eq_pow_of_forall_monoidHom_eq_one.{u_1} {C : Type u_1}
  [CommGroup C] {n : ℕ} [NeZero n] (c : C) (h : ∀ (f : C →* Multiplicative (ZMod n)), f c = 1) : ∃ c', c = c' ^ n
Langlands.GaloisCohomology.PoitouTate.Internal.unitsPairing.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] {n : ℕ} [NeZero n]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ NumberField.IsTotallyComplex K)
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1)) :
  Langlands.GaloisCohomology.PoitouTate.Internal.UnitsDatum Ω S →+ ZMod n
Langlands.GaloisCohomology.PoitouTate.Internal.unitsPairing_apply.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] {n : ℕ} [NeZero n]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ NumberField.IsTotallyComplex K)
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
  (d : Langlands.GaloisCohomology.PoitouTate.Internal.UnitsDatum Ω S) :
  (Langlands.GaloisCohomology.PoitouTate.Internal.unitsPairing ι S hS hK z) d =
    (Langlands.GaloisCohomology.PoitouTate.finiteTrace ι S n hK)
      (((Langlands.GaloisCohomology.compactCupRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
            (Langlands.GaloisCohomology.zmodMulPairingRight n
              (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) ⋯)
            ⋯)
          ((ModuleCat.Hom.hom (Langlands.GaloisCohomology.PoitouTate.Internal.kummerCompactδ ι n hS))
            ((Langlands.GaloisCohomology.PoitouTate.Internal.unitsData S ι) d)))
        ((CategoryTheory.ConcreteCategory.hom
            (Langlands.ProfiniteCohomology.cohomologyπ
              (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
          z))
Langlands.GaloisCohomology.PoitouTate.Internal.unitsPairing_eq_zero_of_unitsClass_eq_zero.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] {n : ℕ} [NeZero n]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ NumberField.IsTotallyComplex K)
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
  (d : Langlands.GaloisCohomology.PoitouTate.Internal.UnitsDatum Ω S)
  (h : (Langlands.GaloisCohomology.PoitouTate.Internal.unitsClass Ω S) d = 0) :
  (Langlands.GaloisCohomology.PoitouTate.Internal.unitsPairing ι S hS hK z) d = 0
Langlands.GaloisCohomology.PoitouTate.Internal.classPairing.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] {n : ℕ} [NeZero n]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ NumberField.IsTotallyComplex K)
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1)) :
  Additive (Langlands.GaloisCohomology.SIdeleClassGroup S) →+ ZMod n
Langlands.GaloisCohomology.PoitouTate.Internal.classPairing_unitsClass.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] {n : ℕ} [NeZero n]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ NumberField.IsTotallyComplex K)
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
  (d : Langlands.GaloisCohomology.PoitouTate.Internal.UnitsDatum Ω S) :
  (Langlands.GaloisCohomology.PoitouTate.Internal.classPairing ι S hS hK z)
      ((Langlands.GaloisCohomology.PoitouTate.Internal.unitsClass Ω S) d) =
    (Langlands.GaloisCohomology.PoitouTate.Internal.unitsPairing ι S hS hK z) d
Langlands.GaloisCohomology.PoitouTate.Internal.cupSymbol_one.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {n : ℕ}
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Langlands.GaloisCohomology.PoitouTate.Internal.cupSymbol ι S z v 1 = 0
Langlands.GaloisCohomology.PoitouTate.Internal.cupSymbol_eq_of_isArithmeticArtinLift.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {n : ℕ}
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (a : (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)ˣ)
  (σ :
    Gal(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
  (hσ :
    Langlands.ClassFieldTheory.Local.Artin.IsArithmeticArtinLift (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) a σ) :
  Langlands.GaloisCohomology.PoitouTate.Internal.cupSymbol ι S z v a =
    Langlands.ProfiniteCohomology.QZ.toRationalModIntegers
      ((Langlands.ProfiniteCohomology.zmodToQZ n)
        (Langlands.ProfiniteCohomology.zmodCocycleHom z ((Langlands.Galois.localizationHom ι S v) σ)))
Langlands.GaloisCohomology.PoitouTate.Internal.unitsPairing_of_divAbove_eq_neg_single.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] {n : ℕ} [NeZero n]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ NumberField.IsTotallyComplex K) (hn : IsPrimePow n)
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
  {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} (hv : v ∉ S)
  (t : Additive ↥(Langlands.GaloisCohomology.sInvariantSubgroup Ω S))
  (ht : (Langlands.GaloisCohomology.divAbove S) t = -fun₀ | ⟨v, hv⟩ => 1)
  (σ :
    Gal(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
  (hσ :
    Langlands.ClassFieldTheory.Local.Artin.IsArithmeticArtinLift (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
      (Langlands.GaloisCohomology.localUniformizer v) σ) :
  (Langlands.GaloisCohomology.PoitouTate.Internal.unitsPairing ι S hS hK z) (t, 0) =
    Langlands.ProfiniteCohomology.zmodCocycleHom z ((Langlands.Galois.localizationHom ι S v) σ)
Langlands.GaloisCohomology.PoitouTate.Internal.classPairing_eq_neg.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] {n : ℕ} [NeZero n]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ NumberField.IsTotallyComplex K) (hn : IsPrimePow n)
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
  (c : Additive (Langlands.GaloisCohomology.SIdeleClassGroup S)) :
  (Langlands.GaloisCohomology.PoitouTate.Internal.classPairing ι S hS hK z) c =
    -Multiplicative.toAdd
        (((Langlands.GaloisCohomology.continuousCharEquivSIdeleClass Ω ⋯ hK)
            (Langlands.GaloisCohomology.PoitouTate.Internal.cocycleCharacter z))
          (Additive.toMul c))
Langlands.GaloisCohomology.PoitouTate.Internal.toAdd_continuousCharEquivSIdeleClass_sPresentation_mulSingle.{u}
  {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] {n : ℕ} [NeZero n]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ NumberField.IsTotallyComplex K) (hn : IsPrimePow n)
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
  (v : ↑S) (a : (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)ˣ)
  (σ :
    Gal(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
          ↑v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v))
  (hσ :
    Langlands.ClassFieldTheory.Local.Artin.IsArithmeticArtinLift
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)) a σ) :
  Multiplicative.toAdd
      (((Langlands.GaloisCohomology.continuousCharEquivSIdeleClass Ω ⋯ hK)
          (Langlands.GaloisCohomology.PoitouTate.Internal.cocycleCharacter z))
        ((Langlands.GaloisCohomology.sPresentation S) (Pi.mulSingle v a, 1))) =
    -Langlands.ProfiniteCohomology.zmodCocycleHom z ((Langlands.Galois.localizationHom ι S ↑v) σ)
Langlands.GaloisCohomology.PoitouTate.Internal.eq_zero_of_forall_finiteTrace_compactCupRes_eq_zero_left.{u}
  {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] {n : ℕ} [NeZero n]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ NumberField.IsTotallyComplex K) (hn : IsPrimePow n)
  (x :
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
  (hx :
    ∀
      (y :
        ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
            (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) 2)),
      (Langlands.GaloisCohomology.PoitouTate.finiteTrace ι S n hK)
          (((Langlands.GaloisCohomology.compactCupRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
                (Langlands.GaloisCohomology.zmodMulPairingRight n
                  (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) ⋯)
                ⋯)
              y)
            x) =
        0) :
  x = 0
Langlands.GaloisCohomology.PoitouTate.Internal.eq_zero_of_forall_finiteTrace_compactCupRes_eq_zero_right.{u}
  {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] {n : ℕ} [NeZero n]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ NumberField.IsTotallyComplex K) (hn : IsPrimePow n)
  (y :
    ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) 2))
  (hy :
    ∀
      (x :
        ↑(Langlands.ProfiniteCohomology.cohomology
            (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1)),
      (Langlands.GaloisCohomology.PoitouTate.finiteTrace ι S n hK)
          (((Langlands.GaloisCohomology.compactCupRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
                (Langlands.GaloisCohomology.zmodMulPairingRight n
                  (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) ⋯)
                ⋯)
              y)
            x) =
        0) :
  y = 0
Langlands.GaloisCohomology.PoitouTate.rootsOfUnityPairingStatement.{u} :
  Langlands.GaloisCohomology.PoitouTate.RootsOfUnityPairingStatement
```

## Outline of the proofs

The sum `T = classPairing z + ψ_z`, read on the idèles, has a kernel which contains the `n`-th
powers and `positiveUnitIdelesOutside S` (so it is open,
`isOpen_of_pow_mem_of_positiveUnitIdelesOutside_le`, hence closed), the principal idèles
(`SIdeleClassGroup.mk_diagonalUnits`), and the local groups at the places `v ∉ S`
(`finiteIdeleInclusion_mem_of_localUniformizer_mem`: a local element is a power of
`localUniformizer v` times a unit; at the uniformizer `T` vanishes by the computation above). By the
density of the principal idèles with the local groups outside `S`
(`Langlands.Global.IdeleDensity.eq_top_of_isClosed`) the kernel is all idèles, so `T = 0`.

Left kernel: if `classPairing z = 0` then `ψ_z = 1` (`unitsClass_surjective`), so `χ_z = 1`
(`continuousCharEquivSIdeleClass` is injective) and `z = 0` (`eq_zero_of_cocycleCharacter_eq_one`).
Right kernel: write `y = δ_c(e(d))` (`surjective_kummerCompactδ`, `unitsData_surjective`); every
homomorphism `f : C_S → ℤ/n` is some `ψ_χ` (`continuousCharEquivSIdeleClass` is onto), and every
continuous `χ` is `χ_z` for a cocycle `z` (`cocycleOfCharacter`), so `f(cls d) = 1` for all `f`; by the
characters of `C_S / C_S^n` with values in `ℚ/ℤ` (`exists_eq_pow_of_forall_monoidHom_eq_one`,
`CharacterModule.exists_character_apply_ne_zero_of_ne_zero`) `cls d = c'^n`, so `d - n d'` has class
zero for a datum `d'` of class `c'`, and `y = n • δ_c(e(d')) = 0`.

## Declarations

In the order of the file:

- `cocycleCharacter` (def): The continuous character `G → ℤ/n` of a `1`-cocycle with values in `ℤ/n`.
- `cocycleCharacter_apply` (theorem).
- `cocycleOfCharacter` (def): The `1`-cocycle of a continuous character `G → ℤ/n`.
- `cocycleCharacter_cocycleOfCharacter` (theorem).
- `eq_zero_of_cocycleCharacter_eq_one` (theorem): A cocycle with trivial character is zero.
- `finiteIdeleInclusion_mem_of_localUniformizer_mem` (theorem): A subgroup of the idèles containing `positiveUnitIdelesOutside S` and the uniformizer `localUniformizer v` at a place `v ∉ S` contains the whole local group at `v`.
- `exists_eq_pow_of_forall_monoidHom_eq_one` (theorem): In a commutative group, an element on which every homomorphism to `ℤ/n` is trivial is an `n`-th power.
- `unitsPairing` (def): The pairing of the data with a character `z`: the trace of the cup product of the Kummer class with compact support of a datum with `z`.
- `unitsPairing_apply` (theorem).
- `unitsPairing_eq_zero_of_unitsClass_eq_zero` (theorem).
- `classPairing` (def): The pairing of the `S`-idèle classes with a character `z`: the pairing of any datum with the given class (`classPairing_unitsClass`).
- `classPairing_unitsClass` (theorem).
- `cupSymbol_one` (theorem): The cup symbol of the unit `1` is zero.
- `cupSymbol_eq_of_isArithmeticArtinLift` (theorem): **The cup symbol is the value of the local character at an Artin lift.**
- `unitsPairing_of_divAbove_eq_neg_single` (theorem): The pairing of a datum `(t, 1)` with `div(t) = -v`, `v ∉ S`, is the value of `z` at the localization of an Artin lift of `localUniformizer v`.
- `classPairing_eq_neg` (theorem): **The pairing is minus the character of class field theory.** For a character `z` of `G_S`, the pairing `classPairing z` of the `S`-idèle classes with `z` is minus the character `continuousCharEquivSIdeleClass χ_z` of the `S`-idèle class group.
- `toAdd_continuousCharEquivSIdeleClass_sPresentation_mulSingle` (theorem): **The reciprocity character at the places of `S`.** For `v ∈ S`, `a ∈ K_vˣ` and an arithmetic Artin lift `σ` of `a` (local class field theory), the character `ψ_z` of the `S`-idèle class group attached to `z` takes at the class of the idèle `a` at `v` the value `-z(σ)`, `σ` read in `G_S` through `localizationHom ι S v`: the character `continuousCharEquivSIdeleClass` is the geometric normalization of reciprocity at every place.
- `eq_zero_of_forall_finiteTrace_compactCupRes_eq_zero_left` (theorem): **Trivial left kernel.** A character of `G_S` with values in `ℤ/n` pairing trivially with `H_c²(G_S, μ_n)` is zero.
- `eq_zero_of_forall_finiteTrace_compactCupRes_eq_zero_right` (theorem): **Trivial right kernel.** A class of `H_c²(G_S, μ_n)` pairing trivially with all characters of `G_S` with values in `ℤ/n` is zero.
- `rootsOfUnityPairingStatement` (theorem): **The pairing `H_c²(G_S, μ_n) × H¹(G_S, ℤ/n) → ℤ/n` is perfect.**

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BasePairing.lean` (the characters of the cocycles `gsCharOfCocycle`, `eq_zero_of_gsCharOfCocycle_eq_one`, `exists_gsCharOfCocycle_eq`, the `n`-th powers `exists_nsmul_eq_of_forall_zmod` and the structure of the proofs of the two kernels). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The comparison `classPairing_eq_neg` replaces the source's computation through its own global Artin map (`charEquiv`, `gsCompactInv_gsCupClass`): it rests on the Library's `continuousCharEquivSIdeleClass`, local class field theory (`Local.invariant_characterClass_cup`) and the density of `Kˣ` with the local groups outside `S`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected printing (Springer, 2013), Chapter VIII, §3, Theorem (8.3.10), p. 458 (`C_S(k)/N C_S(K) ≅ G(K|k)^ab`); Chapter VIII,
  §6, Theorem (8.6.7), p. 485, and the explicit pairing with Proposition (8.6.8), pp. 487–488.
- J. Neukirch, *Algebraic Number Theory* (Springer, 1999), Chapter VI, Theorem (5.5) and Proposition (5.6), p. 391 (the global norm residue symbol and
  its compatibility with the local ones).
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge, 2006), Chapter I, §4, Theorem 4.10, pp. 56–57.
