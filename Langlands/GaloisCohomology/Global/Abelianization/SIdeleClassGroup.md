# The `S`-idèle class group and its narrow variant

`Langlands/GaloisCohomology/Global/Abelianization/SIdeleClassGroup.lean`, namespace
`Langlands.GaloisCohomology`.

Throughout, `K` is a number field (`K : Type u`), `I_K = Ideles K` is Mathlib's idèle group
`NumberField.IdeleGroup (𝓞 K) K` (the Library's abbreviation of the module
`Langlands.Global.Adelic`), and `S` is a set of finite places of `K`
(`Set (HeightOneSpectrum (𝓞 K))`).

**The groups.** `unitIdelesOutside S` is the subgroup `U^S` of the idèles whose component is `1` at
every place of `S` and a unit of the valuation ring at every finite place outside `S`; the
archimedean components are arbitrary. `positiveUnitIdelesOutside S` is the subgroup `U^S_+` of
those elements of `U^S` whose component at every real place is positive (`positiveIdeles K`: the
real component, read in `ℝ` by Mathlib's `InfinitePlace.Completion.ringEquivRealOfIsReal`, is
positive). The **`S`-idèle class group** is

`SIdeleClassGroup S = I_K / K^× U^S`  (`sIdeleClassSubgroup S = principalIdeles K ⊔ unitIdelesOutside S`)

and the **narrow `S`-idèle class group** is `NarrowSIdeleClassGroup S = I_K / K^× U^S_+`. Both are
`abbrev`s of quotient groups, with their quotient topologies; `SIdeleClassGroup.mk S` and
`NarrowSIdeleClassGroup.mk S` are the classes of idèles, `ofIdeleClasses S` the maps from the
idèle class group, and `NarrowSIdeleClassGroup.toSIdeleClassGroup S` the surjection from the
narrow group onto the other one. Membership in `U^S` can be read on valuations
(`mem_unitIdelesOutside_iff_valued`, from `mem_units_iff_valued_eq_one`).

In the notation of Neukirch–Schmidt–Wingberg, where `S` contains the archimedean places and
`C_S(K) = I_K / K^× U_{K,S}` with `U_{K,S}` equal to `1` at `S` and to the local units elsewhere,
`SIdeleClassGroup S` is `C_{S ∪ S_∞}(K)` divided by the image of all archimedean components, and
`NarrowSIdeleClassGroup S` is `C_{S ∪ S_∞}(K)` divided by the image of the archimedean components
that are positive at the real places, the identity component of `∏_{v | ∞} K_v^×`.

**Two facts on the idèle topology.**

* `positiveUnitIdelesOutside_le_ker`: for `n ≠ 0`, a continuous homomorphism `Λ` from the idèles to
  a discrete group in which `g ^ n = 1` for all `g`, and which kills the integral local units at
  the finite places outside `S` (inserted by `finiteIdeleInclusion`), kills `U^S_+`.
* `isOpen_of_pow_mem_of_positiveUnitIdelesOutside_le`: for finite `S` and `n ≠ 0`, a subgroup of
  the idèles that contains every `n`-th power and `U^S_+` is open.

**Parity.** The square of an element of `U^S` lies in `U^S_+` (`sq_mem_positiveUnitIdelesOutside`),
and the two groups agree when `K` has no real place (`positiveUnitIdelesOutside_eq`). Hence, if `n`
is odd or `K` is totally complex, precomposition with `toSIdeleClassGroup S` is an isomorphism
`NarrowSIdeleClassGroup.precompToSIdeleClassGroupEquiv S n h` from the homomorphisms
`SIdeleClassGroup S →* Multiplicative (ZMod n)` onto the homomorphisms from the narrow group.

## Complete types

```lean
@Langlands.GaloisCohomology.finiteIdeleProjection_finiteIdeleInclusion_of_ne : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] {v w : Langlands.Global.FinitePlace K},
  w ≠ v →
    ∀ (a : (Langlands.Global.FiniteCompletion K v)ˣ),
      (Langlands.Global.finiteIdeleProjection K w) ((Langlands.Global.finiteIdeleInclusion K v) a) = 1

@Langlands.GaloisCohomology.infiniteIdeleProjection_finiteIdeleInclusion : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] (w : Langlands.Global.InfinitePlace K)
  (v : Langlands.Global.FinitePlace K) (a : (Langlands.Global.FiniteCompletion K v)ˣ),
  (Langlands.Global.infiniteIdeleProjection K w) ((Langlands.Global.finiteIdeleInclusion K v) a) = 1

@Langlands.GaloisCohomology.finiteIdeleProjection_infiniteIdelesInclusion : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] (v : Langlands.Global.FinitePlace K)
  (z : (Langlands.Global.InfiniteAdeles K)ˣ),
  (Langlands.Global.finiteIdeleProjection K v) ((Langlands.Global.infiniteIdelesInclusion K) z) = 1

@Langlands.GaloisCohomology.infiniteIdeleProjection_infiniteIdelesInclusion : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] (w : Langlands.Global.InfinitePlace K)
  (z : (Langlands.Global.InfiniteAdeles K)ˣ),
  (Langlands.Global.infiniteIdeleProjection K w) ((Langlands.Global.infiniteIdelesInclusion K) z) =
    ContinuousMulEquiv.piUnits z w

@Langlands.GaloisCohomology.positiveIdeles : (K : Type u) → [inst : Field K] → [inst_1 : NumberField K] → Subgroup (Langlands.Global.Ideles K)

@Langlands.GaloisCohomology.mem_positiveIdeles : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] {x : Langlands.Global.Ideles K},
  x ∈ Langlands.GaloisCohomology.positiveIdeles K ↔
    ∀ (w : Langlands.Global.InfinitePlace K) (hw : NumberField.InfinitePlace.IsReal w),
      0 <
        (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
          ↑((Langlands.Global.infiniteIdeleProjection K w) x)

@Langlands.GaloisCohomology.sq_mem_positiveIdeles : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] (x : Langlands.Global.Ideles K),
  x ^ 2 ∈ Langlands.GaloisCohomology.positiveIdeles K

@Langlands.GaloisCohomology.positiveIdeles_eq_top : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] [NumberField.IsTotallyComplex K],
  Langlands.GaloisCohomology.positiveIdeles K = ⊤

@Langlands.GaloisCohomology.unitIdelesOutside : {K : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) → Subgroup (Langlands.Global.Ideles K)

@Langlands.GaloisCohomology.mem_unitIdelesOutside : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {x : Langlands.Global.Ideles K},
  x ∈ Langlands.GaloisCohomology.unitIdelesOutside S ↔
    (∀ v ∈ S, (Langlands.Global.finiteIdeleProjection K v) x = 1) ∧
      ∀ v ∉ S,
        (Langlands.Global.finiteIdeleProjection K v) x ∈
          (Submonoid.ofClass (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)).units

@Langlands.GaloisCohomology.mem_units_iff_valued_eq_one : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] {v : Langlands.Global.FinitePlace K}
  (a : (Langlands.Global.FiniteCompletion K v)ˣ),
  a ∈ (Submonoid.ofClass (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)).units ↔ Valued.v ↑a = 1

@Langlands.GaloisCohomology.mem_unitIdelesOutside_iff_valued : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {x : Langlands.Global.Ideles K},
  x ∈ Langlands.GaloisCohomology.unitIdelesOutside S ↔
    (∀ v ∈ S, (Langlands.Global.finiteIdeleProjection K v) x = 1) ∧
      ∀ v ∉ S, Valued.v ↑((Langlands.Global.finiteIdeleProjection K v) x) = 1

@Langlands.GaloisCohomology.positiveUnitIdelesOutside : {K : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) → Subgroup (Langlands.Global.Ideles K)

@Langlands.GaloisCohomology.mem_positiveUnitIdelesOutside : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {x : Langlands.Global.Ideles K},
  x ∈ Langlands.GaloisCohomology.positiveUnitIdelesOutside S ↔
    x ∈ Langlands.GaloisCohomology.unitIdelesOutside S ∧ x ∈ Langlands.GaloisCohomology.positiveIdeles K

@Langlands.GaloisCohomology.positiveUnitIdelesOutside_le_unitIdelesOutside : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
  Langlands.GaloisCohomology.positiveUnitIdelesOutside S ≤ Langlands.GaloisCohomology.unitIdelesOutside S

@Langlands.GaloisCohomology.sq_mem_positiveUnitIdelesOutside : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {x : Langlands.Global.Ideles K},
  x ∈ Langlands.GaloisCohomology.unitIdelesOutside S → x ^ 2 ∈ Langlands.GaloisCohomology.positiveUnitIdelesOutside S

@Langlands.GaloisCohomology.positiveUnitIdelesOutside_eq : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] [NumberField.IsTotallyComplex K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
  Langlands.GaloisCohomology.positiveUnitIdelesOutside S = Langlands.GaloisCohomology.unitIdelesOutside S

@Langlands.GaloisCohomology.finiteIdeleInclusion_mem_positiveUnitIdelesOutside : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {v : Langlands.Global.FinitePlace K},
  v ∉ S →
    ∀ {a : (Langlands.Global.FiniteCompletion K v)ˣ},
      a ∈ (Submonoid.ofClass (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)).units →
        (Langlands.Global.finiteIdeleInclusion K v) a ∈ Langlands.GaloisCohomology.positiveUnitIdelesOutside S

@Langlands.GaloisCohomology.sIdeleClassSubgroup : {K : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) → Subgroup (Langlands.Global.Ideles K)

@Langlands.GaloisCohomology.narrowSIdeleClassSubgroup : {K : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) → Subgroup (Langlands.Global.Ideles K)

@Langlands.GaloisCohomology.narrowSIdeleClassSubgroup_le : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
  Langlands.GaloisCohomology.narrowSIdeleClassSubgroup S ≤ Langlands.GaloisCohomology.sIdeleClassSubgroup S

@Langlands.GaloisCohomology.SIdeleClassGroup : {K : Type u} →
  [inst : Field K] → [NumberField K] → Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) → Type u

@Langlands.GaloisCohomology.NarrowSIdeleClassGroup : {K : Type u} →
  [inst : Field K] → [NumberField K] → Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) → Type u

@Langlands.GaloisCohomology.SIdeleClassGroup.mk : {K : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
        Langlands.Global.Ideles K →* Langlands.GaloisCohomology.SIdeleClassGroup S

@Langlands.GaloisCohomology.SIdeleClassGroup.mk_surjective : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
  Function.Surjective ⇑(Langlands.GaloisCohomology.SIdeleClassGroup.mk S)

@Langlands.GaloisCohomology.SIdeleClassGroup.ker_mk : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
  (Langlands.GaloisCohomology.SIdeleClassGroup.mk S).ker = Langlands.GaloisCohomology.sIdeleClassSubgroup S

@Langlands.GaloisCohomology.SIdeleClassGroup.mk_eq_one_iff : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {x : Langlands.Global.Ideles K},
  (Langlands.GaloisCohomology.SIdeleClassGroup.mk S) x = 1 ↔ x ∈ Langlands.GaloisCohomology.sIdeleClassSubgroup S

@Langlands.GaloisCohomology.SIdeleClassGroup.mk_diagonalUnits : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (a : Kˣ),
  (Langlands.GaloisCohomology.SIdeleClassGroup.mk S) ((Langlands.Global.diagonalUnits K) a) = 1

@Langlands.GaloisCohomology.SIdeleClassGroup.mk_eq_one_of_mem : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {x : Langlands.Global.Ideles K},
  x ∈ Langlands.GaloisCohomology.unitIdelesOutside S → (Langlands.GaloisCohomology.SIdeleClassGroup.mk S) x = 1

@Langlands.GaloisCohomology.SIdeleClassGroup.principalIdeles_le : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
  Langlands.Global.principalIdeles K ≤ Langlands.GaloisCohomology.sIdeleClassSubgroup S

@Langlands.GaloisCohomology.SIdeleClassGroup.ofIdeleClasses : {K : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
        Langlands.Global.IdeleClasses K →* Langlands.GaloisCohomology.SIdeleClassGroup S

@Langlands.GaloisCohomology.SIdeleClassGroup.ofIdeleClasses_ideleClassMap : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (x : Langlands.Global.Ideles K),
  (Langlands.GaloisCohomology.SIdeleClassGroup.ofIdeleClasses S) ((Langlands.Global.ideleClassMap K) x) =
    (Langlands.GaloisCohomology.SIdeleClassGroup.mk S) x

@Langlands.GaloisCohomology.SIdeleClassGroup.ofIdeleClasses_surjective : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
  Function.Surjective ⇑(Langlands.GaloisCohomology.SIdeleClassGroup.ofIdeleClasses S)

@Langlands.GaloisCohomology.SIdeleClassGroup.hom_ext : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {G : Type u_1} [inst_2 : Monoid G]
  {f g : Langlands.GaloisCohomology.SIdeleClassGroup S →* G},
  (∀ (x : Langlands.Global.Ideles K),
      f ((Langlands.GaloisCohomology.SIdeleClassGroup.mk S) x) =
        g ((Langlands.GaloisCohomology.SIdeleClassGroup.mk S) x)) →
    f = g

@Langlands.GaloisCohomology.NarrowSIdeleClassGroup.mk : {K : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
        Langlands.Global.Ideles K →* Langlands.GaloisCohomology.NarrowSIdeleClassGroup S

@Langlands.GaloisCohomology.NarrowSIdeleClassGroup.mk_surjective : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
  Function.Surjective ⇑(Langlands.GaloisCohomology.NarrowSIdeleClassGroup.mk S)

@Langlands.GaloisCohomology.NarrowSIdeleClassGroup.ker_mk : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
  (Langlands.GaloisCohomology.NarrowSIdeleClassGroup.mk S).ker = Langlands.GaloisCohomology.narrowSIdeleClassSubgroup S

@Langlands.GaloisCohomology.NarrowSIdeleClassGroup.mk_eq_one_iff : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {x : Langlands.Global.Ideles K},
  (Langlands.GaloisCohomology.NarrowSIdeleClassGroup.mk S) x = 1 ↔
    x ∈ Langlands.GaloisCohomology.narrowSIdeleClassSubgroup S

@Langlands.GaloisCohomology.NarrowSIdeleClassGroup.mk_diagonalUnits : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (a : Kˣ),
  (Langlands.GaloisCohomology.NarrowSIdeleClassGroup.mk S) ((Langlands.Global.diagonalUnits K) a) = 1

@Langlands.GaloisCohomology.NarrowSIdeleClassGroup.mk_eq_one_of_mem : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {x : Langlands.Global.Ideles K},
  x ∈ Langlands.GaloisCohomology.positiveUnitIdelesOutside S →
    (Langlands.GaloisCohomology.NarrowSIdeleClassGroup.mk S) x = 1

@Langlands.GaloisCohomology.NarrowSIdeleClassGroup.principalIdeles_le : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
  Langlands.Global.principalIdeles K ≤ Langlands.GaloisCohomology.narrowSIdeleClassSubgroup S

@Langlands.GaloisCohomology.NarrowSIdeleClassGroup.ofIdeleClasses : {K : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
        Langlands.Global.IdeleClasses K →* Langlands.GaloisCohomology.NarrowSIdeleClassGroup S

@Langlands.GaloisCohomology.NarrowSIdeleClassGroup.ofIdeleClasses_ideleClassMap : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (x : Langlands.Global.Ideles K),
  (Langlands.GaloisCohomology.NarrowSIdeleClassGroup.ofIdeleClasses S) ((Langlands.Global.ideleClassMap K) x) =
    (Langlands.GaloisCohomology.NarrowSIdeleClassGroup.mk S) x

@Langlands.GaloisCohomology.NarrowSIdeleClassGroup.ofIdeleClasses_surjective : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
  Function.Surjective ⇑(Langlands.GaloisCohomology.NarrowSIdeleClassGroup.ofIdeleClasses S)

@Langlands.GaloisCohomology.NarrowSIdeleClassGroup.hom_ext : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {G : Type u_1} [inst_2 : Monoid G]
  {f g : Langlands.GaloisCohomology.NarrowSIdeleClassGroup S →* G},
  (∀ (x : Langlands.Global.Ideles K),
      f ((Langlands.GaloisCohomology.NarrowSIdeleClassGroup.mk S) x) =
        g ((Langlands.GaloisCohomology.NarrowSIdeleClassGroup.mk S) x)) →
    f = g

@Langlands.GaloisCohomology.NarrowSIdeleClassGroup.toSIdeleClassGroup : {K : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
        Langlands.GaloisCohomology.NarrowSIdeleClassGroup S →* Langlands.GaloisCohomology.SIdeleClassGroup S

@Langlands.GaloisCohomology.NarrowSIdeleClassGroup.toSIdeleClassGroup_mk : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (x : Langlands.Global.Ideles K),
  (Langlands.GaloisCohomology.NarrowSIdeleClassGroup.toSIdeleClassGroup S)
      ((Langlands.GaloisCohomology.NarrowSIdeleClassGroup.mk S) x) =
    (Langlands.GaloisCohomology.SIdeleClassGroup.mk S) x

@Langlands.GaloisCohomology.NarrowSIdeleClassGroup.toSIdeleClassGroup_surjective : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
  Function.Surjective ⇑(Langlands.GaloisCohomology.NarrowSIdeleClassGroup.toSIdeleClassGroup S)

@Langlands.GaloisCohomology.exists_pow_eq_of_pos : ∀ {K : Type u} [inst : Field K] {w : Langlands.Global.InfinitePlace K} {n : ℕ},
  n ≠ 0 →
    ∀ (a : (Langlands.Global.InfiniteCompletion K w)ˣ),
      (∀ (hw : NumberField.InfinitePlace.IsReal w),
          0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw) ↑a) →
        ∃ b, b ^ n = a

@Langlands.GaloisCohomology.exists_pow_eq_of_infiniteIdelesInclusion_mem : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] {n : ℕ},
  n ≠ 0 →
    ∀ (z : (Langlands.Global.InfiniteAdeles K)ˣ),
      (Langlands.Global.infiniteIdelesInclusion K) z ∈ Langlands.GaloisCohomology.positiveIdeles K → ∃ y, y ^ n = z

@Langlands.GaloisCohomology.integralUnitIdeles_mem_of_isClosed : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] {H : Subgroup (Langlands.Global.Ideles K)},
  IsClosed ↑H →
    ∀ {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))},
      (∀ v ∉ S,
          ∀ (a : (↥(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v))ˣ),
            (Langlands.Global.HeckeFunctionalEquation.integralUnitIdeles K) (Pi.mulSingle v a) ∈ H) →
        ∀
          (u :
            (v : Langlands.Global.FinitePlace K) → (↥(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v))ˣ),
          (∀ v ∈ S, u v = 1) → (Langlands.Global.HeckeFunctionalEquation.integralUnitIdeles K) u ∈ H

@Langlands.GaloisCohomology.integralUnitOfMem : {K : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      {v : Langlands.Global.FinitePlace K} →
        (a : (Langlands.Global.FiniteCompletion K v)ˣ) →
          a ∈ (Submonoid.ofClass (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)).units →
            (↥(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v))ˣ

@Langlands.GaloisCohomology.exists_eq_infiniteIdelesInclusion_mul_integralUnitIdeles : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {x : Langlands.Global.Ideles K},
  x ∈ Langlands.GaloisCohomology.unitIdelesOutside S →
    ∃ u,
      (∀ v ∈ S, u v = 1) ∧
        x =
          (Langlands.Global.infiniteIdelesInclusion K) ((Langlands.Global.ideleProductEquiv K) x).1 *
            (Langlands.Global.HeckeFunctionalEquation.integralUnitIdeles K) u

@Langlands.GaloisCohomology.positiveUnitIdelesOutside_le_ker : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] {G : Type u_1} [inst_2 : Group G] [inst_3 : TopologicalSpace G]
  [DiscreteTopology G] (Λ : Langlands.Global.Ideles K →ₜ* G) {n : ℕ},
  n ≠ 0 →
    (∀ (g : G), g ^ n = 1) →
      ∀ {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))},
        (∀ v ∉ S,
            ∀ a ∈ (Submonoid.ofClass (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)).units,
              Λ ((Langlands.Global.finiteIdeleInclusion K v) a) = 1) →
          Langlands.GaloisCohomology.positiveUnitIdelesOutside S ≤ (↑Λ).ker

@Langlands.GaloisCohomology.infiniteIdeleProjection_assemble : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (m : Langlands.Global.Arithmetic.SUnitIdeleTopology.model K T) (w : Langlands.Global.InfinitePlace K),
  (Langlands.Global.infiniteIdeleProjection K w) ((Langlands.Global.Arithmetic.SUnitIdeleTopology.assemble K T) m) =
    ContinuousMulEquiv.piUnits m.1 w

@Langlands.GaloisCohomology.isOpen_of_pow_mem_of_positiveUnitIdelesOutside_le : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))},
  S.Finite →
    ∀ {n : ℕ},
      n ≠ 0 →
        ∀ (N : Subgroup (Langlands.Global.Ideles K)),
          (∀ (x : Langlands.Global.Ideles K), x ^ n ∈ N) →
            Langlands.GaloisCohomology.positiveUnitIdelesOutside S ≤ N → IsOpen ↑N

@Langlands.GaloisCohomology.eq_one_of_sq_eq_one_of_odd : ∀ {G : Type u_1} [inst : Group G] {n : ℕ}, Odd n → ∀ {g : G}, g ^ 2 = 1 → g ^ n = 1 → g = 1

@Langlands.GaloisCohomology.zmod_pow_eq_one : ∀ {n : ℕ} (z : Multiplicative (ZMod n)), z ^ n = 1

@Langlands.GaloisCohomology.NarrowSIdeleClassGroup.precompToSIdeleClassGroup : {K : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
        (n : ℕ) →
          (Langlands.GaloisCohomology.SIdeleClassGroup S →* Multiplicative (ZMod n)) →*
            Langlands.GaloisCohomology.NarrowSIdeleClassGroup S →* Multiplicative (ZMod n)

@Langlands.GaloisCohomology.NarrowSIdeleClassGroup.precompToSIdeleClassGroup_apply_mk : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ)
  (f : Langlands.GaloisCohomology.SIdeleClassGroup S →* Multiplicative (ZMod n)) (x : Langlands.Global.Ideles K),
  ((Langlands.GaloisCohomology.NarrowSIdeleClassGroup.precompToSIdeleClassGroup S n) f)
      ((Langlands.GaloisCohomology.NarrowSIdeleClassGroup.mk S) x) =
    f ((Langlands.GaloisCohomology.SIdeleClassGroup.mk S) x)

@Langlands.GaloisCohomology.NarrowSIdeleClassGroup.precompToSIdeleClassGroup_injective : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ),
  Function.Injective ⇑(Langlands.GaloisCohomology.NarrowSIdeleClassGroup.precompToSIdeleClassGroup S n)

@Langlands.GaloisCohomology.NarrowSIdeleClassGroup.precompToSIdeleClassGroup_surjective : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ),
  Odd n ∨ NumberField.IsTotallyComplex K →
    Function.Surjective ⇑(Langlands.GaloisCohomology.NarrowSIdeleClassGroup.precompToSIdeleClassGroup S n)

@Langlands.GaloisCohomology.NarrowSIdeleClassGroup.precompToSIdeleClassGroupEquiv : {K : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
        (n : ℕ) →
          Odd n ∨ NumberField.IsTotallyComplex K →
            (Langlands.GaloisCohomology.SIdeleClassGroup S →* Multiplicative (ZMod n)) ≃*
              (Langlands.GaloisCohomology.NarrowSIdeleClassGroup S →* Multiplicative (ZMod n))

@Langlands.GaloisCohomology.NarrowSIdeleClassGroup.precompToSIdeleClassGroupEquiv_apply : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ)
  (h : Odd n ∨ NumberField.IsTotallyComplex K)
  (f : Langlands.GaloisCohomology.SIdeleClassGroup S →* Multiplicative (ZMod n)),
  (Langlands.GaloisCohomology.NarrowSIdeleClassGroup.precompToSIdeleClassGroupEquiv S n h) f =
    (Langlands.GaloisCohomology.NarrowSIdeleClassGroup.precompToSIdeleClassGroup S n) f
```

## Outline of the proofs

* `positiveUnitIdelesOutside_le_ker`. An element `x` of `U^S` is its archimedean part times the
  idèle of integral units `integralUnitIdeles K u` (of the module
  `Langlands.Global.Factors.HeckeFiniteRamification`) with `u_v = 1` on `S`
  (`exists_eq_infiniteIdelesInclusion_mul_integralUnitIdeles`). If `x` is positive at the real
  places, its archimedean part is an `n`-th power (`exists_pow_eq_of_pos`: positive real roots at
  the real places, `infiniteUnitPowers_eq_top_of_isComplex` at the complex ones), so `Λ` kills it.
  The kernel of `Λ` is closed, and an idèle of integral units that is `1` on `S` lies in every
  closed subgroup containing the integral local units outside `S`
  (`integralUnitIdeles_mem_of_isClosed`): it is the limit, in the product topology of the integral
  units, of its truncations to finite sets of places. This is the argument of
  `Langlands.Global.IdeleDensity.integralUnitIdeles_mem`, there for the whole local groups.
* `isOpen_of_pow_mem_of_positiveUnitIdelesOutside_le`. Let `T` be `S` as a finite set. The set of
  idèles that are units outside `T` (open: `Arithmetic.SUnitIdeleTopology.isOpen_sUnitIdeles`),
  `n`-th powers at the places of `S` (open in each `K_v^×`:
  `Arithmetic.SUnitIdelePowerQuotient.isOpen_finite_powers`) and `n`-th powers at every
  archimedean place (`isOpen_infinite_powers`) is open and contains `1`. Each of its elements `x`
  is `y ^ n` times an element of `U^S_+`, where `y` has the chosen roots at `S` and at `∞` and is
  `1` elsewhere (built with `SUnitIdeleTopology.assemble`); so the subgroup contains a
  neighbourhood of `1`.
* Parity: for `n` odd, `ψ(u)² = ψ(u²) = 1` and `ψ(u)ⁿ = 1` give `ψ(u) = 1`
  (`eq_one_of_sq_eq_one_of_odd`).

## Declarations

In the order of the file:

- `finiteIdeleProjection_finiteIdeleInclusion_of_ne` (theorem): The component at a finite place `w` of the idèle inserted at another finite place is `1`.
- `infiniteIdeleProjection_finiteIdeleInclusion` (theorem): The archimedean components of an idèle inserted at a finite place are `1`.
- `finiteIdeleProjection_infiniteIdelesInclusion` (theorem): The finite components of an archimedean idèle are `1`.
- `infiniteIdeleProjection_infiniteIdelesInclusion` (theorem): The component at an archimedean place `w` of the archimedean idèle `z` is the component of `z` at `w`.
- `positiveIdeles` (def): The idèles whose component at every real place is positive.
- `mem_positiveIdeles` (theorem): Membership in `positiveIdeles K`.
- `sq_mem_positiveIdeles` (theorem): The square of an idèle is positive at every real place.
- `positiveIdeles_eq_top` (theorem): If `K` has no real place, every idèle is positive.
- `unitIdelesOutside` (def): The idèles whose component is `1` at every place of `S` and a unit of the valuation ring at every finite place outside `S`; the archimedean components are arbitrary.
- `mem_unitIdelesOutside` (theorem): Membership in `unitIdelesOutside S`.
- `mem_units_iff_valued_eq_one` (theorem): A unit of a finite completion is a unit of the valuation ring exactly when its valuation is `1`.
- `mem_unitIdelesOutside_iff_valued` (theorem): Membership in `unitIdelesOutside S`, read on valuations.
- `positiveUnitIdelesOutside` (def): The elements of `unitIdelesOutside S` that are positive at every real place.
- `mem_positiveUnitIdelesOutside` (theorem): Membership in `positiveUnitIdelesOutside S`.
- `positiveUnitIdelesOutside_le_unitIdelesOutside` (theorem): `U^S_+ ⊆ U^S`.
- `sq_mem_positiveUnitIdelesOutside` (theorem): The square of an element of `unitIdelesOutside S` is positive at every real place.
- `positiveUnitIdelesOutside_eq` (theorem): If `K` has no real place, the positivity condition is empty.
- `finiteIdeleInclusion_mem_positiveUnitIdelesOutside` (theorem): An integral local unit at a finite place outside `S`, inserted as an idèle, lies in `positiveUnitIdelesOutside S`.
- `sIdeleClassSubgroup` (def): The subgroup `K^× U^S` of the idèles.
- `narrowSIdeleClassSubgroup` (def): The subgroup `K^× U^S_+` of the idèles.
- `narrowSIdeleClassSubgroup_le` (theorem): `K^× U^S_+ ⊆ K^× U^S`.
- `SIdeleClassGroup` (def): The `S`-idèle class group `I_K / K^× U^S`: the idèles modulo the principal idèles and the idèles that are `1` at the places of `S`, local units at the other finite places and arbitrary at the archimedean places.
- `NarrowSIdeleClassGroup` (def): The narrow `S`-idèle class group `I_K / K^× U^S_+`: as `SIdeleClassGroup S`, with only the archimedean components positive at the real places divided out.
- `SIdeleClassGroup.mk` (def): The class of an idèle in the `S`-idèle class group.
- `SIdeleClassGroup.mk_surjective` (theorem): Every class is the class of an idèle.
- `SIdeleClassGroup.ker_mk` (theorem): The kernel of the class map.
- `SIdeleClassGroup.mk_eq_one_iff` (theorem): An idèle has trivial class exactly when it lies in the subgroup divided out.
- `SIdeleClassGroup.mk_diagonalUnits` (theorem): Principal idèles have trivial class.
- `SIdeleClassGroup.mk_eq_one_of_mem` (theorem): The idèles of the unit subgroup have trivial class.
- `SIdeleClassGroup.principalIdeles_le` (theorem): The principal idèles lie in the subgroup divided out.
- `SIdeleClassGroup.ofIdeleClasses` (def): The `S`-idèle class group as a quotient of the idèle class group.
- `SIdeleClassGroup.ofIdeleClasses_ideleClassMap` (theorem): The map from the idèle class group on classes of idèles.
- `SIdeleClassGroup.ofIdeleClasses_surjective` (theorem): The map from the idèle class group is surjective.
- `SIdeleClassGroup.hom_ext` (theorem): Two homomorphisms out of the `S`-idèle class group that agree on classes of idèles are equal.
- `NarrowSIdeleClassGroup.mk` (def): The class of an idèle in the narrow `S`-idèle class group.
- `NarrowSIdeleClassGroup.mk_surjective` (theorem): Every class is the class of an idèle.
- `NarrowSIdeleClassGroup.ker_mk` (theorem): The kernel of the class map.
- `NarrowSIdeleClassGroup.mk_eq_one_iff` (theorem): An idèle has trivial class exactly when it lies in the subgroup divided out.
- `NarrowSIdeleClassGroup.mk_diagonalUnits` (theorem): Principal idèles have trivial class.
- `NarrowSIdeleClassGroup.mk_eq_one_of_mem` (theorem): The idèles of the unit subgroup have trivial class.
- `NarrowSIdeleClassGroup.principalIdeles_le` (theorem): The principal idèles lie in the subgroup divided out.
- `NarrowSIdeleClassGroup.ofIdeleClasses` (def): The narrow `S`-idèle class group as a quotient of the idèle class group.
- `NarrowSIdeleClassGroup.ofIdeleClasses_ideleClassMap` (theorem): The map from the idèle class group on classes of idèles.
- `NarrowSIdeleClassGroup.ofIdeleClasses_surjective` (theorem): The map from the idèle class group is surjective.
- `NarrowSIdeleClassGroup.hom_ext` (theorem): Two homomorphisms out of the narrow `S`-idèle class group that agree on classes of idèles are equal.
- `NarrowSIdeleClassGroup.toSIdeleClassGroup` (def): The `S`-idèle class group as a quotient of the narrow one.
- `NarrowSIdeleClassGroup.toSIdeleClassGroup_mk` (theorem): The surjection to `SIdeleClassGroup S` on classes of idèles.
- `NarrowSIdeleClassGroup.toSIdeleClassGroup_surjective` (theorem): The map to `SIdeleClassGroup S` is surjective.
- `exists_pow_eq_of_pos` (theorem): For `n ≠ 0`, a unit of the completion at an archimedean place `w`, positive if `w` is real, is an `n`-th power.
- `exists_pow_eq_of_infiniteIdelesInclusion_mem` (theorem): For `n ≠ 0`, an archimedean idèle that is positive at every real place is the `n`-th power of an archimedean idèle.
- `integralUnitIdeles_mem_of_isClosed` (theorem): An idèle of integral units that is `1` on `S` lies in every closed subgroup of the idèles that contains the integral local units at all finite places outside `S`.
- `integralUnitOfMem` (def): An element of `(Submonoid.ofClass (v.adicCompletionIntegers K)).units` as a unit of the valuation ring.
- `exists_eq_infiniteIdelesInclusion_mul_integralUnitIdeles` (theorem): An idèle of `unitIdelesOutside S` is its archimedean part times an idèle of integral units that is `1` on `S`.
- `positiveUnitIdelesOutside_le_ker` (theorem): A continuous homomorphism from the idèles to a discrete group of exponent dividing `n ≠ 0` that kills the integral local units at the finite places outside `S` kills `positiveUnitIdelesOutside S`.
- `infiniteIdeleProjection_assemble` (theorem): An archimedean component of the idèle with prescribed archimedean part and components in the local factors of `SUnitIdeleTopology.model`.
- `isOpen_of_pow_mem_of_positiveUnitIdelesOutside_le` (theorem): For finite `S` and `n ≠ 0`, a subgroup of the idèles that contains every `n`-th power and `positiveUnitIdelesOutside S` is open: it contains the open set of the idèles that are units at the finite places outside `S` and `n`-th powers at the places of `S` and at the archimedean places.
- `eq_one_of_sq_eq_one_of_odd` (theorem): In a group in which `g ^ n = 1` for every `g`, with `n` odd, an element of order dividing `2` is `1`.
- `zmod_pow_eq_one` (theorem): Every element of `ℤ/n`, written multiplicatively, has order dividing `n`.
- `NarrowSIdeleClassGroup.precompToSIdeleClassGroup` (def): Precomposition with `toSIdeleClassGroup S`, on homomorphisms to `ℤ/n`.
- `NarrowSIdeleClassGroup.precompToSIdeleClassGroup_apply_mk` (theorem): Precomposition on classes of idèles.
- `NarrowSIdeleClassGroup.precompToSIdeleClassGroup_injective` (theorem): Precomposition with the surjection `toSIdeleClassGroup S` is injective.
- `NarrowSIdeleClassGroup.precompToSIdeleClassGroup_surjective` (theorem): If `n` is odd or `K` has no real place, every homomorphism from the narrow `S`-idèle class group to `ℤ/n` factors through the `S`-idèle class group: it kills the image of `unitIdelesOutside S`, whose squares lie in `positiveUnitIdelesOutside S`.
- `NarrowSIdeleClassGroup.precompToSIdeleClassGroupEquiv` (def): If `n` is odd or `K` has no real place, homomorphisms from the `S`-idèle class group to `ℤ/n` are the homomorphisms from the narrow `S`-idèle class group, by precomposition with `toSIdeleClassGroup S`.
- `NarrowSIdeleClassGroup.precompToSIdeleClassGroupEquiv_apply` (theorem): The isomorphism `precompToSIdeleClassGroupEquiv` is precomposition.

## Source and licence

The definitions of the groups and the parity reduction follow the repository
`leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>),
commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/ClassFieldGSDefs.lean`
(`unitsOutside`, `unitsOutsidePos`, `sIdeleSubgroup`, `sIdeleSubgroupPos`, `SIdeleClassGroup`,
`SIdeleClassGroupPos` with `mk`, `mk_surjective`, `mk_diagonal`, `mk_eq_one_of_mem`,
`toSIdeleClassGroup`), `ClassFieldGSFull.lean` (`sq_mem_unitsOutsidePos`,
`mem_unitsOutsidePos_of_isTotallyComplex`, `eq_one_of_sq_eq_one_of_odd`, `precompPos`,
`precompPos_injective`, `precompPos_surjective`, `precompPosEquiv`) and `ClassFieldGS.lean`
(`zmod_pow_eq_one`). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Changes: the groups are
defined on Mathlib's `NumberField.IdeleGroup` with the Library's projections
`finiteIdeleProjection`, `infiniteIdeleProjection` and integral units
`(Submonoid.ofClass (v.adicCompletionIntegers K)).units`, in place of the source's own idèle group
and unit levels; positivity is read through `ringEquivRealOfIsReal`; the names are new
(`unitIdelesOutside`, `positiveUnitIdelesOutside`, `NarrowSIdeleClassGroup`,
`precompToSIdeleClassGroup`). The topological lemmas (`positiveUnitIdelesOutside_le_ker`,
`isOpen_of_pow_mem_of_positiveUnitIdelesOutside_le` and the lemmas before them) are not in the
source, which obtains openness from its own conductors and congruence subgroups.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected
  printing (Springer, 2013), Chapter VIII, §3, p. 454 (the `S`-idèle group, the `S`-idèle class
  group `C_S(K) = I_K / K^× U_{K,S}`).
- J. Neukirch, *Algebraic Number Theory* (Springer, 1999), Chapter V, §1, p. 322 (in
  characteristic `0` every subgroup of finite index of `K^*` is open, with reference to Chapter
  II, (5.7)).
