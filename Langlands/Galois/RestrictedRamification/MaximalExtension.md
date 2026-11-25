# The maximal extension unramified outside `S` and its Galois group `G_S`

`Langlands/Galois/RestrictedRamification/MaximalExtension.lean`, namespace `Langlands.Galois`.

For a number field `K : Type u`, a field `Ω : Type v` over `K` and a set `S` of finite places of
`K`, `maximalUnramifiedOutside K Ω S` is the compositum `K_S` of the finite subextensions of
`Ω / K` that are unramified outside `S` (the real places may ramify), and
`GaloisGroupUnramifiedOutside K Ω S = Gal(K_S / K)` is `G_S`. When `Ω / K` is Galois:

- a finite subextension is unramified outside `S` if and only if it lies in `K_S`;
- `K_S / K` is Galois, so `G_S` is a profinite group (compact, Hausdorff, totally disconnected);
- for `T ⊆ S` restriction is a continuous surjection `G_S → G_T`, transitive in towers;
- restriction is a continuous surjection `Gal(Ω / K) → G_S`. For `Ω = AlgebraicClosure K`,
  `Gal(Ω / K)` is Mathlib's `Field.absoluteGaloisGroup K`; `G_S` is *not* defined as a quotient
  of it;
- if `Ω` is moreover separably closed, every finite extension `H / K` (a field of its own, not a
  subfield of `Ω`) in which the places outside `S` are unramified embeds over `K` into `K_S`
  (`nonempty_algHom_maximalUnramifiedOutside`).

```lean
noncomputable def maximalUnramifiedOutside (K : Type u) [Field K] (Ω : Type v) [Field Ω] [Algebra K Ω]
    (S : Set (HeightOneSpectrum (𝓞 K))) : IntermediateField K Ω
abbrev GaloisGroupUnramifiedOutside (K Ω) … (S) : Type v := Gal(maximalUnramifiedOutside K Ω S / K)
theorem isUnramifiedOutside_iff_le [NumberField K] [IsGalois K Ω] {E : IntermediateField K Ω}
    [FiniteDimensional K E] : IsUnramifiedOutside S E ↔ E ≤ maximalUnramifiedOutside K Ω S
instance isGalois_maximalUnramifiedOutside [NumberField K] [IsGalois K Ω] :
    IsGalois K (maximalUnramifiedOutside K Ω S)
noncomputable abbrev GaloisGroupUnramifiedOutside.profiniteGrp : ProfiniteGrp.{v}
noncomputable def GaloisGroupUnramifiedOutside.quotientMap : Gal(Ω/K) →ₜ* GaloisGroupUnramifiedOutside K Ω S
noncomputable def GaloisGroupUnramifiedOutside.restrict (Ω) {S T} (h : T ⊆ S) :
    GaloisGroupUnramifiedOutside K Ω S →ₜ* GaloisGroupUnramifiedOutside K Ω T
theorem GaloisGroupUnramifiedOutside.restrict_apply (h : T ⊆ S) (σ) (x : maximalUnramifiedOutside K Ω T) :
    ((restrict Ω h σ x : maximalUnramifiedOutside K Ω T) : Ω) =
      ((σ ⟨x, maximalUnramifiedOutside_mono K Ω h x.2⟩ : maximalUnramifiedOutside K Ω S) : Ω)
```

The embedding, with its complete type as printed by `#check` with `pp.fullNames`:

```lean
@Langlands.Galois.nonempty_algHom_maximalUnramifiedOutside : ∀ {F Ω : Type u_1} [inst : Field F]
  [NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] [IsGalois F Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) [IsSepClosed Ω] (H : Type u_2)
  [inst_6 : Field H] [NumberField H] [inst_8 : Algebra F H] [FiniteDimensional F H],
  (∀ v ∉ S, Algebra.IsUnramifiedIn (NumberField.RingOfIntegers H) v.asIdeal) →
    Nonempty (H →ₐ[F] ↥(Langlands.Galois.maximalUnramifiedOutside F Ω S))
```

## Outline of the proofs

- The family of finite subextensions unramified outside `S` is directed (it contains `⊥` and is
  stable under compositum, by `IsUnramifiedOutside.sup`), so an element of `K_S` lies in one of
  them (`mem_maximalUnramifiedOutside_iff`), and a finite set of elements of `K_S` lies in one of
  them. A finite `E ≤ K_S` is then contained in one finite subextension unramified outside `S`
  (take the elements of a basis of `E`), and a subfield of a field unramified outside `S` is
  unramified outside `S`.
- `K_S / K` is normal because a conjugate of a finite subextension unramified outside `S` is again
  one (`IsUnramifiedOutside.map`); separability is inherited from `Ω`.
- `G_S` is compact by Mathlib's instance for Galois groups of Galois extensions, Hausdorff by
  `krullTopology_t2`, totally disconnected by Mathlib's instance (Krull topology).
- `quotientMap` is Mathlib's `AlgEquiv.restrictNormalHom`, continuous by
  `InfiniteGalois.restrictNormalHom_continuous`, surjective by `AlgEquiv.restrictNormalHom_surjective`
  (`Ω / K` normal); being a continuous surjection from a compact space to a Hausdorff space it is a
  quotient map. `restrict h σ` is defined by extending `σ` to `Ω` (`lift`) and restricting to
  `K_T`; it does not depend on the extension (`restrictFun_apply`), is multiplicative, and is
  continuous because its composite with `quotientMap K Ω S` is `quotientMap K Ω T`.
- *Finite levels.* An open subgroup `U` of `G_S` contains the fixing group of a finite
  subextension `E ≤ K_S`; `E` is ramified only at finitely many places `R`, so `E ≤ K_T` for
  `T = T₁ ∪ (R ∩ S)`, and the kernel of `G_S → G_T` fixes `E`.
- *Embedding* (the base field is called `F` in the statement). Choose a `K`-embedding `φ : H → Ω`
  (`IsSepClosed.lift`) and regard `Ω` as an `H`-algebra through it. The image of `H` is the
  intermediate field `E = (⊥ : IntermediateField H Ω).restrictScalars K`; it is finite over `K` and
  unramified outside `S` (`isUnramifiedOutside_restrictScalars_iff` with `isUnramifiedOutside_bot`), so `E ≤ K_S`
  (`le_maximalUnramifiedOutside`), and `φ` factors through `K_S`.

## Declarations

- `maximalUnramifiedOutside`, `GaloisGroupUnramifiedOutside`.
- `le_maximalUnramifiedOutside`, `maximalUnramifiedOutside_mono`, `maximalUnramifiedOutside_eq_iSup`.
- With `[NumberField K] [IsGalois K Ω]`: `mem_maximalUnramifiedOutside_iff`,
  `exists_subset_of_subset_maximalUnramifiedOutside`, `isUnramifiedOutside_iff_le`,
  instance `isGalois_maximalUnramifiedOutside`.
- Namespace `GaloisGroupUnramifiedOutside`: instances `compactSpace`, `t2Space`,
  `totallyDisconnectedSpace`; `profiniteGrp K Ω S`; `quotientMap K Ω S`, `quotientMap_apply`,
  `quotientMap_surjective`, `isQuotientMap_quotientMap`; `lift σ` (a chosen extension to `Ω`) with
  `quotientMap_lift`, `lift_apply`, `lift_inv_apply`; `restrictFun`, `restrictFun_apply`,
  `restrictHom Ω h`, `restrictHom_apply`, `restrictHom_quotientMap`, `continuous_restrictHom`;
  `restrict Ω h`, `restrict_apply`, `restrict_toMonoidHom`, `restrict_quotientMap`,
  `restrict_surjective`, `restrict_restrict`, `restrict_refl`, `mem_ker_restrict`,
  `isQuotientMap_restrict`; `finite_setOf_ramified_below` (finitely many places of `K` ramify in a
  finite subextension) and `exists_finite_ker_restrict_le` (an open subgroup of `G_S` contains the
  kernel of `G_S → G_T` for a finite `T ⊆ S` containing any given finite `T₁ ⊆ S`).
- With `[NumberField F] [IsGalois F Ω] [IsSepClosed Ω]` and `F`, `Ω` in one universe:
  `nonempty_algHom_maximalUnramifiedOutside`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/MaxUnramifiedOutside.lean` (lines
28–36), `RestrictedRamification/IsUnramifiedOutsideIffLeMaxUnramifiedOutside.lean` (lines 1–103)
`PoitouTate/PoitouTateInfinite/Restrict.lean`, `PoitouTate/PoitouTateInfinite/Levels.lean`
(lines 18–80: `finite_setOf_ramified_below`, `exists_finite_ker_gsRes_le`) and
`PoitouTate/PoitouTateInfinite/LevelModulesDefs.lean` (`isQuotientMap_gsResCont`); `gsAutLift` of
`RestrictedRamification/BaseChangeMackey.lean` (lines 351–366) is `lift`. The repository has no
licence file; its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`). Changes: names (`maxUnramifiedOutside` →
`maximalUnramifiedOutside`, `galUnramifiedOutside` → `GaloisGroupUnramifiedOutside`,
`isUnramifiedOutside_iff_le_maxUnramifiedOutside` → `isUnramifiedOutside_iff_le`, `gsRes`,
`gsResCont` → `restrictHom`, `restrict`, `gsAutExtend` → `lift`, `exists_finite_ker_gsRes_le` →
`exists_finite_ker_restrict_le`; the source's `finitePlaceUnder` is Mathlib's
`HeightOneSpectrum.under`); the source's conjunction
`galUnramifiedOutside_isProfinite` is replaced by the three instances and `profiniteGrp`; the
quotient map from `Gal(Ω / K)` is a named continuous homomorphism; `K` and `Ω` may lie in different
universes. `nonempty_algHom_maximalUnramifiedOutside` is not from the source.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter VIII, §3, p. 452 (`k_S`, `G_S = G(k_S | k)`).
- J. Neukirch, *Algebraic Number Theory* (translated by N. Schappacher, Springer 1999), chapter IV,
  §1: Proposition (1.1), p. 262 (the Galois group of a Galois extension is compact Hausdorff in the
  Krull topology), Definition (1.3), p. 264 (profinite groups).
