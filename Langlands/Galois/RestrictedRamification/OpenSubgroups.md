# Open subgroups of `G_S` and finite subextensions of `K_S`

`Langlands/Galois/RestrictedRamification/OpenSubgroups.lean`, namespace `Langlands.Galois`.

Let `K` be a number field, `Ω / K` Galois, `S` a set of finite places of `K` and `L` a number field
with `K → L → Ω` (a scalar tower) whose image lies in `K_S`. Then:

- `L / K` is unramified outside `S`, and `K_S` is also the maximal extension of `L` in `Ω`
  unramified outside the places `S_L = finitePlacesAbove L S` of `L` above `S`
  (`restrictScalars_maximalUnramifiedOutside`);
- the subgroup of `G_S(K)` fixing `L` is open, and as a topological group it is `G_{S_L}(L)`
  (`fixingOpenSubgroupEquiv`), i.e. Neukirch–Schmidt–Wingberg's `G_S(L) = G(k_S | L)`;
- every open subgroup of `G_S(K)` is the subgroup fixing some finite subextension of `Ω / K` lying
  in `K_S` (`exists_fixingOpenSubgroup_eq`).

```lean
theorem restrictScalars_maximalUnramifiedOutside (S)
    (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) :
    (maximalUnramifiedOutside L Ω (finitePlacesAbove L S)).restrictScalars K = maximalUnramifiedOutside K Ω S
def GaloisGroupUnramifiedOutside.fixingOpenSubgroup (S) (hL) : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S)
theorem GaloisGroupUnramifiedOutside.mem_fixingOpenSubgroup_iff (σ : GaloisGroupUnramifiedOutside K Ω S) :
    σ ∈ fixingOpenSubgroup S hL ↔
      ∀ x : L, σ (embeddingMaximalUnramifiedOutside hL x) = embeddingMaximalUnramifiedOutside hL x
def GaloisGroupUnramifiedOutside.fixingOpenSubgroupEquiv (S) (hL) :
    (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) ≃ₜ*
      GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S)
theorem GaloisGroupUnramifiedOutside.exists_fixingOpenSubgroup_eq
    (U : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S)) :
    ∃ (L : IntermediateField K Ω) (_ : NumberField L)
      (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S), fixingOpenSubgroup S hL = U
```

(Variables: `K L Ω : Type*`, `[NumberField K] [NumberField L] [Algebra K L] [Algebra K Ω]
[Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]`.)

## Outline of the proofs

- *Abstract part.* If `E'.restrictScalars F = E` for intermediate fields `E` of `Ω / F` and `E'` of
  `Ω / L`, the identity of the common underlying set is an `F`-isomorphism `E ≃ₐ[F] E'`, and an
  element of `Gal(E / F)` fixing the image of `L` is the same as an element of `Gal(E' / L)`
  (`fixingMulEquivOfRestrictScalarsEq`). The inverse map is continuous: an open neighbourhood of
  `1` fixes a finite `K' ≤ E`; the `L`-span of a basis of `K'` in `E'` is finite over `L`.
- *`K_S` over `L`.* `L` lies in a finite subextension unramified outside `S`
  (`exists_le_of_algebraMap_mem`), hence is unramified outside `S`. A finite extension `M` of `L` in
  `Ω` is unramified outside `S_L` over `L` if and only if it is unramified outside `S` over `K`
  (`isUnramifiedOutside_restrictScalars_iff`); conversely, a finite subextension `E` of `Ω / K`
  unramified outside `S` lies in the compositum of `E` with a field containing `L`, which is a
  finite extension of `L` unramified outside `S_L`.
- *The equivalence.* A continuous bijective homomorphism from the compact `G_{S_L}(L)` to the
  Hausdorff open subgroup is a homeomorphism (`Continuous.homeoOfEquivCompactToT2`).
- *Every open subgroup.* An open subgroup `U` of `G_S` is closed; by infinite Galois theory it is
  the fixing group of its fixed field `E ≤ K_S`, which is finite over `K` because `U` is open
  (`InfiniteGalois.isOpen_iff_finite`). Take `L` the image of `E` in `Ω`.

## Declarations

- Abstract part (any tower `F → L → Ω`, `h : E'.restrictScalars F = E`):
  `mem_of_restrictScalars_eq`, `mem_of_restrictScalars_eq'`, `fieldEquivOfRestrictScalarsEq` with
  `coe_fieldEquivOfRestrictScalarsEq`, `coe_fieldEquivOfRestrictScalarsEq_symm`;
  `embeddingOfRestrictScalarsEq` with `coe_embeddingOfRestrictScalarsEq`,
  `fieldEquivOfRestrictScalarsEq_embedding`; `fixingOfRestrictScalarsEq`,
  `mem_fixingOfRestrictScalarsEq_iff`; `autOfRestrictScalarsEq`, `autOfRestrictScalarsEqInv`,
  `autOfRestrictScalarsEqInv_mem`, `fixingMulEquivOfRestrictScalarsEq` with
  `coe_fixingMulEquivOfRestrictScalarsEq_apply`, `fieldEquivOfRestrictScalarsEq_apply_apply`,
  `coe_fixingMulEquivOfRestrictScalarsEq_symm_apply`,
  `continuous_coe_fixingMulEquivOfRestrictScalarsEq_symm`.
- Number fields: `exists_le_of_algebraMap_mem`, `isUnramifiedIn_of_algebraMap_mem`,
  `restrictScalars_maximalUnramifiedOutside`, `maximalUnramifiedOutsideEquiv hL :
  maximalUnramifiedOutside K Ω S ≃ₐ[K] maximalUnramifiedOutside L Ω (finitePlacesAbove L S)`,
  `embeddingMaximalUnramifiedOutside hL : L →ₐ[K] maximalUnramifiedOutside K Ω S`, instance
  `finiteDimensional_fieldRange_embeddingMaximalUnramifiedOutside`.
- Namespace `GaloisGroupUnramifiedOutside`: `fixingOpenSubgroup`, `coe_fixingOpenSubgroup`,
  `mem_fixingOpenSubgroup_iff`, `fixingOpenSubgroupEquiv`, `fixingOpenSubgroupEquiv_toMulEquiv`,
  `coe_fixingOpenSubgroupEquiv_apply`, `maximalUnramifiedOutsideEquiv_apply_apply`,
  `coe_fixingOpenSubgroupEquiv_symm_apply`, `mem_fixingOpenSubgroup_iff_of_image`,
  `exists_fixingOpenSubgroup_eq`.

- `exists_embeddingMaximalUnramifiedOutside_eq S hL x hx`: an element of `K_S` fixed by the subgroup
  fixing a finite extension `L ⊆ K_S` lies in `L` (infinite Galois correspondence,
  `InfiniteGalois.fixedField_fixingSubgroup`).
- The quotient by a normal open subgroup. For `L ⊆ K_S` finite over `K` (`hL`):
  `coe_fixingOpenSubgroup_eq_fixingSubgroup`; if the subgroup `P` of `G_S` fixing `L` is normal,
  `L / K` is Galois (`isGalois_of_fixingOpenSubgroup_normal`); for `L / K` Galois, restriction to `L`
  is a surjective homomorphism `galRestrict hL : G_S →* Gal(L/K)` (`galRestrict_apply`,
  `algebraMap_galRestrict_apply`, `galRestrict_surjective`) with kernel `P` (`mem_ker_galRestrict_iff`,
  `ker_galRestrict`); for `P` normal, `quotientGalEquiv hL : G_S ⧸ P ≃* Gal(L/K)`
  (`quotientGalEquiv_mk`) and `card_gal_eq_index : Nat.card Gal(L/K) = [G_S : P]`. The names
  `galRestrict`, `galRestrict_apply`, `algebraMap_galRestrict_apply` are also those of Mathlib's
  restriction to rings of integers (root namespace); files that open `Langlands.Galois` write
  `Galois.galRestrict` for these.

Complete types of these, as printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.Galois.exists_embeddingMaximalUnramifiedOutside_eq.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  {L : IntermediateField K Ω} [NumberField ↥L]
  (hL : ∀ (x : ↥L), (Algebra.algebraMap (↥L) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (x : ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
  (hx : ∀ σ ∈ Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL, σ x = x) :
  ∃ y, (Langlands.Galois.embeddingMaximalUnramifiedOutside hL) y = x
Langlands.Galois.coe_fixingOpenSubgroup_eq_fixingSubgroup.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {L : Type u} [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) :
  ↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL) =
    (Langlands.Galois.embeddingMaximalUnramifiedOutside hL).fieldRange.fixingSubgroup
Langlands.Galois.isGalois_of_fixingOpenSubgroup_normal.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {L : Type u} [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (hN : (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).Normal) : IsGalois K L
Langlands.Galois.galRestrict.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {L : Type u} [Field L] [NumberField L]
  [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) [IsGalois K L] :
  Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S →* Gal(L/K)
Langlands.Galois.galRestrict_apply.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {L : Type u}
  [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) [IsGalois K L]
  (σ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) (x : L) :
  (Langlands.Galois.embeddingMaximalUnramifiedOutside hL) (((Langlands.Galois.galRestrict hL) σ) x) =
    σ ((Langlands.Galois.embeddingMaximalUnramifiedOutside hL) x)
Langlands.Galois.algebraMap_galRestrict_apply.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {L : Type u}
  [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) [IsGalois K L]
  (σ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) (x : L) :
  (Algebra.algebraMap L Ω) (((Langlands.Galois.galRestrict hL) σ) x) =
    ↑(σ ((Langlands.Galois.embeddingMaximalUnramifiedOutside hL) x))
Langlands.Galois.galRestrict_surjective.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {L : Type u}
  [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) [IsGalois K L] :
  Function.Surjective ⇑(Langlands.Galois.galRestrict hL)
Langlands.Galois.mem_ker_galRestrict_iff.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {L : Type u}
  [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) [IsGalois K L]
  (σ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) :
  σ ∈ (Langlands.Galois.galRestrict hL).ker ↔ σ ∈ Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL
Langlands.Galois.ker_galRestrict.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {L : Type u} [Field L] [NumberField L]
  [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) [IsGalois K L] :
  (Langlands.Galois.galRestrict hL).ker = ↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
Langlands.Galois.quotientGalEquiv.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {L : Type u}
  [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) [IsGalois K L]
  [(↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).Normal] :
  Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S ⧸
      ↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL) ≃*
    Gal(L/K)
Langlands.Galois.quotientGalEquiv_mk.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {L : Type u}
  [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) [IsGalois K L]
  [(↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).Normal]
  (σ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) :
  (Langlands.Galois.quotientGalEquiv hL) ↑σ = (Langlands.Galois.galRestrict hL) σ
Langlands.Galois.card_gal_eq_index.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {L : Type u}
  [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) [IsGalois K L]
  [(↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).Normal] :
  Nat.card Gal(L/K) = (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).index
```

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseChangeDefs.lean` (all but
`isUnramifiedOutside_restrictScalars_iff_of_isUnramifiedIn`, which is in `Unramified.lean`) and
`RestrictedRamification/FiniteOpen.lean` (lines 47–113). The repository has no licence file; its
text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`). Changes: `gsFieldEquiv` → `maximalUnramifiedOutsideEquiv`,
`gsEmbedding` → `embeddingMaximalUnramifiedOutside`, `gsOpenSubgroup` → `fixingOpenSubgroup`,
`gsBaseChange` → `fixingOpenSubgroupEquiv`, `exists_gsOpenSubgroup_eq` →
`exists_fixingOpenSubgroup_eq`; the source stated the last theorem for `K : FiniteSubfield`
(subfields of `AlgebraicClosure ℚ`) with `L` again a `FiniteSubfield`; here `K` is any number
field, `Ω / K` any Galois extension and `L` an intermediate field of `Ω / K`. The source's version
of `restrictScalars_maximalUnramifiedOutside` for an intermediate field `L` is the special case
`algebraMap L Ω x = x`. `card_gal_eq_index` is from the source's
`Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/GaloisCohomologyRatios/PFinite.lean`
(lines 38–43); `exists_embeddingMaximalUnramifiedOutside_eq` and the other declarations on the quotient
by a normal open subgroup contain no text of the source.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter VIII, §3, p. 452 (`G_S(K) = G(k_S | K)` for a finite
  subextension `K` of `k_S`, with `S` standing for the primes of `K` above `S`).
- J. Neukirch, *Algebraic Number Theory* (translated by N. Schappacher, Springer 1999), chapter IV,
  §1, Theorem (1.2), p. 263 (closed subgroups correspond to subextensions, open subgroups to finite
  subextensions).
