# The slope of the relative inverse Herbrand function past the last break

Lean module: `Langlands.LocalFactor.Ramification.Herbrand.SlopeProof`
(namespace `Langlands.Ramification.HerbrandBridge`). It imports
`Langlands.LocalFactor.Ramification.Herbrand.ConvexityProof`,
`Langlands.LocalFactor.CommonClosure`, `Langlands.Galois.Local.UnramifiedCriterionProof` and
`Langlands.Weil.Local.AssemblyProof`.

## Main results

Let `F : PadicField.{u} p` and `E : FiniteIntermediateExtension F.Carrier`. Write `ψ_{E/F}` for
`relativeHerbrandPsi E` (module `SubextensionProof`), `G_F^v` for
`absoluteUpperRamificationGroup F v`, `G_E` for `E.field.fixingSubgroup`, and `I_F` for
`F.absoluteInertia F.canonicalTopologicalData`. Let `e_F` and `e_E` be the canonical
ramification indices `F.canonicalTopologicalData.ramificationIndex` and
`(canonicalData F E).ramificationIndex`. The latter is the Library's `fieldData F E`, i.e. the
canonical data of `E.asPadicField`.

- `relativeHerbrandPsi_sub_eq E hv₀ hG hs hst`. Suppose `0 ≤ v₀` and `G_F^{v₀} ≤ G_E`. Then for
  `v₀ ≤ s ≤ t`,
  `ψ_{E/F}(t) - ψ_{E/F}(s) = (e_E / e_F) · (t - s)`.
  So `ψ_{E/F}` is affine with slope `e(E/F) = e_E / e_F` on `[v₀, ∞)`.
- `relativeHerbrandPsi_sub_eq_of_upperGroup_le E hv₀ hW hs hst`: the same conclusion, stated
  with `fieldData F E`. The hypothesis is on the actual Weil groups: `upperGroup F v₀ ≤
  weilSubgroup F E`. Every element of `G_F^{v₀}` (`v₀ ≥ 0`) lies in `I_F`
  (`absoluteUpperCanonicalInertia`). So it is the projection of an element of Weil inertia
  (`localInertiaEquiv`), which lies in `upperGroup F v₀`. The hypothesis therefore gives
  `G_F^{v₀} ≤ G_E`.

## Steps

1. Ramp sums (`rampSum_sub_eq`). If two weight sequences `c, d` agree at every index
   `j > x`, then for `x ≤ y` the increments `rampSum c N y - rampSum c N x` and
   `rampSum d N y - rampSum d N x` agree. A ramp `ramp i` with `i + 1 ≤ x` equals `1` at both
   `x` and `y`.
2. Increments of Herbrand functions (`herbrandPhi_sub_eq`). This is for a finite Galois `L`
   with realization `T`, base `K` and intermediate `E`. Let `H` be the image of `Gal(L/E)`
   in `Gal(L/K)`. Suppose the real lower group `G_{u₀}` lies in `H`, with `u₀ ≥ 0`. Then
   `φ_{L/E}(y) - φ_{L/E}(x) = [G_0 : G_0 ∩ H] · (φ_{L/K}(y) - φ_{L/K}(x))` for `u₀ ≤ x ≤ y`.
   For integers `j > x` the group `G_j` lies in `G_{u₀} ≤ H`. So the lower group orders over
   `E` and over `K` agree there (`lowerGroupOrder_subfield_mul_relIndex` with relative index
   `1`). Both functions are ramp sums divided by their order at `0`
   (`herbrandPhi_eq_sum`). The two orders at `0` differ by the factor `[G_0 : G_0 ∩ H]`.
3. Slope of the relative index (`herbrandPhi_herbrandPsi_sub_eq`, `relativeIndex_sub_eq`).
   If the upper group `G^{v₀}`, which is the lower group `G_{ψ(v₀)}`, lies in `H`, then
   `φ_{L/E}(ψ_{L/K}(t)) - φ_{L/E}(ψ_{L/K}(s)) = [G_0 : G_0 ∩ H] · (t - s)` for
   `v₀ ≤ s ≤ t`. `relativeSubgroup F h` is the image of `Gal(M/K)` in `Gal(M/F)` used by
   `relativeIndex`.
4. Absolute comparison. This is generic in a p-adic field `K` inside the algebraic closure of
   `F` and a finite Galois `M ⊇ K`.
   - `absoluteRelativeRestriction F h` is restriction from the absolute Galois group to
     `Gal(M/F)`, transported to `M` viewed over `K`.
   - `autCongr_restrictNormalHom_mem_relativeSubgroup_iff` and
     `mem_comap_absoluteRelativeRestriction_iff`: an element restricts into
     `relativeSubgroup` exactly when it fixes the image of `K`.
   - `map_absoluteRelativeRestriction_upper`: `G_F^v` maps onto the upper group of `M/F`, for
     `v ≥ -1`. This uses `absoluteUpperFiniteImage` and `map_autCongr_upperRamificationGroup`.
   - `relativeIndex_sub_eq_relIndex`: if `G_F^{v₀}` fixes `K`, the slope is the index of
     `I_F ∩ G_K` in `I_F`. Here `G_K` is the preimage of `relativeSubgroup`. Inertia
     `G_0 = G^0` is the image of `I_F`, and `Subgroup.relIndex_comap` moves the index to
     the absolute group.
   - `comap_absoluteRelativeRestriction_galoisClosure` and
     `relativeHerbrandPsi_sub_eq_relIndex` specialize this to `K = E.asPadicField` and its
     Galois closure. The preimage is then `G_E`.
5. Ramification index (`relIndex_absoluteInertia_mul_of_mem_iff`,
   `fixingSubgroup_relIndex_absoluteInertia_mul`): `[I_F : I_F ∩ G_E] · e_F = e_E`.
   - The Library image `S` of `G_E` under the extension Galois map is a conjugate of `G_E`
     (`intermediateClosureCorrection_conj_mem`). Conjugation fixes the normal subgroup `I_F`,
     so `[I_F : I_F ∩ G_E] = [I_F : I_F ∩ S]`.
   - `relIndex_sup_of_normal` is a general group lemma: for normal `N`,
     `[S ⊔ N : S] = [N : N ∩ S]`. Every element of `S ⊔ N` is `n s` with `n ∈ N`, `s ∈ S`.
   - The Library gives `[G_F : S] = [E : F]` (`extensionGaloisMap_range_index`) and
     `[G_F : S ⊔ I_F] = f(E/F)` (`extensionGaloisMap_range_sup_absoluteInertia_index`).
     It also gives `e_E · f(E/F) = [E : F] · e_F`
     (`ramificationIndex_mul_extensionResidueDegree`).
   - Cancelling `f(E/F) > 0` gives the identity.

## Sources

- Deligne–Henniart (1981), §3.2, Proposition (iii), printed p. 102 (PDF p. 14). For
  `t > α(M/L)`, the slope of `ψ_{M/L}` at `t` is the ramification index `e` of `M/L`.
  DH81 defines `α(M/L)` by reference to §0.6; it vanishes exactly for tame `M/L`. The Lean
  statement does not use `α`. Its hypothesis is that `G_F^{v₀} ⊆ G_E` for some `v₀ ≥ 0`, and
  it proves that `ψ_{E/F}` is affine of slope `e(E/F)` on `[v₀, ∞)`. This is the form
  requested for the dimension-one exact case. The second assertion of (iii) (slopes `e/p^k`
  below `α`) and parts (i) and (ii) are not claimed.
- Serre, *Local Fields* IV §3. The explicit formula `φ(u) = ∫_0^u dt/(G_0 : G_t)` and its
  inverse (printed p. 73, PDF p. 80) give the slopes `|G_t|/|G_0|` of `φ`. Remark 2
  (printed p. 75, PDF p. 82) defines the relative functions `ψ_{E/F} = φ_{L/E} ∘ ψ_{L/F}`.
  The implemented proof uses these through the ramp-sum form of the Library polygons (module
  `ConvexityProof`) rather than through derivatives.

Integration uses module-specific names for local instances. Their types, values,
and local instance scopes are unchanged.
