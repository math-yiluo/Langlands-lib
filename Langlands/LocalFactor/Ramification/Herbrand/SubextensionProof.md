# Herbrand's theorem for finite subextensions

Lean module: `Langlands.LocalFactor.Ramification.Herbrand.SubextensionProof`
(namespace `Langlands.Ramification.HerbrandBridge`). It imports
`Langlands.LocalFactor.Ramification.Herbrand.TransportProof`,
`Langlands.ClassFieldTheory.Local.ReciprocitySystem`, `Langlands.Weil.Local.IntermediateWeil`,
`Langlands.VirtualRepresentation.Weil.Ramification` and `Mathlib.FieldTheory.Normal.Closure`.

## What the module proves

All upper groups are the Library groups `Padic.upperRamificationGroup`,
`canonicalUpperRamificationGroup`, `absoluteUpperRamificationGroup` and `upperGroupIn` (from
`TransportProof`). For `M` finite Galois over a base, `r_M` denotes
`AlgEquiv.restrictNormalHom M`.

### One finite Galois extension

Let `K → E → L` be fields with `Padic p`-algebra structures and scalar towers. Here `L` is a
p-adic field with a realization `T : L.TopologicalData`. For `σ : Gal(L.Carrier/E)`:

- `restrictScalars_mem_lowerRamificationGroupInt_iff`: `σ.restrictScalars K` lies in the
  integer lower group `Padic.lowerRamificationGroupInt T K i` if and only if `σ` lies in
  `Padic.lowerRamificationGroupInt T E i`.
- `restrictScalars_mem_upperRamificationGroup_iff` is Herbrand's subgroup formula:
  `σ.restrictScalars K ∈ Padic.upperRamificationGroup T K v` if and only if
  `σ ∈ Padic.upperRamificationGroup T E (φ_{T,E}(ψ_{T,K}(v)))`. Here `φ_{T,E}` is
  `Padic.herbrandPhi T E` and `ψ_{T,K}` is `Padic.herbrandPsi T K`. No Galois hypothesis is
  needed.
- `relativeHerbrandPsi_tower`: let `K → E → M → L` be p-adic fields with `M`, `L` Galois over
  `K` and over `E`, and `L` Galois over `M`, with realizations `S` of `M` and `T` of `L`. Then
  `φ_{T,E} ∘ ψ_{T,K} = φ_{S,E} ∘ ψ_{S,K}` at every real argument.

### Restriction and cofinality for any base and any extension

Let `K : PadicField p` and let `Ω` be a field that is a `K.Carrier`- and `Padic p`-algebra,
with the scalar tower.

- `restrictNormalHom_mem_upper_of_le`: for finite Galois subfields `N ≤ M` of `Ω` and
  `v ≥ -1`, if `r_M τ` lies in the canonical upper group of `M` of index `v`, then `r_N τ` lies
  in that of `N`.
- `mem_upperGroupIn_iff_of_cofinal`: let `P` be a property of finite Galois subfields such
  that every `N` lies in some `M` with `P M`. Then for `v ≥ -1`, `τ ∈ upperGroupIn K Ω v` if and
  only if `r_M τ` is in the canonical upper group of index `v` for every `M` with `P M`.
- `mem_absoluteUpperRamificationGroup_iff_autCongr`: for
  `e : AlgebraicClosure K.Carrier ≃ₐ[K.Carrier] Ω`,
  `τ ∈ absoluteUpperRamificationGroup K v` if and only if
  `e.autCongr τ ∈ upperGroupIn K Ω v`. This restates `TransportProof`.

### A subfield inside a fixed extension

Now let `F`, `K` be p-adic fields with an algebra `F.Carrier → K.Carrier`, and let `Ω` be an
extension of both with scalar towers `F → K → Ω`, `Padic p → F → Ω` and `Padic p → K → Ω`. Let
`M` be a finite Galois subfield of `Ω` over `F` that contains the image of `K`; the hypothesis
`h` records this.

- `extendFiniteGalois h`, a named definition, is `M` as a finite Galois subfield of `Ω` over
  `K` (`Subfield.toIntermediateField`).
- `extendFiniteGaloisEquiv h`, a named definition, is the identity of carriers, as an
  isomorphism over `F` between the two p-adic fields `finiteGaloisPadicField F M` and
  `finiteGaloisPadicField K (extendFiniteGalois h)`.
- `extension_padicScalarTower` gives the `Padic p → F` scalar tower on finite Galois subfields
  over `K`.
- `relativeIndex F M h v`, a named definition, is `φ_{M/K}(ψ_{M/F}(v))`, computed with the
  canonical realization of `M` over `K`.
- `restrictNormalHom_restrictScalars_mem_upper_iff`: for `τ : Gal(Ω/K.Carrier)`,
  `r_M (τ.restrictScalars F)` lies in the canonical upper group of `M/F` of index `v` if and
  only if the restriction of `τ` to `extendFiniteGalois h` lies in the canonical upper group
  over `K` of index `relativeIndex F M h v`.
- `relativeIndex_eq_of_le`: if `M₀ ≤ M`, then `relativeIndex F M h = relativeIndex F M₀ h₀`.
- `neg_one_le_relativeIndex`: `-1 ≤ v` implies `-1 ≤ relativeIndex F M h v`.
- `exists_le_of_finiteGalois`, assuming `Ω/F` Galois: every finite Galois subfield `N` over
  `K` lies in some finite Galois `M` over `F` containing a given `M₀`.
- `restrictScalars_mem_upperGroupIn_iff`, assuming `Ω/F` Galois, `h₀` for `M₀`, and `v ≥ -1`.
  For every `τ : Gal(Ω/K.Carrier)`, `τ.restrictScalars F ∈ upperGroupIn F Ω v` if and only if
  `τ ∈ upperGroupIn K Ω (relativeIndex F M₀ h₀ v)`.

### Finite intermediate fields of the base closure

Let `F : PadicField.{u} p` and `E : FiniteIntermediateExtension F.Carrier`, with
`E.asPadicField` its Library p-adic structure.

- `asPadicField_isScalarTower`: the `Padic p` scalar tower through `E` into
  `AlgebraicClosure F.Carrier`, for the `Padic p`-algebra of `E.asPadicField`.
- `galoisClosure E` is a named definition: the normal closure of `E.field` over `F.Carrier`, as
  a finite Galois subfield. `algebraMap_mem_galoisClosure` records that it contains `E`.
- `relativeHerbrandPsi E v` is a named definition: `ψ_{E/F}(v)`, which is `relativeIndex` for
  `galoisClosure E`. `neg_one_le_relativeHerbrandPsi` says it maps `[-1, ∞)` into itself.
- `intermediateGaloisMap_mem_absoluteUpperRamificationGroup_iff E hv τ`. For `v ≥ -1` and every
  `τ : Field.absoluteGaloisGroup E.field`, consider the Library embedding
  `Weil.Local.intermediateGaloisMap F E`. Then `intermediateGaloisMap F E τ` lies in
  `absoluteUpperRamificationGroup F v` if and only if `τ` lies in
  `absoluteUpperRamificationGroup E.asPadicField (relativeHerbrandPsi E v)`. That is,
  `G_F^v ∩ G_E = G_E^{ψ_{E/F}(v)}`.
- `intermediateWeilEquiv_mem_upperGroup_iff E hv w` is the same statement for the Library upper
  groups `LocalWeil.Ramification.upperGroup` of the local Weil groups. It holds for every `w`
  in the Weil group of `E.asPadicField`, along `Weil.Local.intermediateWeilEquiv F E`, the
  identification with its fixing subgroup.

## Sources

Jean-Pierre Serre, *Local Fields*, GTM 67, Springer (1979). Registered as
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`. Chapter IV, §3, printed
pp. 74–76 (PDF pp. 81–83):

- Proposition 15 (transitivity of `φ` and `ψ`), and with it the independence used for
  `relativeIndex_eq_of_le`.
- Remark 2 (p. 75): for a subextension `E` of a finite Galois `L/K`, Serre defines
  `φ_{E/K} = φ_{L/K} ∘ ψ_{L/E}` and notes that this is independent of `L`. Hence
  `ψ_{E/K} = φ_{L/E} ∘ ψ_{L/K}`, which is `relativeIndex` and `relativeHerbrandPsi`.
- Remark 3 (p. 76): `H(t) = H ∩ G(t)` for a subgroup `H`. This is the subgroup formula proved
  here, finite and absolute.

The intermediate-field form is the input "`β(W_i) ≤ ψ_{L_i/K}(β(W))` and
`α(χ_i) = ψ_{L_i/K}(α(V))`" of Deligne–Henniart (1981), §4.5 and §4.8 (registered as
`deligne-henniart-1981-variation`, printed pp. 110–111). The cofinality, extension and
closure-change lemmas are internal steps.

## Proof (as implemented)

1. **Subgroup formula in one field.** The integer lower group of `L` over a base is defined
   by the action on the integer ring. That action does not see the base, so
   `σ.restrictScalars K` and `σ` satisfy the same conditions (`Iff.rfl`, with `⊤` at negative
   indices). The upper group is the integer lower group of index `⌈ψ(v)⌉`
   (`upperRamificationGroup_eq_lower`). At the index `φ_{T,E}(ψ_{T,K}(v))` over `E`, we have
   `ψ_{T,E}(φ_{T,E}(u)) = u` (`herbrandPsi_herbrandPhi`), which gives the formula.
2. **Independence.** By the `TowerProof` laws `herbrandPsi_tower` (for `K → M → L`) and
   `herbrandPhi_tower` (for `E → M → L`), `φ_{T,E}(ψ_{T,K}(v))` equals
   `φ_{S,E}(φ_{T,M}(ψ_{T,M}(ψ_{S,K}(v))))`, and the middle pair cancels.
3. **Restriction between finite Galois subfields** (`restrictNormalHom_mem_upper_of_le`).
   Give `M` the `N`-algebra structure of the inclusion. Then `M/N` is Galois, and the
   `TowerProof` theorem `upperRestrictionCompatibility` says that restriction to `N` maps the
   upper group of `M` onto that of `N`. Restricting `r_M τ` to `N` gives `r_N τ`
   (`restrictNormal_commutes`, `restrictNormalHom_apply`). Cofinality follows at once.
4. **Fields over `K`.** `extendFiniteGalois h` has the same carrier as `M`. It is
   finite-dimensional and Galois over `F` exactly as `M` is (definitional on the carrier),
   hence over `K`: `Module.Finite.of_restrictScalars_finite` and
   `IsGalois.tower_top_of_isGalois`.
5. **Herbrand in `M`** (`restrictNormalHom_restrictScalars_mem_upper_iff`).
   - Conjugation by the carrier identity `extendFiniteGaloisEquiv h` carries `r_M` of
     `τ.restrictScalars F` to the restriction of scalars of the restriction of `τ` to
     `extendFiniteGalois h`. This is checked on elements.
   - `TransportProof` (`autCongr_mem_upperRamificationGroup_iff`) moves the upper-group
     condition across this identity.
   - Step 1 for the field `finiteGaloisPadicField K (extendFiniteGalois h)` over `F → K`
     finishes.
6. **Independence of `M`** (`relativeIndex_eq_of_le`). This is step 2 for the fields
   `extendFiniteGalois h₀ ⊆ extendFiniteGalois h`, which are Galois over `F` and over `K`. The
   larger is Galois over the smaller. The algebra is the inclusion.
7. **Endpoint.** `ψ` and `φ` are strictly increasing and fix `-1`
   (`herbrandPsi_neg_one`, `herbrandPhi_neg_one`).
8. **Cofinal fields** (`exists_le_of_finiteGalois`). Injectivity of `K → Ω` gives the scalar
   tower `Padic p → F → K`. So `K` and then `N` are finite over `F`. The normal closure of `N`
   over `F` in `Ω` is finite and Galois (`normalClosure.is_finiteDimensional`,
   `IsGalois.normalClosure`) and contains `N` (`AlgHom.fieldRange_le_normalClosure`). Its
   supremum with `M₀` is the required field.
9. **Main comparison** (`restrictScalars_mem_upperGroupIn_iff`). On the `F` side, membership
   is tested on the cofinal family `M₀ ≤ M`, using `N ⊔ M₀`. Let `τ` be in the `F`-side group
   and let `N` be finite Galois over `K`.
   - Step 8 gives `M ⊇ M₀` containing `N`.
   - Step 5, with step 6 rewriting the index to `relativeIndex F M₀ h₀ v`, puts the
     restriction of `τ` to `extendFiniteGalois` of `M` in the right upper group.
   - Step 3, with step 7 for `v ≥ -1`, restricts further to `N`.

   Conversely, for `M ⊇ M₀` apply the hypothesis to `extendFiniteGalois` of `M`, then step 6
   and step 5.
10. **Intermediate fields.** Write `e` for `Weil.Local.intermediateClosureEquiv F E`, from
    `AlgebraicClosure E.field` to `AlgebraicClosure F.Carrier` over `E`.
    - By `intermediateGaloisMap_apply`, `intermediateGaloisMap F E τ` is
      `(e.autCongr τ).restrictScalars F.Carrier`.
    - Step 9 applies with `K = E.asPadicField`, `Ω = AlgebraicClosure F.Carrier` and
      `M₀ = galoisClosure E`. The base closure is Galois over `F.Carrier` (characteristic zero).
    - `mem_absoluteUpperRamificationGroup_iff_autCongr` returns to the absolute group of `E`.

    For the Weil groups, `intermediateWeilEquiv_projection` is definitional and the Library
    `upperGroup` is a preimage under `localProjection`, so the Galois statement applies to
    `localProjection E.asPadicField w`.

All instance arguments for `E.asPadicField` come from the generic statements. The only extra
instance is `asPadicField_isScalarTower`, stated for the algebra of `E.asPadicField` itself.
Only the standard axioms `propext`, `Classical.choice` and `Quot.sound` are used.
