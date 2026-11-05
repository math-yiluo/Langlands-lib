# Proof: the rational norm kernel of a local-field torus is compact

Author: Worker 1505.

`Langlands.Plancherel.torusNormKernelCompactness` proves the published
proposition `Langlands.Plancherel.TorusNormKernelCompactnessStatement.{u}` of
[TorusNormKernelCompactnessStatement](TorusNormKernelCompactnessStatement.md),
for every universe `u` and both characteristics. Let `F` be a nonarchimedean
local field and `T` an actual group scheme over `Spec F` with
`IsAffineHom T.X.hom`, `LocallyOfFiniteType T.X.hom` and `IsTorus T`. Then
`rationalCommonNormKernel T` is compact in `rationalPointTopology F T.X`.
The hypotheses of the statement are unchanged. The subgroup is the actual
common kernel of the normalized absolute values of all actual `F`-rational
characters.

## Route

The proof does not split `T` into anisotropic and split parts as Renard does.
It argues with norms from a splitting field:

1. **Finite splitting.** The published `torusFiniteGaloisSplitting` gives a
   finite (Galois) extension `E / F` and an isomorphism
   `e : T_E ≅ splitTorus (Spec E) I`, with `I` finite. Only finiteness of
   `E / F` is used afterwards. `E` gets the module topology over `F`, which
   makes it a topological ring.
2. **Norm characters.** For each `i`, the split coordinate character
   `splitCharacter e i` of `T_E` gives the actual rational character
   `normCharacter (splitCharacter e i)` of `T` over `F`, from
   [NormCharacter](TorusNormKernel/NormCharacter.md). By `normCharacter_eval`,
   its value at `t ∈ T(F)` is `Algebra.norm F (χ_i(t_E))`, where
   `t_E = rationalExtend F E T t`. For `t` in the common norm kernel this value
   has unit valuation (`valuation_eval_of_mem`, through the published
   `fieldNormUnits_ker`). So the coordinates `χ_i(t_E)` lie in
   `KU = {u : Eˣ | v(Algebra.norm F u) = 1}`.
3. **Compactness in `E`.** `KU` is compact (`isCompact_units_valuation_norm_eq_one`).
   This is [FieldNormCompact](TorusNormKernel/FieldNormCompact.md) applied with
   the Library's canonical complete normed structure
   `Langlands.LocalGalois.localNormedField F`. Its topology is the given one,
   and norm one is unit valuation (`localNorm_eq_one_iff`, from the published
   `localNormedField_le`). `F` is proper because it is locally compact.
4. **Regular functions.** Fix a global section `f` of `T`, and let `f_E` be its
   pullback to `T_E`. By [SplitCoordinates](TorusNormKernel/SplitCoordinates.md)
   there is a continuous `Φ : (I → Eˣ) → E` with
   `f_E(s) = Φ(χ_i(s))_i` at every rational point `s` of `T_E`.
   `rationalPointAlgebraHom_rationalExtend` shows that `f_E(t_E)` is the image
   of `f(t)` under `F → E`. Its proof uses the published `rationalExtend_fst`
   and `Scheme.ΓSpecIso_naturality`. Hence, for `t` in the kernel, `f(t)` lies
   in the preimage under `F → E` of the compact set `Φ(KU^I)`.
5. **Boundedness and compactness.** That preimage is compact, since `F → E` is
   an injective linear map from a finite-dimensional space, hence a closed
   embedding (`isCompact_preimage_algebraMap`). Compact subsets of `F` are
   valuatively bounded by a nonzero element (`exists_vle_of_isCompact`). So the
   kernel is algebraically bounded in the Library's sense. It is closed (the
   published `isClosed_rationalCommonNormKernel`), and the published
   `localFieldAffineBoundedCompactness_proof` makes closed algebraically
   bounded sets of finite-type affine points compact.

The normed-field structure on `F` is installed only inside the small lemmas
`localNorm_eq_one_iff`, `isCompact_units_valuation_norm_eq_one`,
`exists_vle_of_isCompact` and `isCompact_preimage_algebraMap`. The main theorem
works with the given field, valuation and topology instances throughout.

## Provenance

This proves the torus case of Renard, *Représentations des groupes réductifs
p-adiques* (2026), V.2.6, Proposition, printed p.108 (PDF p.114), as recorded
on the statement page. The implemented route differs from Renard's: it uses
the norm characters `N_{E/F} ∘ χ` from a finite splitting field instead of the
anisotropic/split decomposition. All structural inputs are published Library
results: the finite Galois splitting of tori, the Weil restriction of `𝔾ₘ` with
its norm, the point-topology comparisons, and the local-field bounded
compactness criterion.
