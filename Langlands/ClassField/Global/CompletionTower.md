# Completions in towers of number fields

This module collects the glue between global and local Galois theory that the reciprocity
proof for cyclic cyclotomic extensions needs (task fb66219f). The setting is a tower
`F ⊆ K ⊆ L` of number fields with finite places `v | w | u` (`LiesOver` instances). The
completions carry the Library's algebra structures given by the completion maps (scoped
instances of `Langlands.Global.AdelicFunctoriality.FiniteExtension`).

Everything is in the namespace `Langlands.ClassField.Global.CompletionTower`.

## Towers of completions

- `completionMap_comp`: `completionMap w u ∘ completionMap v w = completionMap v u`. Both are
  continuous ring maps `F_v → L_u` that agree on the dense image of `F`
  (`denseRange_algebraMap`), and `DenseRange.equalizer` concludes.
- The instance `isScalarTower_completion` gives `IsScalarTower F_v K_w L_u`. The three fields
  may lie in different universes.
- The instance `normal_completion` gives `Normal F_v K_w` when `K / F` is Galois. It comes
  from the Library's `isGalois_adicCompletion`.
- `localNorm_localNorm`: for places `p₀ | v | w` of `ℚ ⊆ F ⊆ K`, the local norms compose:
  `N_{F_v/ℚ_{p₀}} ∘ N_{K_w/F_v} = N_{K_w/ℚ_{p₀}}`. This is Mathlib's `Algebra.norm_norm`
  applied to the tower above.
- `normSymbolAt_localNorm`: the cyclotomic symbol of
  `Langlands.Global.Arithmetic.LocalNormSymbol` is compatible with local norms. For
  `b ∈ K_wˣ`, `normSymbolAt m p₀ v (N_{K_w/F_v} b) = normSymbolAt m p₀ w b`.

## Decomposition maps

Here `K / F` and `L / F` are Galois. `decompositionHom v u : Gal(L_u/F_v) → Gal(L/F)` is the
Library's map (module `Langlands.ClassField.Global.FundamentalClassStatement`).

- `decompositionHom_restrictNormal`: for `σ ∈ Gal(L_u/F_v)`, restricting
  `decompositionHom v u σ` to `K` gives `decompositionHom v w` of the restriction of `σ`
  to `K_w`. The two sides agree on `K`, as one sees by mapping into `L_u`.
- `restrictNormalHom_surjective_completion`: restriction `Gal(L_u/F_v) → Gal(K_w/F_v)` is
  surjective (Mathlib's `AlgEquiv.restrictNormalHom_surjective`).
- `unitsLocalMap_cyclicClass`: let `E / F` be Galois, `χ` a character of `Gal(E/F)` and
  `a ∈ Fˣ`. The local component `unitsLocalMap v w 2` of the global carry class
  `cyclicClass F E χ a` is the local carry class over `F_v` of the image of `a`, for the
  character `χ ∘ decompositionHom v w`. This applies `CyclicClassAlgebra.map_cyclicClass`
  with the scalar tower `F → F_v → E_w`.

## Fixed fields

Let `L / F` be Galois and let `H ≤ Gal(L/F)` be a normal subgroup. Mathlib makes the
fixed field `L^H` Galois over `F` (`IsGalois.of_fixedField_normal_subgroup`).

- `numberField_fixedField` is the instance saying `L^H` is a number field, via the Library's
  `intermediateField_numberField`.
- `fixedFieldPlace H u` is the place of `L^H` below `u`, namely `u.under (𝓞 L^H)`.
  `liesOver_fixedFieldPlace` says it lies over `v`.
- `restrictNormal_eq_one_iff`: for `σ ∈ Gal(L_u/F_v)`, the restriction of `σ` to the
  completion of `L^H` is trivial exactly when `decompositionHom v u σ ∈ H`. The proof
  combines the decomposition-map compatibility above, the injectivity of the decomposition
  map (`decompositionHom_injective`, module `Langlands.ClassField.Global.IdeleSemilocal`),
  and the Galois correspondence `fixingSubgroup (fixedField H) = H`.
- `exists_injective_factor`: let `r : G → Q` be a surjective group homomorphism, and let `θ`
  be a homomorphism with the same kernel. Then `θ = θ' ∘ r` for an injective `θ'`. The
  construction uses `QuotientGroup.kerLift` and `quotientKerEquivOfSurjective`. In the
  reciprocity proof, `r` is local restriction to the completion of a fixed field and `θ` a
  local character.

## Provenance

These are standard compatibilities between completions and decomposition groups. See
Neukirch, *Algebraic Number Theory*, Chapter II §9, before Proposition (9.6) and (9.6),
printed p.170 (PDF p.185): `G(L_w|K_v) ≅ G_w(L|K)`. The Lean statements and proofs are
internal to this formalization.
