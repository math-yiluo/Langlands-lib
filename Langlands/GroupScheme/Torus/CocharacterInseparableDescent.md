# Purely inseparable descent of cocharacter data

Module `Langlands.GroupScheme.Torus.CocharacterInseparableDescent`, namespace
`Langlands.GroupScheme.CocharacterDatum`. It imports Worker 1001's
`Langlands.GroupScheme.Torus.CocharacterDatum`,
`Langlands.GroupScheme.Torus.CocharacterCoefficientDescent` and
`Langlands.GroupScheme.Torus.FrobeniusTensorPower`.

Setting: `k` is a field of exponential characteristic `p`, `Z` is an affine
commutative group scheme over `Spec k`, and `Λ` is a torsion-free additive
commutative group. Points of `Z` with coefficients in a `k`-algebra `S` are
the `Lie.AffinePoints Z.toGrp S`. For a `k`-algebra map `f : S →ₐ[k] S'`,
`coeffMap f` sends points over `S[Λ]` to points over `S'[Λ]` by applying `f`
to coefficients. `IsDatum χ m x` (from `CocharacterDatum`) says that the point
`x` over `S[Λ]` is multiplicative and that the character `χ` takes the value
`X^m` on it.

## Statements

- `IsDatum.exists_of_pow_mem_range`. Fix `e : ℕ` and set `q = p ^ e`. The
  Frobenius hypothesis `hF` says: for every `k`-algebra `A` and every
  `k`-algebra map `g : A →ₐ[k] A` with `a ^ q = (g a) ^ q` for all `a : A`,
  every point `x` of `Z` over `A` satisfies `x ^ q = (g_* x) ^ q`, where
  `g_* = Lie.affineMap Z.toGrp g`. Let `F` and `L` be field extensions of `k`
  with `L` an `F`-algebra compatibly with `k`, and assume every `ℓ ^ q` with
  `ℓ : L` lies in the image of `F`. Then for every cocharacter datum `x` of
  weight `m` over `L[Λ]` for `χ`, some point `x'` over `F[Λ]` is a cocharacter
  datum for `χ` of the same weight `m`.

## Proof

1. Setup. Let `i₁, i₂ : L → L ⊗[F] L` be the two inclusions `ℓ ↦ ℓ ⊗ 1` and
   `ℓ ↦ 1 ⊗ ℓ`, and let `φ : L ⊗[F] L → L ⊗[F] L` be `a ⊗ b ↦ 1 ⊗ a b`
   (`includeRight` composed with `lmul'`). All three are `F`-algebra maps,
   restricted to `k`. Then `φ ∘ i₁ = i₂` and `φ ∘ i₂ = i₂`. Let `g` be the
   coefficient map `mapAlgHom Λ φ` of `(L ⊗[F] L)[Λ]`.
2. Frobenius identity. `ExpChar F p` follows from `ExpChar k p` because
   `k → F` is injective. `pow_eq_pow_mapAlgHom_includeRight_lmul'` (from
   `FrobeniusTensorPower`) gives `a ^ q = (g a) ^ q` for every
   `a : (L ⊗[F] L)[Λ]`.
3. The quotient. Let `v = coeffMap i₁ x * (coeffMap i₂ x)⁻¹`, a point over
   `(L ⊗[F] L)[Λ]`. By `Lie.affineMap_comp`, `g_* (coeffMap f y)` equals
   `coeffMap (φ ∘ f) y`, so step 1 gives
   `g_* v = coeffMap i₂ x * (coeffMap i₂ x)⁻¹ = 1`. By `hF` and step 2,
   `v ^ q = (g_* v) ^ q = 1`.
4. Triviality. `v` is multiplicative (`IsMult.coeff_map`, `IsMult.mul`,
   `IsMult.inv`), so `IsMult.expMap_nsmul` gives `[q]_* v = v ^ q = 1`, which
   equals `[q]_* 1`. Since `q ≠ 0` and `Λ` is torsion-free, `[q]_*` is
   injective (`expMap_nsmul_injective`), so `v = 1`. Hence
   `coeffMap i₁ x = coeffMap i₂ x`.
5. Descent of coordinates. By `coord_affineMap`, every coordinate value `c` of
   `x` (an element of `L[Λ]`) has equal images under `mapAlgHom Λ i₁` and
   `mapAlgHom Λ i₂`. Equalizer descent of coefficients
   (`exists_mapAlgHom_ofId_eq_of_includeLeft_eq_includeRight`) puts it in the
   image of `F[Λ]`.
6. Descent of the datum. Let `f : F → L` be the inclusion, as a `k`-algebra
   map. Then `mapAlgHom Λ f` is injective (`mapAlgHom_injective`). By step 5
   and `exists_affineMap_eq`, `x = coeffMap f x'` for some point `x'` over
   `F[Λ]`. Finally, `IsDatum.of_coeff_map` shows that `x'` is a datum of the
   same weight `m`.

## Provenance

This is the standard argument that a homomorphism from a diagonalizable group
is defined over `F` once it is defined over a purely inseparable extension
`L` of exponent `e`, here phrased through the equalizer `L ⇉ L ⊗[F] L`. The
statement, hypotheses and route were specified by Worker 1001 for torus
cocharacter detection (task 6d0882ee); the Lean code uses their
`CocharacterDatum` API. It is a derived internal step, not quoted from a
source. Worker 1001 applies it with `F` the separable closure of `k` in a
finite extension `L` of `k`, and proves the Frobenius hypothesis `hF` from a
splitting of `Z` over a field extension.
