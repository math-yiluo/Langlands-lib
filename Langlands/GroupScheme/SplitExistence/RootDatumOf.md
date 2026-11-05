# The root datum of the Chevalley group

Module `Langlands.GroupScheme.SplitExistence.RootDatumOf`, namespace
`Langlands.GroupScheme.SplitExistence` (the main part is in `ChevalleyData`). Internal helper of
the proof of the split reductive Existence Theorem (task 2132924b). It checks the Library's
three conditions of `IsRootDatumOf` (pairing, roots, reflections by normalizing points) for the
transport of `P` to the lattices of `D(X)`. This is derived content.

## Declarations

- `rootPairingMapEquiv P f g : RootPairing.Equiv P (P.map (Equiv.refl _) f g)`: a root pairing
  is isomorphic to its transport along linear equivalences `f` of weights and `g` of coweights.
  The weight map is `f`, the coweight map is `g⁻¹`, and the index map is the identity.
- `cocharEquiv k P : Y ≃ₗ[ℤ] cocharacterLattice (Tk k)` (`X` finite free): the identification
  dual to `charEquiv` under the perfect pairings `P` and `latticePairing (Tk k)`. The latter is
  perfect by the Library's `IsSplitTorus.isPerfPair_latticePairing`.
- `latticePairing_charOf_cocharEquiv`:
  `latticePairing (charOf x) (cocharEquiv y) = P.toLinearMap x y`.
- `chevDatum k P`: the root datum `P.map (Equiv.refl J) charEquiv cocharEquiv` on the
  character and cocharacter lattices of `D(X)`.
  - `chevDatum_root`: its roots are `charOf α_j`.
  - `chevDatum_coroot`: its coroots are `cocharEquiv α_j^∨`.
  - `chevDatum_toLinearMap`: its pairing is `latticePairing (Tk k)`.
  - `chevDatum_reflection_charOf`: its reflection `s_α` sends `charOf x` to
    `charOf (s_α x)`.
- `chevDatumEquiv k P : RootPairing.Equiv P (chevDatum k P)`, an instance of
  `rootPairingMapEquiv`.
- `ChevGroup.HasNormalizer G α`: some `k`-point `n` of `G` normalizes `t` through some
  automorphism `σ` of `D(X)` with `σ⁻¹ ≫ charOf x = charOf (s_α x)` for all `x`.
- `ChevGroup.hasNormalizer_simple`: simple roots have this property, with `n = weylPoint i`
  and `σ = torusAut s_i` (module `Normalizing`), since `s_i⁻¹ = s_i`.
- `ChevGroup.hasNormalizer_hom_comp`: the same `σ` also satisfies
  `σ ≫ charOf x = charOf (s_α x)`, because `s_α` is an involution.
- `ChevGroup.hasNormalizer_reflectionPerm_self`: the property passes from `α` to `-α`, because
  `s_{-α} = s_α`.
- `ChevGroup.hasNormalizer_reflectionPerm`: it passes from `α` to `s_j α` for a simple root
  `α_j`. Take `n_j n n_j⁻¹` (Library `IsNormalizingPoint.mul`, `IsNormalizingPoint.inv`) and
  use `s_{s_j α} = s_j s_α s_j` (Mathlib `reflection_reflectionPerm`).
- `ChevGroup.hasNormalizer` (`J` finite, `P` reduced): every root has the property, by
  Mathlib's `RootPairing.Base.induction_reflect`.
- `ChevGroup.isRootDatumOf` (`J` finite, `P` reduced, `X` finite free, `G.H` affine and locally
  of finite type): **`IsRootDatumOf G.t (chevDatum k P)`**.
  - The pairing condition is `chevDatum_toLinearMap`.
  - The root condition is `roots_t` (module `Roots`).
  - For the reflection condition, take the normalizing point given by `hasNormalizer`. Its
    action `characterAut σ` and `chevDatum.reflection α` agree on every `charOf x`, and these
    are all characters (`charEquiv` is surjective).
