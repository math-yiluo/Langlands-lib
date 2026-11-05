# An equivariant additive function on an extension by a closed additive subgroup

Module `Langlands.GroupScheme.LinearAdditiveExtension.EquivariantFunction`, namespace
`Langlands.GroupScheme.LinearAdditiveExtension`.

Setting: `k` is a field and `D = D(Λ)` is the diagonalizable group of an additive commutative
group `Λ`. `q : E ⟶ D` is a homomorphism of group schemes over `Spec k`, with full actual kernel
`kernel q` and inclusion `ι = kernelι q`. `a : kernel q ⟶ 𝔾ₐ` is a homomorphism, and `χ` is a
character of `D`. The main result `exists_equivariant` assumes that `E` is affine over `Spec k`
and that `q` is flat and surjective. It produces a function `fE : E ⟶ 𝔾ₐ` such that, on every
test scheme `T`, for all points `g` of `E` and `u` of the kernel,

`f(g · ι(u)) = f(g) + χ(q(g)) · a(u)`.

In Milne's language this is a scheme section of the pushout of the extension along `a`. That
pushout is a `𝔾ₐ`-torsor over the affine scheme `D`, and such torsors are trivial; compare the
torsor arguments in Milne, *Algebraic Groups* (2022), §15h (proofs of 15.25 and 15.27). The Lean
proof is internal and constructs no pushout. It applies the Library's degree-one Amitsur
exactness for faithfully flat covers, `AffineAdditiveCocycle.AddCocycle.exists_coboundary`.

## Coordinates

- `cd v` is the coordinate in `Γ(T)` of a point `v` of `𝔾ₐ` on a test scheme `T`, from the
  published `AdditiveGroupQuotient.coord`.
- Its lemmas are `cd_comp` (naturality), `cd_mul`, `cd_one` and `cd_inv` (additivity),
  `cd_injective` and `cd_ofCoord`.
- `cd_act`: the action `VectorGroup.weightAction χ` multiplies `cd` by
  `VectorGroup.charValue χ`.
- `charValue_mul_inv` and `charValue_pow` are multiplicativity facts for `charValue`.

## Points of the extension

- `chi q χ g` is `charValue χ T (g ≫ q)`, the value of `χ ∘ q` at a point `g` of `E`. Its lemmas
  are `chi_mul`, `chi_one`, `chi_mul_inv` and `chi_comp`.
- `kernel_comp_q`, `mul_kernel_comp_q` and `chi_mul_kernel`: kernel points map to `1` in `D`,
  so right translation by them preserves `q` and `chi`.
- `kpt q g g' h` is the kernel point `g⁻¹ g'` of two points with the same image (hypothesis
  `h`). It is obtained through the published `kernelPointsEquiv`. `kpt_comp` gives its image in
  `E`, and `eq_kpt` characterizes it, since `ι` is a monomorphism.
- `pairValue q a χ g g' h = χ(q(g)) · a(g⁻¹ g')`, with `pairValue_congr`, `pairValue_comp`
  (naturality) and `pairValue_trans`. The last is the cocycle identity, because
  `a(g⁻¹ g'') = a(g⁻¹ g') + a(g'⁻¹ g'')` and `χ(q(g)) = χ(q(g'))`.

## The cocycle on the cover

- `cover q` is `E` as a scheme over the underlying scheme of `D`, via `q`.
- `lowerObj`, `lowerPt` and `lowerHom` view schemes and points over `D` as schemes and points
  over `Spec k`. `lowerPt_comp_q` says that two points of the cover have the same image in `D`.
- `cocycle q a χ : AddCocycle (cover q)` is `pairValue` on pairs of points of the cover. Its
  naturality and cocycle laws are `pairValue_comp` and `pairValue_trans`.

## The equivariant function

`exists_equivariant` applies `exists_coboundary`. Its hypotheses hold: `D` and `E` are affine,
and `q` is flat and surjective. This gives `β ∈ Γ(E)` with
`cocycle(x, y) = x^*β − y^*β`. The function is `fE := ofCoord (−β)`. For a test point `g` and
a kernel point `u`, the proof evaluates the coboundary formula on the pair
`(g, g · ι(u))` over `D`. The lowered scheme has the same underlying scheme as `T`, so the
comparison map `e` is the identity on underlying schemes. The kernel point of the pair is `u`
itself.
