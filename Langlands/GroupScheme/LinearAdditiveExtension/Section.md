# The homomorphic section determined by a corrected crossed homomorphism

Module `Langlands.GroupScheme.LinearAdditiveExtension.Section`, namespace
`Langlands.GroupScheme.LinearAdditiveExtension`.

The setting is that of `Correction`. A morphism `c : E ⟶ 𝔾ₐ` satisfies `hc₁`,
`c(g h) = c(g) + χ(q g) c(h)`, and `hc₂`, `c(ι u) = a(u)`, on every test scheme. The subgroup
`a` is closed.

- `cd_one_comp`: `c(1) = 0`.
- `eq_of_cd_eq_zero`: two points with the same image in `D` on which `c` vanishes are equal.
  Their quotient is a kernel point `u` with `χ(q g) a(u) = 0`. Since `χ(q g)` is a unit,
  `a(u) = 0`. A closed immersion is a monomorphism, so `u = 1`.

`exists_section` assumes also `hlin`, that `q` is quasi-compact, flat and surjective, and
`hc₃`: every value of `c` lies in the range of `a`. It concludes that `q` has a homomorphic
section. The proof:

1. By `hc₃` at the universal point, `c = c₀ ≫ a` for some `c₀ : E ⟶ kernel q`.
2. Let `w = (b(q⁻¹, c₀))⁻¹ : E ⟶ kernel q` and `σ = 𝟙 · (w ≫ ι) : E ⟶ E`. So
   `σ(g) = g · ι(b(q(g)⁻¹, c₀(g))⁻¹)`. Then `σ ≫ q = q`. By `hc₁`, `hc₂` and `hlin`,
   `c(σ(g)) = c(g) − χ(q g) χ(q g)⁻¹ c(g) = 0` for every point `g`.
3. By uniqueness, `σ` is invariant under right translation by the kernel, so it descends
   (`descend`) to `s : D ⟶ E` with `q ≫ s = σ`. Cancelling the epimorphism `q` gives
   `s ≫ q = 𝟙`.
4. `s` preserves the unit and multiplication. After cancelling `q` (respectively `q ⊗ q`), both
   sides are points with the same image in `D` on which `c` vanishes. For products this uses
   `hc₁`. Uniqueness gives equality. Mathlib's `Grp.homMk''` packages `s` as a homomorphism of
   group schemes, which is a section of `q`.
