# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergenceProof`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergenceProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergenceProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergenceProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Ordinary absolute convergence of the two-block Jacquet integral**

Proof of `Langlands.AllField.RankinSelberg.TwoBlockJacquetConvergenceStatement`.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergence.RadicalIwasawa`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockConvergence.uniformizerUnit_isUniformizingElement` (theorem): The canonical uniformizer is a uniformizing element of the canonical valuation.
- `Langlands.AllField.RankinSelberg.TwoBlockConvergence.exists_functional_growth` (theorem): **Growth of one inverse-character functional.** For a representation of Whittaker type
  and a functional equivariant for the inverse standard character, there is one base
  `B ≥ 1` such that every vector `v` has a constant `C` with `|ℓ(ρ(g) v)| ≤ C B^e` whenever
  `g` is bounded by `e` for the canonical uniformizer.
- `Langlands.AllField.RankinSelberg.TwoBlockConvergence.exists_blockTensor_growth` (theorem): **Growth of block-tensor contractions.** If every block functional grows at most like
  `B_i^e` on elements bounded by `e`, then every tensor `w` has a constant `C` with
  `|(ℓ_0 ⊗ ℓ_1)((τ_0 ⊗ τ_1)(b) w)| ≤ C (B_0 B_1)^e` whenever both blocks of `b` are bounded
  by `e`.
- `Langlands.AllField.RankinSelberg.TwoBlockConvergence.tensorContraction_blockTensor_twist` (theorem): The block tensor of the opposite twists is the scalar `|det b_0|^(-u) |det b_1|^u`
  times the untwisted block tensor, after contraction.
- `Langlands.AllField.RankinSelberg.TwoBlockConvergence.finite_image_sectionEval_integralOpen` (theorem): A section takes finitely many values on the compact subgroup `K₀ = GL_(t+1)(O)`.
- `Langlands.AllField.RankinSelberg.TwoBlockConvergence.exists_integral_growth` (theorem): **Uniform growth on `K₀`.** The block-tensor growth of `exists_blockTensor_growth`
  holds with one constant for all the values of a section on `K₀`.
- `Langlands.AllField.RankinSelberg.TwoBlockConvergence.norm_inv_leviHalfModulus_le_one` (theorem): If `|det b_0| = q^d` and `|det b_1| = q^(-d)`, the inverse half modulus of the upper
  block parabolic at `b` has norm at most one.
- `Langlands.AllField.RankinSelberg.TwoBlockConvergence.residue_pow_rpow_neg` (theorem): `(q^d)^(-u) = (q^(-u))^d`.
- `Langlands.AllField.RankinSelberg.TwoBlockConvergence.norm_integrand_le` (theorem): **Pointwise bound.** If `u(x) = q k` with `k ∈ K₀`, the blocks of `q` bounded by `d`,
  `|det q_0| = q^d` and `|det q_1| = q^(-d)`, and the untwisted block tensors of the values
  of `f` on `K₀` grow at most like `C B^e`, then `|f(u(x))(ℓ) ψ(x)| ≤ C (B q^(-2u))^d`.
- `Langlands.AllField.RankinSelberg.TwoBlockConvergence.integrable_integrand_one` (theorem): **Integrability at the identity.** Under the uniform growth bound on `K₀` and a lower
  Iwasawa factorization of every `u(x)` controlled by a box exponent, the integrand at the
  identity is integrable as soon as `B q^(-2u) q^(ab) < 1`.
- `Langlands.AllField.RankinSelberg.TwoBlockConvergence.exists_bound_isAbsIntegrable_of_factorization` (theorem): **Assembly.** Given the lower Iwasawa factorization of every `u(x)` controlled by a box
  exponent, there is a real bound beyond which every section of the twisted induction has an
  absolutely integrable integrand at every ambient element.
- `Langlands.AllField.RankinSelberg.twoBlockJacquetConvergence` (theorem): **JPSS 1983, Section (4.6).** Ordinary absolute convergence of the two-block Jacquet
  integral for opposite real twists `(τ_1 |det|^(-u), τ_2 |det|^u)` and all large real `u`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockConvergence.valuation_le_of_mem_levelSet`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
