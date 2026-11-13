# Proof of Deligne--Henniart wild virtual stability

Lean module: `Langlands.LocalFactor.DeligneHenniartVirtualStabilityProof`.

## Target

`virtualStabilityProof : VirtualStabilityStatement.{uF, uV}` proves the Library
proposition `Langlands.LocalFactor.NonabelianSystem.DeligneHenniart.VirtualStabilityStatement`
(module `Langlands.LocalFactor.DeligneHenniartStatement`) with no further hypotheses.
Its type is exactly that proposition, at arbitrary universes `uF` (the field) and `uV`
(the representations).

The proposition is Deligne--Henniart, *Sur la variation, par torsion, des constantes
locales d'équations fonctionnelles de fonctions L*, Invent. Math. 64 (1981), Theorem 4.6
(printed p. 110) with its uniqueness coset `U(α(V)/2)`, its compatibility with the
witness of Theorem 4.2 modulo `U(1)`, the uniqueness of that witness modulo `U(1)`, and
the valuation (4.2.2) (printed p. 108). For every prime `p`, `p`-adic field `F`,
reciprocity family `e` and local-constant assignment `ε` forming a system
(`IsSystem F e ε`), every additive character `ψ` of the bottom field `K`, and every virtual
representation `v` of the Weil group with nonempty break support all of whose breaks are
positive, with `a` its minimum break, there is `γ ∈ K^×` such that:

- `ord_K γ = wildArtinSum F v + deg v · n(ψ)`;
- `γ` is an exact witness (`ExactWitness F e ε v a ψ γ`): for every dimension-zero test
  `w` (signed, possibly zero) all of whose breaks lie below `a/2`, every Haar measure `μ`
  and every Weil element `g` with reciprocity image `γ`, the local constant of the
  continuous tensor product `w ⊗ v` with respect to `ψ` and `μ` equals the determinant
  character of `w` at `g`;
- an element `γ'` is an exact witness exactly when `γ' γ⁻¹ ∈ U^{⌈a/2⌉}`;
- there is an approximate witness `γ₀` (`ApproximateWitness F e ε v a ψ γ₀`, the relation
  (4.2.1) of DH81: the same equality for tests with breaks below `a`, after raising both
  sides to a power `p^n` whose exponent may depend on `w`, `μ` and `g`) with
  `γ γ₀⁻¹ ∈ U^1`, and an element `γ₀'` is an approximate witness exactly when
  `γ₀' γ₀⁻¹ ∈ U^1`.

The exact and approximate witness relations are the Library definitions in
`DeligneHenniartStatement`; nothing in them is changed or assumed here.

## Proof (as implemented)

The Library theorem `virtualStability_of_inputs` (module
`Langlands.LocalFactor.DeligneHenniartVirtualReduction`) proves
`VirtualStabilityStatement.{uF, uV}` from four Library propositions. The proof is the
single term applying it to Library proofs of those four propositions:

1. `LocalClassField.AbsoluteReciprocityRealUnitImages.{uF}` (an absolute geometric
   reciprocity map sends `U^{⌈v⌉}` onto the abelian upper ramification group of index
   `v ≥ 0`). It is the third conjunct (`.2.2.1`) of
   `AbsoluteUpperReciprocityTheorems.{uF}`, obtained as
   `absoluteUpperReciprocityTheorems_of_finiteRealImages` (module
   `Langlands.ClassFieldTheory.Local.AbsoluteReciprocityFiniteReduction`) applied to
   `finiteReciprocityRealUnitImages_of_normCardinality` (module
   `Langlands.ClassFieldTheory.Local.UpperReciprocityNormReduction`) applied to
   `NormUnitImage.finiteAbelianNormUnitImageCardinality.{uF, uF}` (module
   `Langlands.ClassFieldTheory.Local.NormUnitImageCardinalityProof`). So the finite real
   unit images come from the norm-quotient cardinalities, and the absolute ones from the
   finite ones.
2. `LocalClassField.CommonClosureGeometricStatement.{uF, uF}`:
   `LocalClassField.commonClosureGeometricProof` (module
   `Langlands.ClassFieldTheory.Local.CommonClosureGeometricProof`).
3. `IntermediateGeometricStatement.{uF}`: `intermediateGeometricProof` (module
   `Langlands.LocalFactor.DeligneHenniartIntermediateGeometricProof`).
4. `TopLayerNormTraceStatement.{uF, uF, uF}` (DH81 Corollary 3.12(i), printed p. 107):
   `TopLayer.topLayerNormTrace` (module
   `Langlands.LocalFactor.DeligneHenniartTopLayerProof`).

All four are instantiated at the field universe `uF`, as `virtualStability_of_inputs`
requires; the representation universe `uV` enters only through the target. The
mathematics of DH81 4.5–4.8 (the induction basis, the element `N_{L/K}(a)^{-1}` built
from a linearizer `a` of the inducing character, the valuation computation and the lattice
induction) is in `DeligneHenniartVirtualReduction` and the modules it imports; see their
Markdown. The Lean check of this module reports only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.
