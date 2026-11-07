# Proof of Brauer induction for relative Weil groups

Proof contribution to task `4bfab030-61e7-4f44-a043-60487db8e088`, revision 1
(Worker 1833).

`Langlands.ClassField.Global.RelativeWeilGroup.inducedCharacterGenerationStatement`
proves the unchanged Library proposition
`Langlands.ClassField.Global.RelativeWeilGroup.InducedCharacterGenerationStatement.{u, uV}`
of the module `Langlands.VirtualRepresentation.Global.RelativeWeilInductionGenerationStatement`.
For every class family `c`, all number fields `F E : Type u` with `[Algebra F E]`
and `[IsGalois F E]`, and every carrier universe `uV`, it gives

`Submodule.span ℤ (inducedCharacterGenerators.{u, uV} c F E) = ⊤`

in `ContinuousVirtual.{u, uV} c F E`. That is, the classes
`Ind_{W_H}^{W_{E/F}} θ`, for subgroups `H` of `Gal(E/F)` and continuous
characters `θ` of `W_H`, span the continuous exact virtual group of `W_{E/F}`.
No hypothesis is placed on `c` (no `IsArithmeticClassFamily c`, no
`FundamentalClass.Restriction c`), on the fields, or on the representations.

## Declarations

In the namespace `Langlands.ClassField.Global.RelativeWeilGroup`, with the local
instance `relativeGaloisTopology` as in the statement:

- The imported `isOpen_ker_projection c F E` from the shared statement module:
  the kernel of `projection c F E` is open. It is
  `galoisPreimage c F E ⊥` (`MonoidHom.comap_bot`), which is open by the
  published `isOpen_galoisPreimage`.
- `ker_projection_comm c F E`: the kernel is commutative. By the published
  `exact c F E` it is the range of `inclusion c F E`, the image of the
  commutative idele class group.
- `inducedCharacterGeneration c F E : InducedCharacterGeneration.{u, uV} c F E`
  applies the general theorem
  `Langlands.VirtualRepresentation.ExactGrothendieckGroup.span_quotientInducedGenerators_eq_top`
  to `π = projection c F E` with `Q = Gal(E/F)`. For this `π`, the set
  `quotientInducedGenerators π _` is definitionally the published
  `inducedCharacterGenerators c F E`. Both consist of the classes
  `continuousInduce (H.comap (projection c F E)) _ (characterClass θ)`, and
  `galoisPreimage c F E H` is by definition `H.comap (projection c F E)`.
- `inducedCharacterGenerationStatement : InducedCharacterGenerationStatement.{u, uV}`
  quantifies the previous theorem over all `c`, `F` and `E`.

## The implemented proof

The proof follows the route in item 3 of "Relation to the source" in the
statement's Markdown. Two changes avoid irreducible decompositions and
semisimplicity. The general theorem is proved in
`Langlands.VirtualRepresentation.QuotientInducedGeneration`, by strong induction
on the dimension of a continuous representation `A`.

1. **Clifford step** (`Langlands.VirtualRepresentation.CliffordReduction`). The
   kernel `C_E` is commutative, so it has a common eigenvector with eigenvalue
   function `χ`. Let `S ⊇ C_E` be the stabilizer of `χ` and `W` its eigenspace.
   Instead of decomposing an irreducible representation, the module gives an
   injective intertwiner `Ind_S^{W_{E/F}} W ↪ A`. In the exact virtual group
   this gives `[A] = [Ind_S W] + [A / Ind_S W]`, and the quotient has smaller
   dimension. Injectivity comes from the independence of eigenspaces for
   distinct eigenvalue functions.
2. **Scalar case** (`ScalarKernelGroup`, `ScalarKernelInduction`,
   `ScalarKernelBrauer`). On `W` the kernel acts by scalars. The determinant-one
   scalar multiples of the image of `S` form a finite group `H₀`, which is the
   `H₀ = G ∩ SL(V_η)` of the sketch. The published finite Brauer theorem
   `Langlands.FiniteRep.BrauerTheory.finiteBrauerTheory` (conjunct
   `IntegralBrauerSpanningStatement`) writes the tautological representation
   of `H₀` as a signed sum of `Ind_A ψ`. The sketch keeps the part on which the
   finite central subgroup of scalars acts tautologically. The proof uses the
   additive map `scalarLiftVirtual` instead: the tautological part, made a
   representation of `S` by `s ↦ z • σ(h)` when `ρ(s) = z • h`. It sends the
   tautological representation to `[W]`. It sends `Ind_A ψ` either to `0` or to
   `Ind_T θ`, where `T ⊇ C_E` and `θ` is a continuous character. This combines
   the central-product step and the single Mackey double coset of the sketch.
3. **Transitivity** (`ExactInductionTransitivity`). Induction in stages
   `Ind_S^{W_{E/F}} Ind_T^S θ = Ind_T^{W_{E/F}} θ` turns the generators of `S`
   into generators of `W_{E/F}`. Every subgroup `T` containing `C_E` is
   `π⁻¹(π T)`, so these are exactly the classes in `inducedCharacterGenerators`.

Every identity used is an isomorphism of genuine continuous representations, or
the defining short-exact relation, so it holds in the exact virtual group. The
proof does not use the Galois-side or Hecke global functional equations, any
local Langlands result, or any Brauer generation statement for `W_{E/F}`.

## Public theorems used

- From the target's imports: `isOpen_galoisPreimage`, `exact`, `inclusion`,
  `projection`, `continuousInduce`, `characterClass`.
- `Langlands.FiniteRep.BrauerTheory.finiteBrauerTheory` (finite Brauer theory).
- `Langlands.LieKolchin.exists_common_eigenvector`, `LieKolchin.weightSpace` and
  `LieKolchin.iSupIndep_weightSpace` (common eigenvectors and independence of
  eigenspaces).
- Exact virtual groups: `ExactGrothendieckGroup.ofRepresentation_shortExact`,
  `ofRepresentation_eq_of_equiv`, `ofRepresentation_eq_add_of_equiv_prod`,
  `induce_ofRepresentation`, `FiniteRepresentation.rank_eq_add_of_shortExact`
  and `rank_induce`.
- Continuity: `isContinuous_restrict`, `isContinuous_induce`,
  `isContinuous_quotient`, `isContinuous_of_injective_intertwiner` and
  `isContinuous_iff_of_equiv`.
- Finite representations: `FiniteRep.induceRepEquiv`, `FiniteRep.indCoindEquiv`,
  `FiniteRep.modelEquiv`, `FiniteRep.brauerExpansion`, and the coset
  coordinates `FiniteRepresentation.Induction.coordinates`,
  `Induction.factor_mul_out` and `Induction.coset_mul`.

## Sources

The statement is a derived relative form of Tate, *Number theoretic background*
(1979), Proposition (2.3.1), printed p.11 (registered source
`tate-1979-number-theoretic-background`). Its comparison with the source is in
the statement's Markdown. This proof is the route of item 3 of that Markdown,
as derived by Worker 84, with the two changes described above. It is not quoted
from the source.

## Dependencies

The module imports the target statement module and
`Langlands.VirtualRepresentation.QuotientInducedGeneration`.
