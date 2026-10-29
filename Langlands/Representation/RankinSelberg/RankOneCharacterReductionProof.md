# Proof of the reduction of full rank-one Whittaker type to a quasicharacter

`Langlands.RankinSelberg.rankOneCharacterReduction` proves exactly the
published `Langlands.RankinSelberg.RankOneCharacterReductionStatement.{uF,uV}`.
The field universe `uF` and the carrier universe `uV` remain independent
level parameters. The theorem has no parameters or hypotheses beyond those
quantified in the statement. For every prime `p`, every `PadicField.{uF} p`
with its canonical topology, every bundled unitary additive character `ψ`,
every complex module `V : Type uV` and every actual representation `π` of
GL(1) on `V`, the full predicate `IsOfWhittakerType 0 (standardCharacter ψ 0) π`
implies that there is a continuous quasicharacter `χ` together with an actual
`π.Equiv (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ))`. The equivalence goes
from `π` to the scalar representation. The carrier is never replaced by `ℂ`
or a universe lift. No irreducibility, finite dimension, nonzero vector,
chosen equivalence or action continuity is assumed.

## Implemented proof

The proof uses only the full Whittaker-type premise and published Library
and Mathlib results. It has four steps.

1. **The dual is one-dimensional.** The premise destructures into
   smoothness (the first part of admissibility) and a complex linear
   equivalence `e` from the standard Whittaker-functional submodule to `ℂ`.
   The fixed-vector finiteness and finite generation clauses are not used.
   The published `Whittaker.glFunctionals_rankOne` shows that this submodule
   is the whole algebraic dual `Module.Dual ℂ V`. Composing
   `Submodule.topEquiv.symm`, `LinearEquiv.ofEq` along that equality, and
   `e` gives `D : Module.Dual ℂ V ≃ₗ[ℂ] ℂ`.

2. **The carrier is linearly equivalent to `ℂ`.** The helper
   `dual_symm_one_bijective` proves that the functional `f := D.symm 1` is
   bijective, for any `V : Type uV`. Every functional `φ` equals
   `D φ • f`, since both have the same image under `D`. If `f v = 0`, then
   `φ v = 0` for every functional `φ`. Mathlib's
   `Module.forall_dual_apply_eq_zero_iff` then gives `v = 0`. This is
   separation by linear forms; it applies because every complex vector
   space is projective. Hence `f` is injective. The functional `f` is
   nonzero because `D f = 1`. Choosing `v` with `f v ≠ 0`, the vector
   `(z / f v) • v` maps to `z`, so `f` is surjective.
   `LinearEquiv.ofBijective` turns `f` into `L : V ≃ₗ[ℂ] ℂ`.

3. **Transporting the action gives a character.** The helper
   `eq_coord_smul_symm_one` records `v = L v • L.symm 1` for every vector.
   The helper `transportedScalar π L` is the monoid homomorphism
   `g ↦ L (π g (L.symm 1))` to `ℂ`. It sends `1` to `L (L.symm 1) = 1`.
   Multiplicativity follows by expanding `π h (L.symm 1)` in the
   coordinate `L` and using linearity of `π g` and `L`. The lemma
   `transportedScalar_apply` gives `L (π g v) = transportedScalar π L g * L v`
   for every `g` and `v`. Since the source is a group,
   `MonoidHom.toHomUnits` turns this homomorphism into
   `c : GL(1) →* ℂˣ`. The character of the field's units is
   `χ := c.comp GeneralLinear.scalar`. The helper
   `scalar_determinant_rankOne` proves `scalar (determinant g) = g` for
   every `g` in GL(1). It compares the single matrix entry, and Mathlib's
   simp set evaluates the one-by-one determinant. Hence
   `χ (determinant g) = c g`. The scalar representation `rankOneCharacter χ`
   acts on `z` by `χ (determinant g) * z`. Therefore
   `Representation.Equiv.mk L` intertwines `π` with `rankOneCharacter χ`.

4. **Continuity.** Smoothness of the vector `L.symm 1` gives an open
   subgroup `K` of GL(1) fixing it (`Representation.mem_invariants` unfolds
   `fixedVectors`). For `k ∈ K`, `c k = L (L.symm 1) = 1`. Thus `c` is
   constant on the identity neighbourhood `K`, so it is continuous at `1`.
   GL(1) is a topological group, so Mathlib's `continuous_of_continuousAt_one`
   shows that `c` is continuous. The published `GeneralLinear.scalarContinuous`
   gives continuity of the scalar homomorphism, and the composite `χ` is
   continuous. The pair `⟨χ, continuity⟩` is the bundled
   `Quasicharacter F.Carrier`.

The general helper `exists_quasicharacter_equiv_of_isOfWhittakerType` proves
steps 1–4 for any field `F` with a topology. It has one instance
hypothesis, `IsTopologicalGroup (GeneralLinear 1 F)`, which only step 4
uses. The final theorem installs the canonical field topology
`F.canonicalTopologicalData.topology`. It supplies that instance from the
published `F.canonicalGeneralLinearTopologicalGroup 1` and applies the
helper. The statement writes the group as `GeneralLinear (0 + 1)`. This is
definitionally `GeneralLinear 1`, and the helper applies to it directly.

## Scope and provenance

The proof uses no two-block multiplicativity, Section 7 result, analytic
factor existence assumption, proof hole or new axiom. Development inspection
reports only `propext`, `Classical.choice` and `Quot.sound`, and level
parameters `uF` and `uV`. The proof is an internal derivation from published
Library definitions and lemmas and from Mathlib. It is not a transcription of
a separately numbered literature result. The opposite direction, from a
continuous quasicharacter to full Whittaker type, is the separate
`rankOneWhittakerType` in `RankOneWhittakerTypeProof`.
