# Galois transport of the actual Mackey constituents

`Langlands.Global.Harris.proposition48MackeyConstituentGaloisConjugate` proves
exactly `Langlands.Global.Harris.Proposition48MackeyConstituentGaloisConjugateStatement`
at independent universes `uF` (local field) and `uV` (spectral carrier).
If `τ` restricts to `σ` on `D`, the Galois conjugate of a Mackey constituent
for `a` is a Mackey constituent for `τ * a`, without any extra hypothesis on
`Q`, `D`, or the chosen automorphisms.

## Source

Michael Harris, *The local Langlands conjecture for GL(n) over a p-adic
field, n < p*, Invent. Math. 134 (1998), 177–210 (registered source
`harris-1998-local-langlands`), proof of Proposition 4.8. The Mackey
characters are the conjugate characters composed with norms on the
composita (printed p.202; `math_9611226v1.tex`, lines 1579–1597). Transport of
these constituents is used in the prime orbit of the proof (printed p.203,
lines 1646–1655). The operator plan `operator-external-inputs-plan-2026-11-16`,
Remark 4.2 (`external-inputs-plan.tex`, line 881), spells out the transport
identity. The Lean proof implements this step via finite-place weak induction;
it does not require the prime-orbit hypotheses of the surrounding argument.

## Implemented proof

1. Write `b = τ * a`, `A_i = i(E')`, and `C_i = D · A_i` for `i = a, b`.
   The image of `A_a` under `τ` is `A_b` by composition of the actual
   embeddings of `E'`; the image of `D` is `D` because the restriction `σ`
   is bijective. `IntermediateField.map_sup` then gives the image equality
   for the composita. `equivMap` followed by `equivOfEq` gives the restrictions
   `e_A : A_a ≃+* A_b` and `e_C : C_a ≃+* C_b` of `τ` on these subfields of `L`.
2. With `j_i : E' ≃+* A_i` the equivalence onto the image, `j_b = e_A ∘ j_a`,
   so `j_b⁻¹ ∘ e_A = j_a⁻¹`. `HeckeCharacter.comap_trans` identifies the
   pullback of the conjugate character on `A_b` with that on `A_a`. The
   isomorphisms `e_A` and `e_C` commute with the inclusions `A_i → C_i`.
   `ideleClassNorm_equiv` makes the norm square commute, so pulling back the
   Mackey character from `C_b` along `e_C` gives the Mackey character on
   `C_a`. Equivalently the character on `C_b` is the pullback of the one on
   `C_a` along `e_C.symm`, with no twist.
3. The inclusions `D → C_i` commute with `σ` and `e_C`, and thus also with
   their inverses. Apply `IsWeakAutomorphicInductionOf.arithmeticComap` to
   the inverse square and rewrite the inducing character by step 2. By
   definition, pulling the cuspidal class back along `σ.toRingEquiv.symm`
   is `IsoClass.galoisConj σ`, and `IsMackeyConstituent` uses precisely the
   inclusion algebra `D → C_i` used by this square.
