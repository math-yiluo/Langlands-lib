# The dual cusp forms lie in a cuspidal contragredient

Module `Langlands.Global.RankinSelberg.CuspidalTransposeInverseContragredientStatement`.
Author: Worker 381.

## Statement

`Langlands.Global.RankinSelbergGlobal.CuspidalTransposeInverseContragredientStatement.{u}`
is a Prop-valued definition, not proved here. It states exactly:

```lean
∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
  (T : Automorphic.CuspidalOperatorRealization F r),
  ∃ T' : Automorphic.CuspidalOperatorRealization F r,
    Automorphic.OperatorRealization.IsContragredientOf T'.realization T.realization ∧
      ∀ x : T.Space, ∃ x' : T'.Space,
        cuspFunction F T' x' = dualFunction F (r + 1) (cuspFunction F T x)
```

## Meaning

For every [actual cuspidal operator realization](../../Automorphic/CuspidalOperatorRealization.md)
`T` of `GL_(r+1)` over the number field `F` there is another one, `T'`, such that

* `T'` realizes the contragredient of `T` in the sense of the published
  [contragredient relation](../../Automorphic/Contragredient.md): some pairing of `T` with
  `T'`, invariant under the finite adelic, standard compact and real Lie algebra operators,
  has partial map a bijection from `T'` onto the contragredient functionals of `T`;
* for every vector `x` of `T`, with cusp form `φ = cuspFunction F T x` on
  `GL_(r+1)(𝔸)`, the dual cusp form `φ̃(g) = φ(w_n ᵗg⁻¹)` (`dualFunction`, with `w_n` the
  long Weyl element) is the cusp form of a vector `x'` of `T'`.

## Source

J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004), registered as
`cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3).

* Printed p.201: Gelfand and Kazhdan show that `π̃_v ≅ π_v^ι`, where `ι` is the outer
  automorphism `g^ι = ᵗg⁻¹`.
* Printed p.203 (for `GL_2`): "if we let `φ̃(g) = φ(ᵗg⁻¹) = φ(w_n ᵗg⁻¹)`, then
  `φ̃ ∈ V_π̃`".
* Printed p.206 (for `GL_n`): the action of the outer automorphism on automorphic forms is
  `φ̃(g) = φ(g^ι) = φ(w_n g^ι)`; printed p.207: for `W ∈ W(π, ψ)`,
  `W̃(g) = W(w_n g^ι) ∈ W(π̃, ψ⁻¹)`.

So for a cuspidal representation `(π, V_π)` the functions `φ̃`, `φ ∈ V_π`, lie in the space of
cusp forms `V_π̃` of the contragredient. In the source this combines the elementary fact
that `{φ̃ : φ ∈ V_π}` is an irreducible cuspidal subspace realizing `π^ι = π ∘ ι` with the
Gelfand–Kazhdan isomorphism `π^ι ≅ π̃` at every place.

**Correspondence.** `V_π̃` is taken here to be some actual cuspidal operator realization
`T'` of the contragredient of `T`, and "`φ̃ ∈ V_π̃` for every `φ ∈ V_π`" is the last clause.
The statement does not assert that every vector of `T'` is a dual cusp form, nor that `T'` is
unique (uniqueness is multiplicity one,
[`CuspidalOperatorMultiplicityOneStatement`](../../Automorphic/CuspidalOperatorMultiplicityOneStatement.md)).

## Relation to Library results

The published `Automorphic.cuspidalContragredientExistence` gives some cuspidal
contragredient `T'` of `T`; it says nothing about the dual cusp forms. The present statement
asks for a cuspidal contragredient containing all of them.

## Use

It is a premise of
[`ContragredientDualWhittakerReductionStatement`](ContragredientDualWhittakerReduction.md).
