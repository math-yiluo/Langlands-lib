# A uniform exponent for quasi-finite commutative group schemes

`Langlands.GroupScheme.QuasiFiniteCommutativeUniformExponentStatement.{u}`
states SGA 3, Exposé IX, Lemma 6.1, for schemes: a commutative group
scheme `K` of finite presentation over a quasi-compact scheme `S`,
whose structure morphism is quasi-finite, is killed by some positive
integer.

The source is the registered
`sga3-expose-ix-gille-polo-2009`, *SGA 3*, Exposé IX, Gille–Polo
recomposed edition (2009), Lemma 6.1, printed pages 52–53, original
margin 64. The proof continues through Lemma 6.2 on pages 53–54.
The retained PDF has the statement on page 22 and the proof on
pages 23–24, with PDF pages counted from one. The source content hash
is `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.

The Lean hypotheses correspond to the source as follows:

| Source condition | Lean condition |
| --- | --- |
| Quasi-compact base | `CompactSpace S` |
| Commutative group scheme | `K : GroupScheme S` and `IsCommMonObj K.X` |
| Finite presentation over `S` | `LocallyOfFinitePresentation K.X.hom`, `QuasiCompact K.X.hom`, and `QuasiSeparated K.X.hom` |
| Quasi-finite over `S` | `LocallyQuasiFinite K.X.hom`, together with quasi-compactness and finite type already implied above |
| Positive integer killing the group | `∃ n : ℕ, 0 < n ∧ ∀ T x, x ^ n = 1` |

The power identity is quantified over every `S`-scheme `T : Over S`
and every `T`-point `x : T ⟶ K.X`. It expresses the source's
`n · id_K = 0` in multiplicative notation. Yoneda identifies these
two formulations. No flatness, separatedness, affineness,
noetherianity, or multiplicative-type hypothesis is imposed.

This file defines a proposition only. It supplies an independently
reviewable prerequisite target for the finite-subgroup spreading
argument; it does not provide a proof of Lemma 6.1.
