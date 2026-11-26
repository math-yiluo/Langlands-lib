# Complex conjugation of complex standard modules

Module `Langlands.Representation.Archimedean.ComplexStandardModuleConjugation`
(namespace `Langlands.Archimedean.ComplexConjugation`). Definitions and proved lemmas; no
statement is left open.

## Content

Let `c : GL_n(ℂ) → GL_n(ℂ)` be entrywise complex conjugation. It is a group automorphism of
order two, it preserves the unitary group `U(n)`, the diagonal torus (conjugating the
diagonal entries) and the upper unipotent subgroup, and it is the restriction of a
real-linear map of the matrix algebra. Precomposition with `c` therefore carries the smooth
principal series of the characters `χ_i` to the principal series of the characters
`χ_i ∘ conj`. For the standard module of a list `ds` of complex character blocks
(`complexStandardModule n ds`, the principal series of the position characters of `ds`)
this is the standard module of the conjugate blocks `ds.map ComplexCharacterData.conj`,
because `ComplexCharacterData.conj d` has the character `d.character ∘ complexConjugation`
and `|conj z| = |z|`.

| Declaration | Content |
| --- | --- |
| `matrixConj n` | `A ↦ A.map conj` on `n × n` complex matrices, as a continuous `ℝ`-linear map |
| `glConj n` | the induced group homomorphism of `GL_n(ℂ)`; `glConj_glConj` says it is an involution |
| `matrixConj_mem_unitaryGroup`, `glConj_mem_unitaryCompact` | `c` preserves unitary matrices and `U(n)` |
| `glConj_diagonalUnits` | `c(diag(a)) = diag(conj a)` |
| `glConj_mem_upperUnipotent` | `c` preserves the upper unipotent subgroup |
| `conjComp n` | the linear map `f ↦ f ∘ c` on functions on `GL_n(ℂ)`; `conjComp_conjComp` says it is an involution |
| `conjComp_rightTranslation` | `(R(k) f) ∘ c = R(c k) (f ∘ c)` |
| `contMDiff_conjComp` | `f ∘ c` is smooth when `f` is |
| `rightDerivative_conjComp` | for smooth `f`, `R(X)(f ∘ c)(g) = (R(conj X) f)(c g)` |
| `conjComp_rightDerivative` | for smooth `f`, `(R(X) f) ∘ c = R(conj X)(f ∘ c)` |
| `complexPositionCharacter_map_conj`, `principalSeriesCharacter_map_conj` | the position characters and the principal-series character of `ds.map conj` are those of `ds` composed with conjugation |
| `conjComp_mem_complexStandardModule` | `f ∘ c` lies in the standard module of `ds.map conj` when `f` lies in that of `ds` |
| `conjComp_mem_kFiniteVectors`, `conjComp_mem_kFiniteFunctions` | `U(n)`-finiteness is preserved, so `f ↦ f ∘ c` maps the `U(n)`-finite functions of the standard module of `ds` into those of `ds.map conj` |
| `contMDiff_of_mem_kFiniteFunctions` | functions of a complex standard module are smooth |

Here `R(k)` is right translation (`Whittaker.rightTranslation`) and `R(X)` the right
derivative along the real direction `X` (`rightDerivative (matrixModel ℂ n)`).

## Proofs

The group-theoretic statements are entrywise computations. Smoothness and the derivative
formula use the extension `unitsExtension f` of `f` to all matrices
(`Langlands.Representation.Archimedean.PrincipalSeriesStability`): `f ∘ c` agrees on
`GL_n(ℂ)` with `unitsExtension f ∘ matrixConj n`, which is smooth on the invertible matrices,
and `contMDiff_of_contDiffOn` applies. For the derivative,
`mfderiv_eq_fderiv_of_eq_comp` computes `R(X)(f ∘ c)(g)` as the Fréchet derivative at `1` of
`y ↦ unitsExtension f (conj(g y))`; the chain rule gives
`fderiv (unitsExtension f) (c g) (conj g · conj X)`, which is `(R(conj X) f)(c g)` by
`rightDerivative_eq_fderiv`. For `U(n)`-finiteness, the span of the right translates of
`f ∘ c` lies in the image under `conjComp n` of the span of the right translates of `f`,
which is finite-dimensional.

## Provenance

Derived, elementary content. These are the standard facts that a continuous field
automorphism of `ℂ` acts on principal series of `GL_n(ℂ)` by conjugating the inducing
characters, stated for the Library's standard modules
(`Langlands.Representation.Archimedean.StandardModule`). They are used in
`Langlands.Automorphic.ComplexPlaceParameterArithmeticTransport`, where an isomorphism of
number fields identifies a complex completion with `ℂ` through the conjugate of the selected
embedding.
