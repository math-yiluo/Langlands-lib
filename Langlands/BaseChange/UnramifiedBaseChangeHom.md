# Unramified base change on the spherical Hecke algebra of \(GL_n\)

`Langlands.BaseChange.unramifiedBaseChangeHom` proves
`UnramifiedBaseChangeHomStatement.{u, v}`. It applies `satakeCharacter` at the
independent field universes `u` and `v` in the construction
`unramifiedBaseChangeHom_of_satakeCharacters`. The fields share a prime \(p\),
the rank is \(n=r+1\), and the power \(l\) is any natural number, including zero.
[Target statement](UnramifiedBaseChangeHomStatement.md), [Satake character theorem](SatakeCharacter.md)

Henniart–Lemaire define the homomorphism \(b\colon H_E\to H_F\) through the Satake
isomorphisms in *Changement de base et induction automorphe pour \(GL_n\) en
caractéristique non nulle*, Mém. SMF 124 (2011), §I.1.3, printed p. 6. Their
§I.3.1, printed pp. 24–25, describes it by the substitution \(X_j\mapsto X_j^l\).
The Lean proof implements this substitution on character evaluations using the
Library's generation theorem. The registered source is
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.

## Character evaluation

For each parameter \(s\), choose Satake characters \(\omega^F_s\) and \(\omega^E_s\)
using the existence part of `SatakeCharacterStatement`. The product homomorphism
`SF` maps \(f\) to the function \(s\mapsto\omega^F_s(f)\). If two elements have
the same image, every Satake character kills their difference by
`IsSatakeCharacter.unique`. Character separation then makes `SF` injective.
Define `pullback` by sending \(\phi\) to \(s\mapsto\omega^E_{s^l}(\phi)\). Both
homomorphisms are formed with `AlgHom.pi`.

## Closure of the range under power substitution

`exists_polynomial_power_elementary` substitutes \(X_j^l\) into the elementary
symmetric polynomial \(e_i\). This substitution commutes with variable
permutations, so `MvPolynomial.esymmAlgHom_fin_surjective` expresses the resulting
polynomial as \(Q_i(e_1,\dots,e_n)\). Evaluating on a tuple of complex units and
using `elementaryCoefficient_ofTuple` and `Eigenvalues.power_ofTuple` gives
\[
e_i(s^l)=Q_i(e_1(s),\dots,e_n(s))
\]
for every unordered parameter \(s\).

Let \(T_i^K\) be the standard Hecke element for \(K=F,E\), and let
\(c_{K,i}=(\sqrt{q_K})^{i(n-i)}\), where \(q_K\) is the residue cardinality.
The character identity on the standard elements is
\(\omega_s^K(T_i^K)=c_{K,i}e_i(s)\). The positive residue cardinality makes
each \(c_{K,i}\) nonzero. In `powerScalar_mem_range`, the images under `SF` of
\(c_{F,j}^{-1}T_j^F\) for \(1\le j\le n\) are the functions \(e_j\) as elements of
`SF.range`. Evaluating \(Q_i\) inside this subalgebra and multiplying by \(c_{E,i}\)
gives \(s\mapsto\omega^E_{s^l}(T_i^E)\). Thus `pullback` maps the subalgebra generated
by the standard elements into `SF.range`.

In top degree the elementary symmetric function is the product of the tuple
entries, so \(e_n(s^l)=e_n(s)^l\). The top normalization is \(1\), and
`pullback` sends \(T_n^E\) to the image of \((T_n^F)^l\).
For any \(\phi\), `sphericalHeckeGeneration` supplies \(m\) with
\((T_n^E)^m\phi\) in the generated subalgebra. The element \(T_n^F\) is a unit
by `standardHeckeElement_last_isUnit`. Multiplying the image of \((T_n^E)^m\phi\)
on the left by the image of \(((T_n^F)^l)^{-m}\) gives the image of \(\phi\)
under `pullback` in `SF.range`.

## Existence and uniqueness

Restrict the codomain of `pullback` to `SF.range` and compose with the inverse
of `AlgEquiv.ofInjective SF`. The resulting algebra homomorphism \(b\)
satisfies \(\omega^F_s(b\phi)=\omega^E_{s^l}(\phi)\). Character uniqueness
gives `IsUnramifiedBaseChangeHom F E l r b` for every choice of the two
characters in that predicate. Any other homomorphism satisfying the predicate
has the same composite with `SF`. Injectivity of `SF` gives equality.
