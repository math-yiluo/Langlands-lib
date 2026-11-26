# Finite-order determinant twists under arithmetic pullback

`Langlands.Automorphic.Unramified.cuspidalDeterminantTwistArithmeticComap`
proves `Langlands.Automorphic.Unramified.CuspidalDeterminantTwistArithmeticComapStatement`
with both of its universe parameters `uF` and `uE` and with no hypothesis
beyond those of the statement. Let `e : F ≃+* E` be an isomorphism of number
fields, `c` and `c'` actual cuspidal classes of rank `r + 1` over `E`, and `χ`
a Hecke character of `E`. If `c'` is the finite-order determinant twist of `c`
by `χ`, then `c'.arithmeticComap e` is the finite-order determinant twist of
`c.arithmeticComap e` by `HeckeCharacter.comap e χ`. The proof uses no
spectral or multiplicity statement. It compares the three operator actions of
the actual realizations directly.

## The determinant character

`determinantTwistScalar_comap` shows that the pulled-back character, evaluated
on the determinant of an adelic matrix `g` over `K`, equals `χ` evaluated on
the determinant of the entrywise transported matrix
`AdelicGLTransport.adelicEquiv n e g`. The proof combines
`HeckeCharacter.comap_onIdeles`, the formula for `comap` on idele
representatives, with `AdelicGLTransport.determinant_adelicEquiv`, which says
that the adelic determinant commutes with arithmetic transport.
`determinantTwistScalar_comap_ofFinite` and
`determinantTwistScalar_comap_ofInfinite` specialise this to finite adelic
elements and to elements of the standard compact subgroup at the infinite
places. They use `AdelicGLTransport.adelicEquiv_ofFinite`,
`AdelicGLTransport.adelicEquiv_ofInfinite`, and the fact that
`ArchimedeanCompactTransport.compactEquiv` is the restriction of
`AdelicGLTransport.infiniteEquiv`.

## The three operator equations

`OperatorRealization.DeterminantTwistEquations.of_arithmeticTransportEquations`
starts from realizations `S'`, `T'` over `K` and `S`, `T` over `L`, and from
linear equivalences `φ : S' → S` and `ψ : T' → T` satisfying
`ArithmeticTransportEquations e`. These equations carry the finite adelic,
standard compact and enveloping-algebra actions over `K` to the actions of
their arithmetic images over `L`. Let `q : S → T` satisfy
`DeterminantTwistEquations χ`. Then the composite `ψ⁻¹ ∘ q ∘ φ` satisfies
`DeterminantTwistEquations (HeckeCharacter.comap e χ) S' T'`.

Each equation is an instance of the private lemma `conjugate_equation` about
abstract complex modules. If `φ A' = A φ`, `ψ B' = B ψ` and `B q = c • q A`, then
`B' (ψ⁻¹ q φ) = c • (ψ⁻¹ q φ) A'`. For the finite action, `A'` is
`S'.finiteRepresentation d` and `A` is the action of
`AdelicGLTransport.finiteEquiv n e d` on `S`. The scalar is `χ` on the
determinant of the transported element. By
`determinantTwistScalar_comap_ofFinite` this equals the pulled-back character
on the determinant of `d`. The compact equation is the same with
`determinantTwistScalar_comap_ofInfinite`. The enveloping-algebra equation
uses the scalar `1`, since a determinant twist leaves the infinitesimal action
unchanged. The lemma is stated through equalities of scalars. It is applied
in term mode, so the proof never rewrites inside the actions of the
realizations.

## The relation and the classes

`OperatorRealization.IsFiniteOrderDeterminantTwist.of_isArithmeticTransport`
destructures the two arithmetic transports and the twist relation, and applies
the previous lemma. Finite order of `HeckeCharacter.comap e χ` follows from
`HeckeCharacter.hasFiniteOrder_comap_iff`.
`OperatorRealization.IsFiniteOrderDeterminantTwist.arithmeticComap` applies
this to `OperatorRealization.isArithmeticTransport_arithmeticComap`, which
says that `S.arithmeticComap e` is an arithmetic transport of `S` along `e`.
Its witness is the inverse of the restricted pullback `arithmeticComapEquiv`.

The main theorem chooses representatives `S` and `T` of `c` and `c'` with
`Quotient.inductionOn₂`. On the classes of `S` and `T`, the class relation
`CuspidalOperatorRealization.IsoClass.IsFiniteOrderDeterminantTwist` is by
definition the relation between `S.realization` and `T.realization`. The class
`CuspidalOperatorRealization.IsoClass.arithmeticComap e` of `S` is the class
of `S.arithmeticComap e`, whose realization is `S.realization.arithmeticComap e`.
The realization-level lemma therefore gives the conclusion.

## Sources

The Galois pullback and twist conventions come from L. Clozel and
C. S. Rajan, *Solvable base change*, arXiv:1806.02513v1 (2018), registered as
`clozel-rajan-2018-solvable-base-change`, with file SHA-256
`d63e845fb86bb7dcdb01f72480374894161ebc289ab52eee1b7e97d84d1d2b4d`.
In §1.1 (PDF p. 2) the Galois conjugate `σπ` of a representation `π` of
`GL(n, 𝔸_F)` is `g ↦ π(σ⁻¹(g))`. The Library writes this conjugate as
`CuspidalOperatorRealization.IsoClass.galoisConj σ`, which is the pullback
`arithmeticComap σ⁻¹`. With `e = σ⁻¹`, the theorem gives the
compatibility `σ(π ⊗ (χ ∘ det)) ≅ σπ ⊗ (σχ ∘ det)` with `σχ = χ ∘ σ⁻¹`,
the character `HeckeCharacter.comap σ⁻¹ χ`. Section 2 iterates a relation
`σ''(π_L) ≃ π_L ⊗ ω_L` to `σ''^d(π_L) ≃ π_L ⊗ ω_L ∘ N_{L/K}` (PDF p. 6). It
then computes `τ(π_L ⊗ ψ⁻¹) ≃ π_L ⊗ ω_L ⊗ τ(ψ)⁻¹ ≃ π_L ⊗ ψ⁻¹` (PDF p. 7). Both
steps use this compatibility of Galois conjugation with twisting. The
Library relation additionally requires the twisting character to have finite
order, and the statement keeps that requirement on both sides.
