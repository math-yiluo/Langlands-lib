# Smooth families in actual normalized product induction

`Langlands.Plancherel.productInducedSmoothTensorFamilyEquiv` identifies
diagonal invariant scalar-smooth tensors with actual dependent families in
the normalized product induction. Its map evaluates the tensor in the fixed
compact picture and then performs the actual normalized extension in every
parameter fiber. The coefficient action is the canonical self-twist action,
including inverse pullback on smooth functionals.

## Source, provenance and scope

This is a derived construction toward J.-L. Waldspurger, *La formule de
Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*,
J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082, VI.1, printed pp.295–296 (PDF pp.61–62).
The registered source is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

The passage defines canonical representative transport on coefficient
spaces, restriction to a fixed compact picture, and the diagonal-invariant
tensor description of smooth families. Its example on p.296 shows that the
coefficient stabilizer action can be nontrivial. The present module connects
the concrete algebraic tensor evaluation of `SmoothTensorFamilies` to the
actual inducing fibers and actual self-twist transport of `CompactSelfTwist`.
The generic subgroup setting, unitary stabilizer comap, supplied torus
coordinates and explicit formulas are derived content.

The result concerns the unitary parameter cover of one fixed irreducible
admissible inducing object. The comparison with sections over every
representative of the actual isomorphism-class orbit remains a separate
descent construction. It does not assert that the full stabilizer is
unitary or finite: it uses its actual unitary part. Comparison with the
discrete-series stabilizer and any finiteness theorem remain separate.

## Data and explicit hypotheses

Let `G` be a locally compact nonarchimedean group, and let `P`, `M`, `U` be
actual subgroups with a semidirect decomposition
`h : IsSemidirectDecomposition P M U`. The family
`ν : I → (M →* ℝ≥0ˣ)` consists of continuous positive characters.
The global compact restriction and extension retain these hypotheses:

- `P` and `U` are closed;
- `K` is an actual compact open subgroup;
- `h.projection : P →* M` is continuous;
- every element of `G` has a factorization `p * k`, with `p ∈ P`, `k ∈ K`.

The inducing object `π` is a canonical complex
`IrreducibleAdmissibleRep` of `M`. These are properties of the specified
input representation. No irreducibility of parabolic induction is needed.
Admissibility and irreducibility are used for inducing Schur, not assumed
as consequences of the subgroup data. The pointwise family restriction
itself works for any canonical smooth inducing object `A`.

Supply a finite type `J` and a multiplicative equivalence

\[
 e:X_u=\operatorname{unitaryUnramifiedCharacters}(\nu)
       \simeq J\to\mathrm{Circle}.
\]

Smoothness in this module is defined using these coordinates. There is no
claim of invariance under an arbitrary abstract group isomorphism of
coordinates. The intended rational-character specialization, its coordinate
comparisons, and the general reductive realization of the structural
hypotheses remain separate. The group, positive-character index,
representation carrier and torus-index universes are independent.
Second countability, a compact quotient, a norm on the coefficient space
and a Hermitian structure are not required.

The normalization is the existing full-parabolic positive Haar
half-character in `Aubert.General.normalizedInduction`, as used by
`ProductCompactPicture`. Its comparison with the source's Levi-inflated
normalization remains separate. No formal degree, intertwining operator,
wave packet or analytic Plancherel assertion is constructed here.

## The actual unitary stabilizer and its coefficient action

`unitaryUnramifiedInclusion` is the literal subgroup inclusion
`ι : X_u →* unramifiedCharacters ν`. For a canonical smooth-dual class `ω`,
`unitaryClassTwistStabilizer` is

\[
 S_\omega=\iota^{-1}
   \bigl(\operatorname{unramifiedTwistStabilizer}(\nu,\omega)\bigr).
\]

Thus membership is actual equality of twisted isomorphism classes.
`unitaryClassStabilizerInclusion` maps it into that full stabilizer.
The subgroup is neither an arbitrary parameter group nor postulated to
act trivially. Write `ω = [π]`. Its torus homomorphism
`unitaryStabilizerTorusHom` is `τ(s) = e(s)`.
The coefficient representation `unitaryStabilizerCompactRepresentation`
is the previously proved full stabilizer representation composed with
this inclusion, on

\[
 W=\operatorname{ProductInducedCompactPicture}(h,K,\pi).
\]

The previously proved representation laws use admissible Schur and explicit
identity and product lifts. They require no coherence hypothesis on chosen
vector equivalences.

## Actual dependent families and restriction

`unitaryTorusParameter` is the actual character `χ_z = ι(e⁻¹z)`.
`ProductInducedTorusFamilies` is the dependent product

\[
 \prod_{z\in J\to\mathrm{Circle}} H_{\chi_z},\qquad
 H_\chi=\operatorname{productInducedCoefficientObject}
          (h,h_U,\pi\otimes\chi).
\]

Here `Hχ` consists of actual normalized induced functions on `G × G`
with values in the vector tensor the actual smooth contragredient of the
twisted representation. It is not a copy of an unrelated fixed vector space.

`productInducedFamilyRestriction` is `LinearEquiv.piCongrRight` applied to
`productInducedCompactEquiv` in every fiber. Write it as `R`.
The forward evaluation theorem states, for `k ∈ K × K`,

\[
  (RF)(z)(k)=D_{\chi_z}\bigl(F(z)(k)\bigr),
\]

where `Dχ = productCompactTwistTensorEquiv ν χ π.obj` removes the
smooth-dual twist and keeps every underlying functional. The inverse
formula `productInducedFamilyRestriction_symm_mul` states

\[
 (R^{-1}q)(z)(pk)
   =\sigma_{\chi_z}(p)\,
        D_{\chi_z}^{-1}\bigl(q(z)(k)\bigr).
\]

The action `σχ` is the actual normalized product-parabolic inducing
representation, not a selected free scalar. The imported extension theorem
proves independence of the factorization and global smoothness.

## Canonical transport between the dependent fibers

For an actual self-twist equivalence
`a : π ≃ π ⊗ η`, `parameterSelfTwistEquiv` constructs

\[
  a_\chi:\pi\otimes\chi \simeq \pi\otimes(\chi\eta)
\]

by twisting `a` and applying the proved equality of double-twist actions.
The underlying vector map is still `a`. The theorem
`parameterSelfTwistEquiv_tensor` proves

\[
 D_{\chi\eta}\circ(a_\chi\otimes(a_\chi^{-1})^*)
   = S_{\eta,a}\circ D_\chi.
\]

Tensor induction reduces this to the literal vector and inverse-functional
formula on pure tensors, and linearity on sums.
`productInducedParameterSelfTwist_restriction` lifts this identity to
actual normalized induced functions.

`unitaryTorusParameter_mul_stabilizer` proves
`χ_(z τ(s)) = χ_z ι(s)`. Using the canonical class lift,
`unitaryTorusFiberEquiv` therefore gives an actual inducing equivalence
from the fiber at `z` to that at `z τ(s)`.
`unitaryTorusInducedFiberEquiv`, written `T_(s,z)`, is its actual
normalized product-induced coefficient transport. The tensor identity
`unitaryTorusFiberEquiv_tensor` and function extensionality prove

\[
 R_{z\tau(s)}\,T_{s,z}=\rho(s)\,R_z.
\]

This is `unitaryTorusInducedFiberEquiv_restriction`, where `ρ` is the
genuine compact coefficient representation above.
`productInducedTwistedTransport_independent` applies the existing
inducing Schur result to the twisted inducing object, using the proved
twist-invariance of admissibility and irreducibility.
Consequently `unitaryTorusInducedFiberEquiv_eq_transport` identifies
`T_(s,z)` with transport through **any** inducing equivalence between the
same fibers. The selected class lift introduces no choice dependence.

## Smooth families and the invariant tensor equivalence

`productInducedSmoothFamilies` is the submodule preimage under `R` of
`finiteSmoothEquivariantFamilies J W τ ρ`. The theorem
`mem_productInducedSmoothFamilies_iff` characterizes this without an
abstract covariance substitute: a dependent family belongs precisely when
its restriction is a finite scalar-smooth family and

\[
    F(z\tau(s))=T_{s,z}F(z)
\]

for every actual unitary stabilizer element and parameter.
The proof applies the injective compact restriction and the transport
square in both directions.

Finite scalar smoothness means an actual finite sum
`q(z) = ∑ i, f_i(z) • w_i`, with fixed `w_i ∈ W` and
`f_i ∈ smoothFiniteTorusFunctions J`. The imported scalar smoothness
predicate is real `ContDiff ∞` after the finite-torus angle lift.
No unspecified vector-valued smoothness convention is substituted for
this finite tensor condition.

`productInducedSmoothTensorRepresentation` is the diagonal action

\[
 s\cdot(f\otimes w)
   =\bigl(z\mapsto f(z\tau(s)^{-1})\bigr)\otimes\rho(s)w.
\]

The main equivalence is

\[
 [\,C^\infty(J\to\mathrm{Circle})\otimes_{\mathbb C}W\,]^{S_\omega}
   \simeq_{\mathbb C}
   \operatorname{productInducedSmoothFamilies}.
\]

It composes the proved concrete tensor-evaluation equivalence with the
inverse of compact restriction restricted to the submodule preimage.
`productInducedSmoothTensorFamilyEquiv_restriction` proves that its
restriction is exactly tensor evaluation. Its
`productInducedSmoothTensorFamilyEquiv_eval_mul` theorem gives the
normalized `p k` extension formula above with `q(z)` equal to that tensor
evaluation. The inverse theorem
`productInducedSmoothTensorFamilyEquiv_symm_evaluation` recovers `RF`
pointwise from the invariant tensor of a family. Thus both directions use
the actual functions and normalized extension.
