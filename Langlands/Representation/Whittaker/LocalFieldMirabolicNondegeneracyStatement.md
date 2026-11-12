# Absence of degenerate mirabolic submodules over local fields

Author: Worker 5165.

`Langlands.Whittaker.LocalFieldMirabolicNondegeneracyStatement.{uF,uV}`
states the admissible generic case of Bernstein–Zelevinsky (1977), Theorem
4.9, using the actual full upper-unipotent character quotient. This file
contains a proposition definition only. Its proof is a separate obligation.

For every nonarchimedean local field `F`, every `n : ℕ`, every continuous
nontrivial unitary additive character `ψ`, and every irreducible admissible
generic complex representation `π` of `GL_(n+1)(F)`, let `U` be any invariant
subspace for the restriction of `π` to the actual mirabolic subgroup
`mirabolic n F`. If the standard character-localized upper-unipotent
coinvariants of `U` form the zero vector space, then `U = ⊥`.
The field and vector-space universes `uF` and `uV` are independent. No
characteristic-zero restriction is imposed.

## Source translation

The original is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472, registered as `bernstein-zelevinsky-1977-induced-i`, file
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA-256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The relevant original passages were read, including the rendered page of
Theorem 4.9. A bounded search of current project and Library errata notes
found no source-specific note.

- Section 2.1, printed p.446 (one-based PDF p.7), fixes a locally compact
  nonarchimedean field without a characteristic restriction.
- Section 3.1, printed p.450 (PDF p.11), defines `P_r` by its last row
  `(0, …, 0, 1)`, its radical `V_r`, and the character
  `θ(v) = ψ(v_(r-1,r))`.
- Sections 3.2 and 3.5, printed pp.451–452 (PDF pp.12–13), define
  `Φ⁻`, `Ψ⁻` and the top derivative `τ^(r) = Ψ⁻(Φ⁻)^(r-1)(τ)`.
- Section 4.7, printed p.455 (PDF p.16), defines degeneration by vanishing
  of this top derivative.
- Theorem 4.9, printed p.456 (PDF p.17), says that an irreducible
  nondegenerate representation of `G_r` has no nonzero degenerate
  `P_r`-submodules.

Here `r = n + 1`. The Library's `Mirabolic.upperUnipotent n F` is the full
upper-unitriangular subgroup inside `P_r`. Its published
`upperUnipotentEquiv` identifies it with `GeneralLinear.upperUnipotent r F`.
The character in this statement is exactly `standardCharacter ψ n`
transported along that equivalence. Its complex value is
`ψ(Σ_i u_(i,i+1))`.

The full character quotient imposes all relations
`π(u)v = ψ(Σ_i u_(i,i+1)) v`. Taking the successive radical character
quotients in the definition of the top derivative imposes these same
relations: the successive last-column radicals generate the full upper
group, and the product of their characters is the character of the
superdiagonal sum. The inverse half-modulus normalizations change the
remaining actions, not the underlying quotient; the twists are trivial on
the subsequent upper-unipotent groups. Thus vanishing of this quotient
expresses precisely degeneration in Theorem 4.9. This is a mathematical
translation of the source, not a claim that a comparison with the
Library's p-adic normalized derivative functors has already been proved.
A proof using those functors must supply that comparison.

`IsGeneric ψ n π` supplies irreducibility, admissibility (including
smoothness), and a nonzero standard Whittaker functional. Such a functional
factors through the full character quotient, so this quotient is nonzero.
This gives the source's nondegeneracy hypothesis. The statement uses the
admissible generic case needed for mirabolic restriction; it does not
assert Theorem 4.9 for arbitrary nonadmissible representations.

## Lean objects and boundary cases

`U : Subrepresentation (π.comp (mirabolic n F).subtype)` is a genuine
mirabolic invariant subspace, with its induced representation
`U.toRepresentation`. It need not be invariant under the ambient general
linear group. `Jacquet.Localization.Coinvariants` is the actual vector-space
quotient by the span of the character relations, with no finiteness or
normalization premise. `Subsingleton` means that this quotient is the zero
vector space. The conclusion is equality with the bottom invariant
subspace. No finite-length, multiplicity-one, Kirillov-model, or
restriction-injectivity assumption is introduced.

Rank one (`n = 0`) is included. Both the mirabolic and upper-unipotent groups
are trivial, the character relations vanish, and the hypothesis says that
the subspace `U` itself is zero. The bottom subspace is included at every
rank.

The proposition is a substantive prerequisite to mirabolic restriction
injectivity. Its publication alone does not prove injectivity.
