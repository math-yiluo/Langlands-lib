# Haar conjugation on the full upper block parabolic

`Langlands.Parabolic.localFieldGeneralLinearModulusCompatibility` proves
`Langlands.Parabolic.LocalFieldGeneralLinearModulusCompatibilityStatement`
at the statement's universe `u`, with no further hypotheses. For every field
`F` with `LocalFieldData F`, every rank \(n\), including \(n=0\), and every
ordered block shape \(B\), the Haar character of conjugation on the closed
radical \(U_B\subseteq \mathrm{GL}_n(F)\), restricted to the parabolic
\(P_B\), equals \(\delta_B\circ\pi_B\). Here \(\delta_B\) is
`T.leviModulus B` and \(\pi_B\) is the diagonal-block projection
`B.leviProjection F`.

## Conventions

The proof works with the matrix subgroup `B.unipotentSubgroup F` of
\(\mathrm{GL}_n(F)\). It is closed, so it is locally compact and carries
its Borel σ-algebra. On it, the statement's character
`HaarModulus.closedRestrictCharacter` is by definition
`HaarModulus.restrictCharacter`, written \(\chi\) below. Its value at \(g\)
is `mulEquivHaarChar` of the conjugation \(c_g(u)=gug^{-1}\). By
`mulEquivHaarChar_smul_map` this value is the scalar \(c\) with
\(c\cdot(c_g)_*\mu=\mu\) for a Haar measure \(\mu\). This is the module of
Bernstein and Zelevinsky 1977, §1.7, printed p. 444: there
\(\int f(\sigma^{-1}u)\,d\mu(u)=\mathrm{mod}_U(\sigma)\int f\,d\mu\), that
is, \(\sigma_*\mu=\mathrm{mod}_U(\sigma)^{-1}\mu\).

The Library has two forms of the radical. `B.unipotentRadical F` is the
kernel of \(\pi_B\) inside `B.parabolic F`. `B.unipotentSubgroup F` is its
image in \(\mathrm{GL}_n(F)\). The continuous group isomorphism
`B.unipotentRadicalAmbientEquiv F`, written \(e\) below, maps the first
onto the second by forgetting the intermediate parabolic.

## Radical elements

Let \(u\) lie in the kernel radical.
`Langlands.AllField.Parabolic.unipotentFiniteContainment` applied to the
one-point set \(\{u\}\) gives a compact open subgroup \(K\) of the kernel
radical that contains \(u\). Its preimage \(L\) under \(e^{-1}\) is a
compact open subgroup of `B.unipotentSubgroup F` that contains \(e(u)\).
Conjugation by \(e(u)\) maps \(L\) onto itself, since \(L\) is a subgroup
containing \(e(u)\). Then
`Langlands.HaarModulus.normalizerCharacter_eq_one_of_preimage` gives
\(\chi(u)=1\). That lemma evaluates the Haar measure normalized by
\(L\mapsto 1\) on \(L\) and on its preimage, which is \(L\) again.

## Block-diagonal elements

Let \(m\) be an element of the Levi `B.Levi F`, and let \(\mu\) be the
Haar measure on `B.unipotentSubgroup F`. The pushforward
\(\nu=e^{-1}_*\mu\) is a Haar measure on the kernel radical, and
\(e_*\nu=\mu\). `Langlands.AllField.glBlockModulusHaar` gives
\[
(\mathrm{Ad}\,m)_*\nu=\delta_B(m)^{-1}\nu,
\]
where \(\mathrm{Ad}\,m\) is `B.leviAction F m`. Conjugation by
`B.leviInParabolic F m` on `B.unipotentSubgroup F`, written \(\varphi\),
satisfies \(e\circ\mathrm{Ad}\,m=\varphi\circ e\); both sides send \(u\) to
the same matrix by definition. Pushing the displayed equality forward
along \(e\) gives \(\varphi_*\mu=\delta_B(m)^{-1}\mu\). By
`mulEquivHaarChar_eq`, the value \(\chi(m)\) is
\(\mathrm{haarScalarFactor}(\mu,\varphi_*\mu)\), so it equals
\(\mathrm{haarScalarFactor}(\mu,\delta_B(m)^{-1}\mu)\). From
`mul_haarScalarFactor_smul` and `haarScalarFactor_self`,
\(\delta_B(m)^{-1}\) times this factor is \(1\), so \(\chi(m)=\delta_B(m)\).

## Every parabolic element

The equivalence `B.decomposition F` factors \(g\in P_B\) as
\(g=u\cdot s(\pi_B(g))\). Here \(u\) is the radical element
`B.unipotentPart F g` and \(s\) is the block-diagonal section
`B.leviInParabolic F`. Since \(\chi\) is a homomorphism,
\(\chi(g)=\chi(u)\,\chi(s(\pi_B(g)))=\delta_B(\pi_B(g))\). This is the
asserted equality of homomorphisms on `B.parabolic F`.

No case is singled out. At rank zero the block shape is empty, the
parabolic, Levi and radical are trivial groups, the same argument applies,
and `T.leviModulus B` is an empty product.

## Relation to the source

Bernstein and Zelevinsky 1977 define the module in §1.7, printed p. 444,
and the standard parabolic triples of \(\mathrm{GL}_n\) in §§2.1–2.2,
printed p. 446. They do not write out \(\delta_B\). It comes from the
linear action \(X_{ij}\mapsto m_iX_{ij}m_j^{-1}\) on the strictly
upper-block entries; in the Library this computation is
`Langlands.AllField.glBlockModulusHaar`. The radical step corresponds to
their use of the fact that the radical is a limit of compact subgroups
(§2.3, printed p. 446). By §1.9, printed p. 445, such a group has trivial
modular character. The Lean proof shows this directly for the conjugation
module, without passing through the modular character.

## Dependencies

A traversal from the theorem recursively expanded every reached constant
of the project (the module roots `Langlands`, `FontaineWintenberger`,
`Nyll`, `StacksCore` and `StacksFrontier`) by
`Lean.ConstantInfo.getUsedConstantsAsSet`, through types and values. It
did not expand Lean or Mathlib constants. It was run on 26 November 2026
at Library commit `66a181ec9cda271c1ff0dcf555f386b52dc687c7`, in the
Library's Lean environment.

| Traversal root | Project constants | Defining project modules | Constants from classification modules |
| --- | ---: | ---: | ---: |
| `localFieldGeneralLinearModulusCompatibility` (type and proof) | 362 | 37 | 0 |
| `LocalFieldGeneralLinearModulusCompatibilityStatement` | 169 | 16 | 0 |

The 362 constants include compiler-generated auxiliary declarations; 201
of them have names that are not internal details in the sense of
`Lean.Name.isInternalDetail`. A classification module
means one whose name has a `Classification` component, for example the
modules under `Langlands.Representation.Classification`,
`Langlands.AllField.Representation.Classification` and
`Langlands.AllFieldBZ.Representation.Classification`. No declaration from
any such module is reached, so the proof uses no classification theorem.

Imports are a separate matter. The import closure of this proof module,
counting the module itself, has 662 project modules. Fourteen of them lie
under `Langlands.Representation.Classification`. All fourteen are already
imported by the statement module, through
`Langlands.Representation.Aubert.GeneralLinearSpecialization`. The two
modules that only the proof imports,
`Langlands.AllField.Group.GL.BlockModulusHaarProof` and
`Langlands.AllField.Representation.Parabolic.UnipotentFiniteContainment`,
add no further classification module. Importing a module does not make
its declarations dependencies.

## Source

- `bernstein-zelevinsky-1977-induced-i`,
  SHA-256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
  §§1.7–1.9 and 2.1–2.3, printed pp. 444–446.
