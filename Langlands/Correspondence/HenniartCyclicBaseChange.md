# Local cyclic base change of prime degree for supercuspidal classes

This module gives definitions and one proposition; it proves nothing about
base change. It formalizes input (I3) of Option II of the operator's note
*The numerical local Langlands correspondence for GL_n: counts on the two
sides and the recommended route of proof*
(`operator-numerical-llc-route-2026-11-16`, `numerical-LLC-route.tex`):
Theorem `thm:BC` of §6.4 (lines 1109–1134), in the weak form that §7.1
(`sec:units`), item 6 (lines 1309–1310) recommends.

Throughout, `p` is a prime with `[Fact p.Prime]`, the positive rank is
\(n=k+1\) and is written `k.succPNat` in Lean. The field universe `uK` and the
representation universe `uV` are independent. A supercuspidal class of rank
\(n\) over a p-adic field `K` is an element of the Library's
`SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat`.

## Definitions in `Langlands.Henniart.Numerical`

### Cyclic steps of prime degree

`CyclicPrimeStep.{uK} p` is a cyclic extension \(M/L\) of prime degree of
p-adic fields; the case \(\ell=p\) is allowed. Its fields are:

- `base : PadicField.{uK} p`, the field \(L\);
- `top : PadicField.{uK} p`, the field \(M\);
- `embedding : base.Carrier →ₐ[Padic p] top.Carrier`, the embedding of \(L\)
  in \(M\) over \(\mathbb Q_p\). This is how the Library represents
  extensions of p-adic fields (`Langlands/Weil/Local/ExtensionWeil.lean`);
- `isGalois`: \(M/L\) is Galois for the algebra structure
  `Weil.Local.extensionAlgebra base top embedding` that the embedding gives;
- `card_prime`: for that algebra structure the group
  \(\Gamma=\operatorname{Gal}(M/L)\) of \(L\)-algebra automorphisms of \(M\)
  has prime order, measured by `Nat.card`.

A group of prime order is cyclic, so \(M/L\) is cyclic. For a step `S`,
`S.algebra` is this algebra structure and `S.Gal` is the type \(\Gamma\) of
`S.top.Carrier ≃ₐ[S.base.Carrier] S.top.Carrier`.

### Invariants of a step

- `S.degree` is \(\ell=[M:L]\), the Library's `Weil.Local.extensionDegree`,
  that is the `Module.finrank` of \(M\) over \(L\). For a Galois extension it
  equals the order of \(\Gamma\) (Mathlib's `IsGalois.card_aut_eq_finrank`),
  hence is the prime of `card_prime`. The module does not restate this.
- `S.residueDegree` is the residue degree \(f(M|L)\), the Library's
  `Weil.Local.extensionResidueDegree`: the dimension of the residue field of
  `S.top.canonicalTopologicalData` over that of `S.base.canonicalTopologicalData`,
  for the residue map induced by the embedding.
- `S.ramificationIndex` is the ramification index \(e(M|L)\): the normalized
  valuation `ord` of the canonical realization of \(M\), applied to the image
  under the embedding of the chosen uniformizer of the canonical realization
  of \(L\), and converted to `ℕ` by `Int.toNat`. This copies the Library's
  absolute index `PadicField.TopologicalData.ramificationIndex`, the
  `ord` of `p`. Mathematically the valuation of the image is positive, so
  `toNat` loses nothing.
- `S.differentExponent` is the exponent \(d(M|L)\) of the different of
  \(\mathcal O_M/\mathcal O_L\). It is the infimum in `ℕ` of the exponents
  \(d\) with `differentIdeal 𝒪_L 𝒪_M = 𝔭_M ^ d`. Here `differentIdeal` is
  Mathlib's different ideal, and \(\mathcal O_L\), \(\mathcal O_M\) are the
  integer rings of the canonical realizations. Their algebra structure is the
  Library's `relativeIntegerAlgebra`, installed exactly as in the published
  target `LocalClassField.PrimeRamifiedDifferent`. Since the different is a
  nonzero ideal of a discrete valuation ring, there is exactly one such
  \(d\). The module does not prove this. If the set were empty, Lean's
  `sInf ∅ = 0` would apply.
- `S.wildDifferentExponent` is \(c(M|L)=d(M|L)-e(M|L)+1\), the wild part of
  the different exponent, computed in `ℤ`. In the tame case \(d=e-1\) it is
  \(0\). Computing in `ℤ` rather than truncating in `ℕ` keeps the formula
  literal.

### Herbrand function

`S.herbrandPsi : ℝ → ℝ` is the Herbrand function \(\psi_{M/L}\). By definition
it is the Library's `Langlands.Ramification.Padic.herbrandPsi` with
`T = S.top.canonicalTopologicalData` over `K = S.base.Carrier`, for
`S.algebra` and the scalar tower over `Padic p` from
`Weil.Local.extensionAlgebra_isScalarTower`. That function is defined on the
whole real line. It is the inverse of the Library's `herbrandPhi`, which is
Serre's \(\varphi_{M/L}\) built from the lower ramification groups of the
integer ring of `T` (Serre, *Local Fields*, IV.3), extended by the identity
below \(-1\). Serre defines \(\varphi_{M/L}\) and its inverse
\(\psi_{M/L}\) only on \([-1,\infty)\). So `S.herbrandPsi` agrees with
Serre's \(\psi_{M/L}\) on \([-1,\infty)\), and \(\psi(x)=x\) for \(x<-1\).
The Library proves \(\psi(x)=x\) for all \(x\le0\)
(`Ramification.Padic.herbrandPsi_of_nonpos`).

### Galois action on supercuspidal classes

`S.galoisAutomorphism g` is \(g\in\Gamma\) viewed as an automorphism of \(M\)
over \(\mathbb Q_p\) (`AlgEquiv.restrictScalars`).

`S.galoisConjugate g k` is the bijection \(\Pi\mapsto\Pi^g\) of the rank-\(n\)
supercuspidal classes over \(M\). Convention: \(\Pi^g(x)=\Pi(g(x))\), where
\(g(x)\in\mathrm{GL}_n(M)\) applies \(g\) to every entry of \(x\). In Lean it is
the Library's `GeneralLinear.SupercuspidalClass.fieldPullbackEquiv` along
\(g\), which pulls a representation back along the entrywise isomorphism
`GeneralLinear.fieldEquiv`. The inverse bijection pulls back along
\(g^{-1}\). Both \(g\) and \(g^{-1}\) are continuous for the canonical topology
of \(M\) (`VirtualRepresentation.PadicSupercuspidal.continuous_algEquiv`). With
this convention \((\Pi^g)^h=\Pi^{gh}\), a right action. Nothing below depends
on choosing \(g\) rather than \(g^{-1}\): invariance under all of \(\Gamma\),
the orbit, and the condition "\(\Pi_1^g\ne\Pi_1\) for \(g\ne1\)" are the same
for both choices.

`S.galoisConjugateSigma g` applies \(\Pi\mapsto\Pi^g\) to a class of any
positive rank, packaged as `Σ k : ℕ, SupercuspidalAutomorphicClass … k.succPNat`,
and keeps the rank.

`S.galoisOrbit τ₁` is the \(\Gamma\)-orbit of a class \(\Pi_1\) of rank
\(k_1+1\), as a multiset with one entry \(\Pi_1^g\) for each \(g\in\Gamma\). It
is `Finset.univ.val.map` over \(\Gamma\). The `Fintype` structure on \(\Gamma\)
comes from finiteness, because `card_prime` makes `Nat.card Γ` nonzero. With
\(\Gamma=\{1,g,\dots,g^{\ell-1}\}\) this is the cuspidal support
\(\Pi_1,\Pi_1^g,\dots,\Pi_1^{g^{\ell-1}}\) of
\(\Pi_1\boxplus\Pi_1^{g}\boxplus\dots\boxplus\Pi_1^{g^{\ell-1}}\) in the route
note.

### Norm characters

`S.normCharacters` is the set \(\Xi\) of characters \(\eta\) of \(L^\times\)
that are trivial on the norm group \(N_{M/L}(M^\times)\). Characters are the
Library's `Correspondence.QuasiCharacter S.base`, the continuous homomorphisms
\(L^\times\to\mathbb C^\times\) for the canonical topology of \(L\). These are
the characters the twist module `Langlands.Correspondence.HenniartTwistSwanStatement`
uses. Triviality means that `LocalClassField.normSubgroup S.base.Carrier S.top.Carrier`,
the image of the norm map \(M^\times\to L^\times\), is contained in the kernel
of \(\eta\). By local class field theory \(\Xi\) is a group of order \(\ell\)
(route note, line 1110). The module defines \(\Xi\) as a set and does not prove
its finiteness or its order.

### Candidate base-change maps

`CyclicBaseChangeMap S` is the type of maps that send, for every rank
\(n=k+1\), a supercuspidal class over \(L\) to a multiset of supercuspidal
classes over \(M\) of arbitrary positive ranks. Each entry carries its rank
\(k'+1\) as the first component of a `Σ`-pair. The multiset stands for the
cuspidal support of the base change \(\mathrm{Ch}(\pi)\), with multiplicities.

### Swan exponent of a supercuspidal class

`supercuspidalSwanExponent K π : ℕ` is the conductor `Numerical.conductor K π`
of a rank-\(n\) class, read in `ℕ` through `WithTop.untopD 0`, minus \(n\) with
truncated subtraction. The conductor is the first level at which \(\pi\) has a
nonzero vector fixed by the last-row congruence subgroup (JPSS 1981, §5).
`WithTop.untopD` is the name of `WithTop.untop'` in the pinned Mathlib; it
sends \(\top\) to the default \(0\) and a finite value to itself. When the
conductor equals a natural number \(a\), the value is \(a-n\). So, by
definition and when the conductor is finite,
`supercuspidalSwanExponent K π = s` exactly when `HasSupercuspidalSwan K π s`
from `Langlands.Correspondence.HenniartRefinedStrata` holds. When the
conductor is \(\top\), the value is \(0\) while `HasSupercuspidalSwan K π s`
fails for every \(s\), because that predicate requires a finite conductor.
Mathematically the conductor of a supercuspidal class is finite (JPSS 1981);
this module neither assumes nor uses that fact. The truncation gives \(0\) for
unramified characters of \(\mathrm{GL}_1\), as in the route note's convention
(lines 183–185).

### The weak base-change property

`IsWeakCyclicBaseChange S Ch` is the following proposition. Write
\(\mathrm{Ch}(\pi)\) for `Ch k π`. Write \(\eta\pi\) for
`supercuspidalCharacterTwist S.base k η π`, the twist
\((\eta\circ\det)\otimes\pi\) of the twist module. For every \(k\) and every
rank-\(n\) supercuspidal class \(\pi\) over \(L\):

- **(W1)** The ranks of the entries of \(\mathrm{Ch}(\pi)\) add up to \(n\).
  For every \(g\in\Gamma\), mapping \(\Pi\mapsto\Pi^g\) over \(\mathrm{Ch}(\pi)\)
  returns \(\mathrm{Ch}(\pi)\).
- **(W2)** \(\mathrm{Ch}(\eta\pi)=\mathrm{Ch}(\pi)\) for every \(\eta\in\Xi\).
- **(W3a)** Suppose \(\eta\pi\ne\pi\) for every \(\eta\in\Xi\) with
  \(\eta\ne1\). Then \(\mathrm{Ch}(\pi)=\{\Pi\}\) for a single class \(\Pi\) of
  rank \(n\). Moreover, for every rank-\(n\) class \(\pi'\) over \(L\),
  \(\mathrm{Ch}(\pi')=\mathrm{Ch}(\pi)\) holds if and only if
  \(\pi'=\eta\pi\) for some \(\eta\in\Xi\).
- **(W3b)** Suppose \(\eta\pi=\pi\) for every \(\eta\in\Xi\). Then
  \(\ell\mid n\), and there is a class \(\Pi_1\) of rank \(k_1+1=n/\ell\)
  with \(\Pi_1^g\ne\Pi_1\) for every \(g\ne1\), such that \(\mathrm{Ch}(\pi)\)
  is the orbit `S.galoisOrbit Π₁`. Moreover \(\pi\) is the only rank-\(n\)
  class \(\pi'\) over \(L\) with \(\mathrm{Ch}(\pi')=\mathrm{Ch}(\pi)\). The
  quotient \(n/\ell\) is natural-number division, which is exact because
  \(\ell\mid n\). Since \(\Gamma\) has prime order, "\(\Pi_1^g\ne\Pi_1\) for
  every \(g\ne1\)" is the route note's "\(\Pi_1^g\not\cong\Pi_1\)" for a
  generator \(g\).
- **(W4)** In `ℤ`, with \(f=\) `S.residueDegree`,
  \(c=\) `S.wildDifferentExponent` and
  \(\operatorname{sw}=\) `supercuspidalSwanExponent`,
  \[
  f\sum_{\rho\in\mathrm{Ch}(\pi)}\operatorname{sw}(\rho)
  =\sum_{\eta\in\Xi}\operatorname{sw}(\eta\pi)-f\,c\,n .
  \]
  The left sum runs over the multiset with multiplicities. The right sum is
  Mathlib's `finsum` over \(\Xi\), written `∑ᶠ η ∈ S.normCharacters, …`.
  By local class field theory \(\Xi\) is finite, and then this is the
  ordinary sum over \(\Xi\). In general, `finsum` adds up the nonzero terms
  with \(\eta\in\Xi\) when there are finitely many of them, and is \(0\)
  when there are infinitely many.

In addition, for every \(k\):

- **(W3c)** Every \(\Gamma\)-invariant rank-\(n\) class \(\Pi\) over \(M\)
  has \(\{\Pi\}=\mathrm{Ch}(\pi)\) for some rank-\(n\) class \(\pi\) over \(L\).
  Likewise, suppose \(\ell\mid n\) and \(\Pi_1\) has rank \(n/\ell\) with
  \(\Pi_1^g\ne\Pi_1\) for every \(g\ne1\). Then `S.galoisOrbit Π₁` is
  \(\mathrm{Ch}(\pi)\) for some rank-\(n\) class \(\pi\) over \(L\).

The hypotheses of (W3a) and (W3b) are stated separately. The fact that one of
them always holds (the stabilizer of \(\pi\) in \(\Xi\), a group of prime
order \(\ell\), is trivial or everything) is not part of the proposition.

## Statement in `Langlands.Henniart`

`LocalCyclicBaseChangeStatement.{uK, uV} : Prop` is input (I3). For every
prime `p` and every cyclic step `S : Numerical.CyclicPrimeStep.{uK} p` there
is a map `Ch : Numerical.CyclicBaseChangeMap.{uK, uV} S` with
`Numerical.IsWeakCyclicBaseChange S Ch`. The module does not prove it. Task
7340 (simple trace formula and local base change) has it as its target.

## Provenance

The whole package comes from Arthur–Clozel, *Simple algebras, base change,
and the advanced theory of the trace formula* (1989,
`arthur-clozel-1989-base-change`), Chapter 1, §6, from printed p. 51, in the
form of Henniart, *La conjecture de Langlands locale numérique pour GL(n)*
(1988, `henniart-1988-numerical`), 6.1–6.5, printed pp. 513–517. This is how
the route note's Theorem `thm:BC` (lines 1111–1129) states it. Henniart writes
\(L/K\) for the extension, top over base; the route note and this module
write \(M/L\).

- (W1) is (BC1) read on cuspidal supports. \(\mathrm{Ch}(\pi)\) has rank
  \(n\), and the image of \(\mathrm{Ch}\) consists of \(\Gamma\)-invariant
  classes (Henniart 6.1(7), from Arthur–Clozel Ch. 1, Theorem 6.2 and
  Proposition 6.8).
- (W2) is the case \(\eta\in\Xi\) of (BC2), Henniart 6.1(1).
- (W3a)–(W3c) are (BC3)(a)–(c), Henniart Propositions 6.4 (printed p. 515,
  proof to p. 517) and 6.5 (p. 517). Proposition 6.4 calls the integer \(r\)
  the "indice" of the stabilizer of \(\pi\) in \(\Xi\). As the route note's
  comments after `thm:BC` explain (line 1133), the proof and Proposition 6.5
  show that the order of the stabilizer is meant.
- (W4) is (BC4), Henniart 6.1(5) (printed p. 514):
  \(f_{L/K}\,s(\mathrm{Ch}_{L/K}\pi)=-f_{L/K}\,c_{L/K}\,n+\sum_{\eta\in\Xi}s(\eta\pi)\).
  Henniart deduces it from the \(\varepsilon\)-identity 6.1(4), which is
  Arthur–Clozel Ch. 1, Proposition 6.9(ii) (printed pp. 60–61). On the left,
  \(\operatorname{sw}(\mathrm{Ch}\,\pi)\) is the sum of the Swan exponents over
  the cuspidal support, as the route note defines it for non-supercuspidal
  representations (line 1104).

## The weak form

The proposition is the weak form of the base-change package. It is the route
note's own formulation in §7.1, item 6 (lines 1309–1310). For the descent it
suffices to assume maps \(\mathrm{Ch}_{M/L}\) with \(\Gamma\)-invariant image,
compatible with \(\boxplus\), satisfying (BC3) and (BC4). The Shintani
character identity in (BC1) and the identity (BC5) do not occur in Lemmas
`lem:slopebc` and `lem:step`. Accordingly, the module:

- takes only supercuspidal inputs and returns cuspidal supports, a multiset
  of supercuspidal classes over \(M\), instead of classes of \(\mathrm{GL}_n(M)\);
- omits the character identities, (BC5), and (BC2) for characters outside
  \(\Xi\).

Theorem `thm:BC` implies this weak form. Let \(\mathrm{Ch}(\pi)\) be the
cuspidal support of the base change of a supercuspidal \(\pi\). Then (W1)
follows from (BC1), (W2) from (BC2), and (W3a)–(W3c) from (BC3). In case (a)
of (BC3) the base change is supercuspidal; in case (b) it is the \(\boxplus\)
of its cuspidal support. So in both cases equal cuspidal supports mean equal
base changes. (W4) is (BC4) once the route note's Swan exponent
\(\operatorname{sw}(\pi)=a(\pi)-n\) (lines 183–185) is read through the Lean
conductor. The route note (lines 179–181) takes \(a(\pi)\) to be the
\(\varepsilon\)-factor conductor. Its identification with the new-vector level
`Numerical.conductor` is a separate premise of the project (JPSS 1981,
Theorem 5.1; `Conductor.ConductorExponentStatement`). This argument is an
informal explanation, not a Lean proof.

The descent (route note lines 1136–1195) uses only the cuspidal support of
\(\mathrm{Ch}(\pi)\), its \(\Gamma\)-invariance, the fibres in (BC3) and the
conductor identity (BC4). `S.herbrandPsi` is the function \(\psi_{M/L}\) of
Lemma `lem:slopebc` (line 1137).
