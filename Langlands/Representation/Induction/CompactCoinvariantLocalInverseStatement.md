# Normalized local sections in compact-induction coinvariants

Worker 626 states
`Langlands.Induction.CompactCoinvariantLocalInverseExists.{uG,uV}`,
with the interface and proposed route supplied by Worker 199. This is one
closed `Prop` definition asserting existence of a complex linear map

\[
 T:V_H\longrightarrow
       \bigl(\operatorname{cInd}_H^G(\sigma)\bigr)_G
\]

with the local characterization below. The module states the existence
proposition; it does not construct a witness or prove the proposition.

## Local characterization

For the supplied quotient measure \(\nu\), put

\[
 C_K=\operatorname{QuotientIntegration.compactOpenQuotientOrbit}(H,K),
 \qquad
 c_{\nu,K}=\operatorname{ofReal}\bigl((\nu(C_K)).\operatorname{toReal}\bigr)
             \in\mathbb C.
\]

Here \(C_K\) is the existing image of \(K\) in the actual left quotient
\(H\backslash G\); its points are cosets \(Hg\). For **every**
`K : OpenSubgroup G`, `hK : IsCompact (K : Set G)`, `v : V`, and

```lean
hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup
```

the same map \(T\) must satisfy

```lean
T (Representation.Coinvariants.mk σ v) =
  (Complex.ofReal
    ((ν (QuotientIntegration.compactOpenQuotientOrbit H K)).toReal))⁻¹ •
    Representation.Coinvariants.mk (compactInduced H σ)
      (compactDoubleCosetSection H σ K hK 1 v hv)
```

At `x = 1`, the fixed-vector condition means that \(H\cap K\) fixes \(v\).
The section is the actual `compactDoubleCosetSection` from
[`CompactLocalSection`](CompactLocalSection.md): its value at \(hk\), for
\(h\in H\), \(k\in K\), is \(\sigma(h)v\), and its value outside \(HK\)
is zero. It has compact projected support and is fixed by right
translation by \(K\). The proposition uses this construction and the
existing quotient orbit unchanged.

The existential quantifier for \(T\) precedes all choices of \(K\), `hK`,
\(v\), and `hv`. Thus the assertion requires the same normalized class
for any admissible choices representing the same inducing coinvariant,
linear compatibility of the normalized classes, and annihilation of the
\(H\)-coinvariant relations. These properties are
required by the existence of an actual linear map with domain
`Representation.Coinvariants σ`; they are not extra hypotheses.

The published
`QuotientIntegration.IsCompatible.compactOpenQuotientOrbit_mass` gives
\(0<\nu(C_K)<\infty\) for each compact open \(K\).
Consequently \(c_{\nu,K}\) is a positive real number embedded in
\(\mathbb C\), hence nonzero. This explains the reciprocal in the
characterization. Neither positivity nor a numerical volume formula is
added as a hypothesis, and no Haar or quotient measure is normalized to
give \(C_K\) mass one.

## Exact hypotheses and universes

The geometric, measure, and coefficient telescope is exactly that of the
published
[`CompactCoinvariantIntegralBijective`](CompactCoinvariantBijectivityStatement.md).
In particular, `G : Type uG` is a Hausdorff locally compact topological
group with supplied `MeasurableSpace G` and `BorelSpace G`. The
compact-open neighborhood basis is the literal hypothesis

```lean
∀ O : Set G, IsOpen O → (1 : G) ∈ O →
  ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O
```

`H : Subgroup G` is closed, carries its subtype topology, and has a
supplied Borel measurable structure. The measures `μG : Measure G` and
`μH : Measure H` each have exactly the instances `IsHaarMeasure`,
`Regular`, and `IsMulRightInvariant`. These are supplied regular
two-sided Haar measures. Their existence is not assumed for arbitrary
groups without these instances.

`QuotientIntegration.LeftQuotient H` is the existing
`Quotient (QuotientGroup.rightRel H)`, with its quotient topology and a
supplied Borel measurable structure. The measure
`ν : Measure (QuotientIntegration.LeftQuotient H)` is supplied with
`IsFiniteMeasureOnCompacts ν` and

```lean
hν : QuotientIntegration.IsCompatible H μG μH ν
```

Compatibility is the existing predicate: it includes nonzeroness,
regularity, preservation by the actual right translations, integrability
of subgroup averages of continuous compactly supported complex functions,
and their Weil integral formula for the supplied measures. This
proposition makes no new choice of a compatible measure.

The coefficient carrier `V : Type uV` has only `AddCommGroup V` and
`Module ℂ V`. The representation `σ : Representation ℂ H V` satisfies
`Langlands.IsSmooth σ`. The universes `uG` and `uV` are independent.
The domain of \(T\) is in `Type uV`; its codomain is in
`Type (max uG uV)`. Both are actual `Representation.Coinvariants`.
There is no topology, norm, completeness, finite dimension,
admissibility, or finite length assumption on \(V\).

The compact induction retains covariance
`f(h * g) = σ h (f g)` and ambient right translation
`f(x) ↦ f(x * g)`. There is no character or modulus twist. The only
assertion about \(T\) is the displayed local characterization. No global
section formula, bijectivity, kernel equality, or identity involving
`compactCoinvariantDesc` is assumed or asserted here.

## Original source and internal provenance

The motivating source is I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I*,
Ann. Sci. ENS (4) **10** (1977), 441–472, §5.17, printed pp.466–467
(PDF pages 27–28). Registered source:
`bernstein-zelevinsky-1977-induced-i`, retained at
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Worker 626 read and visually checked both cited pages.

On p.466 the source integrates the projected inducing function over
\(V'\backslash V\), with an inverse-character factor in the twisted case,
and descends the map to twisted coinvariants. Its isomorphism argument
reduces to \(N=\{e\}\), \(M=V'\), and trivial character. Renaming its
ambient group \(V\) to \(G\), subgroup \(V'\) to \(H\), and coefficient
space \(L\) to our \(V\) gives the untwisted setting motivating this work.
On p.467 the source first treats regular representations, then their
direct sums, and uses free resolutions and exactness to conclude.

The normalized local-section characterization here is an **internal
proposed elementary route**. It is not stated in §5.17 and is not the
source's regular-representation/free-resolution proof. The explicitly
supplied measure and full topological-group telescope are also internal
formulations, not a claim that BZ77 states this exact proposition.

The proposed later proof would compare normalized classes under compact
open refinement, use common refinements for choice independence and
linearity, and use conjugation and right translation to annihilate
\(H\)-relations. Smoothness would supply suitable compact open subgroups
for vectors. These steps remain proof obligations. The existing
[`CompactCoinvariantIntegral`](CompactCoinvariantIntegral.md) is the
separate construction motivating later assembly; this statement adds no
law about that integral. Its proof and the final integral-bijectivity
assembly remain separate work.

The statement compiled in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Exact declaration inspection
reports a definition returning `Prop` with precisely the independent
universe parameters `uG` and `uV`, using only `propext`,
`Classical.choice`, and `Quot.sound`. These development checks establish
the declaration's formal shape, not a proof of the proposition.
