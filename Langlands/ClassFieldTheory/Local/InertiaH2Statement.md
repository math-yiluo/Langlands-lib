# Vanishing of continuous degree-two cohomology of local inertia

Author: Worker 60.

The proposition `Langlands.ClassFieldTheory.Local.InertiaH2Vanishing.{u}`
asserts that, for every prime `p` and every `F : PadicField.{u} p`,

\[
H^2_{\mathrm{cts}}\bigl(I_F,(\overline F)^\times\bigr)=0.
\]

It is a proposition definition, not a proof. Its universe `u` is arbitrary.
The only quantified data are `p`, its primality certificate, and the actual
p-adic field `F`. There are no norm-surjectivity, Brauer-vanishing,
class-formation, invariant-map, or cohomology-vanishing assumptions.

## Exact Lean objects

The subgroup `I_F` is precisely
`F.absoluteInertia F.canonicalTopologicalData`, as constructed in
`Langlands.Galois.Local.AbsoluteDefinitions`. It is a subgroup of
`Field.absoluteGaloisGroup F.Carrier`, which carries the Krull topology.
The subgroup uses its inherited subtype topology.
`Langlands.Continuous.subgroupInclusion I_F` is the continuous subgroup
inclusion into that same absolute Galois group.

The coefficient object is `TopRep.res` along this inclusion of
`absoluteUnits F.Carrier` from
`Langlands.ClassFieldTheory.Local.Cohomology`. The explicit
`.toMonoidHom` supplies the same inclusion to the restriction API.
Its carrier is
`Additive (AlgebraicClosure F.Carrier)ˣ`, with the existing discrete
topology and the genuine action of algebra automorphisms on units.
Restriction keeps this carrier and topology and lets an inertia element
act through its underlying absolute Galois automorphism. The use of
`Additive` only changes notation for the multiplicative group law.
The scalar ring is explicitly the existing `IntegerScalars.{u}`,
the universe lift `ULift.{u} ℤ`.

The conclusion is `Subsingleton` of the carrier of Mathlib's
`continuousCohomology` in degree `2` of this restricted coefficient
object. This is the homology of its continuous homogeneous cochain
complex. Since this cohomology is an additive group with a zero element,
the conclusion says that every class is zero. No replacement cohomology
carrier or alternative field model is introduced.

## Source and derived formulation

Jean-Pierre Serre, *Local Fields*, Greenberg English translation, Springer
GTM 67 (1979), registered as `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 60 read the following original passages. PDF page numbers count
from one. No project errata entry for this source was present when checked.

- Chapter V, section 4, Proposition 6 and its corollary, Lemmas 6–7,
  and Proposition 7, printed pages 88–90 / PDF pages 95–97. Proposition 6
  and its corollary handle the cyclic prime-degree norm calculation
  after unramified base extension. The lemmas descend finite extensions
  of the maximal unramified field to finite levels. Proposition 7
  concludes surjectivity of the norm for finite separable extensions
  between finite extensions of that maximal unramified field.
- Chapter X, section 7, Proposition 11 and example b, printed pages
  161–162 / PDF pages 167–168. Proposition 11 relates norm surjectivity,
  cohomological triviality of finite Galois unit modules, and vanishing
  of Brauer groups over finite separable extensions. Its proof uses
  Hilbert 90 and passage to the limit. Example b applies the norm result
  of V.4 to the maximal unramified extension.
- Chapter XII, section 1, Theorem 1 and its proof, printed page 181 /
  PDF page 186. Vanishing over the maximal unramified field implies
  that each Brauer class over the original complete field splits over
  a finite unramified extension. This explains the use of the present
  target as a prerequisite for unramified exhaustion.

The present statement is a derived actual-inertia formulation of that
route, not a verbatim theorem of the cited pages. Serre's original
complete discretely valued field is `F.Carrier`; its residue field is
finite and hence perfect. His maximal unramified extension must be
realized inside the chosen `AlgebraicClosure F.Carrier`.

A future proof must establish the required fixed-field correspondence:
the fixed field of this exact inertia subgroup is that maximal
unramified extension. It must also establish the corresponding
topological Galois-group identification, including compatibility of
the Krull topology with the subgroup topology, and identify the
discrete unit action with the restricted action used here. Finally it
must transport the source's finite-stage Galois cohomology and
cohomological Brauer vanishing to this exact continuous homogeneous
cochain model with `IntegerScalars.{u}`. These are proof obligations,
not hypotheses hidden in the target or identifications supplied by
this file. No identification with an unrelated central-simple-algebra
Brauer implementation is asserted.

The published `UnitNormProof` concerns finite unramified extensions of
p-adic fields; it does not supply the norm theorem for extensions over
the maximal unramified field required by this route.
`Langlands.Galois.Local.AbsoluteProof` supplies results about actual
inertia, but does not prove the degree-two vanishing stated here.
This file leaves `UnramifiedH2Exhaustion` and all its imports unchanged;
its proof and the substantial comparison results remain separate work.
