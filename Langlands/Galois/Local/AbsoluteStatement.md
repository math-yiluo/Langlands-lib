# Complete target for the p-adic residue exact sequence

Author: Worker 9.

`Langlands.LocalGalois.PadicResidueExactness` quantifies over every natural number
\(p\), every proof that \(p\) is prime, every `Langlands.PadicField p` in an
arbitrary universe, and every supplied `F.TopologicalData`. It installs exactly
the supplied topology, valuation relation and local-field certificate.
Characteristic zero is derived from the algebra structure over `Padic p`.
There is no extra conclusion supplied as a hypothesis.

The body is `LocalResidueProperties F.Carrier`. The homomorphism and inertia in
that body are definitionally the `F.absoluteResidueHom T` and
`F.absoluteInertia T` constructions. For the actual algebraic closure
\(L=\operatorname{AlgebraicClosure}F\), its constructed valuation ring \(B\), and
the supplied residue field \(k\), the target requires:

1. The chosen norm preserves the supplied topology and integer ring. The
   constructed valuation on \(L\) extends the supplied valuation, \(B\) is the
   integral closure of the original integer ring, and every \(F\)-automorphism
   preserves that valuation.
2. The field \(k\) is finite. With `standardResidueAlgebra`, the residue field of
   \(B\) is an algebraic closure of \(k\). The explicit comparison with the chosen
   `AlgebraicClosure k` agrees with the natural residue embedding of every
   original integral element.
3. The constructed homomorphism sends the residue of every integral element to
   the residue of its image under the field automorphism, expressed through that
   closure comparison. It is continuous, surjective and open for the existing
   Krull topologies.
4. Its kernel is exactly `absoluteInertia`. Membership in this subgroup means
   acting trivially on the residues of all elements of \(B\). The subgroup also
   equals the inverse image of Mathlib's valuation-subring inertia under the
   decomposition-group comparison map.
5. Inertia is normal and closed. Its inherited topology is compact, totally
   disconnected and Hausdorff.
6. There is a topological group equivalence \(G_F/I_F\simeq G_k\), with the
   quotient topology, sending the class of every automorphism to its image under
   this particular residue map.
7. Reduction commutes with restriction at every normal intermediate field of
   \(L/F\), expressed using the constructed residue inclusion. This includes
   every finite Galois level.

`LocalResidueProperties` also exposes the same package for any characteristic-zero
nonarchimedean local field. Its nested `letI` clauses install proved constructions;
they do not quantify over assumed solutions to the residue problem.

The source correspondence and valuation/closure choices are described in
`AbsoluteDefinitions.md`. The cited original is Serre, *Local Fields*, Greenberg
English translation, Springer GTM 67 (1979): Chapter I, section 7,
Propositions 20–22 and the inertia definition, pp. 20–23 (PDF 28–31);
Chapter II, section 2, Proposition 3 and Corollaries 2–3,
pp. 28–29 (PDF 36–37); Chapter III, section 5, Theorems 2–3 and
Corollaries 1–3, pp. 54–55 (PDF 61–62). The retained original is
`C:/Central-Library/Serre--Local Fields--1979.pdf`, registered as
`serre-1979-local-fields`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
These finite/discrete-valuation source results motivate the derived infinite
statement; the topological passage and explicit transports require the proofs.

The Lean module imports `Langlands.Galois.Local.AbsoluteDefinitions`. That module
uses `Langlands.Galois.Local.SpectralProof` and
`Langlands.LocalField.Definitions`; its constructors fix all valuation, residue
algebra and closure choices used in this proposition. The environment is
Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

Both `LocalResidueProperties` and `PadicResidueExactness` are definitions
returning `Prop`. Publishing these statements does not prove them. The subsequent
proof must establish the entire Library statement
`Langlands.LocalGalois.PadicResidueExactness`, with exact-target validation,
independent semantic review and publication.
