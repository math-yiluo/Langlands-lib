# Clozel's prescribed one-split-place division existence statement

Worker 1728. This is an unproved Prop-valued statement of the one-place
case of Laurent Clozel, Représentations galoisiennes associées aux
représentations automorphes autoduales de GL(n), Publications mathématiques
de l'IHÉS 73 (1991), 97–145, Section 2, Proposition 2.3(i),(ii), its proof and
following choice-of-places remark, printed pp.105–106 (one-based PDF pp.10–11).
The construction uses the preceding Lemmas 2.1–2.2 and notation, printed
pp.101–105. Registered source clozel-1991-selfdual-galois, SHA256
9de7c13c9ae108e481de170327a06e44845cf87a6aabc1d5600176ee695e91ac.

The parameters are actual totally real and totally imaginary number fields
E and K, a specified quadratic K/E algebra structure, n, and a supplied
actual finite place v0 of E. Put d = Module.finrank Q E. The proposition
assumes n > 1, IsSplitPlace E K v0, and

- n odd; or
- 4 divides n; or
- n even and d even.

The final case includes multiples of four, already covered by the second
case, and is equivalent to the union of cases printed in Proposition 2.3(ii).
The split-place premise means an actual E_v0-algebra identification of
E_v0 tensor_E K with E_v0 times E_v0, carrying conjugation to the swap.
Clozel's remark permits prescribing this finite place.

The conclusion existentially quantifies the actual carrier A, its ring,
its E- and K-algebra structures, their scalar tower, and
D : CentralSimpleUnitaryData E K A n. It requires D.IsDivision, the existing
HasHarrisSignature for its second-kind involution, division at every actual
K-completion above v0, and the concrete maximal-Witt quasi-split
algebra-with-involution model at every other finite E-place. In particular,
local division includes both conjugate places over the split place. The
archimedean signatures retain their existing meaning as actual involution-
preserving real algebra equivalences. The distinguished real embedding is
existential in HasHarrisSignature, as in the source. No global algebra,
involution, signatures, global division or realization witness is a premise.
The quantified A lives in Type(max u v), allowing arbitrary field universes;
when E and K have universe zero, so does A.

This is a statement, not a theorem or an instance. Its declaration is
Langlands.Shimura.FiniteUnitary.ClozelOnePlaceExistenceStatement.
The explicit tensor and matrix models are in FiniteScalarExtension and
FiniteModels. The former's isDivision_of_isDivisionAt proves the elementary
reflection from division of an actual completed algebra, with injective
scalar extension and finite dimensionality retained. The global arithmetic
existence proof remains to be supplied against this precise proposition.

If this existence proposition is later proved and its conclusion chosen,
it supplies the actual CentralSimpleUnitaryData and the D.IsDivision
premise used by
Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel.DivisionCMRepresentabilityStatement
(the latter calls K by the name F). Applying that representability statement
also requires its own proof. At universe zero, the resulting Harris signature
can be converted by HarrisSignatureCharts.ofSignature only after choosing
a CM section Phi and proving IsCMSection E K Phi. The normalized consumer
uses a section obtained from an imaginary quadratic subfield L, its chosen
embedding, and the actual map L -> K. These arithmetic choices and the
consumer's compatible rational algebra/towers are further selections, not
outputs of this existence proposition. The tensor, Picard, duality,
polarization, finite Weil-transition, rational profinite integer/adele and
torsion finite-etaleness premises of representability are retained. Signature
charts alone do not discharge the PEL positivity, determinant, tensor,
integral auxiliary choices or moduli comparison obligations of its proof.

Harris 1999, Galois properties of cohomological automorphic forms on GL(n),
Section 1, printed pp.301–302, gives the motivating signatures and local
conditions. Section 4, printed p.308 (PDF p.10), further fixes the oriented
local value inv_w(B) = 1/n and requires a definite companion algebra with
specified local comparisons away from the selected places and their
conjugates. Registered source
harris-1999-cohomological-automorphic-forms-525a222c4489ee9d, SHA256
525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26.
Clozel's local division condition gives a primitive invariant, whose
numerator need not be 1. The exact oriented specialization, an actual
Brauer/cyclic-algebra comparison, the definite companion and the actual
inter-algebra local comparisons remain host obligations. No freely supplied
rational-valued invariant function replaces them here. Harris's printed [C4]
in Lemma 1.3 does not match a bibliography entry in that edition; the verified
Clozel original above is the source for this existence statement.
