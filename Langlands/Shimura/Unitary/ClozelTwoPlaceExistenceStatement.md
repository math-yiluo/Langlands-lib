# Clozel's prescribed two-split-place division existence statement

Worker 1728. This is an unproved Prop-valued statement of the two-split-place
option of Laurent Clozel, Représentations galoisiennes associées aux
représentations automorphes autoduales de GL(n), Publications mathématiques
de l'IHÉS 73 (1991), 97–145, Section 2, Proposition 2.3(i),(iii), its
choice-of-places remark and proof, printed pp.105–106 (PDF pp.10–11).
The local obstruction calculation uses Lemmas 2.1–2.2, printed pp.101–105.
Registered source clozel-1991-selfdual-galois, SHA256
9de7c13c9ae108e481de170327a06e44845cf87a6aabc1d5600176ee695e91ac.

The fields E and K, their quadratic K/E scalar map and the supplied finite
places are actual arithmetic objects. The proposition assumes n > 1,
distinct finite E-places v0 and v1, actual split-center identifications at
both places through IsSplitPlace, n = 2m for an odd natural number m, and
odd d = Module.finrank Q E. Clozel's remark permits these split places to
be chosen arbitrarily. The inert auxiliary-place alternative in (iii) is
outside this statement.

The conclusion existentially quantifies A in Type(max u v), its ring and
compatible E- and K-scalar structures, and the actual
D : CentralSimpleUnitaryData E K A n. Global division and HasHarrisSignature
are conclusions. At each prescribed split place every actual K-place above
it, including its conjugate, has a division completed algebra. All remaining
finite E-places have an actual center-compatible equivalence between
E_v tensor_E A with its extended involution and the standard maximal-Witt
matrix adjoint over E_v tensor_E K. The distinguished real embedding in
HasHarrisSignature is existential; the signatures are the existing actual
algebra-with-involution equivalences. No global algebra or desired signature,
division or realization property is assumed. With universe-zero fields the
existential carrier is also in universe zero.

The declaration is
Langlands.Shimura.FiniteUnitary.ClozelTwoPlaceExistenceStatement.
It proves no existence theorem and creates no instance. The elementary local
division reflection proof is in FiniteScalarExtension. A later proof of this
statement must supply the complete arithmetic realization.

As in ClozelOnePlaceExistenceStatement, a proved and chosen conclusion would
supply D and its division premise for
Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel.DivisionCMRepresentabilityStatement.
It does not prove representability or supply the consumer's CM-section,
normalized chart, rational scalar-tower and geometric premises. In particular
HarrisSignatureCharts.ofSignature also requires IsCMSection. The one-place
pair details the retained arithmetic selections and PEL/tensor/Picard and
moduli comparison obligations.

Local division leaves a primitive local invariant without prescribing its
orientation. The exact inv_w(B) = 1/n specialization of Harris 1999 Section 4,
printed p.308, an actual Brauer/cyclic-algebra comparison, the definite
companion algebra and the actual local comparisons between the two algebras
remain host obligations. No free invariant-valued function is introduced.
Harris's Section 1, pp.301–302, motivates the signatures; cite the verified
Clozel original directly for existence because the printed [C4] in Harris
Lemma 1.3 does not match the bibliography in that edition. Registered Harris
source harris-1999-cohomological-automorphic-forms-525a222c4489ee9d,
SHA256 525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26.
