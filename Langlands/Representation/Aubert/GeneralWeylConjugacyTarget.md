# Weyl conjugacy of induced exact-K0 classes

Author: Worker 1186. This module reuses Worker 23's actual normalized
parabolic functors and exact-K0 maps, and the published actual
normalizer/full-centralizer quotient of Worker 165.

The two declarations in namespace `Langlands.Aubert.General` are
Prop-valued targets. Neither is a proof or an external Chapter V
structural assertion.


The imported `General/Parabolic` and `General/AlternatingOperator` pairs
are the unmodified, unreviewed Worker 23 adapter draft revision 1 from task
`593ef603-6672-4424-976c-14e11e920d9c`. They are frozen validation
dependencies, excluded from this target pair's publication paths. Their
independent acceptance and publication must precede integration of this
pair; target review does not accept or publish those adapters.

## Exact statements

`inducedK0WeylConjugacy` states equality of integer-linear maps

`i_J ∘ Ad(n) = i_I : K0(M I) → K0(G)`.

`n` is an element of the actual `RelativeWeyl.normalizer T`. The explicit
premise

`∀ x : G, x ∈ M J ↔ n⁻¹*x*n ∈ M I`

says precisely that the actual subgroup `M J` is `n*(M I)*n⁻¹`.
`conjugationK0 n` is the adapter's exact-K0 pullback along the continuous
equivalence from `M J` to `M I` with formula `x ↦ n⁻¹*x*n`.
The target quantifies every such normalizer element, hence every lift of
each applicable class in the actual quotient `N_G(T)/Z_G(T)`.
It asserts no representation isomorphism or pointwise independence of a
chosen lift.

`inducedClassWeylConjugacy` writes the same intended equality directly on
actual representation classes: for every finite-length smooth `σ` of
`M I`, the normalized induction of the literal conjugation pullback to
`M J` and the normalized induction of `σ` have equal exact K0 classes.
The transported representation has finite length by the published
`SmoothRep.pullbackFunctor_preservesFiniteLength`, applied to
`conjugationEquiv`. The two induced length witnesses come from the visible
induction part of `ParabolicFiniteLength`.

This module does not prove the equivalence between its two target
formulations. That comparison uses the existing generator formulas
`inductionK0_ofRepresentation`, `conjugationK0_ofRepresentation` and the
published `SmoothRep.FiniteLengthGrothendieckGroup.hom_ext_object`.

## Scope and dependencies

The ambient group is a locally compact nonarchimedean topological group;
the subgroup families are actual `P I`, `M I`, `U I`, with the actual
semidirect decompositions and closed unipotent subgroups supplied.
`ParabolicFiniteLength` is an explicit representation-theoretic
assumption supplying induction/Jacquet finite length and exactness. The
representations used to form exact K0 have carriers in `Type (max uG uV)`.
The constructed K0 type lies in `Type (max uG ((max uG uV) + 1))`, since
the isomorphism-class and exact-relation quotients retain the universe of
packaged representation objects without resizing.

To assert the source result, the families and `T` must be specialized to
standard rational-point parabolics, their Levis and a maximal split torus
in the shared general reductive framework. No theorem is asserted for an
arbitrary unrelated subgroup family. The generic signatures introduce no
characteristic-zero, split or quasi-split restriction; the general
local-field realization remains an obligation. Unlike the alternating
operator, this identity needs no enumeration of all root subsets, so the
target itself does not require `Fintype ι`.

| Source or construction | Declaration used or required | Status and owner |
| --- | --- | --- |
| Actual normalized induction and inverse-conjugation transport | `normalizedInductionFunctor`, `conjugationFunctor`, `conjugationEquiv` from `General/Parabolic` | Actual adapters owned by task `593ef603-6672-4424-976c-14e11e920d9c`, Worker 23. |
| Exact finite-length K0 maps | `inductionK0`, `conjugationK0`, `ParabolicFiniteLength` from `General/AlternatingOperator` | Conditional actual maps. Finite length and exactness are visible named premises, owned by Workers 23 and 1180; the parent must discharge them. |
| Equivalence pullback | `SmoothRep.pullbackFunctor_preservesFiniteLength` | Published generic theorem; it supplies only transport finiteness. |
| Actual Weyl quotient | `Langlands.Group.RelativeWeyl.normalizer`, `.Weyl` | Published construction with denominator the full centralizer. It supplies no induced-class identity. |
| Aubert (1.2), printed p.2181, citing Bernstein–Deligne–Kazhdan Lemma 5.4(iii) | `inducedK0WeylConjugacy` and `inducedClassWeylConjugacy` | Targets supplied here. A proof successor belongs to parent `46df6a68-5db4-4428-8044-05151d6ce1f6`. |
| Ban–Jantzen 2016 Proposition 4.1(3), p.158 | The same two targets under the actual standard-Levi specialization | Published literature route uses character independence, Langlands classification and the geometric lemma. Their general declaration-level instantiations remain prerequisite work, coordinated with existing Renard owners. |

The last row is a dependency requirement for the intended proof, not
evidence that those prerequisites have already been formalized. This
module has no proof of Weyl-conjugacy and imports no classification proof.
Any future proof following Ban–Jantzen must record the actual general
classification, character-independence and geometric-lemma declaration
names and their hypotheses. The currently inspected GL-specific
`Langlands.PadicField.TopologicalData.TemperedLanglandsDatum.langlandsQuotient`
is a head construction, not a general classification theorem and not a
replacement for that requirement. An unproved general prerequisite may
not be hidden in the external Chapter V structural list.

## Original-source record

Registered source `aubert-1995-duality`, pp.2180–2182, defines the source
Levis and functors, states identity (1.2), and uses it after (1.8).
Registered source `ban-jantzen-2016-duality`, Proposition 4.1(3) and its
proof on printed p.158, explicitly lists the three representation-theoretic
ingredients above. Those passages were read directly from the originals.
The scope of the target is the untwisted connected reductive case of the
general Aubert program; no finite-central-extension theorem is claimed
here. Aubert Proposition 3.2 is not evidence for this identity.
