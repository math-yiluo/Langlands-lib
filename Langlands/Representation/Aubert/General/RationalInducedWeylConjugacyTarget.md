# Weyl conjugacy on the standard rational-point family

Author: Worker 1186. This pair specializes the published generic
`General.inducedK0WeylConjugacy` and `General.inducedClassWeylConjugacy`
targets to the actual standard family constructed by Worker 165. Both new
declarations are universally quantified propositions; neither proves an
instance or makes a representation-theoretic identity a structural field.

`RationalInducedK0WeylConjugacyStatement` states `i_J ∘ Ad(n) = i_I` as an
equality of integer-linear maps on exact finite-length Grothendieck groups.
`RationalInducedClassWeylConjugacyStatement` states equality of the actual
normalized induced representation classes. In both statements `n` ranges
over every element of the normalizer of `torusPoints i`, the literal image
of the maximal split torus on rational points. Its premise is exactly
`x ∈ levi J ↔ n⁻¹*x*n ∈ levi I`. The conjugation functor therefore acts on
`σ` by the pullback `x ↦ σ(n⁻¹*x*n)`. No isomorphism of the two induced
representations is asserted. No choice of a Weyl lift or independence
assumption is substituted for the universal quantifier.

The scope is every connected reductive group scheme over every
nonarchimedean local field, with an actual maximal split torus and a generic
cocharacter. The labels are literally `SimpleRoot i ν`; `parabolic`, `levi`
and `unipotent` are the existing identity-test standard subgroup functors
at their actual character subsets. The ambient group is `RationalPoint k G.X`
with its canonical evaluation topology `pointTopology`. The declarations
impose no characteristic-zero, split, quasisplit, positive-rank or
nonempty-root premise. No finite enumeration is needed for these identities.

The explicit premises are:

- Local compactness, the nonarchimedean-group property and Hausdorffness of
  the canonical topology. These are not replaced by an arbitrary topology.
- `StandardCocharacterStatement`, which supplies the actual standard-to-dynamic
  subgroup comparisons. The imported adapter derives each semidirect
  decomposition, rather than taking a free decomposition family.
- Closed standard unipotent and parabolic point subgroups, continuous
  standard Levi projections, and the compact-limit condition on each
  unipotent subgroup.
- Preservation of finite length by the actual normalized induction and
  Jacquet functors, separately named `hiFl` and `hrFl`.

`standardParabolicFiniteLength` derives the four finite-length/exactness
conditions required by the generic target from these premises and the
published topological exactness theorems. No proof of finite-length
preservation, closedness, projection continuity or the compact-limit
condition is supplied here. The exact K0 groups impose all actual short
exact sequence relations. Representation carriers have universe
`max (u + 1) v`, matching the existing rational-point operator interface.

No Coxeter system or root action is used: the statement directly quantifies
actual normalizer elements carrying the two literal Levi subgroups onto
one another. Scheme/point normalizer and centralizer comparisons remain
separate structural targets; they are needed when comparing with the
scheme Weyl quotient, not to define this statement on the actual group.
The actual quotient retains the full-centralizer denominator.

The provenance is a derived specialization of Aubert 1995, identity (1.2),
printed p.2181, used immediately before (1.8) on p.2182, and Ban–Jantzen 2016,
Proposition 4.1(3), printed p.158. The original-source record and dependency
analysis are in `../GeneralWeylConjugacyTarget.md`. The intended
Ban–Jantzen route requires general character independence, Langlands
classification and the geometric lemma; their proof declarations and
hypotheses must be recorded by the parent. They are representation-theoretic
obligations, outside the permitted final external Chapter V structural
boundary. Aubert Proposition 3.2 supplies no evidence.

The parent task `46df6a68-5db4-4428-8044-05151d6ce1f6` owns the proof
successors and discharge of these premises. Only this target pair is selected
for publication; the imported constructions retain their separate owners.
