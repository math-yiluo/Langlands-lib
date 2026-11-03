# Root association and the actual support-category conjugation witness

Authors: Worker 593 and Worker 165. Worker 165 supplied the assembly route
from the existing character-image and structural-conjugation declarations.

This internal adapter derives the actual Levi-conjugation condition from
the existing `rootAssociation` predicate, keeping the same rational point.
It uses only the structural inputs already visible in the rational support
targets. It does not assert any Jacquet vanishing or support presentation.

The field `k` is arbitrary. The group scheme is connected reductive, its
given torus is maximal split, and its cocharacter is generic. The standard
cocharacter statement and the actual normalizer and centralizer comparison
predicates are explicit inputs. There is no hypothesis on the characteristic,
splitness of the ambient group, relative rank, finiteness or nonemptiness of
the simple-root type, or a Coxeter realization.

`levi_map_conj_of_rootAssociation` unpacks a witness at the actual rational
point `n`. It transports its normalizer membership through `normalizerEquiv`
and rewrites its character image using `weylCharacterAction_point_mk`.
The published
`GroupScheme.standardLeviConjugationStatement_of_standardCocharacterStatement`
derives the structural conjugation statement from the stated standard
cocharacter input. Then `levi_map_conj_of_character_image` evaluates that
statement on the actual rational-point Levis. The conclusion is the literal
image equality
`(levi I).map (MulAut.conj n) = levi J`, where forward conjugation is
`x ↦ n * x * n⁻¹`. Transporting normalizer membership preserves the ambient
point; no replacement representative is chosen.

`conjugationMembership_of_rootAssociation` applies
`Langlands.Aubert.General.conjugationMembership_of_map_eq`. Its conclusion is
exactly `x ∈ levi J ↔ n⁻¹ * x * n ∈ levi I`. Thus the orientation agrees
with the support-category predicate.

`rootAssociationLeviConjugationEquiv` uses the existing `conjugationEquiv`
construction to give a continuous group equivalence from `levi J` to `levi I`
by inverse conjugation. For this construction only, a topological group
structure on the rational points is assumed; the result applies in particular
to the canonical evaluation topology used by the rational targets.

`no_associated_levi_iff_no_rootAssociation` proves a logical equivalence
between the target's exact quantified exclusion condition and absence of
root-association witnesses at all `J ⊆ K`. The forward implication supplies
the membership equivalence just proved to contradict the exclusion. The
reverse implication eliminates the impossible root-association witness.
The actual target is preserved; this equivalence is available for use in
its proof without replacing its statement.

Provenance is internal composition of published structural and
normalizer-comparison APIs. The proof bodies invoke no Langlands
classification, character independence, geometric lemma, adjointness,
finite-length theorem, or representation-theoretic cuspidal-support theorem.
The imported `RationalStandardComplex` supplies the actual `rootAssociation`
definition and the existing framework; no theorem about its complex is used.
All imported hypotheses and source boundaries remain as stated in those
modules. In particular, this adapter does not prove the standard cocharacter
statement that it assumes.
