# Actual coefficient action on rational normalizer points

This internal construction uses the actual coefficient conjugation on rational
points of a base-changed group and restricts it to the existing normalizer
subgroup. Its point map, inverse and multiplication convention are those of
`GaloisPointComparison.rationalConjugate`. Its full-character covariance uses
the existing character-lattice coefficient action.

The first lemmas work over arbitrary base schemes. For a supplied commutative
group scheme `C`, group scheme `H` and map `j : C.toGrp ⟶ H`,
`IsNormalizingPoint.baseChangeBasePoint` pulls back the given normalizing point
itself along an arbitrary base map, together with the supplied normalizing
automorphism. It applies the base-change functor to the normalizing equation;
`baseChange_innerIso_hom` identifies the inner automorphism of the actual
pulled-back point. The given automorphism is not replaced by an existentially
selected one.

For maps `b : S ⟶ B` and `a : S ⟶ S` with `a ≫ b = b`,
`IsNormalizingPoint.baseChange_descent` follows that pullback by the canonical
ambient descent isomorphism. The published naturality square and normalizer
transport theorem identify its normalizing automorphism as conjugation of the
pulled-back original automorphism by the canonical commutative-group descent
isomorphism. `baseChange_descent_of_eq` states the same result for any target
point identified with this explicit point; the generic point-equality lemma
justifies the substitution.

Now let `k` and `K` be fields in an arbitrary common universe, with a supplied
`k`-algebra structure on `K`. Supply a commutative group scheme `T`, a group
scheme `G` over `k`, and a map `i : T.toGrp ⟶ G`. Write `T_K`, `G_K` and `i_K`
for their actual base changes. No splitness, reductivity, smoothness,
affineness, finiteness or Galois-extension assumption is used.

`rationalConjugate_eq_baseChange_descent` identifies the existing coefficient
conjugate of each rational point with its explicit pullback along the spectrum
map of the coefficient automorphism, followed by the canonical descent
isomorphism. Its proof applies the existing rational/coefficient point
equivalence. The projection formula for coefficient conjugation and the
projection identities for point pullback and canonical descent give equality
of the underlying scheme maps. Thus the construction has exactly the original
coefficient convention.

`torusAutGaloisTransport` names the corresponding explicit canonical transport
of an automorphism of `T_K`. `IsNormalizingPoint.rationalConjugate` combines the
point identity with the generic transport lemma. It proves that the existing
coefficient conjugate of the original representative normalizes through this
specific transported automorphism. Consequently
`rationalConjugate_mem_normalizerPoints` preserves membership in the entire
existing normalizer subgroup.

`normalizerGaloisAction` is a group homomorphism from `K ≃ₐ[k] K` to
multiplicative automorphisms of that same normalizer subgroup. Its forward map
is existing coefficient conjugation and its inverse uses the inverse
coefficient automorphism. Subtype extensionality and the existing coefficient
identity, composition and multiplication formulas prove its inverse and group
laws. `normalizerGaloisAction_coe` records exact equality of the carrier map
with the existing coefficient map.

For `weylAction_normalizerGaloisAction` only, assume that the underlying scheme
map of `i_K` is a monomorphism. Uniqueness identifies the chosen normalizing
automorphism of the conjugate point with the explicit transported one. The
published `characterAut_descentTransport` then proves that simultaneous
coefficient transport of the normalizer point and any character intertwines
the full existing Weyl character action. This holds for every character,
without root-membership or split-torus hypotheses.

The provenance is internal: these results follow from the imported point,
canonical descent, conjugation, normalizer and character constructions. No new
external literature assertion is made. This unit supplies actual normalizer
transport and character covariance. It does not assert preservation of a
canonical valuation class, compatibility of the induced apartment action with
the normalizer action, a metric, special point, original supplied-model fixer
comparison or descent of the building. The full `BuildingComparisonStatement`
remains open.
