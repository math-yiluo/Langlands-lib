# Normalized exponents for arbitrary actual parabolics

Author: Worker 6. Module `Langlands.Representation.Exponents.ArbitraryParabolic`, namespace `Langlands.Aubert.General.RepresentedParabolic`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VII.1.1, printed p.220 / PDF p.226. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The normalization is VI.1.2, printed pp.135–136 / PDF pp.141–142, particularly (VI.1.2.2) and the following modular-function convention remark.

This module applies the published normalized Jacquet functor and compact-open generalized-weight construction to the literal rational-point images of an arbitrary represented parabolic and its specified Levi and radical. It extends the domain of the definitions to every smooth representation; Renard begins VII.1.1 with an admissible representation. The decomposition and finiteness assertions that use admissibility remain separate results. The published standard-family definitions of Worker 1507 in `NormalizedJacquetSplitComponent` are imported unchanged and compared below.

## Actual objects and hypotheses

The field is `k : Type u`, with `[Field k]`, and the objects `G`, `P`, `M`, `U` are group schemes over `Spec k`. The actual maps are

- `p : P ⟶ G`, with `hp : IsParabolicSubgroup p`;
- `l : M ⟶ P`, with `hl : IsRationalLeviSubgroup l`;
- `r : U ⟶ P`, with `hr : LeviSubgroup.IsGeometricUnipotentRadical r`;
- `hmul : IsIso (subgroupMultiplication l r)`, for this same pair `l,r`;
- `a : A.toGrp ⟶ M`, with `ha : IsSplitComponent a`, where `A` is a commutative group scheme.

The choice of the geometric radical and the multiplication isomorphism explicitly refer to `r`, independently of the existential radical in `hl`. No universal existence of these objects or of such a decomposition is asserted. The generic functor itself needs only radical closedness and Levi normalization; the Levi and multiplication witnesses are retained in the wrapper's arguments to specify the intended actual parabolic data.

For the topological construction, `[TopologicalSpace k]` and `[IsAffineHom G.X.hom]` are assumed. The ambient point topology is the published `RationalPointFamily.pointTopology`, the canonical topology on `rationalPoints G`. Closedness additionally uses `[T2Space k]`. The Jacquet functor assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for this topology. All subgroup topologies are induced from this same ambient group. The split-component topology is the published `RationalPointFamily.splitComponentPointTopology ha`, constructed from the affineness supplied by `ha`.

The construction therefore applies whenever these displayed field and point-topology hypotheses hold. It includes the intended nonarchimedean local-field setting of arbitrary characteristic without restricting to `PadicField`, characteristic zero, split ambient groups or `GL_n`. No reductivity or local-field hypothesis is needed for these intrinsic constructions beyond the actual parabolic, Levi, radical and topology inputs. Representations are `SmoothRep.{0, u, v} ℂ (rationalPoints G)`, with independent field/group universe `u` and representation-carrier universe `v`.

## Point maps and their intrinsic laws

`pointImage j` is exactly `(rationalPoints.map j).range`. Thus the Levi and radical subgroups of `G(k)` are `pointImage (l ≫ p)` and `pointImage (r ≫ p)`.

`splitComponentPointsMap j a` is the homomorphism from `A(k)` into `pointImage j` obtained by mapping through `a` and then through the range restriction of `j`. The theorem `splitComponentPointsMap_val` identifies its ambient value with `j(k)(a(k)(t))`. The theorem `splitComponentPointsMap_mem_center` maps the centrality of the actual split component through the surjective map onto the Levi image, using `Subgroup.map_center_le_center`.

`pointImage_le_normalizer` proves that the Levi image normalizes the radical image. It specializes the geometric radical's all-test normality to `Spec k`, conjugates by the actual Levi point there, and maps the resulting equality through `p(k)`. There is no assumed point-level normalization predicate.

`isClosed_pointImage` uses the published closed rational-point subgroup theorem for a closed subgroup map, obtaining the required monomorphism from the underlying closed immersion. `isClosed_pointImage_comp` applies this to a composite of closed subgroup maps. Consequently `isClosed_leviPoints` deduces closedness of the literal Levi image from `hp` and `hl`, and radical closedness follows from `hp` and `hr`. In particular the Levi image is locally compact by closedness in the locally compact ambient group.

`continuous_splitComponentPointsMap` proves continuity for the actual composite `a ≫ j` into `G(k)`, then uses the induced topology of `pointImage j`. Its source is the same canonical split-component topology used by the published standard-family wrapper.

## Normalized quotient and exponent definitions

`jacquetFunctor p l r hp hr hl hmul` is an abbreviation for
`normalizedJacquetFunctor (pointImage (r ≫ p)) (pointImage (l ≫ p))`, with the closedness and normalization proofs just derived. This is the published actual coinvariant quotient, not a substitute functor. Its radical relations are the span of `π(n)v - v`, and its Levi action is the quotient action twisted by `HaarModulus.closedInverseHalfCharacter`.

`jacquetFunctor_obj_splitComponentPointsMap_apply` specializes the published action formula to the actual split-component point map. On the class of `x` it reads

`r(t)[x] = δ(t)^(-1/2) [π(t)x]`,

where `t` in the ambient action means `j(k)(a(k)(t))`, and `δ^(-1/2)` is precisely the Library's inverse-half Haar character for conjugation on the closed radical image. Renard writes the twist as `δ_P^(1/2)` in (VI.1.2.2). His remark on printed p.136 / PDF p.142 explains that his modular function is the inverse of the usual convention; this is the source identification used in the imported `Parabolic` and `NormalizedJacquetSplitComponent` modules.

`normalizedJacquetWeightSpace` is the published `generalizedWeightSpace` for this normalized Jacquet representation and the actual central split-component point map. It is a subrepresentation of the Levi image. For `χ : A(k) →* ℂˣ`, it is the compact-open union of the fixed generalized-character spaces in Renard's definition. The power is uniform in the torus point, not chosen separately for each point.

`IsNormalizedJacquetExponent` is the Prop-valued `IsGeneralizedWeight` for these data: `χ` has open kernel in the canonical topology of `A(k)`, and its weight space is nonzero. `normalizedJacquetExponents` is the set of those characters, Renard's `Exp(A, r_P^G V)`. The lemmas `isNormalizedJacquetExponent_iff_isOpen_ker_and` and `mem_normalizedJacquetExponents` give these definitional unfoldings.

## Membership and eigencharacter laws

The proofs use local compactness of the Levi image, deduced above, its inherited nonarchimedean group structure, and smoothness of the actual Jacquet object. They reuse the generic results of `SplitComponentWeights`:

- `mem_normalizedJacquetWeightSpace_fixed` states that membership is equivalent to the existence of a compact open subgroup `K` of the Levi image fixing the vector, together with `∃ d : ℕ, ∀ t : A(k), ((r(t) - (χ(t) : ℂ) • 1)^d)x = 0`.
- `mem_normalizedJacquetWeightSpace` removes the compact-open fixed-vector clause using smoothness, retaining the same single power `d` for all `t`.
- `normalizedJacquetWeightSpace_ne_bot_iff` identifies nonzero weight space with `IsGeneralizedEigencharacter` of the normalized quotient action composed with the split-component map.
- `isNormalizedJacquetExponent_iff` identifies the full exponent predicate with that eigencharacter condition. The smooth action and continuity of the actual point map make the open-kernel condition automatic by the published generic theorem. No finite-dimensionality or admissibility is added.

These are intrinsic construction laws. Their implemented proofs instantiate the existing generic weight-space results; they do not prove the direct-sum decomposition of VII.1.1.

## Comparison with the standard-family wrapper

`normalizedGeneralizedWeight_congr` is an internal transport lemma for any locally compact nonarchimedean ambient group `Γ` and any topological group `B`, in an independent universe. Given equal closed radical subgroups `N = N'`, equal Levi subgroups `L = L'`, and equality of the central maps `B →* L` and `B →* L'` after the subgroup identification, it proves equivalence of the generalized-weight predicates on the two actual normalized Jacquet objects. The proof eliminates the two subgroup equalities, obtains equality of the monoid homomorphisms by extensionality, and then uses definitional equality and proof irrelevance. Both Levi groups use the induced topology from `Γ`.

`isNormalizedJacquetExponent_iff_standard` applies this transport to the published `RationalPointFamily.IsNormalizedJacquetExponent`. Its inputs include the standard family `i, ν, I`, a represented standard Levi `j, hj`, its semidirect-decomposition witness `h` and radical closedness `hU`, as well as three explicit compatibility identifications:

1. `eU`: the arbitrary radical image equals the standard radical subgroup;
2. `eM`: the arbitrary Levi image equals the standard Levi subgroup;
3. `eA`: after `MulEquiv.subgroupCongr eM`, the arbitrary split-component point map equals the published standard-family point map.

The source split component is the same `a, ha`, so its canonical topology agrees on both sides; the subgroup equalities transport the quotient action and the subgroup topologies. The result identifies the exponent predicates for each `π, χ`. It assumes these explicit identifications and does not assert conjugacy, universal standard reduction, or the existence of a represented standard Levi.

## Source correspondence and remaining obligations

| Renard VII.1.1 | Lean declaration or input |
| --- | --- |
| An arbitrary `P = MN` and its split component `A` | Actual maps `p,l,r,a`, their stated properties, and the matching multiplication isomorphism |
| The normalized quotient `r_P^G V` | `jacquetFunctor` and its split-component action formula |
| The compact-open union defining `(r_P^G V)_χ` | `normalizedJacquetWeightSpace`, `mem_normalizedJacquetWeightSpace_fixed` |
| A smooth character with nonzero characteristic space | `IsNormalizedJacquetExponent`, its open-kernel and eigencharacter characterizations |
| `Exp(A, r_P^G V)` | `normalizedJacquetExponents`, `mem_normalizedJacquetExponents` |

The actual point-image packaging, its intrinsic laws and the explicit standard-family comparison are derived implementation content. The definitions agree with VII.1.1 and VI.1.2 at the source's admissible inputs and extend them to smooth inputs. This unit does not establish admissibility or finite-length preservation, the characteristic-space direct sums including (VII.1.1.1), finiteness of the exponent set, the `P = G` comparison with III.1.10, the following induction/restriction lemmas, Casselman's criterion, or temperedness. It supplies the arbitrary-parabolic exponent interface needed to formulate the all-parabolic quantifier of VII.2.1. Those representation-theoretic assertions and structural existence/comparison theorems remain separate obligations.
