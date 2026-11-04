# The fixed-Levi terminal-cokernel comparison on the actual rational points

## Result and preserved scope

`Langlands.Aubert.General.RationalPointFamily.rationalFixedLeviComparison`
proves the complete published proposition
`Langlands.Aubert.General.RationalPointFamily.RationalFixedLeviComparisonStatement.{u, v}`
from `Langlands.Representation.Aubert.General.RationalTerminalJacquet`. The
theorem has no parameters outside that proposition. Its independent universes
are `u` and `v`; representation carriers have universe `max (u + 1) v`.

For every connected reductive group scheme `G` over every nonarchimedean local
field `k` in the target, every maximal split torus, generic cocharacter and
linear order on the actual `SimpleRoot i ν` labels, and every standard subset
`I`, it constructs a natural isomorphism

`C.ι ⋙ r_I ⋙ LeviComplex.sharpFunctor … I … Finset.univ ≅ C.ι ⋙ r_I`,

where `C` is the full support subcategory `TerminalJacquet.supportObjects … I`
of smooth representations of the actual group `RationalPoint k G.X` with the
canonical `pointTopology`. Here `r_I` is the actual normalized Jacquet functor
`jacquetFunctor (h I) (hclosed I)`. The parabolic, Levi and unipotent families
are the literal `parabolic i ν`, `levi i ν` and `unipotent i ν`. The
decomposition, monotonicity, association, Levi-decomposition and Levi
unimodularity proofs are exactly the terms that the statement builds from its
premises. This is the content of `TerminalJacquet.FixedLeviComparisonStatement`
at universes `.{u, u, max (u + 1) v}`. Because `C.ι` is a full inclusion, the
naturality covers every actual equivariant map between objects of `C`. The
inverse laws are part of the constructed `CategoryTheory.Iso`.

Every displayed premise and quantifier is retained as a binder: the local
compactness, nonarchimedean-group and Hausdorff instances, `hStandard`,
`hOrder`, `hInter`, `hRoots`, `hN`, `hZ`, the closedness families `hU` and `hM`,
and the restricted compact-limit family `hUcLevi`. Nothing is added: there is
no finite-length, admissibility, finite-generation, endpoint, compactness,
Coxeter, ambient compact-limit, support, exactness or irreducibility premise.
Positive characteristic, nonsplit and non-quasisplit groups, empty simple-root
sets and relative rank zero are all covered, since the argument makes no case
distinction on the group or on `I`.

The implemented argument proves more than the target needs. The full-support
Levi cokernel functor is naturally isomorphic to the identity functor on all of
`SmoothRep(M I)`, not only on Jacquet modules of objects of `Alg({I})`. In
particular, the proof does not use the cuspidality of the Jacquet module.
The task context explicitly permits this direct full-Levi degree-zero route.

## Implemented argument

The proof has four layers. They are listed from the generic complex up to the
rational-point family. All declarations below are in the namespace
`Langlands.Aubert.General`.

**Endpoints of a semidirect decomposition.**
`IsSemidirectDecomposition.parabolic_eq_top_of_levi_eq_top` shows that a
decomposition `P = M ⋉ U` with `M = ⊤` has `P = ⊤`, from `levi_le`.
`IsSemidirectDecomposition.unipotent_eq_bot_of_levi_eq_top` shows that it has
`U = ⊥`: an element `u ∈ U` lies in `P` by `unipotent_le` and in `M = ⊤`. As an
element of `P` it therefore lies in both complement factors, which are disjoint
by `isComplement'.disjoint`, so `u = 1`.

**Degree zero of the generic complex (namespace `Complex`).** Let `P, M, U` be
the families indexed by removed-root sets `s`, with `P ∅ = ⊤` and `U ∅ = ⊥`.

- `initialTerminalMap A` is the actual initial map
  `Complex.initialMap A : A → Degree 0` followed by the canonical quotient
  projection `Complex.terminalProjection A 0`.
- `terminalProjection_zero_injective`: the incoming boundary
  `Complex.boundary A 0` is defined to be `⊥` (by the match in
  `General/Terminal.lean`). If two vectors have the same image, their
  difference lies in `⊥` by `Submodule.Quotient.eq`, so they are equal.
- `initialTerminalMap_bijective`: the initial map is bijective, because it
  underlies the published equivalence `Complex.initialEquiv` at `P ∅ = ⊤` and
  `U ∅ = ⊥`. The projection is injective by the previous item and surjective by
  `Complex.terminalProjection_surjective`.
- `initialTerminalMap_natural`: for every equivariant `φ : A ⟶ B`,
  `initialTerminalMap B ∘ φ = terminalMap φ 0 ∘ initialTerminalMap A`. This
  combines `Complex.initialMap_natural` (the degree map commutes with the
  initial maps) with `Complex.terminalMap_comp_projection` (the terminal map
  commutes with the projections).
- `terminalZeroIso`: the components `SmoothRep.mkIso` of the bijective
  intertwining maps `(initialTerminalMap A).ofBijective` form a natural
  isomorphism `𝟭 ≅ Complex.terminalFunctor … 0` by `NatIso.ofComponents`.
  Its naturality square is checked after `SmoothRep.toRep`, which is faithful,
  by `Rep.hom_ext` and `initialTerminalMap_natural`. The definition is the
  inverse of this isomorphism, `Complex.terminalFunctor … 0 ≅ 𝟭`.
- `terminalIsoOfDegreeEqZero` transports `terminalZeroIso` along an equality
  `k = 0` with `eqToIso`.

**The full-support Levi functor (namespace `LeviComplex`).**
`leviIndex_univ` shows that the full finset of `J`, read in the ambient root
set, is `J`; it uses `Finset.univ_eq_attach` and `Finset.attach_map_val`.
Hence `family_levi_univ`: the restricted Levi `(M J).subgroupOf (M J)` at the
full support is `⊤`, by `Subgroup.subgroupOf_self`. `terminalDegree_univ`
computes `Complex.terminalDegree univ = card J − card J = 0`.

`sharpFunctorUnivIso` constructs
`LeviComplex.sharpFunctor … J … Finset.univ ≅ 𝟭 (SmoothRep (M J))`. By
definition, `LeviComplex.sharpFunctor` unfolds to `StandardComplex.sharpFunctor`
on the restricted families. That abbreviation is `Complex.sharpFunctor` on the
removed-root families `StandardComplex.removedFamily`, and `Complex.sharpFunctor`
is in turn the abbreviation `Complex.terminalFunctor … (terminalDegree univ)`.
At the empty removed set, `removedFamily F ∅ = F (univ \ ∅) = F univ` by
`Finset.sdiff_empty`. The supplied Levi decomposition `hJ univ`, with
`family_levi_univ`, gives the endpoints through the two decomposition lemmas.
The restricted parabolic at the full support is `⊤`, and the restricted radical
is `⊥`. Then `terminalIsoOfDegreeEqZero` applies with `terminalDegree_univ`.
The family proofs passed to it are the ones in the definition of
`LeviComplex.sharpFunctor`, so the result has exactly that functor as source.

**The generic and rational targets.** `TerminalJacquet.fixedLeviComparison`
proves `TerminalJacquet.FixedLeviComparisonStatement` for every generic
standard family, without a `Fintype` instance on the index type. For each `I`
it whiskers `sharpFunctorUnivIso` for `J = I` on the left by
`C.ι ⋙ jacquetFunctor (h I) (hclosed I)`, and composes with the associator and
the right unitor.

`RationalPointFamily.rationalFixedLeviComparison` introduces the target's
binders. It installs the instances that the statement installs (`isAffineHom`,
`Mono` of the torus embedding and `pointTopology`). Then it applies the generic
theorem to the literal `parabolic i ν`, `levi i ν` and `unipotent i ν`, and to
the closedness families `hU` and `hM`. The remaining arguments unify with the
proofs that the statement constructs. The statement's `simpleRelativeRootFintype`
instance is not needed by the generic theorem.

## Declaration dependencies

The proof uses the following published declarations. Names without a prefix
are in `Langlands.Aubert.General`.

| Declarations | Role and underlying proof |
| --- | --- |
| `Complex.initialEquiv`, `Complex.initialMap` (`General/Initial.lean`) | The actual initial map to degree zero, and its equivalence at `P ∅ = ⊤`, `U ∅ = ⊥`. Its proof combines `Complex.degreeZeroEvaluation_bijective` (degree zero has exactly the empty removed-root coordinate) with `Complex.augmentation_empty_bijective`. The latter transfers bijectivity through `Complex.termEquiv` from `Langlands.Aubert.SubgroupTransition.initial_augmentation_injective` (evaluation at one) and `initial_augmentation_surjective` (a function covariant under the full group is determined by its value at one). |
| `Complex.initialMap_natural` | Naturality of the initial map, from `Complex.augmentation_natural` and `Langlands.Aubert.SubgroupTransition.augmentation_natural`. |
| `Complex.boundary`, `Complex.terminalProjection`, `Complex.terminalProjection_surjective` (`General/Terminal.lean`) | The incoming boundary (defined as `⊥` in degree zero), the canonical quotient projection, and its surjectivity (`Submodule.mkQ_surjective`). |
| `Complex.terminalMap`, `Complex.terminalMap_comp_projection`, `Complex.terminalFunctor`, `Complex.sharpFunctor` (`General/Naturality.lean`) | The actual terminal functor and its compatibility with the projection. The compatibility holds by definition (`rfl`). |
| `Complex.terminalDegree` | `Fintype.card ι − I.card`. |
| `StandardComplex.sharpFunctor`, `StandardComplex.removedFamily`, `.removedFamily_antitone`, `.removedFamily_monotone` | The removed-root reindexing used by the standard complex. |
| `LeviComplex.sharpFunctor`, `LeviComplex.family`, `.family_monotone`, `.family_antitone`, `leviIndex` | The actual Levi cokernel functor on the restricted families. |
| `IsSemidirectDecomposition` (`levi_le`, `unipotent_le`, `isComplement'`) | The structure fields used for the endpoints. |
| `TerminalJacquet.FixedLeviComparisonStatement`, `TerminalJacquet.supportObjects`, `jacquetFunctor` | The generic target, the support category `Alg({I})` and the actual normalized Jacquet functor. They are used only as given; their internals are not unfolded. |
| `Langlands.SmoothRep.mkIso`, `Langlands.SmoothRep.toRep` | Smooth isomorphisms from bijective intertwining maps, and the faithful forgetful functor to `Rep`. |

The rational target's own construction terms
(`RationalPointFamily.isSemidirectDecomposition_of_standardCocharacterStatement`,
`standardParabolic_monotone`, `standardUnipotent_antitone`, `rootAssociation`,
`isSemidirectDecomposition_in_levi`, `standardLeviUnipotent_isUnimodular`) occur
because they are part of the statement. The proof passes them through without
using their content.

### Dependency trace

A trace of the theorem's project constants through both their types and values,
including private and auxiliary declarations, gives about 56,500 constants. All
but about one hundred already lie in the trace of the statement itself. The
extra constants are this module's own declarations and the initial-map,
naturality, subgroup initial-term, subgroup transition and `SmoothRep.mkIso`
declarations listed above.

A name scan of the whole trace for classification, geometric, adjoint,
Frobenius, independence, linear independence and cuspidal material finds only
the following. Each lies in the trace of the statement:

- the algebraic `Langlands.GroupScheme.adjoint`, `lieKernelConjugationLinear`,
  `basePointAdjoint`, `adjoint_naturality` and
  `IsNormalizingPoint.adjoint_mem_weightSpace`, which belong to the root and
  split-torus infrastructure and concern the algebraic adjoint action;
- the definitions `IsLeviCuspidal` and `IsCuspidalFor`, which enter through the
  definition of the support category;
- auxiliary side proofs `RationalJacquetCuspidalStatement._proof_1/2/3`
  (`Mono` and decomposition terms shared with the statement's elaboration).

No Langlands classification theorem, character-independence result, geometric
lemma, representation adjointness or cuspidal-support theorem is used. The
module import closure contains `Classification`, `CuspidalSupport` and
`Geometric` modules and `Parabolic.NaturalFirstAdjointness`, all through the
target's own imports. The declaration trace reaches none of their theorems.
The separately owned Jacquet cuspidality statement (task `b752450b`) is not
used.

## Source and provenance

Source: Aubert, erratum to "Dualité dans le groupe de Grothendieck de la
catégorie des représentations lisses de longueur finie d'un groupe réductif
p-adique" (1996), registered `aubert-1996-duality-erratum`, original PDF SHA256
`d76b3ef9ea2310d1a3129da990c1abd6c304027e3e939a5a1f06c666978c145f`, printed
p.4690 / PDF p.4, Remark (1) immediately before (**). It states
"Pour tout E ∈ Alg({I}), on a D̃_{L_I}(r_{L_I}^G(E)) = r_{L_I}^G(E)",
with `D̃` the terminal cokernel `coker d_{|I|}` defined just before. The target
strengthens this object equality to a natural isomorphism. Aubert justifies it
by the cuspidality of `r_{L_I}^G(E)`. The implemented proof uses a different
route: at the full Levi support the retained terminal degree is zero, and the
degree-zero cokernel divides out nothing. The intermediate lemmas above are
internal implementation details of this route. Aubert Proposition 3.2 and its
defective original application are not used. The target pair and every pair in
its import closure are unchanged.
