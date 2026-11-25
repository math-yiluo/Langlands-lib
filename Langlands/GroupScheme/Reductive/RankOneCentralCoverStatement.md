# An actual central cover in semisimple rank one

`Langlands.GroupScheme.RankOneCentralCoverStatement.{u}` is an internal
prerequisite for the rank-one branch of a proof of split reductive root-datum
existence independent of the dynamic-Borel inputs. This module defines the
proposition; it supplies no proof of cover existence.

Let `k : Type u` be an algebraically closed field, let `G` be a connected
reductive group scheme over `Spec k`, and let `T` be a split commutative torus
with a prescribed maximal-torus homomorphism `i : T.toGrp ⟶ G`. The roots are
the published `roots i` from `Langlands.GroupScheme.Torus.Weights`: nonzero
characters of `T` with nonzero weight space in the actual adjoint Lie
representation. Weight-space membership is tested over every test algebra.
The hypotheses require this root set to be nonempty and require
`¬ LinearIndependent ℤ ![α, β]` for every pair of roots in the actual
character lattice.

The conclusion asks for a split commutative torus `C`, a central isogeny
`f : SL₂ × C.toGrp ⟶ G`, and a homomorphism of commutative group schemes
`t : D × C ⟶ T` whose underlying group-scheme map is an isogeny. Here
`D = splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin 1))`.
The first product is the actual categorical product, written `⊗` in the
cartesian monoidal structure on group schemes; the second is
`CommGroupScheme.prod D C`, with that underlying product and its
componentwise commutative law. The compatibility condition is the equality
of actual group-scheme homomorphisms
`(SpecialLinear.FinSucc.diagonalTorus 1 (CommRingCat.of k) ⊗ₘ 𝟙 C.toGrp) ≫ f =
CommGroupScheme.groupHom t ≫ i`.
The diagonal-torus map sends `z` to `diag(z, z⁻¹)` on points over every test
scheme.

`IsIsogeny` retains the finite-flat-surjective convention for the underlying
scheme morphism. `IsCentralIsogeny f` additionally requires local finite
presentation and centrality of the full scheme-theoretic kernel via
`IsCentral (kernelι f)`. This includes possible nonreduced kernels in
positive characteristic; it does not assert surjectivity on points over
each test scheme.

Its provenance is an internal reduction: the explicit matrix computation in
`Langlands.GroupScheme.Reductive.SpecialLinearRoots` gives the two opposite
roots of `SL₂`; the commutative factor has trivial adjoint action; and the
published central-isogeny nonzero-weight comparison, together with
injectivity of character pullback along the torus isogeny, is intended to
transport the rank-one conclusion to `G`. This module does not implement
that consumer reduction or attribute this exact proposition to a numbered
literature result.

The proposition assumes no root datum, reducedness, reflection-existence
theorem, root-cell coordinates, or rank-one classification. Its proof
`rankOneCentralCover` in `Reductive.RankOneCentralCoverProof` meets separate
independence conditions (it avoids the dynamic-Borel route); those
conditions are not additional hypotheses of this proposition. No cover
proof is given in this module. In particular, starting a classification proof
with the assumption that the actual roots are already `±α` would not supply
the input needed for the proposed reducedness argument.
