# Identity and composition of whole varying-torsor system base change

Author: Worker 13.

This internal construction proves identity and composition coherence for the
whole-system comparison in
[EtaleVaryingSystemPullback](EtaleVaryingSystemPullback.md). Its inputs are the
actual constant-associated coherence maps in
[EtaleConstantAssociatedPullbackCoherence](EtaleConstantAssociatedPullbackCoherence.md),
the geometric fiber-product comparisons in
[EtaleTorsorPullbackFunctoriality](EtaleTorsorPullbackFunctoriality.md), and the
contravariant maps of complete systems in
[VaryingSystemCoverChange](VaryingSystemCoverChange.md). It claims no new
external-source result and assumes no desired coherence equation.

Let `X`, `Z`, `W : Scheme.{u}`, let `f : Z ⟶ X` and `g : W ⟶ Z` be etale,
and let `R : Type u` be a commutative ring. Let `I : Type uI` carry a category
with morphisms in universe `vI`, and let `D : I ⥤ GrpCat.{u}`. A cover diagram
`Y : EquivariantDiagram D X.Etale` is equipped with
`hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i)`. A coefficient diagram
`M : EquivariantDiagram D (ModuleCat.{u} R)` is arbitrary. The ring, module
carriers, schemes and groups share universe `u`; index object and morphism
universes are independent. No filteredness, surjectivity of group transitions,
or finiteness, freeness or local constancy of the coefficient diagram is added.

Write `P_f` for the actual geometric cover-diagram pullback and `r_f` for
`EtalePullback.restriction f (ModuleCat R)`, which uses postcomposition on the
small-etale sites. Write `Q_f` for postcomposition of sheaf diagrams with `r_f`,
namely `(Functor.whiskeringRight I _ _).obj r_f`. Write `L_X(Y)` for the
functor from coefficient diagrams to sheaf diagrams
`etaleAssociatedVaryingSystemFunctor X Y hY`. The existing natural isomorphism
is

`lambda_f(Y) : L_X(Y) ⋙ Q_f ≅ L_Z(P_f Y)`.

Every system transition is the existing coefficient-reduction map followed
by the inverse of the proved finite-torsor cover-comparison map. Thus the
comparisons here concern these complete systems, with all their transitions
and coefficient-diagram morphisms. The finite-torsor hypotheses for all
base-changed covers are supplied by the existing pullback theorem.

`etaleSheafDiagramRestrictionId R X` lifts restriction identity to an
isomorphism `Q_id ≅ Id` on the category of sheaf diagrams. It maps the existing
restriction isomorphism through `Functor.whiskeringRight` and uses that
postcomposition with the identity functor is the identity. Its forward component
at a diagram `F` and an index `i` is exactly
`(EtalePullback.restrictionId (ModuleCat R)).hom.app (F.obj i)`.

`etaleSheafDiagramRestrictionComp f g R` similarly constructs
`Q_f ⋙ Q_g ≅ Q_(g ≫ f)`. It uses the canonical comparison for postcomposition
of functors and maps the actual `EtalePullback.restrictionComp` isomorphism
through `Functor.whiskeringRight`. Its forward component at `F` and `i` is
exactly `restrictionComp(f,g).hom.app (F.obj i)`. These two constructions and
their component formulas apply to arbitrary module-sheaf diagrams and do not
require `D`, a cover, or a torsor hypothesis.

`etaleTorsorDiagramPullbackId_evaluation` identifies evaluation of the geometric
diagram identity comparison with the existing action-level comparison. It
projects `P_id(Y_i)` to `Y_i` by the first fiber projection. The proof uses
extensionality of action morphisms and of morphisms over a scheme, then removes
the extra identity map in the diagram comparison.
`etaleTorsorDiagramPullbackComp_evaluation` identifies evaluation of the
single-to-iterated diagram comparison with the existing action-level comparison.
It is definitional. Both geometric facts permit arbitrary base morphisms;
etaleness is required by the sheaf restrictions elsewhere in the file.

`etaleAssociatedVaryingSystemPullbackComp f g R Y hY` constructs the natural
isomorphism

`(L_X(Y) ⋙ Q_f) ⋙ Q_g ≅ L_W(P_(g ≫ f) Y)`.

It composes the functor associator, the sheaf-diagram restriction-composition
isomorphism whiskered by `L_X(Y)`, and `lambda_(g ≫ f)(Y)`. Its forward
component at `M` and `i` is exactly the restriction-composition map on
`L_X(Y)(M).obj i`, followed by the constant-associated comparison for `g ≫ f`
on `Y_i` and `M_i`. Naturality and invertibility come from these constructed
natural isomorphisms.

Let `p_Y : P_id(Y) ⟶ Y` be the genuine identity-pullback projection and
`c_Y : P_(g ≫ f)(Y) ⟶ P_g(P_f(Y))` the genuine single-to-iterated cover map.
Write `q_a` for `etaleAssociatedVaryingSystemCoverChange` along a cover-diagram
map `a`; it reverses the cover arrow. Then
`etaleAssociatedVaryingSystemPullback_id` proves equality of the natural
transformations

`lambda_id(Y).hom = (L_X(Y) whiskered restrictionId).hom ≫ rightUnitor.hom ≫ q_p`.

The explicit functor unitor identifies `L_X(Y) ⋙ Id` with `L_X(Y)`.
Both sides map restricted systems to the actual identity-pullback system.
In particular, `q_p` maps the original-cover system to the identity-pullback
system, as required by contravariance.

`etaleAssociatedVaryingSystemPullback_comp` proves

`lambda_comp(Y).hom = whiskerRight(lambda_f(Y).hom,Q_g) ≫ lambda_g(P_f Y).hom ≫ q_c`.

The source is the twice-restricted system, and the target is the system on the
single-pullback cover diagram. The last arrow `q_c` goes from the iterated-cover
system to the single-cover system. Both sides retain the whole coefficient
diagram, its group actions and every inverse-cover transition.

Each whole-system law is proved by extensionality twice: first at a coefficient
diagram `M`, then at an index `i`. The component formulas reduce the equations
to `etaleConstantAssociatedPullback_id` and
`etaleConstantAssociatedPullback_comp`. The two geometric evaluation lemmas
identify the actual cover maps in those equations. No new comparison-existence
or coherence hypothesis is introduced. Equality of the forward natural
transformations also determines equality of the corresponding isomorphisms.

This unit supplies identity and two-step composition coherence for etale
base change of the existing finite-torsor systems. It does not construct
non-etale or algebraic-closure inverse image, compact supports, cohomological
comparison maps, full-group or Galois actions, or Harris's particular Shimura
torsors. Those remain separate construction or theorem obligations.
