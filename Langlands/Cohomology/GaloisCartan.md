# A Galois–Cartan criterion for higher right derived functors

Worker 749. This module is an internal categorical helper, written for the planned proof
of the Galois-coinduced local acyclicity statement
`AnalyticEtaleGaloisCoinducedLocalAcyclicStatement`. It imports Mathlib's group cohomology
(long exact sequence and low degrees) and the Library module
`Langlands.Cohomology.RightDerivedSequence`.

## Background and provenance

Berkovich proves that the higher direct images from the étale site to the ordinary
topology have the Galois cohomology of the stalk as germs. His argument shows that a
flabby sheaf has flabby germs, by computing the Čech complexes of finite Galois germ
coverings as filtered colimits of Čech complexes over neighbourhoods. See Berkovich,
*Étale cohomology for non-Archimedean analytic spaces* (Publ. Math. IHÉS 78, 1993),
Proposition 4.2.4 and its proof, printed pp. 87–88 (source `berkovich-1993-etale-cohomology`).
Right after the proof, Berkovich recalls the Čech characterization of flabby sheaves from SGA 4, Exp. V, 4.3.
The same characterization is Milne, *Étale Cohomology* (1980), III Proposition 2.12,
printed p. 102 (source `milne-1980-etale-cohomology`).

This module does not formalize those statements. It isolates a dimension-shifting
argument of Cartan type in an abstract form: the coverings are replaced by finite Galois
data, and Čech complexes by group cochain complexes. The proof is internal and follows
the Library's finite test-system argument,
`Langlands.Cohomology.SiteCech.FiniteCechSystem.derivedHomAcyclic_of_homAcyclic`.

## Natural actions (`Langlands.Cohomology.GaloisCartan.NaturalAction`)

Let `D` be a category, `R` a commutative ring in `Type w`, `T : D ⥤ ModuleCat.{w} R` a
functor and `Γ : Type w` a group.

- `NaturalAction Γ T` is a family `act γ : T ⟶ T` of natural endomorphisms. It satisfies
  `act 1 = 𝟙 T` and `act (γ * δ) = act δ ≫ act γ`, which is a left action on every value
  of `T`.
- `representation A F` is the resulting `Representation R Γ (T.obj F)`.
  `rep A F : Rep R Γ` is the bundled representation, and `representation_apply` unfolds
  it.
- `act_naturality_apply` is naturality of `act γ`, stated for elements.
- `repMap A g : rep A F ⟶ rep A F'` is the equivariant map given by `T.map g`, and
  `repMap_hom_apply` unfolds it.

## Galois–Čech systems (`Langlands.Cohomology.GaloisCartan.GaloisCechSystem`)

From here on `D` is abelian. Let `T : ι → D ⥤ ModuleCat.{w} R` be a family of functors.
A `GaloisCechSystem T` consists of the following data.

- For each index `i`, a type `Cover i` of covers. Each cover `c` has a group
  `group i c : Type w`, a target index `target i c`, and a natural action
  `action i c` of that group on `T (target i c)`.
- An augmentation `aug i c : T i ⟶ T (target i c)` that is injective on every object
  (`aug_injective`) and lands in the invariants (`aug_act`). It is onto the invariants:
  every invariant element is in its image (`exists_aug_eq`).
- `local_lift`: for every short exact sequence `S` in `D` and every
  `s : (T i).obj S.X₃`, some cover `c` of `i` and some `t : (T (target i c)).obj S.X₂`
  satisfy `(T (target i c)).map S.g t = (aug i c).app S.X₃ s`.
- `injective_acyclic`: for every injective object `I`, the group cohomology
  `groupCohomology ((action i c).rep I) (n + 1)` is zero for all `n`.

`GaloisAcyclic K F` says that `groupCohomology ((action i c).rep F) (n + 1)` is zero for
all `i`, `c` and `n`. `galoisAcyclic_of_injective` proves this for injective objects.

The remaining results assume that every `T i` is additive and preserves finite limits.

- `map_f_map_g_apply`, `map_f_injective` and `exists_map_f_eq` state left exactness of
  `T j` for elements of a short exact sequence. The last two use preservation of
  monomorphisms and `ShortComplex.Exact.map_of_mono_of_preservesKernel`.
- `aug_naturality_apply` is naturality of the augmentation, stated for elements.
- `surjective_map_g`: if `S` is short exact and `S.X₁` is Galois acyclic, then every
  `(T i).map S.g` is surjective. Proof: take the local lift `t` of `s` on a cover `c`.
  The differences `γ t - t` map to zero in `S.X₃`, so they come from a function
  `ψ : Γ → T(S.X₁)`, and `ψ` is a 1-cocycle. Since `H¹` vanishes, `ψ` is the coboundary
  of some `b` (`groupCohomology.H1π_eq_zero_iff`). Then `t - b` is invariant, so it is
  the augmentation of some `u`, and `(T i).map S.g u = s` by injectivity of the
  augmentation.
- `repShortComplex i c S` is the short complex of representations induced by `S`.
  `repShortComplex_shortExact` shows that it is short exact when `S` is short exact and
  `S.X₁` is Galois acyclic. Exactness and injectivity come from left exactness, and
  surjectivity from `surjective_map_g` at the target index.
- `galoisAcyclic_quotient`: if `S` is short exact, `S.X₂` is injective and `S.X₁` is
  Galois acyclic, then `S.X₃` is Galois acyclic. This uses the exact sequence
  `H^{n+1}(Γ, T S.X₂) → H^{n+1}(Γ, T S.X₃) → H^{n+2}(Γ, T S.X₁)`, which is
  `groupCohomology.mapShortComplex₃_exact`.

## Main results

Now assume also that `D` has enough injectives.

- `isZero_rightDerived_of_galoisAcyclic`: if `F` is Galois acyclic, then
  `((T i).rightDerived (n + 1)).obj F` is zero for every `i` and `n`. The proof is by
  induction on `n`, generalizing `F`, and uses `S : F ⟶ I ⟶ coker`, where `I` is
  `Injective.under F`. In degree one, `surjective_map_g` makes `(T i).map S.g`, and hence
  `R⁰(T i)` of `S.g`, an epimorphism. The connecting morphism into `R¹(T i)(F)` is then
  both an epimorphism and zero. In higher degrees, the connecting morphism is an
  epimorphism onto `R^{n+2}(T i)(F)`, from a module that vanishes by induction, because
  the quotient is Galois acyclic by `galoisAcyclic_quotient`.
- `rightDerivedIsoOfIso e q` gives isomorphic right derived functors for isomorphic
  additive functors.
- `isZero_rightDerived_of_iso`: the same vanishing holds for any additive functor
  isomorphic to some `T i`. This is the form for germ functors such as the Library's
  `etaleUnderlyingSheaf ⋙ (underlyingTopologyPoint X y).sheafFiber`. Their right derived
  functors are `etaleUnderlyingGermCohomology`.

## Intended use and scope

In the planned application, `D` is the category of étale sheaves of modules and the
indices are germs at a point. The covers are finite Galois neighbourhood data, the target
modules are the germ modules on which the deck group acts, and the augmentation is
restriction. Galois acyclicity is then vanishing of the positive group cohomology of the
germ deck-group modules. The data and hypotheses of a `GaloisCechSystem` must be
established separately for such an application: Galois descent of germs, cofinality of
Galois data for local lifting, and vanishing for injective sheaves. This module asserts
none of them. It proves only the abstract implication stated above.
