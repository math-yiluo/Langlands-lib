# Natural maps from `r_P ∘ i_P` vanish off the identity coset

This module is an internal helper. The literature does not state it on its own. It was written
for the Lean proof `inducedProgeneratorCenterInclusion` of the centre inclusion `ℨ_Ω ⊂ ℨ_D`
(Renard 2026, VI.10.4, second Lemma, printed p. 211, PDF p. 217). Renard proves that Lemma
differently: he uses the free `ℨ_D`-module structure of `R_Ω` (the first Lemma of VI.10.4) and
the generic irreducibility VI.8.5. The Lean proof takes another route. By Frobenius
reciprocity it reduces the inclusion to a kernel vanishing property
(`CuspidalSupport/InducedCenterFactorization`), and this module proves that property. Take a
map `r_P^G(i_P^G σ) → σ` that commutes with the endomorphisms of `σ`. The module shows that it
vanishes on the classes of the induced functions `f` with `f(1) = 0`. Its main tool is the
support filtration of the geometric lemma for `r_P^G ∘ i_P^G` (Renard VI.5.1, printed
pp. 161–162, PDF pp. 167–168). VI.5.1 allows any ordering of the orbits with open initial
unions; the proof chooses one in which the identity double coset comes last. The classes of the
functions with `f(1) = 0` then lie in the step below the last one. Every graded piece of that step
sits at a double coset `P w P` with `w ∉ M` and admits no nonzero such map.

## Setting

`G` is a group scheme over a non-archimedean local field `F`, with the point topology on `G(F)`.
`P = M N` is a rational parabolic subgroup (`p : P ⟶ G`, `hp`) with rational Levi subgroup `M`
(`l`, `hl`), geometric unipotent radical `N` (`r`, `hr`) and `hmul : M × N ≅ P`.
`leviInductionFunctor` is `i_P^G`, `leviJacquetFunctor` is `r_P^G`, and
`leviJacquetInductionFunctor` is their composite. The class of `f ∈ i_P^G σ` in the Jacquet
module is `Jacquet.Localization.mk _ (pointImage (r ≫ p)) 1 f`. `Induction.eval _ _ f 1` is the
value `f(1) ∈ σ`. `⁰M(F)` is `Plancherel.rationalCommonNormKernel M`.

## Declarations

- `leviJacquet_mk_mem_step_of_eval_one s hlast σ f hf`. Let
  `s : OrderedDoubleCosets P(F) P(F) (n + 1)` be an ordering of the double cosets
  `P(F) \ G(F) / P(F)` whose last representative lies in `P(F)` (`hlast`). If `f(1) = 0`
  (`hf`), the class of `f` lies in step `n` of the support filtration
  `leviJacquetSupportFiltration … s` of `r_P^G ∘ i_P^G` at `σ`. Step `n` is spanned by the
  classes of the induced functions supported on the union of the first `n` orbits.
- `leviJacquetSupportFiltration_graded_hom_eq_zero hG s E hF σ hsc hfix i hi g hg`. Here `G` is
  connected reductive, `E i` is an intersection datum of the geometric lemma at
  `(s.representative i)⁻¹`, and `hF` identifies graded piece `i` of the support filtration with
  the piece functor `(E i).pieceFunctor`. Assume that `σ` is supercuspidal (`hsc`) and that no
  `t ∈ M(F)` with `tⁿ ∉ ⁰M(F)` for all `n > 0` fixes a nonzero vector of `σ` (`hfix`). If the
  representative of orbit `i` is not in `M(F)` (`hi`), then every map `g` from graded piece `i`
  at `σ` to `σ` that commutes with all endomorphisms of `σ` (`hg`) is zero.
- `leviJacquetInduction_hom_apply_mk_eq_zero hG σ hsc hfix h hh f hf`. Let `G` be connected
  reductive and let `σ` satisfy `hsc` and `hfix` as above. Let `h : r_P^G(i_P^G σ) → σ` be an
  `M(F)`-intertwiner such that `h ∘ r_P^G(i_P^G a) = a ∘ h` for every endomorphism `a` of `σ`
  (`hh`). If `f(1) = 0`, then `h` maps the class of `f` to `0`.

The representation `σ` lives in `SmoothRep.{0, u, max u v}` in the second and third statements.
In that universe the piece functors and `SmoothRep.toRep` take values in the same category of
representations. The first statement holds for any universe level `v`.

## Proofs

`leviJacquet_mk_mem_step_of_eval_one`. Step `n` consists of the classes of functions `f'` that
vanish at every `x` whose coset `P(F) x` lies outside the first `n` orbits. We take `f' = f`.
Let `x` be a point whose coset lies in orbit `i` (`s.covers`). If `i < n`, there is nothing to
prove. Otherwise `i` is the last index. Since its representative lies in `P(F)`, that orbit is
the single coset `P(F)` (`cosetOrbit_self_eq_singleton`). Then `x ∈ P(F)`, and the
`P(F)`-covariance of `f` gives `f(x) = f(x · 1) = σ(x) f(1) = 0`.

`leviJacquetSupportFiltration_graded_hom_eq_zero`. Let `ι` be the isomorphism from graded piece
`i` to `(E i).pieceFunctor` given by `hF`, and put `g' = ι⁻¹ ≫ g`. By naturality of `ι` and the
hypothesis on `g`, `g'` commutes with all endomorphisms of `σ`. The datum `E i` lives at
`z = (s.representative i)⁻¹`, so `z⁻¹ = s.representative i ∉ M(F)`. The piece-vanishing lemma
`pieceFunctor_hom_eq_zero_of_not_mem` then gives `g' = 0`, and `g = ι ≫ g' = 0`.

`leviJacquetInduction_hom_apply_mk_eq_zero`.

1. Geometry. The Library theorem `representedGeometricLemmaGeometry` gives representatives
   `z₁, …, z_m` of `P(F) \ G(F) / P(F)` together with intersection data `D j` at the `z_j`. The
   double coset space is finite, and `G(F)` is Hausdorff, second countable and σ-compact. So
   the orbits of `P(F)` on `P(F) \ G(F)` admit an ordering `s` in which every union of an
   initial segment of orbits is open (`closedSubgroupOrbitOrdering_of_finiteOrbitOrdering`; the
   field `initial_open` of `OrderedDoubleCosets`). This is the ordering of Renard VI.5.1, whose
   support subfunctors are defined on these open sets. `classifiedRepresentatives` gives an
   ordering `t₀` with the representatives `z_j⁻¹`. It keeps the orbits of `s` and their order,
   so `t₀` has the same open initial unions.
2. The identity orbit. Let `j₀` be the orbit of the coset `P(F)`. Its representative lies in
   `P(F)`, so the orbit is a single point of the Hausdorff space `P(F) \ G(F)` and is closed.
   `closedOrbitLast` reorders `t₀` into an ordering `s'` whose last orbit is `j₀`. The initial
   unions of `s'` are still open: the union of all orbits is the whole space, and every other
   initial union of `s'` is an open initial union of `t₀` minus the closed orbit `j₀`. The
   representatives of `s'` are still among the `z_j⁻¹`. This gives intersection data `E i` at
   `(s'.representative i)⁻¹`.
3. Graded pieces. The Library theorem
   `representedGeometricLemmaSupportGraded_of_orbitComparison` holds for any ordering. Applied
   to `s'` and `E`, it identifies each graded piece of the support filtration with the piece
   functor of `E i`.
4. Orbits off `M`. For `i < n'` (every orbit except the last), the representative of orbit `i`
   is not in `M(F)`. Otherwise it would lie in `P(F)`, and orbit `i` would be the single coset
   `P(F)`, which is the last orbit. That contradicts the disjointness of distinct orbits
   (`s'.disjoint`).
5. Vanishing. We view `h` as a morphism `H` of representations. By `hh`, it commutes with
   `r_P^G(i_P^G a)` for every endomorphism `a`. Every graded piece `i < n'` satisfies the
   hypotheses of the second declaration, so every map from it to `σ` that commutes with the
   endomorphisms is zero. The bottom-up vanishing lemma
   `RepFunctorFiltration.hom_apply_eq_zero_of_mem_step_of_lt` then shows that `H` vanishes on
   step `n'`. The first declaration places the class of `f` in step `n'`.

This argument does not occur in Renard's proof of the Lemma (see the first paragraph). Here
`closedOrbitLast` puts the closed identity orbit last, so that the class of `f` falls into the
part of the filtration where `h` vanishes. The vanishing on the pieces at `w ∉ M` comes from
`pieceFunctor_hom_eq_zero_of_not_mem` (`CuspidalSupport/SelfIntersectionPieceVanishing`).
