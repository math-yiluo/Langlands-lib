# Closure properties of Noetherian group-algebra modules of representations

Module `Langlands.Representation.Category.NoetherianClosure`.

## Purpose and scope

In this module, a representation `ρ` of a monoid `G` on a module `V` over a commutative
ring `k` is *Noetherian* when its group-algebra module `ρ.asModule` is a Noetherian
`k[G]`-module (`IsNoetherian k[G] ρ.asModule`). For smooth representations this is the
module-level form of Renard's Noetherian objects (Appendix A.I.3). The order isomorphism
between categorical subobjects and group-algebra submodules
(`Langlands.SmoothRep.groupAlgebraSubobjectOrderIso`) is what connects the two.

Renard, *Représentations des groupes réductifs p-adiques* (9 July 2026 version), VI.7.5,
Theorem and proof (printed p.187 / PDF p.193), uses the following closure properties
of Noetherian representations without stating them separately:

- a representation with a finite filtration whose successive quotients are Noetherian
  is Noetherian (supercuspidal step: `r_Q^G ∘ i_P^G(ρ)` has a filtration with quotients
  `w·ρ`);
- a subrepresentation of a finite direct sum of Noetherian representations is
  Noetherian (general step: `i_P^G(ρ)` embeds into `⊕_{P'} i_P^G i_{P'}^M(ρ_{M'})`);
- a Noetherian representation is of finite type.

This module proves these properties, and a few related ones, at the level of
group-algebra modules. They are derived lemmas, not statements of Renard. Every proof
reduces to a Mathlib result on Noetherian modules, transported through
`Representation.IntertwiningMap.equivLinearMapAsModule`. That equivalence identifies
intertwiners with `k[G]`-linear maps between the group-algebra modules and keeps the
underlying function. The module proves neither VI.7.5 target. It contains no
representation-theoretic input: no Jacquet functor, no induction functor, no cuspidal
decomposition.

## Declarations

### Representations (namespace `Langlands.NoetherianRepresentation`)

Throughout, `k` is a commutative ring, `G` a monoid, and the carriers are additive
commutative groups with `k`-module structures. Carrier universes are independent.

- `of_injective`: if `f : ρ.IntertwiningMap σ` is injective and `σ` is Noetherian, then
  `ρ` is Noetherian. Proof: Mathlib's `isNoetherian_of_injective` applied to the
  `k[G]`-linear map of `f`.
- `of_surjective`: if `f : ρ.IntertwiningMap σ` is surjective and `ρ` is Noetherian, then
  `σ` is Noetherian. Proof: `isNoetherian_of_surjective`.
- `of_equiv`: if `e : ρ.Equiv σ` and `ρ` is Noetherian, then `σ` is Noetherian. This is
  the surjective case.
- `of_extension`: let `i : ρ.IntertwiningMap σ` and `q : σ.IntertwiningMap τ` satisfy
  `ker q ⊆ range i`, stated as: for every `v` with `q v = 0` there is `u` with `i u = v`.
  If `ρ` and `τ` are Noetherian, then `σ` is Noetherian. The lemma does not assume that
  `i` is injective, that `q` is surjective, or that `q ∘ i = 0`. Proof: split `σ` by the
  submodule `ker q` (`isNoetherian_iff_submodule_quotient`). The kernel lies in the
  range of `i`, which is Noetherian as an image of `ρ`, so the kernel is Noetherian
  (`isNoetherian_of_le`). The quotient is isomorphic to the range of `q`, a submodule of
  the Noetherian `τ` (`LinearMap.quotKerEquivRange`).
- `compSubmoduleOrderIso ρ f hf` (definition): for a surjective monoid homomorphism
  `f : H →* G`, the order isomorphism
  `Submodule k[G] ρ.asModule ≃o Submodule k[H] (ρ.comp f).asModule`. It sends a
  submodule to the submodule with the same vectors (`mem_compSubmoduleOrderIso`, by
  `Iff.rfl`). Construction: a subspace is `ρ(G)`-stable exactly when it is
  `ρ(f(H))`-stable, because `f` is surjective. So `ρ` and `ρ.comp f` have the same
  subrepresentations, and Mathlib's `Subrepresentation.subrepresentationSubmoduleOrderIso`
  converts subrepresentations to group-algebra submodules on both sides.
- `comp_surjective_iff`: for a surjective monoid homomorphism `f : H →* G`, `ρ` is
  Noetherian over `k[G]` if and only if `ρ.comp f` is Noetherian over `k[H]`. Proof:
  Noetherianity is well-foundedness of `>` on submodules (`isNoetherian_iff`), and the
  order isomorphism `compSubmoduleOrderIso` transfers it in both directions.
- `directSum`: for a finite index type `ι` and a family `ρ i` of Noetherian
  representations, `Representation.directSum ρ` on `⨁ i, V i` is Noetherian. Proof: the
  component projections are intertwiners. Together they give an injective
  `k[G]`-linear map into the product `Π i, (ρ i).asModule` (`DirectSum.ext_component`),
  and that product is Noetherian for finite `ι` (`isNoetherian_pi`).
- `of_objectRepFiltration`: let `A : Rep k G` have a finite filtration
  `s : ObjectRepFiltration A n` (the published zero-to-full filtration by
  subrepresentations) such that every graded quotient `s.gradedRepresentation i` is
  Noetherian. Then `A` is Noetherian. Proof: induction on the steps. The zero step is
  the zero subrepresentation, whose module is a subsingleton and hence Noetherian. For
  step `i + 1`, apply `of_extension` to the inclusion of step `i` into step `i + 1` and to
  the graded projection `s.gradedProjection i`. Its kernel is step `i`, by
  `Submodule.Quotient.mk_eq_zero`. The last step is all of `A`, so `A` embeds into it
  equivariantly, and `of_injective` concludes. The argument follows the published
  `Langlands.isAdmissible_of_objectRepFiltration`.

### Smooth representations (namespace `Langlands.SmoothRep`)

Here `G` is a topological group and the coefficients are `ℂ`, matching
`Langlands.SmoothRep.directSum` and `Langlands.SmoothRep.pullback`.

- `isNoetherian_of_mono`: if `f : A ⟶ B` is a monomorphism of smooth representations and
  `B` is Noetherian, then `A` is Noetherian. Monomorphisms are injective
  (`SmoothRep.mono_iff_injective`).
- `isNoetherian_of_epi`: if `f : A ⟶ B` is an epimorphism and `A` is Noetherian, then `B`
  is Noetherian (`SmoothRep.epi_iff_surjective`).
- `isNoetherian_directSum`: for a finite index type, the published actual direct sum
  `SmoothRep.directSum A` of Noetherian smooth representations is Noetherian. Its
  representation is literally `Representation.directSum`.
- `finite_of_injective_directSum`: if a smooth `E` has an injective intertwiner into
  `SmoothRep.directSum A`, with `ι` finite and every `A i` Noetherian, then
  `E.representation.asModule` is finitely generated over `ℂ[G]`. The last step is
  Mathlib's instance `IsNoetherian.finite`. This is the shape of the general step of the
  VI.7.5 Theorem. It also matches the published VI.7.2 Lemma statement
  `RationalCuspidalInducedEmbeddingStatement`, which embeds into a
  `SmoothRep.directSum`.
- `isNoetherian_pullback_iff`: for a topological group isomorphism `e : H ≃ₜ* G`, the
  pullback `SmoothRep.pullback e A` is Noetherian over `ℂ[H]` if and only if `A` is
  Noetherian over `ℂ[G]`. This is `comp_surjective_iff` for `e.toMonoidHom`. The
  represented VI.5.3(iii) statement identifies its graded pieces with such pullbacks.

## Provenance

The lemmas are derived: they are standard facts about Noetherian modules over the
group algebra, isolated here because Renard VI.7.5 uses them implicitly. Renard is
cited for that motivation only.
