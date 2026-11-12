# Special tori and Galois-fixed apartment points over the maximal unramified extension

This module states two inputs of Kaletha–Prasad's unramified descent (Chapter 9) as
Prop-valued definitions. Nothing in it proves them.

- `Langlands.Geometry.Building.SpecialTorusExistenceStatement` is KP Proposition 9.3.4.
- `Langlands.Geometry.Building.UnramifiedGaloisFixedApartmentStatement` is the
  Galois-fixed point of a stable special apartment from KP §9.2.1, in its corrected form.
- `Langlands.Geometry.Building.UnramifiedSpecialApartmentStatement` is their conjunction.

All three are universe polymorphic. At universe `u` they range over every
`F : Type u` with `Field F`, `ValuativeRel F`, `TopologicalSpace F` and
`IsNonarchimedeanLocalField F`, in equal and mixed characteristic, and over every
connected reductive group scheme `G` over `Spec F`. No splitness, quasi-splitness,
tameness, rank or residue-characteristic restriction is imposed.

Throughout, `K` is the Library's actual maximal unramified extension
`inertiaFixedField F`, definitionally `UnramifiedClosure F`, with its `F`-algebra
structure. Scalar extension of group schemes, commutative group schemes and their
homomorphisms is the existing base change along `algebraBaseMap F K`.

## Special tori (KP Proposition 9.3.4)

KP §9.2.2 calls a `k`-torus `T ⊂ G` *special* when it contains a maximal `k`-split
torus of `G` and `T_K` is a maximal `K`-split torus of `G_K`. Proposition 9.3.4 says that
every maximal `k`-split torus `S` of `G` lies in a special `k`-torus.

`SpecialTorusExistenceStatement` takes a maximal split torus `iS : S.toGrp ⟶ G` of `G`
(`IsMaximalSplitTorus iS`, a closed split subtorus not contained in a larger one). It asserts
that there are:

- a commutative group scheme `T` over `Spec F` with a homomorphism `iT : T.toGrp ⟶ G`;
- a homomorphism of commutative group schemes `f : S ⟶ T`;

such that

1. `CommGroupScheme.groupHom f ≫ iT = iS`, so `S` lies in `T`;
2. `iT` is a closed subgroup (`IsClosedSubgroup iT`), so `T` is an `F`-subgroup of `G`;
3. the scalar extension `iT_K` is a maximal split torus of `G_K`, as a homomorphism from the
   base change `T_K` of `T`.

Condition 3 contains the splitness of `T_K`. That `T` is an `F`-torus follows from it and
is not stated separately.

## Galois-fixed apartment points (KP §9.2.1)

Let `T` be a commutative group scheme over `Spec F` with a homomorphism `i : T.toGrp ⟶ G`
whose scalar extension `i_K` is a maximal split torus of `G_K` (hypothesis `hi`).
Equivalently, `T` is an `F`-torus whose base change `T_K` is a maximal `K`-split torus. The
statement does not require `T` to contain a maximal `F`-split torus. The scalar extension
`G_K` is affine because `G` is; the module supplies this instance by pullback. The
monomorphism instances needed by the apartment interface come from `hi` through the
published `mono_of_isMaximalSplitTorus`.

The statement quantifies over every `D : KPApartmentData i_K ω`, an `N(K)`-stable
equipollence class of valuations of the root datum of `(G_K, T_K)` (KP Definitions 6.1.2
and 6.1.7). Here `ω = IntegerValuation.order (MaximalUnramified.valuation F)` is the order of
the published integer-valued valuation of `K`. Its premise is the published
`KPApartmentData.GaloisStable F K i D`: for every `σ` in `Aut(K/F)` (that is, every
`σ : K ≃ₐ[F] K`), the published coefficient transport `RootFunctionFamily.galoisAction`
maps every member of `D` into `D`. The conclusion is that some point `x : D.Apartment`
satisfies `RootFunctionFamily.galoisAction F K T G σ x.val = x.val` for every `σ`.
By the published `mem_galoisFixedApartment_iff`, this says exactly that the published
affine subspace `galoisFixedApartment` of `D.Apartment` is nonempty.

KP §9.2.1, as corrected, argues as follows. The apartment of `T_K` is fixed pointwise by
`Gal(K/k')` for a finite Galois extension `k'/k` inside `K` over which `T` is defined and
split. Hence `Γ = Gal(K/k)` acts on that apartment by affine maps through the finite
quotient `Gal(k'/k)`. When `T_K` is defined over `k`, as here, the apartment is
`Γ`-stable, and averaging an orbit gives a fixed point. The proof of KP Proposition 9.3.6
takes such a fixed point in every special `k`-apartment. The stability that KP derive from
the action of `Γ` on the building `B(G_K)` is a premise here. For the classes that occur,
it is a published theorem: `IntegerValuation.IsOmegaCompatible.galoisStable` proves it for
every class satisfying V 6 for a scalar-extended centralizer datum. The published
`KPApartmentData.exists_galoisFixed` handles finite extensions `K/k`. The present
statement is its analogue for the infinite extension `K/F`.

## Sources

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`:

- §9.2.1, printed pp. 325–326 / PDF pp. 356–357: the action of `Γ` on `B(G_K)`, the
  pointwise fixation of the apartment of a torus split over a finite unramified `k'` by
  `Gal(K/k')`, and the action of `Γ` through `Gal(k'/k)` on the apartment of a torus
  defined over `k`.
- §9.2.2, printed p. 326 / PDF p. 357: special `k`-tori and special `k`-apartments.
- Proposition 9.3.4, printed p. 332 / PDF p. 363.
- Proof of Proposition 9.3.6, printed pp. 333–334 / PDF pp. 364–365: a special
  `k`-apartment contains a `Γ`-fixed point.
- Chapter 9 opening, printed p. 323 / PDF p. 354: `k` is discretely valued with
  Henselian valuation ring and perfect residue field, `K` is its maximal unramified
  extension in a fixed separable closure, and `Γ = Gal(K/k)`.

Kaletha–Prasad, *Corrections and additions* (1 November 2024), registered as
`kaletha-prasad-2024-corrections`, PDF p. 39 (Section 9.2): the replacement paragraph for
printed p. 326, which uses a finite Galois extension `k' ⊂ K` over which the torus is
defined and split and shows that `Γ`-orbits are finite. The corrections do not change
Proposition 9.3.4. Their Section 9.3 entries (PDF pp. 39–41) concern Propositions 9.3.11,
9.3.12, 9.3.13, 9.3.24 and 9.3.25.

## Provenance and scope

The provenance is derived. KP work over a Henselian discretely valued field with perfect
residue field. Here `F` is specialized to a nonarchimedean local field, whose residue field
is finite and hence perfect. KP state the fixed-point property for apartments of the
building `B(G_K)`. The Lean statement uses the Library's apartment `D.Apartment` of
valuations of the root datum, identified with the apartment of `T_K` by KP §6.1 and
Remark 9.6.2. The `Γ`-stability of that apartment is a premise. The second statement does
not use that `T` contains a maximal `F`-split torus, so it applies to every `F`-torus that
is maximally split over `K`.

This module asserts neither proposition. It constructs no special torus, centralizer
datum, valuation over `F`, building or integral model, and it does not prove KP
Theorem 9.6.5 or Theorem 9.2.7. These statements are inputs of the decomposition of
`ValuationApartmentAxiomsExistenceStatement` (KP Theorem 9.6.5).
