# Restricted standard subgroup transport by actual character images

This internal derived unit constructs actual conjugation equivalences for the
literal intersections of a standard Levi subgroup functor with a standard
parabolic or standard unipotent subgroup functor. The construction and its
membership formulas apply on every scheme test, including nonreduced tests.
They use the orbit-extension definitions already in the Library.

For the main transport results, let `k : Type u` be any field, `T` a commutative
group scheme over `Spec k`, and `G` a group scheme whose structure morphism is
affine. The map `i : T.toGrp ⟶ G` is monomorphic on the underlying schemes, and
`ν` is a cocharacter. Assume the set `simpleRelativeRoots i ν` is finite. Take
character subsets `I0 ⊆ J0` and `I1 ⊆ J1`, and assume that a standard cocharacter
exists for each of `J0` and `J1`. Finally, let `n : normalizerPoints i` satisfy
both actual character-image equations

```text
weylAction i n '' I0 = I1,
weylAction i n '' J0 = J1.
```

These are literal subsets of the character lattice. No condition is imposed
here on how those equations were obtained. In particular, the construction
requires neither a Coxeter realization nor reductivity, genericity, maximality,
splitness of `T`, a characteristic restriction, or a local-field hypothesis.
The finiteness and the two standard-cocharacter existence assumptions remain
explicit inputs. Empty root sets and empty subsets are allowed.

`restrictedStandardSubgroups_eq_comap_of_character_images` proves both equalities

```text
standardLevi J0 ∩ standardParabolic I0 =
  comap Int(n) (standardLevi J1 ∩ standardParabolic I1),
standardLevi J0 ∩ standardUnipotent I0 =
  comap Int(n) (standardLevi J1 ∩ standardUnipotent I1).
```

Here intersection is the meet of subgroup functors, and `Int(n)` is the actual
`G.innerIso n`. The suppressed parameters of all standard functors are `i, ν`.
The equalities hold as subgroup functors, so they include every object of
`Over (Spec k)`, rather than only field-valued or reduced points.

The primary definition `restrictedStandardParabolicConjEquiv` restricts this
inner isomorphism to give a multiplicative equivalence between the two
restricted parabolic groups on each test scheme `U`.
`restrictedStandardUnipotentConjEquiv` does the same for the restricted
unipotent groups. Their `_apply` and `_symm_apply` lemmas identify their maps
on ambient test points, respectively, as

```text
x ↦ n_U * x * n_U⁻¹,
x ↦ n_U⁻¹ * x * n_U,
```

where `n_U = G.constantPoint n U`. The private
`SubgroupFunctor.carrierEquivOfComapIso` implements the restriction of an
isomorphism using a subgroup-functor comap equality; its inverse laws use the
ambient isomorphism identities and its multiplication law uses composition of
group-object points. No representability of the restricted functors is assumed.

`mem_standardParabolic_unipotent_conj_iff_of_character_images` gives both forward
membership equivalences for an ambient test point belonging to `standardLevi
J0`. The inverse version
`mem_standardParabolic_unipotent_inv_conj_iff_of_character_images` applies to
any ambient point in `standardLevi J1` and proves, simultaneously,

```text
x ∈ standardParabolic I1 ↔ n_U⁻¹ * x * n_U ∈ standardParabolic I0,
x ∈ standardUnipotent I1 ↔ n_U⁻¹ * x * n_U ∈ standardUnipotent I0.
```

This is the inverse-conjugation direction needed when evaluating the target
Levi at `Spec k`. Evaluation uses actual points and does not assert any
identification between points of a sheaf quotient and a quotient of points.

The proof first establishes the arbitrary-base lemma
`Dynamic.orbit_add_of_mem_centralizer`: adding a cocharacter whose image
centralizes a test point leaves its conjugation orbit map unchanged. The two
following membership lemmas reuse exactly the same affine-line extensions and
the same values at zero to preserve dynamic parabolic and unipotent membership.
These preliminary results allow any base scheme and any commutative group
scheme mapping into the ambient group scheme.

`IsStandardCocharacter.exists_add_zsmul_of_face` supplies the finite positivity
argument over a field. Suppose a cocharacter vanishes on `I ⊆ J` and is
strictly positive on `J` outside `I`, and a `J`-standard cocharacter is given.
Bound the finitely many negative pairings with simple roots, then add a
sufficiently large positive integer multiple of the given cocharacter. On `J`
the added pairing is zero; outside `J` it is a positive integer. The result is
an `I`-standard cocharacter. This extends the integer perturbation argument
already implemented in `StandardLeviAnnihilator`.

`cocharacterAut_face_pairing_iff` transfers those zero and strict-positive face
conditions through an automorphism whose character action has the two required
set images. It follows from pairing invariance, injectivity, and the exact
image equations. The private common-family proof uses this with
`normalizingAut i n`. To test a target standard cocharacter, pull it back through
the cocharacter automorphism, correct it by a multiple of a source
`J0`-standard cocharacter, and use the source Levi to centralize that added
multiple. The centralizing-cocharacter submodule in the imported Library
provides centralization of every integer multiple. The orbit is therefore
unchanged, and the dynamic isomorphism transport lemmas give the desired
membership. The reverse implication uses the same argument with the target
`J1`-standard cocharacter.

The previously published `standardLevi_eq_comap_of_finite_of_exists` provides
Levi membership under this same `n`. Subgroup-functor extensionality combines it
with the two membership equivalences to obtain the displayed equalities. The
inverse-membership corollary applies the forward result to the inverse
conjugate and cancels the two ambient conjugations.

The provenance is derived internal content: finite integer bounds, invariant
lattice pairings, the existing centralizing-cocharacter submodule, transport of
dynamic orbit conditions, and restriction of a group-scheme isomorphism to
subgroups. Workers 76 and 165 identified the generic character-image interface
and its required same-representative inverse point formulas. No external
structure theorem is invoked. This unit does not construct standard
cocharacters, prove simple-root finiteness, establish an unconditional Coxeter
realization, or prove the separately named universal associated-transport
statements. Specializing the explicit inputs and transporting representation
data remain separate work.
