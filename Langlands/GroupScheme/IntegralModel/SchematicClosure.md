# Schematic closure of a generic subgroup in an integral model

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Appendix A:
the definition of schematic closure at the start of §A.2, Lemma A.2.1(1)–(3)
and the group-scheme assertion of Lemma A.2.3. These are on printed
pp. 593–595 / PDF pp. 624–626. The registered source is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
Integral models and their morphisms are KP Definition 2.10.1(1)–(2), printed
p. 121 / PDF p. 152, as formalized in the Library's `IntegralModel` and
`IntegralModel.Hom`. The registered corrections
`kaletha-prasad-2024-corrections` (1 November 2024), SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp. 49–50, change Appendix A only in §A.4. They leave §A.2 unchanged.

## Declarations

All rings and schemes are in one arbitrary universe `u`. `R` is a domain with
specified fraction field `K` (`IsFractionRing R K`). `G` and `H` are actual
group schemes over `Spec K`. `N : IntegralModel R K G` and
`M : IntegralModel R K H` are integral models, and `j : H ⟶ G` is a
homomorphism of group schemes.

- `IntegralModel.genericToModel N : G.X.left ⟶ N.group.X.left` is the
  underlying scheme map from the given generic group into the integral model.
  It applies the inverse of the supplied `N.genericIso`, then the first
  projection of the generic-fibre pullback
  `pullback N.group.X.hom (Spec.algebraMap R K) ⟶ N.group.X.left`.
- `IntegralModel.Hom.IsSchematicClosure φ`, for `φ : M.Hom N j`, is the
  conjunction of two clauses:
  1. `IsClosedSubgroup φ.hom`: the underlying scheme morphism of `φ.hom` is a
     closed immersion.
  2. `φ.hom.hom.hom.left.ker = (j.hom.hom.left ≫ N.genericToModel).ker`: the
     ideal-sheaf kernel of the underlying scheme morphism of `φ.hom` equals
     the ideal-sheaf kernel of the generic map `H → G → N.group`, which uses
     the original `j` and `N.genericIso`.
- `IntegralModel.Hom.integralPoints_eq_comap` (proved): for every
  `φ : M.Hom N j` with `IsClosedSubgroup φ.hom`,
  `M.integralPoints = N.integralPoints.comap (rationalPoints.map j)`.
- `IntegralModel.Hom.IsSchematicClosure.integralPoints_eq_comap` (proved):
  the same equality for a `φ` with `φ.IsSchematicClosure`.
- `IntegralModelSchematicClosureStatement.{u}` (unproved proposition):

```lean
def IntegralModelSchematicClosureStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of K))) (N : IntegralModel R K G)
    (H : GroupScheme (Spec (CommRingCat.of K))) (j : H ⟶ G),
    IsClosedSubgroup j →
      ∃ (M : IntegralModel R K H) (φ : M.Hom N j), φ.IsSchematicClosure
```

## The existence proposition

The inputs are an arbitrary discrete valuation ring `R` with specified fraction
field `K`, the actual generic group schemes `G` and `H` over `Spec K`, an
ambient integral model `N` of `G`, and a closed subgroup homomorphism
`j : H ⟶ G`. No model of `H` is an input. The conclusion asks for an actual
`M : IntegralModel R K H` and an actual `φ : M.Hom N j`. Thus `M.group` is a
group scheme over `Spec R` whose structural morphism is affine, flat and
locally of finite type, hence of finite type. `M.genericIso` is a group-scheme
isomorphism from the actual generic fibre of `M.group` to the given `H`, and
`φ.hom : M.group ⟶ N.group` is a homomorphism of group schemes. A proof must
construct these objects and prove the two closure clauses. The proposition
does not ask whether a supplied model is a closure, and it does not use
parahoric or any other model availability.

### Generic compatibility

The field `φ.generic_comm` of `IntegralModel.Hom` is the equality

```lean
(baseChange (Spec.algebraMap R K)).map φ.hom ≫ N.genericIso.hom =
  M.genericIso.hom ≫ j
```

of group-scheme homomorphisms from the generic fibre of `M.group` to `G`. It
is KP Definition 2.10.1(2): `φ.hom` extends `j`. The data `G`, `H`, `j` and
`N.genericIso` are the given ones; only `M`, including `M.genericIso`, and
`φ` are produced. So after the given identifications, the generic fibre of
the produced closed immersion is the original `j`.

### Kernel equality

Mathlib's `Scheme.Hom.ker f` is the largest quasi-coherent ideal sheaf on the
target contained in the section-wise kernels of `f`. Both kernels in clause 2
are ideal sheaves on `N.group.X.left`. This scheme is affine, being affine over
the affine `Spec R`. By Mathlib's `Scheme.ker_of_isAffine`, each kernel is
therefore the ideal sheaf `ofIdealTop` of the kernel of the global-section ring
map, and `IdealSheafData.equivOfIsAffine` identifies ideal sheaves with ideals
of global sections. In coordinate rings `R[N] = Γ(N.group)`, clause 2 says:

- `ker(R[N] → R[M])` equals `ker(R[N] → Γ(H))`.

The second map is the composite `R[N] → K[N] ≅ K[G] → Γ(H)`. When `j` is a
closed subgroup, `H` is affine, being closed in `G` and `G` being identified
with the affine generic fibre of `N`. Then `Γ(H) = K[H]` and
`ker(K[G] → K[H])` is the ideal `I` of `H`. `R[N]` is flat over `R`, so it is
torsion-free and embeds in `K[N] = R[N] ⊗_R K`, and the kernel is `I ∩ R[N]`.
This is KP's ideal of the schematic closure (§A.2, p. 593): "If `I ⊂ k[X]` is
the ideal defining `Y` then the ideal defining `𝒴` is `I ∩ o[𝒳]`."

Clause 1 makes `R[N] → R[M]` surjective. Together, the two clauses identify
`M.group`, as a closed subscheme of `N.group`, with `R[N]/(I ∩ R[N])`. This is
the closed subscheme cut out by the kernel of the generic map, that is,
Mathlib's scheme-theoretic image `Scheme.Hom.image`. This is the smallest
closed subscheme through which `H → N.group` factors, as in KP's definition.
So the predicate fixes the closure with its scheme structure, not just its
underlying set.

## Comparison with KP A.2.1 and A.2.3

KP's §A.2 setting is an affine finite-type `k`-scheme `X` with an integral model
`𝒳` and a closed subscheme `Y ⊂ X`. Here `X` is the group `G`, `𝒳` is `N`, and
`Y` is `H`, embedded in `G` by the closed subgroup homomorphism `j` rather than
as a literal subscheme. KP's §A.2 integral models are affine, flat and of finite
type, as in Definition 2.10.1(1), which matches `IntegralModel`. KP's
Definition 2.10.1 also assumes that the generic variety is reduced. Appendix A
speaks of affine schemes of finite type instead, and the Lean interface needs no
reducedness.

- **A.2.1(1)** (the closure is an integral model of `Y`). The existence
  proposition states this for closed subgroups: `M` is an integral model of
  `H`, and `φ` realizes it as the schematic closure. The lemma is not stated
  for closed subschemes that are not subgroups.
- **A.2.1(2)** (`𝒴(R') = 𝒳(R') ∩ Y(R' ⊗_o k)` for flat `o`-algebras `R'`).
  Only the case `R' = o` is formalized, in group form, as
  `Hom.integralPoints_eq_comap`. It is proved for every compatible closed
  `φ`, without using the kernel equality or a discrete valuation: `R` is
  only a domain with fraction field `K`. The formula for arbitrary flat
  algebras is not stated.
- **A.2.1(3)** (closed flat subschemes of `𝒳` correspond bijectively to
  closed subschemes of `X`, inversely by schematic closure). It is not stated.
  The kernel equality expresses the direction "take the schematic closure" for
  the given `H`. The inverse direction, the bijection and inclusion preservation
  would be internal steps of a proof of the existence target.
- **A.2.3, group-scheme part** (for a flat `o`-group scheme `𝒢` with generic
  fibre `G` and a subgroup `H`, the schematic closure is a flat closed
  `o`-subgroup scheme of `𝒢`). The ambient is the integral model `N`, which is
  affine, flat and of finite type, as in the §A.2 setting. The conclusion
  provides a group scheme `M.group`, flat over `Spec R`, with a group-scheme
  homomorphism `φ.hom` into `N.group` that is a closed immersion. The kernel
  equality makes the closure's scheme structure the one KP defines. KP's
  proof shows that `𝓗` is a closed `o`-subgroup scheme of `𝒢` if and only if
  `H` is a `k`-subgroup of `G`. Only the forward direction is stated, since
  `H` is a subgroup by hypothesis. The Lie algebra assertion
  `Lie(𝓗) = Lie(H) ∩ Lie(𝒢)` is not stated.

## Scope: arbitrary discrete valuation rings (derived)

Appendix A begins with a field `k` with a non-trivial discrete valuation whose
ring of integers is `o`, and it assumes that `k` is Henselian (p. 593). The
Lean proposition quantifies instead over every discrete valuation ring `R`
with specified fraction field `K`. These are the same data, with `R = o` and
`K = k`, except that the target omits the Henselian assumption. This
generalization is derived from KP's proofs, which are purely algebraic and
never use the Henselian property:

- the closure `𝒴` of A.2.1(1) is affine and of finite type as a closed
  subscheme of `𝒳`;
- it is flat because `o[𝒴]` is a subring of `k[Y]`, hence `m`-torsion-free;
  over a discrete valuation ring (a principal ideal domain), torsion-free
  modules are flat;
- its generic fibre is `Y` and the bijection of A.2.1(3) holds because
  `- ⊗_o k` is exact, being a localization;
- in A.2.3, `𝓗 × 𝓗` is a flat closed subscheme of `𝒢 × 𝒢`. The multiplication
  `m` is flat, obtained from a projection by the automorphism
  `(x, y) ↦ (xy, y)`, so `m⁻¹(𝓗)` is flat. Inclusion preservation in A.2.1(3)
  then reduces `m(𝓗 × 𝓗) ⊂ 𝓗` to the generic fibre. The same argument applies
  to inversion and the unit section.

None of these steps uses Henselian lifting, completeness or a residue-field
hypothesis. Hence the general discrete-valuation-ring statement is a derived
formulation of the source's proof, not a literal restatement of its
hypotheses. The Henselian case is the special case `R = o`.

## The integral-point preimage lemma and its proof

`Hom.integralPoints_eq_comap` holds over every domain `R` with specified
fraction field `K` and for every `φ : M.Hom N j` whose underlying morphism is
a closed immersion. It states that the integral-point subgroup of `M`, inside
the given `rationalPoints H`, is the preimage of `N.integralPoints` under the
original `rationalPoints.map j`. The proof is by extensionality.

- `⊆`: `Hom.map_mem_integralPoints` (Library, from `φ.generic_comm`) sends
  integral points of `M` to integral points of `N`.
- `⊇`: let `g : rationalPoints H` with `rationalPoints.map j g` equal to
  `N.integralPointMap x` for an integral section `x` of `N.group`. Put
  `y = rationalPoints.map M.genericIso.inv g`, a rational point of the actual
  generic fibre of `M.group`. Rewriting with `φ.generic_comm` and
  `Iso.inv_hom_id_assoc` gives
  `rationalPoints.map (N.genericHom φ.hom) y = rationalPoints.map j g`.
  The Library lemma `exists_eq_of_integralPointMap_eq`, from
  `ClosedSubgroupIntegralPoints`, applies to the closed subgroup `φ.hom`. It
  produces an integral section `h` of `M.group` whose generic restriction
  `baseChangeSectionHom (Spec.algebraMap R K) M.group h` is `y`. Composing with
  `M.genericIso.hom` and cancelling `M.genericIso.inv ≫ M.genericIso.hom`
  shows `M.integralPointMap h = g`, so `g ∈ M.integralPoints`.

`Hom.IsSchematicClosure.integralPoints_eq_comap` applies this lemma to clause 1
of the closure predicate. This keeps the actual subgroup of the originally
specified generic group `H`, mapped by the original `j`.

## Consumer and exclusions

The intended consumer is KP Proposition 8.3.1. That construction closes a
faithful generic subgroup in a general linear integral model attached to a
stable lattice, then smoothens it. The Library module
`ClosedSubgroupIntegralPoints` proves the section formula for an already
supplied closed integral subgroup, but it does not construct the closure. This
module states the construction as an unproved proposition. It does not prove
it, and it constructs no stable lattice. It proves no smoothening,
finite-index enlargement, parahoric model existence or building-model axiom.
