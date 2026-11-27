# Models of abelian varieties on which relative translations extend

The module `Langlands.AbelianScheme.TranslationExtensionModelStatement` contains two
definitions, a predicate `TranslationExtensionProperty` and a proposition
`TranslationExtensionModelStatement`. It states the proposition and proves nothing. The
content is derived from Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), §4.3,
Proposition 4 (iii), printed p. 106, with its uses in the proofs of §4.3, Proposition 5
(printed pp. 107–108) and §4.4, Corollary 4 (printed pp. 110–111) (literature ID
`bosch-lutkebohmert-raynaud-1990-neron-models`, file SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`; printed page `p` is
PDF page `p + 7`).

## `TranslationExtensionProperty R K B X e`

Let `R` be a discrete valuation ring with fraction field `K`, `B` an abelian variety over `K`
(`AbelianScheme (Spec K)`, with its commutative group law `μ[B.X]`), `X` a scheme over
`Spec R`, and `e : B.X ≅ (Over.pullback (Spec K ⟶ Spec R)).obj X` an isomorphism over
`Spec K` from `B` to the generic fibre `X_K = X ×_R Spec K` of `X`.

The predicate says: for every scheme `Z` in the same universe with a smooth morphism
`z : Z ⟶ Spec R` and every morphism `a : Z_K ⟶ B` over `Spec K` from the generic fibre
`Z_K = (Over.pullback (Spec K ⟶ Spec R)).obj (Over.mk z)` of `Z`, there are

- an open subscheme `V` of `Z ×_R X` (`pullback z X.hom`) and
- a morphism `t : V ⟶ X` over `Spec R`, where `V` lies over `Spec R` through the first
  projection and `z` (`SchemeHomOver (V.ι ≫ pullback.fst z X.hom ≫ z) X.hom`),

such that

1. every point of `Z ×_R X` that does not lie over the closed point of `Spec R` lies in
   `V`;
2. every irreducible component of the closed fibre
   `{x : Z ×_R X // x lies over the closed point}` contains a point of `V`;
3. the morphism `(pr₁, t) : V ⟶ Z ×_R X`
   (`pullback.lift (V.ι ≫ pullback.fst z X.hom) t`) is flat;
4. on the generic fibre, `t` is `(z, x) ↦ a(z) · x`: for every scheme `S` with a morphism
   `k : S ⟶ Spec K` and every `p : S ⟶ V` whose composite to `Spec R` is
   `k ≫ (Spec K ⟶ Spec R)`, write `z_K : S ⟶ Z_K` and `x_K : S ⟶ X_K` for the morphisms
   over `Spec K` induced by the two components of `p` and by `k`; then `p ≫ t` is the
   composite of the product `(z_K ≫ a) · (x_K ≫ e⁻¹)` in the group `S ⟶ B` (computed as
   `lift (z_K ≫ a) (x_K ≫ e.inv) ≫ μ[B.X]` in the category of schemes over `Spec K`)
   with `e` and the projection `X_K ⟶ X`.

Conditions 1 and 2 are the conditions on the domain in the Library's weak Néron mapping
property `Langlands.AbelianScheme.WeakNeronMappingProperty`. For an arbitrary `X`, the
predicate imposes exactly condition 2 as stated (a point of `V` in every irreducible
component of the closed fibre), which in general is stronger than density of `V` in the
closed fibre. In `TranslationExtensionModelStatement` below, `X` and `Z` are smooth over
`Spec R`, so `Z ×_R X` is smooth over `Spec R` and its closed fibre is locally Noetherian;
for this product an open subscheme containing the generic fibre is dense in each fibre over
`Spec R` exactly when it meets every irreducible component of the closed fibre. Condition 4
is stated on `S`-valued points over `Spec K`, in the form used by
`Langlands.AlgebraicGeometry.BirationalGroupLaw.Solution`.

## `TranslationExtensionModelStatement`

`TranslationExtensionModelStatement.{u}` quantifies over a discrete valuation ring `R`
with fraction field `K`, an abelian variety `B` over `K` and a scheme `W` over `Spec R`
which is smooth, separated, locally of finite type and quasi-compact, whose generic fibre
is isomorphic to `B.X` over `Spec K`, and which has the weak Néron mapping property
`WeakNeronMappingProperty R K W.hom`. These are the hypotheses of
`Langlands.AbelianScheme.NeronModelOfWeakNeronModelStatement`. It asserts a scheme `X`
over `Spec R` and an isomorphism `e : B.X ≅ X_K` over `Spec K` such that `X ⟶ Spec R` is
smooth, separated, locally of finite type, quasi-compact and surjective and
`TranslationExtensionProperty R K B X e` holds.

## Correspondence with the source

In BLR §4.3, `X_K` is a smooth `K`-group scheme of finite type whose `K^sh`-points are
bounded (for instance an abelian variety), and `ω` is a left-invariant differential form
of degree `d = dim X_K` generating `Ω^d_{X_K/K}` (BLR §4.2, Propositions 1 and 2 and
Corollary 3, printed pp. 100–102). For a smooth separated `R`-model of finite type with irreducible special
fibre, `ord ω` is the order of `ω` at the generic point of the special fibre (printed
p. 104). The `ω`-minimal models are those of minimal order (Proposition 2, printed
p. 105). Proposition 4 (printed pp. 106–107) glues representatives of the `ω`-minimal
models along the generic fibre to a smooth, separated, faithfully flat `R`-model `X` of
finite type and proves (iii): if `R'` is the local ring of a smooth `R`-scheme `Z` at a
generic point of its special fibre and `K'` its field of fractions, every translation of
`X_{K'}` by a `K'`-valued point extends to an `R'`-birational morphism of `X ⊗_R R'` which
is an open immersion on its domain of definition. The proofs of Proposition 5 (with `Z`
the model `X` itself, printed p. 108) and of Corollary 4 in §4.4 (with `Z` an arbitrary
smooth `R`-scheme, printed p. 111) apply (iii) to the translation by the `K'`-valued point
given by a morphism on `Z_K`.

`TranslationExtensionProperty` is (iii) spread out over `Z`. The morphism `a : Z_K ⟶ B`
gives, at a generic point `ζ` of the special fibre of `Z`, the `K'`-valued point of (iii)
with `R' = O_{Z,ζ}`; the base change of `t` to `Spec R'` is the extension of the
translation by this point, and its domain contains the generic fibre and the generic
points of the special fibre above `ζ` by conditions 1 and 2. Condition 3 records, in place
of "an open immersion on its domain", the flatness of the translation `(z, x) ↦ (z, t(z, x))`
over `Z`; it is what makes a translation carry generic points of the special fibre of
`Z ×_R X` to generic points of the special fibre, because flat morphisms lift
generizations.

The statement replaces the weak Néron model of the source (a family of models) by a
single model `W` with the weak Néron mapping property. For one separated model no gluing
of different models is needed: distinct points of an integral separated scheme have
distinct local rings in its function field, so two components of the special fibre of
`W` are never equivalent in the sense of BLR (printed p. 105). The intended model `X` is
the open subscheme of `W` on which the section `π^{-n₀} ω` of `Ω^d_{W/R}` is a
generator, where `π` is a uniformizer of `R` and `n₀` is the minimum over the irreducible
components of the special fibre of `W` of the order of `ω` at their generic points; it
contains the generic fibre and the `ω`-minimal components of the special fibre, minus
their intersections with the components that are not `ω`-minimal. For a morphism `a` as above, the weak
Néron mapping property of `W`, applied to `Z ×_R X` and to `(z, x) ↦ a(z) · x`, gives an
extension `v` into `W`; the invariance of `ω` under translations and the minimality of
`n₀` show that `(z, x) ↦ (z, v(z, x))` preserves `pr₂^* (π^{-n₀} ω)` as a relative
differential form over `Z`, hence takes values in `Z ×_R X` and is étale by the Jacobian
criterion (BLR §2.2, Corollary 10, printed p. 41). This explains the origin of the
statement; the module does not prove it.

The model `X` and condition 4 are the input of the birational group law on `X` (BLR
§4.3, Proposition 5) and of the Néron mapping property of its solution (BLR §4.4,
Corollary 4), the content of `Langlands.AbelianScheme.NeronModelOfWeakNeronModelStatement`.
