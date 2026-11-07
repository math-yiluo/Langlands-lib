# Bruhat relation, support subspaces and `PQ`-regularity for represented parabolics

Author: Worker 6. Module `Langlands.Representation.Intertwining.PQRegularity`. The group-level part is in namespace `Langlands.Geometric`, the group-algebra kernel in `Langlands`, and the represented-parabolic part in `Langlands.Aubert.General.RepresentedParabolic`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VII.3.1–VII.3.3, printed pp.232–234 / PDF pp.238–240. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The geometric lemma it builds on is VI.5.1, from printed p.161 / PDF p.167.

Renard VII.3 constructs intertwining operators `i_P^G ρ → i_Q^G ρ` for two parabolics `P` and `Q` with the same Levi factor `M`. Its first three subsections set up the objects: the Bruhat order on `P \ G / Q` (VII.3.1), four `Q`-stable support subspaces of `i_P^G(W)` and their images in `r_Q^G i_P^G(W)` (VII.3.2), and three ideals of `ℂ[A_M]` together with `PQ`-regularity (VII.3.3). This module defines these objects. It is a definition unit. The only results it proves are the structural facts used to build the objects: reflexivity and transitivity of the Bruhat relation, right invariance of the support sets, and two membership criteria. It asserts nothing from the VII.3.3 Lemma, the VII.3.2 identifications of subquotients, or the inclusions between the subspaces.

## Group-level objects (`Langlands.Geometric`)

Here `G` is a group with a topology (`[Group G] [TopologicalSpace G]`; the invariance lemmas and the vanishing subfunctor also use `[IsTopologicalGroup G]`), and `P Q : Subgroup G`. Double cosets are Mathlib's `DoubleCoset.Quotient (P : Set G) Q`, with projection `DoubleCoset.mk P Q` and the actual double coset `DoubleCoset.quotToDoubleCoset P Q w ⊆ G` of a class `w`.

### The Bruhat relation (VII.3.1)

- `BruhatLE P Q w w'` means `quotToDoubleCoset P Q w ⊆ closure (quotToDoubleCoset P Q w')`: the double coset `P w Q` is contained in the closure of `P w' Q`. This is Renard's `w̄ ≤_{PQ} w̄'`.
- `BruhatLT P Q w w'` is `BruhatLE P Q w w' ∧ w ≠ w'`.
- `bruhatLE_refl` (from `subset_closure`) and `bruhatLE_trans` (from `closure_minimal`) show that `BruhatLE` is a preorder. Renard calls it a partial order. Antisymmetry is not asserted here.
- `IsBruhatRefinement P Q o`, for a linear order `o` on the double cosets, says `BruhatLE P Q w w' → o.le w w'`. It expresses Renard's choice of a total order `⪯` refining the Bruhat order. The module does not assert that such an order exists.

Renard indexes the double cosets by `W_M \ W_G / W_M`, identified with `P \ G / Q` through V.4.5/V.4.7, and writes `P w̄ Q` for the corresponding double coset. The Lean relation works on the actual double cosets `P(F) \ G(F) / Q(F)` and uses no Weyl group. That identification is not formalized here. The relation itself is the same closure condition.

### Right-invariant support sets

- `preimage_mk_mul_mem P Q T x g`: the union `DoubleCoset.mk P Q ⁻¹' T` of double cosets is stable under right multiplication by `x ∈ Q` (from Mathlib `DoubleCoset.mk_mul_mem`).
- `closure_doubleCoset_mul_mem`: the closure of `P w Q` is right `Q`-stable, because right multiplication by `x` is continuous (`continuous_mul_const`) and maps `P w Q` into itself.
- `boundary_doubleCoset_mul_mem`: so is the boundary set `closure (P w Q) \ P w Q`.

### Vanishing subfunctors

`rawSmoothVanishingSubfunctor P Q Z hZ` works with any subset `Z ⊆ G` that is right `Q`-stable (`hZ : ∀ x : Q, ∀ g ∈ Z, g * x ∈ Z`). It is the published `rawSmoothSupportSubfunctor P Q U hU` (module `SmoothSupportFiltration`) for `U = (quotientMap P '' Z)ᶜ ⊆ P \ G`. Its object at `A : Rep R P` is the space of smoothly induced functions `f` such that `f(x) ≠ 0` forces `P x ∉ P Z`. The invariance proof `hU` writes a point `c` of `P \ G` as `P y` and shows that if `P (y x)` met `P Z` at `P g`, then `P y = P (g x⁻¹)` with `g x⁻¹ ∈ Z`.

`mem_rawSmoothVanishingSubfunctor_iff` proves that `f` lies in this subfunctor if and only if `Induction.eval P A.ρ f g = 0` for every `g ∈ Z`. The reverse direction uses the left `P`-equivariance `f(h g) = A.ρ h (f g)` of induced functions, so vanishing at `g` gives vanishing on `P g`.

Renard's conditions in VII.3.2 concern `Supp(f)`. A smooth vector of the induced representation is invariant under right translation by an open subgroup, so both `{f ≠ 0}` and `{f = 0}` are open. Hence `Supp(f) = {f ≠ 0}`, and "`Supp(f) ∩ Z = ∅`" means "`f` vanishes on `Z`". This is the reason the subspaces below are written as vanishing conditions. That equivalence is a remark explaining the choice and is not formalized.

## The group-algebra kernel (`Langlands`)

For a monoid `H`, a monoid `B`, a complex representation `ρ : Representation ℂ H V` and a monoid homomorphism `φ : B →* H`, `groupAlgebraKernel ρ φ` is `RingHom.ker (Representation.asAlgebraHom (ρ.comp φ))`. That is the kernel of the algebra map `ℂ[B] → End_ℂ(V)` extending `ρ ∘ φ` linearly, an ideal of `MonoidAlgebra ℂ B`. `mem_groupAlgebraKernel_iff` unfolds membership. This is Renard's "restrict `σ` to `A_M` and extend to `ℂ[A_M]`; take the kernel".

## Represented-parabolic objects (`Langlands.Aubert.General.RepresentedParabolic`)

### Setting

The field is `k : Type u` with `[Field k] [TopologicalSpace k] [T2Space k]`, and `G` is a group scheme over `Spec k` with `[IsAffineHom G.X.hom]`. Its rational points carry the published canonical topology `RationalPointFamily.pointTopology` (local instance `regularityAmbientPointTopology`), with `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]`. The two represented parabolics share one Levi scheme `M`:

- `p : P ⟶ G`, `l : M ⟶ P`, `r : N ⟶ P` with `IsParabolicSubgroup p`, `LeviSubgroup.IsGeometricUnipotentRadical r`, `IsRationalLeviSubgroup l` and `IsIso (subgroupMultiplication l r)`. This is `P = MN`.
- `q : Q ⟶ G`, `lQ : M ⟶ Q`, `rQ : U ⟶ Q` with the same four hypotheses. This is `Q = MU`.

The definitions do not require the two embeddings `l ≫ p` and `lQ ≫ q` of `M` in `G` to agree. Renard's setting is the case where they do, and statements using these objects will assume it. Renard also assumes `M` standard, and says this is only for convenience. That is not assumed here. Representations of `M(F)` are `SmoothRep.{0, u, v} ℂ (rationalPoints M)` for the published Levi topology `leviPointTopology l hl`.

Induction and the Jacquet functor are the published normalized ones:

- `leviInductionFunctor p l r hp hr hl hmul`, Renard's `i_P^G`, composed with `leviInducingFunctor` as in the published `leviInductionSupportFiltration`;
- `leviJacquetInductionFunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ`, Renard's `r_Q^G ∘ i_P^G : M(M) → M(M)`, valued in `Rep.{max u v} ℂ (rationalPoints M)` through the Levi `lQ` of `Q`.

### Double cosets

- `parabolicDoubleCosets p q` is `DoubleCoset.Quotient (pointImage p) (pointImage q)`, the actual double cosets `P(F) \ G(F) / Q(F)` of the point images.
- `identityParabolicDoubleCoset p q` is `DoubleCoset.mk _ _ 1`, Renard's `1̄`, the double coset `P(F) Q(F)`.

### The four support subspaces and their images (VII.3.2)

`leviVanishingSubfunctor p l r hp hr hl hmul q Z hZ` is the subfunctor of `i_P^G(-)`, restricted to `Q(F)`, of functions vanishing on a right `Q(F)`-stable set `Z ⊆ G(F)`. It is `rawSmoothVanishingSubfunctor (pointImage p) (pointImage q) Z hZ` precomposed with `leviInducingFunctor`. Being a `RepSubfunctor` of the restriction to `Q(F)`, each of its values is `Q(F)`-stable, as Renard notes. Its variants, for `w` a double coset and `o` a linear order on the double cosets, are:

| Lean | Renard | vanishing set `Z` | Renard's condition |
| --- | --- | --- | --- |
| `initialVanishingSubfunctor … o w` | `F̃^{⪯w̄}_{PQ}` | `⋃_{w' ⪯ w} P w' Q` (`mk ⁻¹' {w' ∣ o.le w' w}`) | `Supp f ∩ ⋃_{w̄' ⪯ w̄} P w̄' Q = ∅` |
| `strictInitialVanishingSubfunctor … o w` | `F̃^{≺w̄}_{PQ}` | `⋃_{w' ≺ w} P w' Q` (`o.lt`) | the same with `≺` |
| `boundaryVanishingSubfunctor … w` | `F̃^{<w̄}_{PQ}` | `closure (P w Q) \ P w Q` | `Supp f ∩ closure (P w̄ Q) ⊆ P w̄ Q` |
| `closureVanishingSubfunctor … w` | `F̃^{≤w̄}_{PQ}` | `closure (P w Q)` | `Supp f ∩ closure (P w̄ Q) = ∅` |

The right-invariance proofs are the three lemmas above. The order `o` is arbitrary in the definitions. Renard uses a total order refining the Bruhat order, which statements can impose with `IsBruhatRefinement`.

`initialSupportImage`, `strictInitialSupportImage`, `boundarySupportImage` and `closureSupportImage` are Renard's `F^{⪯w̄}_{PQ}`, `F^{≺w̄}_{PQ}`, `F^{<w̄}_{PQ}` and `F^{≤w̄}_{PQ}`. Each is the image of the corresponding subfunctor in `r_Q^G i_P^G`, given by the published `leviJacquetImageSubfunctor`: the image in the normalized Jacquet quotient along `Q`, with the action transported from the Levi image to `M(F)`. This is the same construction as the published `leviJacquetSupportFiltration`. The module does not assert Renard's inclusions `F̃^{⪯w̄} ⊂ F̃^{≺w̄} ⊂ F̃^{<w̄}` and `F̃^{≤w̄} ⊂ F̃^{<w̄}`, the isomorphism `F^{≺w̄}/F^{⪯w̄} ≅ F^{<w̄}/F^{≤w̄}`, the reformulated geometric lemma, or `F^{<1̄}/F^{≤1̄} ≅ Id`.

### The ideals and `PQ`-regularity (VII.3.3)

These take a commutative group scheme `A` over `Spec k` and a homomorphism `a : A.toGrp ⟶ M`. Renard's case is `a` the split component `A_M` of `M` (the published `IsSplitComponent a`), but the definitions accept any `a`. `A(F)` acts on representations of `M(F)` through `rationalPoints.map a`. The ideals live in `MonoidAlgebra ℂ (rationalPoints A.toGrp)`, Renard's `ℂ[A_M]`.

- `splitComponentKernel l hl a σ` is `groupAlgebraKernel σ.representation (rationalPoints.map a)`, Renard's `I_σ = ker σ|_{ℂ[A_M]}`.
- `pqRegularityKernel p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ`, Renard's `I^{PQ}_σ = ker [(r_Q^G ∘ i_P^G / F^{<1̄}_{PQ})(E)]|_{ℂ[A_M]}`. Let `S` be the value of `boundarySupportImage … (identityParabolicDoubleCoset p q)` at `σ`, that is `F^{<1̄}_{PQ}(σ)`. The definition takes the Mathlib quotient representation `Representation.quotient` of `(r_Q^G i_P^G)(σ)` by `S.toSubmodule`, then applies `groupAlgebraKernel` with `rationalPoints.map a`.
- `IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ` is `splitComponentKernel l hl a σ ⊔ pqRegularityKernel … a σ = ⊤`, condition (i) of the Lemma: `I_σ + I^{PQ}_σ = ℂ[A_M]`. In a commutative ring, the supremum of two ideals is their sum.
- `pieceSplitComponentKernel D a σ` is defined for a published geometric-lemma intersection datum `D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z` at a representative `z` of a double coset. With `L = M` here, `D.pieceFunctor` is the graded piece `i^M_{Q'} ∘ ι ∘ r^M_{P'}`, Renard's `i^M_{M∩w⁻¹·P} ∘ w ∘ r^M_{M∩w·Q}`. The definition is `groupAlgebraKernel (D.pieceFunctor.obj σ).ρ (rationalPoints.map a)`, the kernel of the `A(F)` action on the full piece.

## Provenance and departures from the source

The provenance is derived. Renard defines `PQ`-regularity as "(i) or (ii)", which his Lemma proves equivalent. Here the definition is condition (i). The equivalence with (ii) and the relation to (iii) are later statements and are not asserted here.

Renard defines `I^{Q,w̄}_σ` on `w ∘ r^M_{M∩w·Q}(E)`, which has no outer induction. His proof of the Lemma (printed p.234 / PDF p.240) identifies that kernel with the kernel on the full piece `i^M_{M∩w⁻¹·P} ∘ w ∘ r^M_{M∩w·Q}(σ)` because parabolic induction is faithful. `pieceSplitComponentKernel` uses the full piece. That piece is a representation of `M(F)` itself, so the action of `A_M` needs no extra data, whereas `A_M ⊂ M ∩ w⁻¹·M` is not part of the published intersection datum. The identification of the two kernels is not asserted.

The other departures are those already described: actual double cosets instead of `W_M \ W_G / W_M`, support conditions written as vanishing conditions, an arbitrary linear order and an arbitrary homomorphism `a` in the definitions, and independent Levi embeddings `l ≫ p` and `lQ ≫ q`.
