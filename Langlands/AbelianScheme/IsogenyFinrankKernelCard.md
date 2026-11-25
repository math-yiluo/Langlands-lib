# The degree of an isogeny in characteristic zero counts its kernel points

Lean module: `Langlands.AbelianScheme.IsogenyFinrankKernelCard`, namespace
`Langlands.AbelianScheme.IsogenyKernelCard`.

The main theorem `finrank_eq_natCard_ker` proves the content of the statement
`Langlands.AbelianScheme.IsogenyFinrankKernelCardStatement`.
Let `α : A ⟶ B` be an isogeny of abelian schemes over an algebraically closed field `k` of
characteristic zero. At every point `y` of `B`, the rank `(hom α).finrank y` of the finite flat
underlying morphism equals the number of elements of the kernel of the homomorphism induced
on `k`-points. The one-line proof of the statement itself is
`Langlands.AbelianScheme.isogenyFinrankKernelCard`, in the separate module
`Langlands.AbelianScheme.IsogenyFinrankKernelCardProof`.

## Provenance

The source is Milne, *Abelian Varieties*, author revision of January 2, 2022 (registered source
`milne-abelian-varieties-1986-author-2022`), Section 8, p. 12. In characteristic zero the
kernel of a homomorphism of abelian varieties is reduced. The degree of an isogeny is the order
of its kernel, and also the rank of `f_* 𝒪_A`. A reduced finite group scheme over an
algebraically closed field has as many `k`-points as its order. The Lean proof follows this
outline. Reducedness comes from smoothness: Cartier's theorem in the Library
(`affineCartierSmooth`) and the Library lemma that schemes smooth over a field are reduced.
Milne instead cites Shatz. The point count uses the Library's étale point-count
`natCard_algHom_eq_finrank`, after showing that a finite reduced algebra over an algebraically
closed field is étale. `overPointsEquiv` is an internal auxiliary equivalence.

## Declarations

### `formallyEtale_of_isReduced`

**Statement.** Let `K` be an algebraically closed field and `A` a reduced commutative
`K`-algebra that is finite as a `K`-module. Then `A` is formally étale over `K`.

**Proof.** `A` is Artinian (finite over a field). A reduced Artinian ring is the product of its
quotients by maximal ideals (Mathlib's `IsArtinianRing.equivPi`, restricted to `K`-scalars).
Each quotient is a field, finite over `K`, hence algebraic, hence separable because `K` is
perfect. Mathlib's characterization `Algebra.FormallyEtale.iff_exists_algEquiv_prod` (finite
products of separable field extensions) finishes.

### `natCard_sections_eq_finrank_of_isReduced`

**Statement.** Let `K` be algebraically closed and `f : X ⟶ Spec K` finite and flat with `X`
reduced. Then for every point `x` of `Spec K` the number of sections
`{z : Spec K ⟶ X // z ≫ f = 𝟙}` equals `f.finrank x`.

**Proof.** `X` is affine. Its global sections `Γ(X, ⊤)` form a finite `K`-algebra (via the
Library's `coordinateAlgebra f`), reduced because `X` is. By `formallyEtale_of_isReduced` it is
formally étale. The Library's `sectionsAlgHomEquiv` identifies sections with `K`-algebra maps
`Γ(X, ⊤) → K`. `natCard_algHom_eq_finrank` counts them as `finrank K Γ(X, ⊤)`, and
`homFinrank_eq_coordinateFinrank` identifies this with `f.finrank x`. This is the Library's
`natCard_sections_eq_homFinrank` with the hypothesis `Etale f` replaced by reducedness of `X`
over an algebraically closed field.

### `overPointsEquiv X` (definition)

For a scheme `X` over `S`, the morphisms `Over.mk (𝟙 S) ⟶ X` in `Over S` are equivalent to the
sections `{z : S ⟶ X.left // z ≫ X.hom = 𝟙 S}`, by taking the underlying morphism.

### `finrank_eq_natCard_ker`

**Statement.** Let `k` be algebraically closed of characteristic zero, `A` and `B` abelian
schemes over `Spec k`, and `α : A ⟶ B` an isogeny. Then for every point `y` of `B.X.left`,
`(hom α).finrank y = Nat.card (GroupScheme.pointsHom (groupHom α) (Over.mk (𝟙 _))).ker`.

**Proof.** Put `f = groupHom α`, with `hom α = f.hom.hom.left` finite and flat
(`isIsogeny_iff`). Let `K` be the Library's group-scheme kernel `GroupScheme.kernel f`.
`kernel_isPullback_scheme` presents its structure morphism `K.hom` as the base change of
`hom α` along the unit section `η` of `B`.

1. *The kernel is finite, flat, smooth and reduced.* Finite and flat by base change. Smooth by
   `affineCartierSmooth`: `K` is a group scheme over a field of characteristic zero, and it is
   affine and of finite type because it is finite. Reduced by
   `SmoothReducedProof.isReduced_of_smooth_over_field`.
2. *The rank is constant.* `B.X.left` is integral (`field_isIntegral`), hence connected, and
   noetherian (`field_isNoetherian`), so `hom α` is locally of finite presentation. The rank
   of a finite flat morphism of finite presentation is locally constant
   (`Scheme.Hom.isLocallyConstant_finrank`). Hence `(hom α).finrank y` equals the rank at
   `η x`, where `x` is the closed point of `Spec k`.
3. *Rank at the unit point.* `Scheme.Hom.finrank_of_isPullback` gives
   `(hom α).finrank (η x) = K.hom.finrank x`.
4. *Counting.* `natCard_sections_eq_finrank_of_isReduced` turns this rank into the number of
   sections of `K.hom`. `overPointsEquiv` identifies these with the points
   `Over.mk (𝟙 _) ⟶ K`. The Library's `kernelPointsEquiv` identifies those with the kernel of the
   homomorphism induced by `f` on points over `Over.mk (𝟙 _)`.
