# Rigidity of families of homomorphisms between diagonalizable groups over a base

Worker 5698.

This module proves that a family of homomorphisms between diagonalizable groups over an
arbitrary scheme `S` does not depend on its parameter, provided the parameter scheme has
preconnected fibres over `S`. It is a relative form of the field statement
`Langlands.GroupScheme.DiagonalizableRigidityStatement` (Milne, *Algebraic Groups* (2017),
Theorem 12.36), and it reuses the character-family locus decomposition of the proof of that
statement in [`Torus.DiagonalizableRigidityProof`](DiagonalizableRigidityProof.md) (namespace
`Langlands.GroupScheme.DiagonalizableRigidity`). The relative formulation (families recorded on
points over an arbitrary base) and its proof are internal to this project. They serve the
centrality results of Conrad, *Reductive group schemes* (2014), Lemma 3.3.1, whose proof uses
rigidity of groups of multiplicative type; SGA 3, Exposé IX (Gille–Polo edition), §5 obtains such
centrality results by a different route, through central homomorphisms and descent.

## Families on points

A family of homomorphisms `D → D'` parametrized by `X : Over S` is recorded on points: a
function

`F : ∀ V : Over S, (V ⟶ X) → (V ⟶ D.X) → (V ⟶ D'.X)`

with

- `hmul`: `F V a (t₁ * t₂) = F V a t₁ * F V a t₂` (multiplicative in the point of `D`), and
- `hnat`: `F W (f ≫ a) (f ≫ t) = f ≫ F V a t` for `f : W ⟶ V` (natural in the test scheme).

No morphism of schemes `X ×_S D → D'` is required. Every such morphism gives a family, but the
families used later (conjugation, descended commutators) are only defined on points.

## Declarations

In the namespace `Langlands.GroupScheme.DiagonalizableRigidity.CharFamily`, extending the
`CharFamily` API of [`Torus.DiagonalizableRigidityProof`](DiagonalizableRigidityProof.md):

- `comp c w`: the restriction of a character family `c : CharFamily X Λ` along `w : W ⟶ X`.
- `mem_locus_comp`: if `w x` lies in the locus `c.Locus m`, then `x` lies in
  `(c.comp w).Locus m`. The proof factors `Spec κ(x) → W → X` through `Spec κ(w x)` by
  `Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField`.
- `app_eq_of_forall_mem_locus`: if every point of `y : Y ⟶ X` lies in `c.Locus m`, then
  `c.app y χ = χ(m)`. This is `app_eq_of_locus` for `c.comp y` at the identity.
- `app_eq_app_of_locus`: two points `y y' : Y ⟶ X` give the same value
  `c.app y χ = c.app y' χ` if, for every `z : Y` and `m`, `y z ∈ c.Locus m` implies
  `y' z ∈ c.Locus m`. The preimages of the (open) loci under `y` form an open cover of `Y`. On
  the member indexed by `m` both values are `χ(m)` by `app_eq_of_forall_mem_locus` and
  naturality, and `eq_of_cover` glues.

In the namespace `Langlands.GroupScheme.RelativeDiagonalizableRigidity`, with `Λ`, `Λ'` arbitrary
abelian groups in universe `u` and `diagonalizable S Λ` the Library's split group `D_S(Λ)`:

- `pointsEquiv S Λ V : (V ⟶ (diagonalizable S Λ).X) ≃* (Multiplicative Λ →* Γ(V.left, ⊤)ˣ)`:
  points of `D_S(Λ)` over `V` are characters. It is `baseChangePointsEquiv` along
  `Gm.toSpecZ S` (module [`AbelianScheme.KernelBaseChange`](../../AbelianScheme/KernelBaseChange.md))
  followed by `Diagonalizable.characterPointsEquiv` over `ULift ℤ`.
- `pointsEquiv_comp`: `pointsEquiv S Λ V' (a ≫ x) = resChar a.left (pointsEquiv S Λ V x)`, from
  `baseChangePointsEquiv_naturality` and `characterPointsEquiv_comp`.
- `charHom F hmul a`: the family at the parameter `a`, transported to a homomorphism of
  character groups. `charHom_apply` unfolds it.
- `charFamily F hmul hnat l : CharFamily X.left Λ`: the `l`-th coordinate (`l : Λ'`) of the
  family, as a family of characters of `D(Λ)` parametrized by the scheme `X.left` with no base.
  A point `y : Y ⟶ X.left` makes `Y` an `S`-scheme through `y ≫ X.hom`. Naturality comes from
  `hnat` and `pointsEquiv_comp`.
- `charFamily_app`: for `x : T ⟶ X` and `g : T ⟶ D_S(Λ)`, the `l`-th coordinate of
  `F T x g` is `(charFamily F hmul hnat l).app x.left (pointsEquiv S Λ T g)`. The proof
  rewrites `F T x g` through the isomorphism `T ≅ Over.mk (x.left ≫ X.hom)` using `hnat`.
- `eq_of_preconnected_fibres`: if every fibre `X.hom ⁻¹' {s}` is preconnected
  (`_root_.IsPreconnected`), then `F V a t = F V a' t` for all `a a' : V ⟶ X` and
  `t : V ⟶ D_S(Λ)`.
- `eq_of_isDiagonalizable`: the same conclusion for any `D D' : GroupScheme S` with
  `IsDiagonalizable D` and `IsDiagonalizable D'`, by transporting the family along the given
  isomorphisms `D ≅ D_S(Λ)`, `D' ≅ D_S(Λ')`.

## Proof of `eq_of_preconnected_fibres`

Compare the characters `pointsEquiv S Λ' V (F V a t)` and `pointsEquiv S Λ' V (F V a' t)` at
each `l : Λ'`. By `charFamily_app` they are the values of the character family
`c = charFamily F hmul hnat l` at `a.left` and `a'.left`. Apply `app_eq_app_of_locus`. Let
`z : V.left` with `a.left z ∈ c.Locus m`. The points `a.left z` and `a'.left z` of `X.left` lie
over the same point `s` of `S`, because `a` and `a'` are morphisms over `S` (`Over.w`). The locus
`c.Locus m` is open and closed (`isOpen_locus`, `isClosed_locus` of the field proof, which hold
for any scheme `X`). A clopen set meeting the preconnected fibre over `s` contains it
(`IsPreconnected.subset_isClopen`), so `a'.left z ∈ c.Locus m`.

The proof uses no finiteness hypothesis on `Λ`, `Λ'`, `X` or `S`.
