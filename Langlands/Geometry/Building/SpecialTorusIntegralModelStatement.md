# The integral model behind special tori

The module states the proposition
`Langlands.Geometry.Building.SpecialTorusIntegralModelStatement.{u}`. It collects the
building input used in Kaletha–Prasad's proof of Proposition 9.3.4, before the lifting of
a maximal torus in the special fibre. This is a derived statement, with no proof in this
module. The Lean statement is reused from Worker 224's revision 1 shared draft for
Task 5514 (`632bdfae-d1a6-4680-acf6-e5c1d32a17d8`); Worker 110 prepared this publication
and revised its source explanation.

## Exact scope

For every `F : Type u` with `[Field F] [ValuativeRel F] [TopologicalSpace F]` and
`[IsNonarchimedeanLocalField F]`, every
`G : GroupScheme (Spec (CommRingCat.of F))` with `IsConnectedReductive G`, every
`S : CommGroupScheme (Spec (CommRingCat.of F))`, and every homomorphism
`iS : S.toGrp ⟶ G` with `IsMaximalSplitTorus iS`, there exists
`M : IntegralModel ↥𝒪[F] F G` with the following four properties.

1. `M.IsSmooth`: the structure morphism of `M.group` is smooth. The `IntegralModel`
   structure already supplies affineness, flatness, local finite type and a generic
   identification `M.genericIso` with `G`.
2. The special fibre
   `((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group).X.left`
   has `ConnectedSpace`.
3. There exist a commutative group scheme `𝒮` over `Spec 𝒪[F]`, a homomorphism
   `j : 𝒮.toGrp ⟶ M.group`, and an isomorphism
   `e : (CommGroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj 𝒮 ≅ S`
   such that `IsSplitTorus 𝒮.toGrp`, `IsClosedSubgroup j`, and
   `M.genericTorusMap 𝒮 j = CommGroupScheme.groupHom e.hom ≫ iS`.
   Thus this closed split integral torus has the specified inclusion of `S` as its
   generic fibre.
4. There exist a commutative group scheme `𝒜` over
   `Spec (CommRingCat.of (fixedFieldIntegers F))` and a homomorphism
   `a : 𝒜.toGrp ⟶ M.baseChangeUnramified.group` such that
   `IsSplitTorus 𝒜.toGrp`, `IsClosedSubgroup a`, and
   `IsMaximalSplitTorus (M.baseChangeUnramified.genericTorusMap 𝒜 a)`.

Here `𝒪[F]` and `𝓀[F]` are the valuation integers and residue field of `F`;
`K = inertiaFixedField F` is its maximal unramified extension, and
`O_K = fixedFieldIntegers F` is the valuation integer ring of `K`.
`M.baseChangeUnramified` is the actual base change along `𝒪[F] → O_K`, with generic
fibre identified with `baseChanged F K G`. The map `genericTorusMap` applies generic
base change and then the model's chosen generic identification. In particular, item 4
concerns a maximal `K`-split torus of this actual `G_K`.

The universe `u` is arbitrary, and equal and mixed characteristic are included.
There is no additional quasi-splitness, residue-field, tameness, simply-connectedness
or rank assumption, and no supplied building, point, model or torus.

## Derived provenance

The main source is Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The locators below use printed pages and the retained PDF's one-based page numbers.
KP works more generally over a Henselian discretely valued field `k` with perfect
residue field, using `o`, `K`, `O` and `Γ = Gal(K/k)`. Here these specialize to
`F`, `𝒪[F]`, `inertiaFixedField F` and `fixedFieldIntegers F`.

The proof of Proposition 9.3.4 (printed p.332 / PDF p.363) first finds
`x ∈ B(G_K)` fixed by `Γ` and the maximal bounded subgroup `S(K)^1`.
It uses Proposition 4.2.13 for boundedness and Theorem 1.1.15 for the fixed point.
Read §9.2.1 with the corrections dated 1 November 2024, PDF p.39, registered as
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
The correction proves finite point orbits by defining and splitting an apartment's
torus over a finite Galois subextension; it also gives a `Γ`-fixed point for every
bounded `Γ`-stable subgroup. Applied to `S(K)^1`, this supplies the required point.

For items 1 and 2, take the descended model `G^0_x` of §9.2.5
(printed pp.327–328 / PDF pp.358–359). Axiom 4.1.20
(printed p.163 / PDF p.194) supplies the smooth affine model `G^1_x` and its relative
identity component `G^0_x` over `O`. Section 9.2.5 descends both to smooth affine
`o`-models with generic fibre `G` and identifies the special fibre of `G^0_x` with
the identity component of that of `G^1_x`. This gives smoothness and the stated
connected special fibre; the generic identification is included in `IntegralModel`.

For item 3, the proof of Proposition 9.3.4 takes the schematic closure of `S` in
`G^1_x`. Proposition B.2.4 (printed p.656 / PDF p.687) says that this is an `o`-torus
with generic fibre `S`, since `S_K` is split and `S(K)^1 ⊂ G(K)^1_x`.
Its connected fibres place it in the relative identity component `G^0_x`, where it
remains closed. Since its generic fibre is split and `o` is a normal Henselian DVR,
the torus itself is split: its étale character lattice has trivial monodromy, as can
be checked at the generic point. This generic-to-integral splitness is an additional
formulation step beyond the word “torus” in B.2.4. The generic identification of the
schematic closure gives `e` and the equality of maps in item 3.

For item 4, choose an apartment of `B(G_K)` through `x` and let `A` be its maximal
`K`-split torus. Axiom 4.1.20(3), applied over `K` with `Ω = {x}`, supplies a closed
split `O`-torus in `G^0_x` with generic fibre `A`. The descent of §9.2.5 identifies this
upstairs model with `M.baseChangeUnramified`. This supplies precisely the torus map
and generic maximal split condition in item 4.

After these inputs, KP applies Proposition 8.2.1(1)
(printed p.286 / PDF p.317) to lift a special-fibre maximal torus containing the
closure of `S`, and then concludes that its generic fibre is a special torus.
Those algebraic steps are retained by Task 5514, whose target is
`Langlands.Geometry.Building.SpecialTorusExistenceStatement`; they are not asserted
or proved by this module.

## Formulation choices and limits

The connected model `G^0_x` is used in place of the `G^1_x` appearing in the proof of
9.3.4, so that the special-fibre connectedness needed by the consumer's
`maximalTorusConjugacy` argument is explicit. Item 3 asks for a split `𝒪[F]`-torus,
with the justification above.

The existing theorem
`IntegralModel.exists_isMaximalSplitTorus_baseChangeUnramified`, in
`Langlands.GroupScheme.IntegralModel.UnramifiedSplitMaximalTorus`, supplies item 4
under the stronger hypothesis of a connected reductive special fibre. The present
statement asks only for a smooth model with connected special fibre, so that
theorem alone does not supply the required model.

The Lean conclusion records neither the point nor a Bruhat–Tits identification of
`M`, a parahoric integral-point formula, reductivity of the special fibre, or an
inclusion between `𝒮` and `𝒜`. The building and its integral models remain construction
obligations for the proof. The module imports the three prescribed Library modules
unchanged and introduces only this proposition definition.
