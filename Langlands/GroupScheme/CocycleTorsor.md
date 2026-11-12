# Torsors of cocycles on affine fpqc covers

Authors: Worker 5015.

This module states and proves `Langlands.GroupScheme.CocycleTorsorExistenceStatement.{u}`,
at arbitrary universe `u`: every Library cocycle on an affine flat surjective cover of an
affine base is the cocycle of an actual torsor. The proof is the theorem
`Langlands.GroupScheme.cocycleTorsorExistence`. The module also proves
`Langlands.GroupScheme.Cocycle.isTrivial_of_torsor_section`: a section of such a torsor over
the base trivializes the cocycle. Together they turn theorems about points of torsors into
vanishing theorems for the Library's `Cocycle`. The Library already had the opposite
direction, `torsorCocycle` and `exists_section_of_isTrivial` in `TorsorCocycle`.
The proofs use only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## The statement

Let `S : Scheme.{u}` be affine. Let `G : GroupScheme S` have affine structure morphism
`G.X.hom`. Let `U : Over S` have affine underlying scheme `U.left`, with `U.hom` flat and
surjective. Let `ξ : Cocycle G U` be an actual natural cocycle, in the convention of
`TorsorCocycle`: values `ξ.toFun a b : Z ⟶ G.X` for all tests `Z` over `S` and
`a b : Z ⟶ U`, natural in `Z`, with `ξ.toFun a c = ξ.toFun a b * ξ.toFun b c`.

The proposition asserts that there are

- an object `X : Over S` with a left action `ModObj G.X X`,
- invertibility of the shear `ModObj.leftSMul G.X X : G.X ⊗ X ⟶ X ⊗ X`,
  `(m, x) ↦ (m • x, x)`, so that `X` is a torsor,
- a point `u : U ⟶ X` over the cover,

such that

1. `X.left` is affine;
2. `X.hom` is surjective;
3. the square formed by `(snd G.X U).left`, `(fst G.X U • (snd G.X U ≫ u)).left`, `U.hom` and
   `X.hom` is a pullback square of schemes. Thus the pullback of `X` to `U` is identified with
   the trivial torsor `G.X ⊗ U` by `(h, a) ↦ h • u(a)`;
4. for every test `Z` and all `a b : Z ⟶ U`, `ξ.toFun a b • (b ≫ u) = a ≫ u`.

Condition 4 says that `ξ.toFun a b` is the group point carrying `b ≫ u` to `a ≫ u`. In
the torsor case this point is unique, so condition 4 is equivalent to
`torsorCocycle hX u = ξ` for the Library's `torsorCocycle`.

The statement asserts flatness of `X.hom` only through condition 3. Every property of
morphisms that descends along fpqc covers and holds for `pullback.snd G.X.hom U.hom`
transfers to `X.hom`. The module records two cases. `CocycleTorsor.surjective_hom` gives
condition 2. `CocycleTorsor.smooth_hom` shows that `X.hom` is smooth, hence flat, whenever
`G.X.hom` is smooth. It uses Mathlib's fpqc descent of smoothness. The pinned Mathlib has no
fpqc descent of flatness itself, so the general statement does not claim it.
Quasi-compactness of `X.hom` follows from condition 1, since a morphism between affine
schemes is affine.

## The implemented proof

### Groupoid descent of affine schemes

`CocycleTorsor.exists_affineQuotient` is a scheme-level descent lemma. Suppose `Y`, `U` and
`M₀` are affine, `q₀ : U ⟶ M₀` is flat and surjective, and `f : Y ⟶ U`. Suppose
`t s : R ⟶ Y` satisfy `IsPullback (t ≫ f) s q₀ (f ≫ q₀)`. Suppose the relation has a unit
`diag` with `diag ≫ t = diag ≫ s = 𝟙` and a composition on composable pairs. Then there are
an affine `M`, a map `q : Y ⟶ M` and a map `h : M ⟶ M₀` with `IsPullback f q q₀ h` and
`IsPullback t s q q`. The proof transfers the two pullback squares to pushout squares of
global sections. It then applies the published ring theorem
`FaithfullyFlatCoalgebraDescent.isPushout_eqLocus_of_groupoid`, with `M = Spec` of the
equalizer subring of `t` and `s`. It follows step by step the published proof of
`etaleEquivalenceRelationCartesianAffineQuotient`. That proof is for étale relations, while
this lemma has no étaleness hypothesis and returns the square over `M₀`.

### The relation of the cocycle

Put `trivialCover G U = G.X ⊗ U`, with points `(h, a)`, and
`relation G U = U ⊗ trivialCover G U`, with points `(b, (h, a))`. The source `src` sends
`(b, (h, a))` to `(h, a)`. The target `tgt` sends it to `(h * ξ(a, b), b)`. So `(h, a)` is
identified with `(h * ξ(a, b), b)`. The unit is `diag : (h, a) ↦ (a, (h, a))`.
`diag_tgt` uses `ξ(a, a) = 1` (`Cocycle.toFun_self`). The composition of two composable
relation points `(b, (h, a))` and `(b', (h', a'))` is `(b, (h', a'))`. `compose_tgt` is the
cocycle identity `ξ(a', b') * ξ(b', b) = ξ(a', b)`. `isPullback_out` is the canonical square
of `U ⊗ (G.X ⊗ U)`, because `tgt ≫ snd G.X U = fst`.

`nonempty_quotient` applies the descent lemma with `q₀ = U.hom`. The chosen quotient gives
the object `torsor ξ` over `S`. It also gives the morphism `proj` from the trivial torsor
over the cover, with the pullback square over `U.hom` and the kernel-pair square of
`(tgt, src)`. As a base change of `U.hom`, `proj` is flat, surjective and quasi-compact.
Mathlib therefore provides `EffectiveEpi proj.left`.

Write `mk ξ h a = lift h a ≫ proj ξ` for the class of `(h, a)`. The kernel-pair square gives
`mk_eq_mk_iff`: `mk ξ h₁ a₁ = mk ξ h₂ a₂` exactly when `h₁ = h₂ * ξ(a₂, a₁)`. The forward
direction lifts the pair to a relation point. The reverse direction uses
`lift a₁ (lift h₂ a₂)`.

### Descent of morphisms and the action

`exists_desc` descends a morphism of objects over `S` along any morphism whose underlying
scheme map is an effective epimorphism. The morphism must take equal values on test points
with equal images. `hom_ext_of_effectiveEpi` is the matching uniqueness statement.
`effectiveEpi_tensorHom` shows that the tensor product of two such fpqc morphisms is again an
effective epimorphism, using Mathlib's `MorphismProperty.pullbackMap`. Hence the morphisms
`𝟙 W ⊗ₘ proj ξ` and `proj ξ ⊗ₘ proj ξ` are effective epimorphisms. The extensionality lemmas
`hom_ext_mk`, `hom_ext_tensor_mk` and `hom_ext_mk_mk` reduce identities of morphisms out of
`torsor ξ`, `W ⊗ torsor ξ` and `torsor ξ ⊗ torsor ξ` to their values on classes `mk ξ g a`.

Left multiplication `actCover : (g, (h, a)) ↦ (g * h, a)` respects the relation, by
`mk_eq_mk_iff` and associativity. It descends along `𝟙 G.X ⊗ₘ proj ξ` to
`smul : G.X ⊗ torsor ξ ⟶ torsor ξ` with `g • mk ξ h a = mk ξ (g * h) a`. The identity and
multiplication laws hold on classes, hence for the universal points. The published
`schemeActionOfPointLaws` then gives the instance `modObj`.

### Simple transitivity

The map `((h₁, a₁), (h₂, a₂)) ↦ h₂ * ξ(a₂, a₁) * h₁⁻¹` respects the relation in both
variables, by the cocycle identity. It descends along `proj ξ ⊗ₘ proj ξ` to
`diff : torsor ξ ⊗ torsor ξ ⟶ G.X`. On classes, `diff(x, y) • x = y` and
`diff(x, m • x) = m` (`diff_smul_universal`, `smul_diff_universal`). For arbitrary test
points `x` and `y`, the point `lift x y ≫ diff ξ` carries `x` to `y`. Any `m` with
`m • x = y` equals it. Mathlib's `ModObj.isIso_leftSMul_iff` turns this into invertibility of
the shear (`isIso_leftSMul`).

### The point and the conclusion

The point is `point ξ = mk ξ 1 (𝟙 U)`. Then
`ξ.toFun a b • (b ≫ point ξ) = mk ξ (ξ(a, b)) b = mk ξ 1 a = a ≫ point ξ` by
`mk_eq_mk_iff` (`toFun_smul_point`). Also `fst G.X U • (snd G.X U ≫ point ξ) = proj ξ`.
So the quotient's pullback square is condition 3 (`isPullback_point`). Surjectivity of
`G.X.hom` follows from its unit section (`surjective_groupScheme_hom`). It descends to
`(torsor ξ).hom` along the fpqc map `U.hom` by Mathlib's descent of surjectivity
(`surjective_hom`). The theorem `cocycleTorsorExistence` assembles these facts.

### Triviality from a section

`Cocycle.isTrivial_of_torsor_section` assumes a torsor `X` (invertible shear), a point
`u : U ⟶ X` satisfying condition 4, and a section `s` of `X.hom`. Let `σ` be the section as a
point of `X` over the terminal object. Take `f = torsorDiff hX (toUnit U ≫ σ) u`, so
`f • (toUnit U ≫ σ) = u`. For test points `a` and `b`, condition 4 becomes
`(ξ(a, b) * (b ≫ f)) • σ_Z = (a ≫ f) • σ_Z`. Uniqueness in the torsor gives
`ξ(a, b) * (b ≫ f) = a ≫ f`, which is the coboundary equation for `f`.

## Provenance and scope

The mathematics is classical: Čech cocycles for an fpqc cover are descent data for the
trivial torsor, and affine morphisms satisfy effective fpqc descent. The implemented route
is internal. It works with rings through the published groupoid form of effective descent
for modules along faithfully flat ring maps: The Stacks Project, Descent, Proposition 35.3.9
(Tag 023N), source `stacks-descent-modules-2026-11-01`, directory SHA-256
`216c92cc547dc34f00f0eaa7354703aced00a51f02c908d58a3758395f4dfe4f`.

The intended consumer is the Bruhat–Tits route to the Library statement
`LocalSimplyConnectedUnramifiedCocycleVanishingStatement`. Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach* (2023), Lemma 8.1.4, printed p.285 / PDF p.316, source
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. Its proof uses
unramified Galois descent: the cohomology set classifies torsors. It then lifts
residue-field points of torsors to integral points with Lemma 8.1.3. This module supplies the classification step for the Library's
scheme-valued cocycles, on arbitrary affine fpqc covers. The derived consequence for complete
rings with finite residue field is a separate unit.

This module proves no cohomology vanishing, no statement about Galois cocycles, and nothing
about `LocalSimplyConnectedCocycleVanishingStatement` itself.
