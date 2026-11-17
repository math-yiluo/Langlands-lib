# Global reflection representatives for split reductive groups over rings

Worker 5397.

Module `Langlands.GroupScheme.Reductive.AffineSplitReflectionRepresentatives`, namespace
`Langlands.GroupScheme.AffineSplitReflection`.

This module proves clause 1 of
[`Reductive.AffineSplitNormalizerWeylStatement`](AffineSplitNormalizerWeylStatement.md)
(Conrad, *Reductive group schemes*, Example 6.4.3). Over an arbitrary commutative ring `R`,
for a split reductive group `G` over `Spec R` with closed fibrewise maximal split torus
`i : 𝔾_m^I ⟶ G`, fibrewise root datum `P` and free root spaces, every element of the Weyl
group `P.weylGroup` is induced by a point of `G(R)`. The result is the theorem
`weylGroup_induced`. It does not use connectedness of `Spec R`.

The module defines one predicate, `Induces`, and proves the theorems listed below. It adds
no axioms. `weylGroup_induced` uses only `propext`, `Classical.choice` and `Quot.sound`.

## The definition `Induces`

`Induces i P n w`, for a point `n : Over.mk (𝟙 (Spec R)) ⟶ G.X` and
`w : RootPairing.Aut P`, holds when there is an automorphism `σ` of the commutative group
scheme `splitTorus.commGroupScheme (Spec R) I` such that

- `IsNormalizingPoint i n σ`: conjugation by `n` carries the torus into itself and restricts
  on it to `σ`;
- for every test scheme `U`, point `x : U ⟶ 𝔾_m^I` and exponent `m : I → ℤ`,
  `∏ j, (pointsEquiv I U (x ≫ σ_*))_j ^ m j = ∏ j, (pointsEquiv I U x)_j ^ (w • m) j`.
  So the character `χ_m ∘ σ` is `χ_{w • m}`.

Provenance: this is the body of the local `let Induces` of
`AffineSplitNormalizerWeylStatement`, spelled the same way and given a name, so that the
composition lemmas below can be stated. That statement's Markdown explains how it encodes
the map `N_G(T)(S) → W(Φ)` of Conrad's Example 6.4.3. The theorem `weylGroup_induced` does
not mention `Induces`: its conclusion spells the body out literally, in the same form as
clause 1 of the statement.

## Theorems

### Descent from localizations (section `Descent`)

- `over_hom_ext_of_localization`: two morphisms `f g : Z ⟶ Y` over `Spec R` between affine
  schemes are equal if `k ≫ f = k ≫ g` for every prime `p` of `R`, every scheme `W` over
  `Spec R_p` and every `k : W ⟶ Z` over `Spec R`. Proof: by
  `HomScheme.TorusChart.hom_ext_of_localization`, it suffices to compare `f` and `g` after
  composing with `Spec (Γ(Z)_P) ⟶ Z` for each prime `P` of `Γ(Z)`. This morphism lies over
  `Spec R_p`, where `p` is the contraction of `P` to `R`, through the local homomorphism
  `R_p → Γ(Z)_P`.
- `isWeylPoint_of_localizations`: if `G` is affine over `Spec R` and the identity
  `n t n⁻¹ = f(t)` defining `IsWeylPoint i n f` holds for torus points `t` defined on
  schemes over some `Spec R_p`, then `IsWeylPoint i n f` holds. Proof: both sides are
  pulled back from the universal point `𝟙 : 𝔾_m^I ⟶ 𝔾_m^I`, and `𝔾_m^I` is affine, so
  `over_hom_ext_of_localization` applies.
- `weylIdentity_of_baseChange`: let `A` be an `R`-algebra and `u v : 𝔾_a ⟶ G` root maps.
  If the base changes of `u` and `v` to `A` give a Weyl point for the base-changed torus,
  then the identity for `weylPoint u v` holds at every torus point over a scheme over
  `Spec A`. Proof: transport through `GroupScheme.baseChangePointsEquiv`, using
  `splitTorus.exponentIso_baseChange` for the torus automorphism.

### Dual numbers (sections `DualTransport` and `LocalScalar`)

Here `dualOver R` is `Spec R[ε]` over `Spec R`, `epsSec R` is the section `ε`, and
`rootPoint u Z c` is the point `u(c)` of `G` over `Z`.

- `dualFactorization_baseChange`: let `x_-` and `x_+` be root maps. A factorization
  `x_+(1) x_-(ε) = x_-(y) · t · x_+(x)` over `R[ε]`, with `t` a torus point, gives one over
  `A[ε]` for the base-changed root maps. The coordinates `y` and `x` are mapped along
  `R[ε] → A[ε]`.
- `snd_dual_of_gauss`: suppose `d` is a unit of `A` such that `x_+` and `d·x_-` satisfy the
  coroot Gauss relation `HasCorootGaussRelation` and the positive separation
  `SeparatesPositive`. Then any factorization as above has `ε`-coefficient of `x` equal to
  `-d⁻¹`. Proof: the Gauss relation for `u = 1 + d⁻¹ε` gives a second factorization of
  `x_+(1) x_-(ε)` with positive coordinate `u⁻¹ = 1 - d⁻¹ε`. Separation identifies the two
  positive coordinates.
- `exists_weylUnit_of_dualFactorization`: over a local ring, with the hypotheses of the
  statement and root parametrizations `x_+` of `P.root a` and `x_-` of `-P.root a`, a dual
  factorization gives a unit `d` such that `weylPoint x_+ (d·x_-)` is a Weyl point for
  `P.reflection a` and the `ε`-coefficient of `x` is `-d⁻¹`. Proof: the Library theorem
  `LocalSplitCell.exists_unit_oppositeNormalization` gives `d` with the Gauss relation,
  separation and the Weyl identity; then apply `snd_dual_of_gauss`.

### The global unit (section `Global`)

- `exists_isWeylPoint_of_dualFactorization`: over an arbitrary ring `R`, a dual
  factorization `x_+(1) x_-(ε) = x_-(y) · t · x_+(x)` gives a unit `c` of `R` such that
  `weylPoint x_+ (c·x_-)` is a Weyl point for `P.reflection a`. Proof: let
  `s = RingRootCell.DualCell.normalizationScalar x`, the negative of the `ε`-coefficient of
  `x`. At each prime `p`, the hypotheses pass to the base change to `R_p`:
  `IsReductive.baseChange`, `IsClosedSubgroup.baseChange`,
  `splitTorus.isFibrewiseMaximalTorus_baseChangeHom`,
  `IsFibrewiseRootDatumOf.baseChange_implicit` and
  `isRootParametrization_baseChangeRoot`. The factorization passes as well, by
  `dualFactorization_baseChange`. Then `exists_weylUnit_of_dualFactorization` gives a unit
  `d_p` of `R_p` with image of `s` equal to `d_p⁻¹`, and with the Weyl identity for
  `d_p·x_-`. So `s` is a unit at every maximal ideal, hence a unit of `R`. Set `c = s⁻¹`.
  Its image in `R_p` is `d_p`, so after base change to `R_p` the Weyl identity holds for
  `c·x_-`. By `weylIdentity_of_baseChange` and `isWeylPoint_of_localizations` it holds
  over `R`.

### The global cell (section `GlobalCell`)

- `exists_dualFactorization`: over an arbitrary ring, with the hypotheses of the statement
  and opposite root parametrizations `x_+` of `P.root a` and `x_-` of `-P.root a`, the
  point `x_+(1) x_-(ε)` has a dual factorization. Proof: choose a cocharacter `mu` whose
  kernel meets the roots only in `±P.root a`, by `LocalRootGroup.exists_kernel_exponent`.
  The relative cocharacter centralizer of `mu`, with the lifted root maps
  (`splitTorus.RelativeCocharacterCentralizer.rootLift`), supplies ring rank-one cell data
  (`splitTorus.RelativeCocharacterCentralizer.cellData`, with positive cocharacter
  `P.root a`, which pairs positively with itself because `P.root a ≠ 0`). The Library
  theorem `RingRootCell.CellData.exists_dualFactorization` factors the point inside the
  centralizer. Composing with the inclusion of the centralizer gives the factorization in
  `G` (`rootLift_comp`, `torusHom_comp`).

### Clause 1 (sections `Clause1` and `Final`)

- `prod_pointsEquiv_exponentCommIso`: for a linear automorphism `f` of `ℤ^I`, the torus
  automorphism `splitTorus.exponentCommIso _ I f` pulls back the character `χ_m` to
  `χ_{f m}`. This follows from `splitTorus.exponentHom_comp_exponentCharacter`.
- `induces_one`: the identity point induces `1`, with `σ` the identity.
- `Induces.mul`: if `n` induces `w` and `n'` induces `w'`, then `n' * n` induces `w * w'`,
  with `σ ≪≫ σ'` (`IsNormalizingPoint.mul`, `mul_smul`).
- `forall_weylGroup_induces`: if every reflection `RootPairing.Equiv.reflection P a` is
  induced by a point, then every element of `P.weylGroup` is. Proof: induction over the
  generators (`RootPairing.weylGroup.induction`), using `induces_one` and `Induces.mul`.
- `exists_induces_reflection`: every reflection `RootPairing.Equiv.reflection P a` is
  induced by a point. Proof: let `x_b` be the global root parametrizations
  `LocalRootGroup.rootParametrizationsOfFreeWeights` from the free root spaces. Take
  `x_+ = x_a` and `x_- = x_{s_a(a)}`; `P.root (P.reflectionPerm a a) = -P.root a` by
  `root_reflectionPerm` and `reflection_apply_self`. Apply `exists_dualFactorization`, then
  `exists_isWeylPoint_of_dualFactorization`, to get a unit `c`. The point is
  `n = weylPoint x_+ (c·x_-)` and `σ = splitTorus.exponentCommIso _ I (P.reflection a)`.
  `IsWeylPoint.isNormalizingPoint` gives the normalizing condition, and the character
  identity is `prod_pointsEquiv_exponentCommIso`, since `Equiv.reflection P a` acts on
  weights by `P.reflection a`.
- `weylGroup_induced`: clause 1. The binders are those of the statement in the same order,
  without the instance `ConnectedSpace (Spec R)`, which the proof does not use. The
  instance `IsAffineHom G.X.hom` is again `hG.isAffineHom` by `haveI`. The conclusion is
  `∀ w ∈ P.weylGroup, ∃ n, ∃ σ, IsNormalizingPoint i n σ ∧ ∀ U x m, …`, which is the
  statement's `Induces n w` with the `let` unfolded. It is `forall_weylGroup_induces`
  applied to `exists_induces_reflection`.

## Relation to the source

Conrad (Example 6.4.3, pp.230–231) says that surjectivity onto `W(Φ)` "holds on the right
because W(Φ) is generated by reflections s_a (a ∈ Φ) that are induced by elements
w_a(X_a) ∈ N_G(T)(S) for any O_S-basis X_a of 𝔤_a". The Lean proof follows this
outline: reduce to generators, then exhibit a representative of each reflection built
from the root groups of `a` and `-a`. It uses `x_{-a}(-c) x_a(1) x_{-a}(-c)` with a unit
`c` of `R` instead of Conrad's normalized `w_a(X_a)`. The unit `c` is found locally on
`Spec R` with Library results for local rings and glued through the dual-number
computation above, rather than by Conrad's construction of `X_{-a}` from `X_a`. Source:
Brian Conrad, *Reductive group schemes*, Panoramas et Synthèses 42–43, SMF, 2014,
registered as `conrad-2014-reductive-group-schemes`.
