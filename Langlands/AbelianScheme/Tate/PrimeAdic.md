# Prime-adic Tate modules from actual torsion groups

This module constructs the integral and rational prime-adic Tate modules of a commutative group scheme `G : Grp (Over S)` on a test scheme `T : Over S`. The prime `p : ℕ` has the hypothesis `Fact p.Prime`. The input levels are the actual torsion groups `Langlands.GroupScheme.Tate.Level G T (p ^ n)` from `Tate.Integral`, rather than a supplied family of abstract modules.

The main declarations are in `Langlands.GroupScheme.Tate.PrimeAdic`. The finite-level scalar helpers preceding that namespace are in `Langlands.GroupScheme.Tate`.

## Source and provenance

The original source is B. Edixhoven, G. van der Geer and B. Moonen, *Abelian Varieties*, preliminary draft built 2012-02-08, Chapter X (10.1)–(10.3), printed pp.141–142, and (10.5), printed p.143 (PDF pp.145–147). Registered source: `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`. These pages were read directly and the file hash was verified. No source-specific errata file was present in the available Library.

The source defines the prime-power inverse limit with multiplication-by-prime transitions, describes the integral scalar action coordinatewise through the residue classes, defines rational scalar extension, and constructs the map induced by a homomorphism. Its ordinary Tate-ℓ discussion uses a prime different from the field characteristic and separable-closure points. It separately discusses the geometric characteristic-p torsion-point limit. Here `p` denotes any prime, without a condition on the characteristic; the construction alone works in this generality. The source's finite étaleness, rank, Galois-action and isogeny results are not asserted here.

The extension to arbitrary commutative group schemes, arbitrary test schemes, and field-valued points is an internal generalization using the published actual kernel construction. The universal linear lift, topology, and explicit functoriality laws are derived constructions. The source writes the rational tensor factors as `T_ℓ X ⊗_{Z_ℓ} Q_ℓ`; this module uses `Q_p ⊗_{Z_p} T_p`, the canonically equivalent ordering over the commutative scalar ring, to obtain the standard left `Q_p`-module instance. No specific comparison equivalence with the source's ordering is exported. The coordinatewise functoriality proofs adapt the published `Tate.Integral` implementation by Worker 143.

## Residue and prime-adic scalars

`level_nsmul_eq_zero G T n x` proves `n • x = 0`. It uses the injective map to sections and the defining equation `x ^ n = 1` for the actual torsion subgroup. `levelZModModule` then equips every `Level G T n` with its canonical `ZMod n`-module structure. This helper allows any natural `n`, including zero; for zero it is the ordinary integer action.

For `h : n ∣ m`, `transition_zmod_smul` proves that the actual transition is semilinear with respect to `ZMod.castHom h (ZMod n)`. The proof represents a residue class by an integer, then uses compatibility of an additive homomorphism with integer multiplication.

`PrimeAdic.levelModule n` restricts scalars along the actual ring homomorphism `PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)`. `transition_smul` proves compatibility with this action for every `n ≤ m`, using the compatibility of the p-adic residue maps with reduction. `toSection_transition_succ` identifies a successive transition with multiplication by `p` on underlying sections, since `p ^ (n + 1) / p ^ n = p`.

## Integral module and universal property

`coherent G T p` is the submodule of the product of the prime-power levels consisting of families satisfying

```text
transition G T (pow_dvd_pow p (Nat.le_succ n)) (x (n + 1)) = x n
```

for every natural `n`. These are precisely the compatible sequences for the successive transition system. Closure under addition follows from additivity of transitions; closure under p-adic scalar multiplication follows from `transition_smul`.

`Integral G T p` is this submodule as a type, with its coordinatewise abelian-group and `ℤ_[p]`-module structures. Its topology is the subtype topology from the product of discrete actual torsion levels. The inherited `IsTopologicalAddGroup` instance makes addition and negation continuous. This unit makes no compactness assertion or assertion about continuity of scalar multiplication as a two-variable map.

`evaluation G T p n` is the `ℤ_[p]`-linear coordinate projection. `evaluation_smul` states its scalar formula explicitly through `PadicInt.toZModPow`. `evaluation_transition` gives successive compatibility, and `continuous_evaluation` gives continuity.

`lift` constructs a linear map into the limit from any family of linear maps into the levels satisfying successive compatibility. `evaluation_lift` gives the coordinate formula; `lift_unique` proves uniqueness by extensionality of linear maps, subtypes and functions. `continuous_lift` shows that this map is continuous if all coordinate maps are continuous. No topology or continuity on the scalar action of the source is required for this last assertion.

`Rational G T p` is the actual tensor product `ℚ_[p] ⊗[ℤ_[p]] Integral G T p`, with its abelian-group and `ℚ_[p]`-vector-space structures. There is no finite-dimensionality or topology assertion for this rational module.

## Actual homomorphisms and field-valued fibres

For an actual group-scheme homomorphism `f : G ⟶ H`, `levelMapLinear T p f n` equips the published map on torsion points with p-adic linearity. As above, integer representatives of residue classes reduce its scalar compatibility to additivity.

`map T p f` is the resulting linear map on integral Tate modules, constructed by the universal lift. `evaluation_map` says that each coordinate is the actual section composed with `f`. `map_id` and `map_comp` prove the identity and composition laws using the category laws on sections. `map_mul` proves additivity in the homomorphism: Mathlib writes pointwise addition of group-scheme homomorphisms as multiplication `f * g`, so its induced map is the sum of the two linear maps. The proof uses compatibility of precomposition with the group-object operation. `continuous_map` follows coordinatewise from the discreteness of each torsion level.

`rationalMap T p f` is scalar extension of `map T p f` by `LinearMap.baseChange ℚ_[p]`. `rationalMap_tmul` gives its formula on pure tensors. `rationalMap_id`, `rationalMap_comp` and `rationalMap_mul` follow from the integral laws and the corresponding scalar-extension laws.

`IntegralAt G p s` and `RationalAt G p s` specialize to a field-valued point `s : Spec Ω ⟶ S` by taking `T = Over.mk s`. The imported `fibreLevelEquiv G s (p ^ n)` identifies each coordinate level with actual points of the torsion-scheme fibre. Choosing an algebraically closed Ω gives geometric points; choosing a separable closure with `p` invertible gives the source's usual field convention. No equivalence between different point fields is asserted.

The bundled abelian-scheme specialization is a separate integration obligation. This unit also does not construct finite étale monodromy, Weil pairings, twists, full/away adelic scalars, or level structures, and does not complete those parts of the host task.
