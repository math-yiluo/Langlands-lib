# Proof: reduction of the representability of the Picard pieces

Authors: Worker 22.

Worker 22 wrote this module and its six helper modules for task
`07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705), by agreement with that
task's first executor, Worker 5705. It proves the published proposition
`Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityReductionStatement`
(module of the same name, by Worker 22). Task 6214
(`2735612e-5097-47df-aa71-a876859f4e5d`) asks for the proof of
`PicardHilbertPiecesRepresentabilityStatement`. Its context records that
Worker 22 proves it under Task 5705 through this reduction.

The main theorem is

```lean
theorem Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction.picardHilbertPiecesRepresentabilityReduction :
    PicardHilbertPiecesRepresentabilityReductionStatement.{u}
```

Its type is the target proposition exactly, for an arbitrary universe `u`. The
proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## What is proved

The statement is an implication. Assume

- (a) `RelativeEffectiveDivisorHilbertPiecesStatement`: the divisor scheme
  `d : D ⟶ Spec A` with universal divisor `W` and its Hilbert-polynomial
  pieces `U' θ`;
- (b) `ProperFlatIntegralLinearSystemStatement`: the linear system of an
  invertible module on a proper flat family with geometrically integral fibres;
- (c'') `FppfQuotientLocallyNoetherianStatement`: fppf quotients by flat
  proper equivalence relations, tested on locally noetherian schemes;
- (bc) `RelativeEffectiveDivisorBaseChangeStatement`: base change of relative
  effective divisors with their ideal modules.

Then `PicardHilbertPiecesRepresentabilityStatement` ("(C)") holds. Let
`f : X ⟶ S = Spec A` be proper, flat and geometrically integral with a
section, over a noetherian ring `A`. Let `𝓛X` be invertible, with sections that
give a closed immersion. Let opens `U T s L c m` satisfy the four hypotheses
of (C):

- `hU1`: invariance under twists by invertible modules from the base;
- `hU2`: base change;
- `hU3`: on a whole piece, `H¹` of `L(m)` vanishes and `H⁰` does not on every
  fibre;
- `hU4`: over noetherian affine bases, the divisors in the linear system of
  `L(m)` have Hilbert polynomial `θ c m`.

Then for every `c` and `m` there are an H-quasi-projective `Q` over `S` and
`β : Q → Pic` with two properties on locally noetherian tests `T`. First,
`β` is injective. Second, the class of a line bundle `L` lies in the image of
`β` exactly when `U T L c m = ⊤`.

The proof follows the intended proof in the Markdown of the statement, which
extracts it from Kleiman's proof of Theorem 4.8 (S. L. Kleiman, *The Picard
scheme*, arXiv math/0504020v1, pp.29–31). The fppf topology replaces the
étale one.

## Notation of the helper modules

All helpers are in the namespace
`Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction`. They work
with Picard-group classes (`Group Y`), not with isomorphisms of modules.

- `icl M hM`: the Picard class of an invertible module `M`.
  `dcl I hI`: the class of the divisor line bundle `O(I)` of an effective
  Cartier ideal (module `...ReductionClasses`, `...ReductionDivisors`).
- `twist L P m = L ⊗ P ⊗ ⋯ ⊗ P`, written with `Nat.rec` as in the statements.
- `mapX f h w : X ×_S T' ⟶ X ×_S T` for `h : T' ⟶ T` over `S`.
- `cP s`: the class of `𝓛X` pulled back to `X ×_S T`.
  `cLW = dcl W - m • cP d` on `X ×_S D`, and `L_W` an invertible module with
  this class (`Group.lineBundleRepresentative`).
- `pt y w = (mapX y)^* cLW`: the class of a point `y : T ⟶ D`.
  `ab T y w`: the same class moved to `T ×_S X` by `relativeSpaceSymmetry`.
- `Zo d Z₀`: an open `Z₀ ⊆ D`, as an object of `Over S`.
  `abelMap … Z₀ : Z₀ → Pic` is the Abel map. It sends `x` to the fppf class of
  `ab T (x ≫ ι) _` (module `...ReductionAbel`).

## The four steps of the main theorem

Fix `c` and `m`. Apply (a) to `f` and `𝓛X`. This gives `D`, `d`, `W`, the
universal property `hcl` (restated as `Classifies`) and the pieces `U'`.
Since `d` is locally of finite presentation over a noetherian ring, `D` is
locally noetherian (`LocallyOfFiniteType.isLocallyNoetherian`). Put
`Z₀ := U D d L_W c m`.

**Step 1: `Z₀ ⊆ U' (θ c m)`.** Let `z ∈ Z₀`. Choose an affine open `V` with
`z ∈ V ⊆ Z₀`; `Γ(D, V)` is noetherian. Let `g : Spec Γ(D, V) ⟶ D` be the
inclusion (`IsAffineOpen.fromSpec`). Then `g⁻¹ Z₀ = ⊤`, so by `hU2'` (base
change, module `...ReductionAbel`) the open of `g^* L_W` is everything. The
pulled-back divisor `J = g^* W` is relative effective Cartier by (a). By (bc)
its class is `dcl J = pt g + m • cP` (`dcl_comap_mapX`). This is also the
class of `(g^* L_W)(m)` (`icl_twist_pt`). So `O(J) ≅ (g^* L_W)(m) ⊗ pr^* N` with
`N` trivial (`nonempty_iso_tensor_of_icl`). Now `hU4` gives the Hilbert
polynomial `θ c m` on the geometric fibres of `J`. The affine-test criterion
of the piece `U' (θ c m)` in (a) then gives `range g ⊆ U' (θ c m)`, and so
`z ∈ U' (θ c m)`.

**Step 2: `Z₀` is H-quasi-projective.** (a) gives an H-quasi-projective
embedding `i` of `U' (θ c m)`. Its composite with the open inclusion
`D.homOfLE` from step 1 is an H-quasi-projective embedding of `Z₀`.

**Step 3: the relation and the quotient.** `exists_relation` (module
`...ReductionRelation`) gives `R` over `S` and `sR, tR : R ⟶ Z₀` with three
properties. First, `sR` is flat and proper. Second, the two composites with
the Abel map agree. Third, `R` represents the pairs of points with equal Abel
class, on locally noetherian tests. Let `G` be the fppf image sheaf of the
Abel map (`imageSheaf`, the sheafification of `Subfunctor.range`), and `ζ` the
corestriction to it (`toImage`, which is `Subfunctor.toRangeSheafify`). Then
`ζ` is locally surjective (a Mathlib instance), and `ζ sR = ζ tR`
(`toImage_comp_eq`). Equality in `G` is equality in `Pic`, since `G` is a
subfunctor. So (c'') applies to `ζ`, `sR` and `tR`. It gives an
H-quasi-projective `Q`, a flat, surjective, locally finitely presented
`π : Z₀ ⟶ Q`, and `e : Q → G` with `π e = ζ`, bijective on locally noetherian
tests.

**Step 4: the quotient represents the piece.** Put `β := e ≫ ι`, where `ι`
is the inclusion `G ⊆ Pic`. On a locally noetherian `T`, `β` is injective
because `e` is bijective and `ι` is injective. Let `L` be a line bundle on
`T ×_S X`.

- *If the class of `L` is `β q`*: let `T₁ = T ×_Q Z₀` with projections
  `k₁ : T₁ ⟶ T` and `z : T₁ ⟶ Z₀`. `T₁` is locally noetherian, because `k₁`
  is a base change of the locally finitely presented `π`. Naturality of `e`
  and `π e = ζ` show that the class of `L` pulled back along `k₁` is the
  Abel class of `z`. Then `class_open` gives
  `k₁⁻¹ U(T, L) = z⁻¹ ι⁻¹ Z₀ = ⊤`. The map `k₁` is surjective, because it is
  a base change of the surjective `π`. So `U(T, L) = ⊤`
  (`eq_top_of_preimage_eq_top`).
- *If `U(T, L) = ⊤`*: apply (b) over `T` to `(σ_T^* L)(m)`, where
  `σ_T^* L = tr f T L` is the transport of `L` to `X ×_S T`. By `hU3` and
  `flat_of_top`, the linear system `l : Λ ⟶ T` is flat, locally of finite
  presentation and surjective. `linsys_class` classifies its universal divisor
  by a point `y : Λ ⟶ D` with `pt y = l^*[σ_T^* L] + pr^*[N_Λ]`. So, by
  S-cls (`scl_sym_eq_iff`), the class of `L` pulled back to `Λ` equals the
  Abel class of `y`. `class_open` then gives `y⁻¹ Z₀ = l⁻¹ U(T, L) = ⊤`, so
  `y` factors through `Z₀` (`IsOpenImmersion.lift`). Hence the pulled-back
  class lies in the range of the Abel map at `Λ`. The single arrow `l` is an
  fppf covering (`mem_fppf_over`), so the class of `L` lies in the sheafified
  image `G`. The surjectivity of `e` at `T` gives a preimage in `Q`.

## Image sheaf lemmas (this module)

- `imageSheaf f ζ0`: the fppf sheaf `(Subfunctor.range ζ0).sheafify` of
  `FppfSheaf S`. It is a sheaf by `Subfunctor.sheafify_isSheaf` and
  `RelativePicard.classSheafPresheaf_isSheaf`. It is an `abbrev`, so the
  Mathlib instance `Presheaf.IsLocallySurjective` for
  `Subfunctor.toRangeSheafify` applies to `toImage`.
- `toImage_ι`, `toImage_app_val`: the corestriction followed by the inclusion
  is `ζ0`.
- `toImage_comp_eq`: two maps into `Z` with equal composites with `ζ0` have
  equal composites with `toImage`. This uses that the inclusion is a mono.

## Helper modules

The import chain is
`...ReductionClasses → ...ReductionDivisors → ...ReductionPoints →
...ReductionSetup → ...ReductionAbel → ...ReductionRelation →
...ReductionProof`, all under `Langlands/AlgebraicGeometry/Picard/` with the
prefix `PicardHilbertPiecesRepresentability`. Each has its own Markdown.

## Library results used

- `Langlands.AlgebraicGeometry.Picard.properFlatIntegralSheafClassTwist`
  (S-cls, the proved `ProperFlatIntegralSheafClassTwistStatement`). It gives
  `Pic(T) = Pic(X_T)/Pic(T)` and is used through `scl_sym_eq_iff`.
- `StructureKernelFlatBaseChange.kernelModuleFlatBaseChangeIso`: the ideal
  module of a closed subscheme commutes with flat base change.
- The Picard-group API (`Group.pullback`, `Group.lineBundleRepresentative`,
  `LineBundle.classOf_eq_iff`, `LineBundle.classOf_tensor`) and
  `RelativePicard.toClassSheaf`, `sheafClassOf`, `map_sheafClassOf`.
- Mathlib: `Subfunctor.sheafify`, `Subfunctor.toRangeSheafify`,
  `Scheme.fppfTopology`, `GrothendieckTopology.mem_over_iff`,
  `Precoverage.generate_mem_toGrothendieck`, `IsOpenImmersion.lift`,
  `IsAffineOpen.fromSpec`, `Scheme.isBasis_affineOpens`.

## Differences from the statement's intended proof

- Step 3 applies (b) over `Z₀` to `(L_W|_{Z₀})(m)` rather than to
  `O(W)|_{Z₀}`. The two have the same class, `dcl W` restricted to `Z₀`.
- `β` is `e` followed by the inclusion, so injectivity on locally noetherian
  tests is immediate from the bijectivity of `e`.
