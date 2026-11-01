# Actual CM class fibers under coarse-level rigidity

This internal construction by Worker 57 proves the stabilizer criterion on the existing Harris CM rational-isogeny classes and constructs a bijection from the original residual group to each specified coarse fiber. Its explicit arithmetic hypothesis is `CoarseLevelHasNoAutomorphisms`, formulated on actual polarized objects and their compatible coarse-level orbits. The fiber bijection is derived from that hypothesis, the fixed-object stabilizer computation and the proved class transitivity.

## Objects, levels and hypotheses

The fields, central simple unitary datum `D` and Harris signature charts `C` are those of `HarrisTaylorCMClassTransitivity`. Lean `E` is totally real, `F/E` is CM quadratic and `L` is the specified imaginary quadratic CM field. The determinant condition uses the existing normalized, conjugated map `D.harrisTaylorReflexStructure C p` for `p : S → Spec F`.

The base is a quasi-separated `Scheme.{0}` with an actual field-valued point `s : Spec Ω → S`. Finite fibers on finite étale covers, invertibility of every positive full-tower torsion order, and finite étaleness of the corresponding roots of unity remain explicit. No connectedness, local Noetherianity or algebraic-closedness assumption is imposed in this fixed-base construction.

The inherited inputs are pullback-tensor comparison preservation, composition, unit coherence, associativity, left-unitor comparison and symmetry; Picard-zero pullback, Mumford-square and universal base change; relative finite Weil transition; the rational profinite-integer/finite-adele comparison; torsion finite étaleness; and `PositivePairAdditivity` at this base. The positive auxiliary involution, polarization, dual and Poincaré constructions and pairing-compatible adelic frames remain the existing actual ones.

Write `G = D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ` for the original opposite Harris group. The compact-open levels `V ≤ U` retain both `hVU` and relative normality `(V.subgroup.subgroupOf U.subgroup).Normal`. Write `C_V` for the implementation's `Classes V`, namely the existing normalized `HarrisNumericalWeilLevel.IsoClass`. Its ambient relation uses actual equivariant rational isogenies with actual rational inverses and rational-unit polarization multipliers. Its numerical subtype requires a single representative satisfying both the determinant condition `Good` and the numerical condition `Num`. The latter includes geometric relative dimension and the central Lie trace formula. No invariance of dimension under arbitrary rational isogenies is asserted.

Let `π : C_V → C_U` be the original inclusion class map. For `g ∈ U`, let `T_g` be the original class map at `normalInverseArrow U V hVU g`. This arrow has transporter `g⁻¹`. The original right frame composition therefore gives the left-action order `T_(gk) x = T_g (T_k x)`, proved in `classMap_normalTranslate_mul` from the transporter and functor composition laws.

## The actual rigidity condition

`CoarseLevelHasNoAutomorphisms U` is a proposition. For every actual positive polarized action `X` satisfying both `Good X` and `Num X`, every monodromy-invariant compatible `U`-orbit `a`, every `q : ℚˣ` and actual action-object isomorphism `e : X.actionObj ≅ X.actionObj`, it considers an actual proof of `PolarizedWeilLevel.Multiple X X q e`. If the existing equivalence `levelIso` for these data fixes `a`, the condition requires `e = Iso.refl _`.

Thus the condition concerns the self-isogeny preserving a specified coarse level. It neither requires nor concludes `q = 1`. It assumes no class-level stabilizer conclusion or fiber bijection. Proving this condition from the published Harris `LevelSufficientlySmall` predicate is a separate, still open arithmetic obligation.

## Stabilizers through the rational-isogeny quotient

`representativeOrbit_forget_normalTranslate` proves that a normal translation by `g ∈ U` disappears on forgetting a fine compatible orbit to `U`. The proof uses functor composition, `levelTower_map_eq_of_target_coset`, the actual Hodge scalar-extension equivalence and the original membership `g ∈ U`. It needs no rigidity or freeness premise. Passing to representatives with their same two condition witnesses gives `classMap_forget_normalTranslate`, the equality `π(T_g x) = π(x)` for every actual fine class.

Under the rigidity hypothesis, `classOf_normalTranslate_eq_self_iff` proves

\[
  [X,T_g a]=[X,a] \quad\Longleftrightarrow\quad g\in V.
\]

For the forward implication, the existing exact `classOf_eq_iff` supplies a rational unit `q`, an actual equivariant rational self-isogeny `e` of this same `X`, its polarization compatibility and its fine-level orbit equation. Naturality of `levelIso` under the inclusion, together with the preceding coarse-orbit equality, makes `e` fix the coarse orbit of `a`. Rigidity forces `e` to be the identity. The accompanying `PolarizedWeilLevelStabilizers` helper then shows that its level transport is the identity for this arbitrary valid multiplier. The already proved fixed-object stabilizer criterion recovers `g ∈ V` in the original group. Conversely, membership in `V` gives equality of the fine orbits by that criterion and hence equality of their classes.

`classMap_normalTranslate_eq_self_iff` extends the result to every `x : C_V` using `classOf_surjective`, retaining determinant and numerical proofs on the same chosen representative. Applying it to `g k⁻¹` at `T_k x`, and using the proved action order, gives `classMap_normalTranslate_eq_iff`:

\[
  T_g x=T_k x \quad\Longleftrightarrow\quad gk^{-1}\in V.
\]

## Residual embedding and exact coarse fiber

For each specified `x : C_V` and rigidity proof, `classResidualEmbedding` is the embedding

\[
  U/(V\cap U)\ \hookrightarrow\ C_V,\qquad [g]\longmapsto T_g x.
\]

Here the Lean quotient is exactly `U.subgroup ⧸ V.subgroup.subgroupOf U.subgroup`, conventionally `U/V` since `V ≤ U`. The equality criterion proves both quotient descent and injectivity using `QuotientGroup.eq_iff_div_mem`. The forward function is defined by `Quotient.lift`; it does not select quotient representatives. `classResidualEmbedding_mk` is its defining computation on every original subgroup element. `classResidualEmbedding_forget` shows that every value has coarse image `π(x)`.

`classResidualFiberEquiv` constructs the equivalence

\[
  U/V\ \simeq\ \{y\in C_V\mid \pi(y)=\pi(x)\}.
\]

Its forward map is the residual embedding paired with the preceding fiber equality. Injectivity is inherited from that embedding. For surjectivity, the published `classMap_exists_normalTranslate` gives, from the equality of coarse images, an original `g ∈ U` with `T_g x = y`. Its quotient class supplies the preimage. `Equiv.ofBijective` constructs the inverse from the proved bijectivity; no inverse or translation witness is assumed. `classResidualFiberEquiv_mk` records the original inverse-right class-map formula for its forward value. The construction requires a supplied fine class and makes no nonemptiness assertion for an arbitrary coarse fiber.

## Original sources and precise remaining scope

Harris and Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99, is registered as `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`. It defines sufficiently small full-adelic levels, the invariant pairing-compatible frame-orbit moduli problem, rational-isogeny equivalence and right frame composition, and asserts the normal `U/V` Galois cover. The present fixed-base stabilizer calculation and fiber equivalence are internal deductions from the implemented class relation and group actions. Their explicit coarse-rigidity hypothesis has not been deduced from the source smallness condition.

Kottwitz, *Points on some Shimura varieties over finite fields*, JAMS 5 (1992), §6, printed p.392, one-based PDF p.20, is registered as `kottwitz-1992-points-shimura-finite-fields`, SHA-256 `c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`. Before asserting the étale and normal-level Galois coverings, that passage restricts to prime-to-p levels for which the moduli objects have no nontrivial automorphisms. It motivates isolating actual object rigidity here. Its different level and isogeny conventions do not supply a proof of the full-adelic Harris smallness implication.

The retained originals at these pages were read. All five pages of the supplied author document `Harris--Publication with errata--undated/Harris--Publication with errata.pdf` were also checked; no entry corrects this Harris–Taylor passage. This is a bounded observation about the supplied list. No source-specific errata note was found in the available project/current Library note filenames.

This construction supplies conditional class stabilizers and an exact set fiber equivalence. It does not prove coarse rigidity, finite order of rational self-isogenies, applicability of moduli existence, equivalence with the full source moduli functor, étaleness of the original scheme projection, invertibility of the exact residual kernel comparison, canonical-model comparison, uniformization or coefficient descent. Those remain separate obligations of the geometric program.
