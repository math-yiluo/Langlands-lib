# Primitive line-bundle lifting from obstruction naturality and H² injectivity

Authors: Worker 5704 wrote this module. The tensor-transport lemma
`nonempty_tensor_iso_of_comp_eq` adapts an idea from the Task 5640 draft (Worker 5640,
building on Worker 225).

Module `Langlands.AlgebraicGeometry.Picard.ArtinianPrimitiveLineBundleLiftingFromPrerequisites`,
namespace `Langlands.AbelianScheme`.

## Role and provenance

This is internal infrastructure for task `60cd926c-5964-46c0-ad0e-111a8faf6631`, which
proves the published `Langlands.AbelianScheme.ArtinianPrimitiveLineBundleLiftingStatement`.
The source correspondence of that target was reviewed with the target statement. The
target is claim 2 of the proof of Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*,
3rd edition, Proposition 6.7, printed pp.117–118 (PDF pp.130–131), registered as
literature ID
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`.

This module proves the target from two published statements whose proofs are not yet in
the Library. The anchor proposition `ArtinianPrimitiveLineBundleLiftingReductionStatement`
is internal: it is exactly this implication, and it is proved in the same module. It follows
the source's argument: the obstruction of `L₀` maps to the obstruction of `q(L₀)` under an
injective map, and the second obstruction is zero. Once the two prerequisite proofs are
published, the task's final proof applies `artinianPrimitiveLineBundleLiftingReduction` to
them.

## The anchor statement

```lean
def ArtinianPrimitiveLineBundleLiftingReductionStatement : Prop :=
  Langlands.AlgebraicGeometry.Picard.SquareZeroObstructionMorphismNaturalityStatement.{u} →
    ArtinianH2PrimitiveInjectivityStatement.{u} →
      ArtinianPrimitiveLineBundleLiftingStatement.{u}
```

The two hypotheses are published Library propositions, used unchanged:

- `Langlands.AlgebraicGeometry.Picard.SquareZeroObstructionMorphismNaturalityStatement`:
  let `f : X' ⟶ X` be a morphism over `Spec R`. Let `i : Y ⟶ X` and `i' : Y' ⟶ X'` be
  closed immersions with square-zero ideals, with `g : Y' ⟶ Y` and `i' ≫ f = g ≫ i`. Let
  `k : I ⟶ f_* I'` be compatible with the inclusions of the ideal modules into the structure
  sheaves. Then the obstruction of `g^* y` is the image of the obstruction of `y`. The image
  is taken under the cohomology pullback `H²(X, I) ⟶ H²(X', f^* I)`, followed by the adjoint
  `f^* I ⟶ I'` of `k`.
- `Langlands.AbelianScheme.ArtinianH2PrimitiveInjectivityStatement`: for an abelian scheme
  `A` over a local Artinian ring `B'` and an elementary thickening `Spec B ⟶ Spec B'`,
  the map `μ^* − p₁^* − p₂^*` is injective. It goes from the ideal `H²` of `A₀ ⊂ A` to the
  ideal `H²` of `A₀ ×_B A₀ ⊂ A ×_{B'} A`, with coefficient maps compatible with the ideal
  inclusions.

The conclusion is the unchanged target `ArtinianPrimitiveLineBundleLiftingStatement`.

## Helper lemmas

Namespace `Langlands.AbelianScheme.ArtinianPrimitiveLineBundleLifting`.

- `nonempty_tensor_iso_of_comp_eq`: take `F : P ⟶ Q`, maps `m p q : Q ⟶ Z` and
  `m' p' q' : P ⟶ Z` with `F ≫ m = m'`, `F ≫ p = p'`, `F ≫ q = q'`, and a module `M` on `Z`.
  An isomorphism `m^*M ≅ p^*M ⊗ q^*M` gives an isomorphism `m'^*M ≅ p'^*M ⊗ q'^*M`. Proof:
  apply `F^*` to the given isomorphism. Then use the comparison `F^*(− ⊗ −) ≅ F^* − ⊗ F^* −`
  (`pullbackTensorComparison`, an isomorphism by `pullbackTensorComparisonIsIso`). Finally
  use `pullbackComp` and `pullbackCongr` to identify `F^* r^* M` with `r'^* M`.
- `pullback_classOf_eq_add`: for a line bundle `L` on `Z` and an isomorphism
  `m'^*L ≅ p'^*L ⊗ q'^*L`, the Picard classes satisfy
  `m'^*[L] = p'^*[L] + q'^*[L]` (`Group.pullback`). Proof: rewrite the pulled-back classes
  as classes of pulled-back line bundles (`Group.pullback_lineBundle_classOf`). Then use
  `Picard.classOf_tensor` and `Picard.classOf_eq_iff`, with `localizedTensorIso` to identify
  the two tensor products.

## Proof of `artinianPrimitiveLineBundleLiftingReduction`

Introduce the hypotheses `hnat` and `hinj` and all binders of the target: `B'`, `B`, `φ`,
`hφ`, `hker`, `A`, `j`, `A₀`, `L`, and the isomorphism `e : m^*L ≅ p1^*L ⊗ p2^*L` on
`A₀ ×_B A₀`.

1. **The thickening of `A`.** Put `i := pullback.fst A.X.hom j`, from `A₀.X.left` to
   `A.X.left`. It is a closed immersion with `i.ker ^ 2 = ⊥`
   (`AffineBaseChangeKernel.isClosedImmersion`, `AffineBaseChangeKernel.ker_sq`, using
   `hφ` and `hker`). `A.X.left` is compact because `A.X.hom` is quasi-compact over an affine
   base.
2. **The product.** Put `P := A.X ⨯ A.X` in `Over (Spec B')`, with projections `p1`, `p2`
   and group law `m := p1 * p2`. `P.hom` is quasi-compact: by
   `Over.prodLeftIsoPullback_hom_fst` it is an isomorphism followed by
   `pullback.fst A.X.hom A.X.hom ≫ A.X.hom`. Put `iP := pullback.fst P.hom j`. It is again
   a closed immersion with square-zero ideal, by the same two lemmas.
3. **Base-changed morphisms.** Let `Fj := Over.pullback j`. For `f : P ⟶ A.X` put
   `g f := (Fj.map f).left`, a map from `pullback P.hom j` to `pullback A.X.hom j`. It
   satisfies `iP ≫ f.left = g f ≫ i` (`pullback.lift_fst`). Then put
   `k f := StructureKernelMorphism.kernelModuleMap f.left i iP (g f) _`. This map is
   compatible with the ideal inclusions (`StructureKernelMorphism.kernelModuleMap_ι`).
4. **Injectivity.** Write `pull f` for the cohomology pullback along `f`, followed by the
   adjoint of `k f`. These are exactly the maps of `ArtinianH2PrimitiveInjectivityStatement`.
   `hinj` with `k m`, `k p1`, `k p2` gives the injectivity of `pull m − pull p1 − pull p2`.
5. **Naturality.** Let `y := [L]` in the Picard group of `A₀.X.left`. Let `ρ` and `ρP` be
   the identifications `SquareZeroRelativeObstructionNaturality.relativeIdealCohomologyAddEquiv`
   for `(A.X.hom, i)` and `(P.hom, iP)` in degree 2. For each `f`, `hnat` gives
   `pull f (ρ (ob_i y)) = ρP (ob_{iP} ((g f)^* y))`. Here `ob` is
   `SquareZeroPicardObstruction.obstructionMap`.
6. **Transporting primitivity.** `Fj.obj P` is `(A ×_{B'} A) ×_{B'} Spec B`. Let
   `c := prod.lift (Fj.map p1) (Fj.map p2)`, a map from it to `A₀.X ⨯ A₀.X`. Then
   `c ≫ fst = Fj.map p1` and `c ≫ snd = Fj.map p2`. Also `c ≫ (fst * snd) = Fj.map m`, by
   `MonObj.comp_mul` and `Functor.map_mul` for `Fj`, which carries the group law of `A` to
   that of `A₀`. Applying `nonempty_tensor_iso_of_comp_eq` to `c.left` and `e` gives
   `(g m)^*L ≅ (g p1)^*L ⊗ (g p2)^*L`. `pullback_classOf_eq_add` then gives
   `(g m)^* y = (g p1)^* y + (g p2)^* y`.
7. **Vanishing.** The obstruction map and `ρP` are additive. By steps 5 and 6,
   `(pull m − pull p1 − pull p2)(ρ (ob_i y))` equals
   `ρP (ob_{iP} ((g m)^* y − (g p1)^* y − (g p2)^* y))`, which is `0`. Injectivity
   (step 4) gives `ρ (ob_i y) = 0`. Since `ρ` is an equivalence, `ob_i y = 0`.
8. **Lifting.** `SquareZeroPicardObstruction.lineBundle_lift_iff` gives a line bundle `M`
   on `A.X.left` with an isomorphism of underlying modules
   `((LineBundle.pullback i).obj M).obj ≅ L.obj`. `ObjectProperty.isoMk` upgrades it to an
   isomorphism in `LineBundle A₀.X.left`. This is the target's conclusion with `L' := M`.

The theorem uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`. The
approved Lean service compiled the module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` with zero errors and warnings.

## Assumptions

The two prerequisite statements are hypotheses here and are not proved in this module.
Their proofs are separate tasks. The target's forbidden inputs (the Picard-zero lifting
statement, the dual-scheme geometry statements and the representability statements) are
not used.
