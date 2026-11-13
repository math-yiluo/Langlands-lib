# The star action over the separable closure is realized at a finite Galois stage: proof

Proof author: Worker 61, for Task 5982 (the S5' proof of the Task 5703 plan). Worker 5375,
the executor of Task 5982, submits it with Worker 61 as coauthor.

This module proves `Langlands.GroupScheme.StarActionFiniteStageStatement` (module
`Langlands.GroupScheme.Reductive.StarActionFiniteStageStatement`). The theorem is
`Langlands.GroupScheme.starActionFiniteStage : StarActionFiniteStageStatement.{u}`, at
universe parameter `u`, with no added hypotheses. `#print axioms` reports only `propext`,
`Classical.choice` and `Quot.sound`. The helper declarations are in the namespace
`Langlands.GroupScheme.StarActionFiniteStage`. Further helpers are in the module
`Reductive/StarActionFiniteStageTower` (see its Markdown).

## Statement proved

Let `k` be a field, `G` a group scheme over `Spec k` with affine structure morphism that is
locally of finite type, and `d : GaloisPinningData k k_s G` Galois pinning data over the
separable closure `k_s = SeparableClosure k`. Then there are a finite Galois extension `L` of
`k`, a `k`-embedding `ι : L →ₐ[k] k_s`, Galois pinning data `d'` over `L` and an
equivalence `e` from the root datum of `d'` to the root datum of `d` such that `e` carries the
base of `d'` onto the base of `d`, and `e ∘ d'.starAction σ = d.starAction τ ∘ e` whenever
`τ (ι x) = ι (σ x)` for all `x : L`.

## Route

`L` is a finite Galois splitting field of the `k`-torus `T` of `d`. The data `d'` keep the
torus `T` and its inclusion into `G` and take a reduced root datum of `(G_L, T_L)`. The
equivalence `e` is base change of characters from `T_L` to `T_{k_s}`, and the base of `d'`
is the base of `d` pulled back along `e`. Base change of characters commutes with compatible
Galois automorphisms (module `Reductive/StarActionFiniteStageTower`). So `e` intertwines the
ordinary Galois actions, and a based projection argument as in the Library proof of
`StarActionIndependenceStatement` gives the star actions.

### 1. Lattice base change as an equivalence (section `Lattice`)

For a field map `b : Spec K ⟶ Spec L`, a split torus `T` over `L` and a root datum `P` of `T`,
`latticeBaseChangeEquiv b T hT P : RootPairing.Equiv P (SplitRootDatum.baseChange b T hT P)`
has weight map `characterLattice.baseChangeEquiv b T hT`, coweight map the inverse of
`cocharacterLattice.baseChangeEquiv b T hT`, and the identity on indices. Compatibility with
the pairing is `SplitRootDatum.baseChange_pairing`. Roots match by `rfl`, and coroots match
by `symm_apply_apply`. The lemma `latticeBaseChangeEquiv_weightMap` records the weight map,
by `rfl`.

The local instance `baseChangeAffine` copies the instance of the statement module. The base
change of an affine-type `G` along `algebraBaseMap k E` has affine structure morphism.

### 2. Star actions over two fields (section `Star`)

`starAction_comp_of_weightMap`: let `d'` and `d` be Galois pinning data over two extensions
`L` and `K` of `k`, and `e` an equivalence of their root data preserving the bases. Suppose
`e.weightMap` intertwines `characterLattice.galoisRepresentation k L d'.torus σ` with
`characterLattice.galoisRepresentation k K d.torus τ`. Then
`e ∘ d'.starAction σ = d.starAction τ ∘ e`.

Proof. `StarActionIndependence.equiv_ext_of_weightMap`, with `conjAut_weightMap` and
`galoisAction_weightMap_apply`, gives `conjAut e (d'.galoisAction σ) = d.galoisAction τ`. So
`d.galoisAction τ * (conjAut e (d'.galoisAction σ))⁻¹ = 1` lies in the Weyl group. Since
`starAction` is `basedRootDatumProjection` composed with `galoisAction`, the cross-field
`comp_basedRootDatumProjection` of the Tower module concludes.

### 3. The finite stage (section `Stage`)

`algebraBaseMap_comp_galoisBaseMap`: if `τ ∘ (L → K) = (L → K) ∘ σ`, then
`algebraBaseMap L K ≫ galoisBaseMap k L σ = galoisBaseMap k K τ ≫ algebraBaseMap L K`, by
functoriality of `Spec`.

`exists_stage`: let `L` and `K` be extensions of `k`, with `K` algebraic over `k` and an
`L`-algebra structure on `K` satisfying
`algebraBaseMap L K ≫ algebraBaseMap k L = algebraBaseMap k K` (`hc`). Let
`d : GaloisPinningData k K G`, and suppose `T_L` is a split torus (`hsplit`). Then the
conclusion of the statement holds with `L` in place of the finite stage, for every pair
`σ`, `τ` with `τ ∘ (L → K) = (L → K) ∘ σ`. The steps:

1. *Reductivity.* `G` is connected reductive by
   `connectedReductiveAlgebraicExtensionReflection` (`K/k` algebraic). Then `G_L` and
   `(G_L)_K` are connected reductive by `connectedReductiveFieldExtensionStatement`.
2. *Tower.* The Tower module provides isomorphisms `T_K ≅ (T_L)_K` (`towerIsoOf`) and
   `G_K ≅ (G_L)_K` (`groupTowerIsoOf`). They satisfy the square `towerIsoOf_square` and the
   identity `baseChange_map_eq_groupTowerIsoOf`. With these,
   `IsMaximalTorus.of_eq_iso_comp_comp_iso` carries maximality of `T_K` in `G_K` (from `d`)
   to maximality of `(T_L)_K` in `(G_L)_K`.
3. *Closedness and maximality over `L`.* `T_L` is split, so it has affine structure morphism
   (`IsSplitTorus.isAffineHom`) and is affine. `G_L` is affine too. `Spec K → Spec L` is
   surjective and flat (`fieldExtension_fpqc`). `IsClosedSubgroup.of_baseChange_of_isAffine`
   descends closedness of `(T_L)_K` in `(G_L)_K` to closedness of `T_L` in `G_L`. Then
   `maximalTorusBaseChange L K`, the Library proof of `MaximalTorusBaseChangeStatement`
   (Milne, Theorem 17.82), gives maximality of
   `T_L` in `G_L`. Its arguments are given explicitly; with placeholders `_` the
   elaboration exhausts the heartbeat limit.
4. *Root datum over `L`.* `rootDatumExistence` gives a finite index type `J'`, a reduced root
   datum `P'` of `(G_L, T_L)` and its witness `hP'`. `IsRootDatumOf.baseChange` shows that
   `SplitRootDatum.baseChange (Spec(L → K)) T_L hsplit P'` is a root datum of
   `((G_L)_K, (T_L)_K)`.
5. *The equivalence.* Let `E₁ = latticeBaseChangeEquiv` (step 1 of this route). Let `E₂` be
   `rootDatumEquivOfTorusCompatibleIso` (module `Reductive/GeometricRootDatumComparison`),
   applied to the root data of `d` and of step 4 with the tower isomorphisms of step 2. Set
   `e = E₂ ∘ E₁`. By `rootDatumEquivOfTorusCompatibleIso_weightMap`, `e.weightMap χ` is
   `towerCharacterOf χ` for every character `χ` of `T_L`.
6. *The data over `L`.* Let `base' = d.base.map e⁻¹`. Then `d'` has the torus and inclusion
   of `d`, the reductivity and maximality of steps 1 and 3, the splitting `hsplit`, the root
   datum `P'` and the base `base'`. The pinning `RootPinning.ofSplitMaximalTorus hGL hsplit _ hiL P' hP' base'`
   supplies the simple-root Lie vectors.
7. *Bases.* `RootPairing.Base.support_map_eq` shows that the support of `base'` is the image
   of the support of `d.base` under `e.indexEquiv.symm`. This gives
   `a ∈ base'.support ↔ e.indexEquiv a ∈ d.base.support`.
8. *Star actions.* Apply `starAction_comp_of_weightMap`. Its hypothesis is, by step 5,
   `towerCharacterOf (σ χ) = τ (towerCharacterOf χ)`. Here `σ χ` and `τ ψ` are
   `characterLattice.transport` along `galoisBaseMap` (by `rfl`,
   `characterLattice.galoisRepresentation_apply`). So the hypothesis is
   `towerCharacterOf_transport` with `aL = galoisBaseMap k L σ` and
   `aK = galoisBaseMap k K τ`. The square `j ≫ aL = aK ≫ j` it needs is
   `algebraBaseMap_comp_galoisBaseMap`. The equalities are chained in term mode with
   `Eq.trans` and `congrArg`. `rw [he]` fails here, because the goal states `e` through the
   projections of `d'`.

### 4. The theorem (`starActionFiniteStage`)

The torus `T` of `d` is a torus over `k`, split over `k_s` by `d.isSplitTorus`. The Library
theorem `torusFiniteGaloisSplitting` gives a finite Galois extension `L` of `k` over which
`T` splits. `IsSepClosed.lift` gives a `k`-embedding `ι : L →ₐ[k] k_s`, and `ι` makes `k_s`
an `L`-algebra. The identity `hc` follows from `ι.commutes` and functoriality of `Spec`. In
this algebra structure `algebraMap L k_s x` is `ι x`. So the compatibility hypothesis
`τ (ι x) = ι (σ x)` of the statement is the hypothesis of `exists_stage`, which supplies
`d'`, `e` and both conclusions.

## Source and provenance

Provenance: derived.

J. Tits, *Classification of algebraic semisimple groups*, in *Algebraic Groups and
Discontinuous Subgroups*, Proc. Sympos. Pure Math. 9, AMS, 1966, pp.33–62, source
`tits-1966-classification-algebraic-semisimple`, §2.3, printed p.39 (PDF p.44). Tits defines
the `*`-action of `Γ = Gal(k_s/k)` on the simple roots through the natural action of `Γ` on
`X^*(T)` followed by a Weyl correction: `σ* = w ∘ σ`, where `w` is the Weyl group element
with `w(σ(Δ)) = Δ`. Tits does not state the finite-stage reduction as a separate result. He
uses it implicitly when he says the full action is known once the fixed field of
`{σ | σ* = id}` is known (see the statement's Markdown). The proof above formalizes the
observation that the same construction can be carried out over a finite Galois splitting
field `L` of `T` inside `k_s`. Base change of characters from `T_L` to `T_{k_s}` is a
Galois-equivariant isomorphism of root data (steps 2, 5 and 8). It preserves the chosen
bases by construction (step 7), so it carries Weyl corrections to Weyl corrections (§2).
The closedness and maximality of `T_L` (step 3), descended from `k_s` to `L`, are
formalization details that Tits does not discuss.
