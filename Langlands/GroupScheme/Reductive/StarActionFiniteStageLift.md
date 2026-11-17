# Lifting Galois pinning data from a finite stage to the separable closure

Author: Worker 148.

Lean module: `Langlands.GroupScheme.Reductive.StarActionFiniteStageLift`. It imports
[`Reductive.StarActionFiniteStageProof`](StarActionFiniteStageProof.md) (and through it the
Library's Galois pinning data, star actions, tower isomorphisms and root-datum comparison
results) and Mathlib's `FieldTheory/Finite/GaloisField`.

This module defines one `Prop`-valued statement,
`Langlands.GroupScheme.StarActionFiniteStageLiftStatement.{u}`, and proves it
(`starActionFiniteStageLift`). It is the converse of the Library statement
`StarActionFiniteStageStatement` ([`Reductive.StarActionFiniteStageStatement`](StarActionFiniteStageStatement.md)).
That statement starts from Galois pinning data over `k_s` and finds matching data at a finite
Galois stage. This one starts from Galois pinning data at a stage `L` and finds matching data
over `k_s`. The module also proves two finite-field consequences about the star action of the
arithmetic Frobenius. Together they show that, over a finite field, the class of a form in the
sense of `FiniteFieldFormClassificationStatement` can be computed at any algebraic stage `L`
that carries Galois pinning data.

## Notation

`k_s = SeparableClosure k`. For a field `E` with `Algebra k E`, a group scheme `G` over
`Spec k` (affine, locally of finite type) and `d : GaloisPinningData k E G`
([`Reductive.StarAction`](StarAction.md)): `d` consists of a torus of `G` defined over `k`,
split and maximal after base change to `E`, a reduced root datum of `(G_E, T_E)`, a base and
a pinning, and includes that `G_E` is connected reductive. `d.toSplitPinning.rootDatum` and
`d.toSplitPinning.base` are its root datum and base. `d.starAction σ`, for
`σ : E ≃ₐ[k] E`, is the star action: the Galois action of `σ` on the character lattice of the
`k`-torus followed by the unique Weyl group element that restores the base, as a based
automorphism of the root datum. `RootPairing.Equiv.comp g h` is "first `h`, then `g`".

## Statement

`StarActionFiniteStageLiftStatement.{u}`: for all fields `k L : Type u` with `Algebra k L` and
`Algebra.IsAlgebraic k L`, every group scheme `G` over `Spec k` with `IsAffineHom G.X.hom` and
`LocallyOfFiniteType G.X.hom`, every `d' : GaloisPinningData k L G` and every
`k`-embedding `ι : L →ₐ[k] k_s`, there are `d : GaloisPinningData k k_s G` and
`e : RootPairing.Equiv d'.toSplitPinning.rootDatum d.toSplitPinning.rootDatum` with

- `a ∈ d'.toSplitPinning.base.support ↔ e.indexEquiv a ∈ d.toSplitPinning.base.support` for
  every root index `a` (`e` carries the base of `d'` onto the base of `d`), and
- for all `σ : L ≃ₐ[k] L` and `τ : k_s ≃ₐ[k] k_s` with `τ (ι x) = ι (σ x)` for all `x : L`:
  `RootPairing.Equiv.comp e (d'.starAction σ).val = RootPairing.Equiv.comp (d.starAction τ).val e`,
  that is, `e ∘ μ_{d'}(σ) = μ_d(τ) ∘ e`.

The statement is about the star action of `G` and makes no claim about `G` beyond the
existence of `d'`. `L` need not be finite or Galois over `k`; it only has to be algebraic.

## Declarations

Namespace `Langlands.GroupScheme.StarActionFiniteStage`:

- `exists_lift d' hc`: the general form. Let `k`, `L`, `K` be fields with `Algebra k L`,
  `Algebra k K`, `Algebra L K` and `Algebra.IsAlgebraic k L`, and
  `hc : algebraBaseMap L K ≫ algebraBaseMap k L = algebraBaseMap k K` (the spectrum maps of
  `k → L → K` and `k → K` agree). For `d' : GaloisPinningData k L G` there are
  `d : GaloisPinningData k K G` and a base-preserving
  `e : RootPairing.Equiv d'.toSplitPinning.rootDatum d.toSplitPinning.rootDatum` with
  `e ∘ μ_{d'}(σ) = μ_d(τ) ∘ e` whenever `τ (algebraMap L K x) = algebraMap L K (σ x)` for all
  `x`. The data `d` have the same torus and inclusion as `d'`.
- `exists_frobenius_lift d'`: for a finite field `k` (`[Fintype k]`) and an algebraic
  extension `L`, every `d' : GaloisPinningData k L G` has `d : GaloisPinningData k k_s G` and
  a base-preserving `e` with
  `e ∘ μ_{d'}(Frob_L) = μ_d(Frob) ∘ e`, where
  `Frob_L = FiniteField.frobeniusAlgEquivOfAlgebraic k L` and
  `Frob = FiniteField.frobeniusAlgEquivOfAlgebraic k k_s` (both `x ↦ x^{#k}`).
- `exists_frobenius_class_of_stage p θ d' f' hf' hθ`: for a finite field `k`, an algebraic
  extension `L`, a group scheme `G₀` over `Spec k` with affine structure morphism, a split
  pinning `p : SplitPinning G₀`, `θ : p.basedRootDatumAut`, `d' : GaloisPinningData k L G` and
  `f' : RootPairing.Equiv p.rootDatum d'.toSplitPinning.rootDatum` carrying `p.base` onto the
  base of `d'` (`hf'`) with `f' ∘ θ = μ_{d'}(Frob_L) ∘ f'` (`hθ`): there are
  `d : GaloisPinningData k k_s G` and `f : RootPairing.Equiv p.rootDatum d.toSplitPinning.rootDatum`
  carrying `p.base` onto the base of `d` with `f ∘ θ = μ_d(Frob) ∘ f`. The conclusion is
  exactly the class predicate `HasClass G d θ` of `FiniteFieldFormClassificationStatement`
  ([`Reductive.FiniteFieldFormClassificationStatement`](FiniteFieldFormClassificationStatement.md)),
  so `FiniteFieldFormExistenceStatement` reduces to producing, for each finite-order `θ`, some
  `G` with Galois pinning data over some algebraic extension `L` and the finite-stage
  condition `hθ`.

Namespace `Langlands.GroupScheme`:

- `StarActionFiniteStageLiftStatement.{u} : Prop`, displayed above.
- `starActionFiniteStageLift : StarActionFiniteStageLiftStatement.{u}`.

## Proofs

*`exists_lift`.* This mirrors the Library proof of `StarActionFiniteStage.exists_stage` with
the roles of the two fields exchanged. `G` is connected reductive over `k`
(`connectedReductiveAlgebraicExtensionReflection` along the algebraic extension `L/k`), hence
`G_K` and `(G_L)_K` are connected reductive (`connectedReductiveFieldExtensionStatement`).
The tower isomorphisms `towerIsoOf` and `groupTowerIsoOf` (module
[`Reductive.StarActionFiniteStageTower`](StarActionFiniteStageTower.md)) compare `T_K` and
`G_K` with `(T_L)_K` and `(G_L)_K`, compatibly with the inclusion (`towerIsoOf_square`,
`baseChange_map_eq_groupTowerIsoOf`). The torus `(T_L)_K` is split
(`IsSplitTorus.baseChange`), so `T_K` is split (`IsSplitTorus.of_iso`). `(T_L)_K` is maximal
in `(G_L)_K` (`maximalTorusBaseChange` for `L → K`), so `T_K` is maximal in `G_K`
(`IsMaximalTorus.of_eq_iso_comp_comp_iso`). `rootDatumExistence` gives a reduced root datum
`P` of `(G_K, T_K)`. The root datum of `d'` transported along `L → K`
(`IsRootDatumOf.baseChange`) is compared with it in two steps: `E₁ = latticeBaseChangeEquiv`
(base change of characters and cocharacters) and `E₂ = rootDatumEquivOfTorusCompatibleIso`
along the tower isomorphisms. Put `e = E₂ ∘ E₁`. Its weight map is the tower character map
`towerCharacterOf`. The data `d` keep the torus and inclusion of `d'`, take the root datum `P`,
the base `d'.base.map e` and the pinning `RootPinning.ofSplitMaximalTorus`. `e` carries the
base of `d'` onto this base by `RootPairing.Base.support_map_eq` and injectivity of
`e.indexEquiv`. For the star actions, `towerCharacterOf_transport` (with
`algebraBaseMap_comp_galoisBaseMap` for the compatibility of `σ` and `τ`) shows that the weight
map of `e` intertwines the Galois actions of `σ` and `τ` on characters, and the Library lemma
`starAction_comp_of_weightMap` turns this into the intertwining of the star actions.

*`starActionFiniteStageLift`.* Make `k_s` an `L`-algebra through `ι`
(`ι.toRingHom.toAlgebra`). The compatibility `hc` holds because `ι` is a `k`-algebra map
(`ι.commutes`), and `exists_lift` applies; `algebraMap L k_s = ι` by definition.

*`exists_frobenius_lift`.* `L` is algebraic over the perfect field `k`, so it is separable
and `IsSepClosed.lift` gives `ι : L →ₐ[k] k_s`. The two Frobenius maps are compatible:
`Frob (ι x) = (ι x)^{#k} = ι (x^{#k}) = ι (Frob_L x)` (`map_pow`). Apply
`starActionFiniteStageLift` with `σ = Frob_L`, `τ = Frob`.

*`exists_frobenius_class_of_stage`.* Take `d`, `e` from `exists_frobenius_lift d'` and
`f = e ∘ f'`. It carries `p.base` onto the base of `d` by `hf'` and the base property of `e`,
and `f ∘ θ = e ∘ μ_{d'}(Frob_L) ∘ f' = μ_d(Frob) ∘ e ∘ f'` by `hθ` and the intertwining of
`e` (rewriting with `RootPairing.Equiv.comp_assoc`).

All declarations use only Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).

## Source and provenance

Provenance: derived. J. Tits, *Classification of algebraic semisimple groups*, in *Algebraic
Groups and Discontinuous Subgroups*, Proc. Sympos. Pure Math. 9, AMS, 1966, pp.33–62, source
`tits-1966-classification-algebraic-semisimple`, SHA-256
`962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`, §2.3, printed p.39
(PDF p.44), defines the `*`-action of `Γ = Gal(K/k)`, `K` a separable closure: "since K is
separably closed, T is split over K, therefore all its characters are defined over K and Γ
operates naturally on X*(T); then, σ(Δ) is the system of simple roots for a certain ordering
of X*(T), there exists a well-defined element w of the Weyl group for which w(σ(Δ)) = Δ, and
we set σ* = w ∘ σ." The same construction can be carried out over any field over which `T`
splits, and the `*`-action over `K` is then the one computed at that stage, transported
along base change of characters. The Library statement `StarActionFiniteStageStatement`
records one direction of this (from `K` down to a finite Galois stage); the present
statement records the other direction (from a stage `L` up to `K = k_s`), in the same
formulation. The finite-field corollaries combine it with the fact that the arithmetic
Frobenius of `k_s` restricts to that of `L`.

## Role in the Library

Support for the proof of `FiniteFieldFormExistenceStatement` (module
`Langlands.GroupScheme.Reductive.FiniteFieldFormExistenceStatement`, submitted separately as
candidate `b6b8e0ed-dbdb-4f23-94b4-492ed29184b7` for Task 6547; this module does not import
it). By `exists_frobenius_class_of_stage`, it is enough to construct the form `G_θ` with
Galois pinning data over a finite extension `L` of `k` (for example of degree a multiple of the
order of `θ`) and to compute its star action of `Frob_L` there.
