# Levi lifts into a quaternionic spin cover

Module `Langlands.GroupScheme.Quaternionic.SpinLeviLift`, namespace
`Langlands.GroupScheme.Quaternionic.SpinKernel`.

## Result

**`spinLeviLift_of_degreeTwoNormOneSimplyConnected`**: the proposition
`CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement` (the reduced-norm-one group
`SL₁(A)` of every four-dimensional central simple algebra `A` over a field is algebraically
simply connected) implies `SpinLeviLiftStatement` (module `SpinKernelAssembly`). That is, in
the setting of `LocalSpinKneserTitsStatement`, for every spin cover `π : S ⟶ O(q)` and every
hyperbolic pair `h : σ.IsHyperbolicPair q e f`, there are homomorphisms
`μ : 𝔾_m ⟶ S` and `ψ : SL₁(D) ⟶ S` with `IsLeviLift h π μ ψ`:

* for every `K`-algebra `A` and `t ∈ Aˣ`, `π(μ(t))` is the image under the Levi morphism
  `leviHom h` of the scalar unit `t · 1 ∈ (A ⊗ D)ˣ`;
* `ψ ≫ π = normOneι ≫ leviHom h`.

The simple-connectedness premise is an explicit hypothesis; it is the open proof Task 5664.

## Proof

The lifts are the published binary lifts of module `BinaryQuaternionSpinLift`:
`μ = BinarySpinLift.scalar σ hdim hsym h hπ hsc` and
`ψ = BinarySpinLift.normOne σ hdim hsym h hπ hsc`. They need `Infinite K`, which holds for a
nonarchimedean local field (`LocalField.infinite_of_isNonarchimedeanLocalField`).

`isLeviLift_binarySpinLift` proves `IsLeviLift` for them, for any field `K` that is infinite.
Both parts are checked after composing with the monomorphism `σ.isometryGroupι q` (from
`isClosedSubgroup_isometryGroupι`) and applying the injective matrix coordinates
`HyperbolicScheme.matrixPointsEquiv`.

* Scalars. For the affine test `T = Spec A`, `BinarySpinLift.scalar_points` gives the
  matrix `extendUnits h C (hyperbolicLevi (σ.baseChange C) (t' · 1))`, where `C` is the
  coefficient algebra of `T` and `t'` is the all-test coordinate of the point `gmPoint A t`.
  `LeviScheme.leviHom_points` gives `extendUnits h C (leviMatrix σ C a')` for the image of
  `unitPoint A (t · 1)`, with `a'` its all-test coordinate. Two coordinate comparisons, both
  through the inverse section isomorphism `φ : A ≅ C` (`Corepresented.affineSectionsIso`),
  identify the arguments:
  * `gm_pointsEquiv_gmPoint`: `t' = φ(t)`. The affine `𝔾_m` coordinate is the all-test
    coordinate followed by `Scheme.ΓSpecIso A`, whose inverse is `φ`
    (`Corepresented.affineSectionsIso_inv_ringHom`).
  * `pointsEquiv_unitPoint`: `a' = (φ ⊗ id)(t · 1)`, by `LeviScheme.pointsEquiv_affine`.

  `normCoverScalarUnits_map` gives `(φ ⊗ id)(t · 1) = φ(t) · 1`, and `leviMatrix` is
  `hyperbolicLevi` of the base-changed involution by definition.
* Norm one. `normOne_comp_points` proves the identity on every relative test point `x` of
  `SL₁(D)`: `BinarySpinLift.normOne_levi_points` gives
  `extendUnits h C (hyperbolicLevi (σ.baseChange C) b)` for the reduced-norm-one coordinate
  `b` of `x`, and `leviHom_points` gives the same expression for `x ≫ normOneι`, since the
  coordinate of `x ≫ normOneι` is `b` by definition (`normOnePointsEquiv_val`). Applied to
  the identity point of `SL₁(D)` this yields equality of the underlying scheme morphisms,
  hence of the homomorphisms (`Grp.hom_ext`).

## Provenance

Internal (Task 5398). The module only compares the published binary lifts with the
published Levi morphism; no literature is transcribed. Simple connectedness of `SL₁(D)` is
not proved here.
