# The quaternionic Kneser–Tits statement from the spin-kernel statements

Module `Langlands.GroupScheme.Quaternionic.SpinKernelAssembly`, namespace
`Langlands.GroupScheme.Quaternionic.SpinKernel`.

The module reduces `LocalSpinKneserTitsStatement` to three statements about lifts of the
Levi morphism to a spin cover. It proves none of the three.

## Setting

* `π : S ⟶ O(q)` is a homomorphism of group schemes over `Spec K`, usually a spin cover
  (`σ.IsSpinCover q π`). `h : σ.IsHyperbolicPair q e f` is a hyperbolic pair, and
  `leviHom h : GL₁(D) ⟶ O(q)` is its Levi morphism (module `LeviGroupScheme`).
* `gmPoint`, `normOnePoint`, `unitMap`, `kernelPoint`, `KernelGenerator` and
  `rationalCoeffEquiv_comp_hom` are from `SpinKernelDescent`.

## Definitions

* **`IsLeviLift h π mu psi`** (a `Prop`), for `mu : 𝔾_m ⟶ S` and `psi : SL₁(D) ⟶ S`:
  - for every `K`-algebra `A` and `t ∈ Aˣ`, `π(mu(t)) = leviHom h (t ⊗ 1)`;
  - `psi ≫ π = normOneι ≫ leviHom h`.
* `negOneRoot` is `-1 ∈ μ₂(K)`.
* **`SpinLeviLiftStatement`** (a `Prop`): in the setting of `LocalSpinKneserTitsStatement`
  (nonarchimedean local `K`, central `D` with `dim_K D = 4`, `σ` with `dim_K D^σ = 3`,
  `m ∈ {4, 5}`, `q` nondegenerate of Witt index `1`), for every spin cover `π` and every
  hyperbolic pair `h` there are `mu`, `psi` with `IsLeviLift h π mu psi`.
* **`SpinKernelGeneratorStatement`** (a `Prop`, the kernel statement Z): in the same
  setting, for every spin cover `π`, hyperbolic pair `h` and `mu`, `psi` with
  `IsLeviLift h π mu psi`, `KernelGenerator hdeg π mu psi` holds. Here `hdeg` is the reduced
  degree `2` obtained from `dim_K D = 4`. So `z(u) = mu(u) psi(u · 1)` is a bijection from
  `μ₂(A)` onto the points of `ker π` over `A`, for every `K`-algebra `A`.
* **`SpinKernelElementaryLiftStatement`** (a `Prop`): in the same setting and for the same
  data, the rational point of `S` corresponding to `z(-1) = mu(-1) psi(-1)` (through
  `GaloisPointComparison.rationalCoeffEquiv`) lies in `parabolicElementarySubgroup S`.

## Results

* `commute_of_comp_eq_one`: for a spin cover, a point `x` of `S` over any `K`-algebra with
  `π(x) = 1` commutes with every point over the same algebra. Write `π = p ≫ ι` with `p` a
  central isogeny onto `O(q)⁰`. Since `ι` is a monomorphism, `p(x) = 1`, and the kernel of a
  central isogeny is central.
* `leviReducedNormSquare_of_kernelGenerator`: for one spin cover, `IsLeviLift` and
  `KernelGenerator` give spin input 1. If `isometryRationalMatrix (π s) = levi σ q _ a`, then
  `π(s) = leviHom h (a)` by `isometryRationalMatrix_leviHom` and injectivity of
  `isometryRationalMatrix`. `exists_sq_eq_reducedNorm_of_comp_eq` then shows that
  `reducedNorm (1 ⊗ a)` is a square.
* `kernelPoint_one`: `z(1) = 1`.
* `kernelElementary_of_kernelGenerator`: for one cover, `KernelGenerator` and
  `z(-1) ∈ S(K)⁺` give spin input 2. Let `π(s) = 1`. The kernel condition at the coefficient
  algebra `K` gives `w ∈ μ₂(K)` with `z(w) = s`. Then `w = ±1` because `w² = 1` in the field
  `K`. If `w = 1` then `s = 1`. If `w = -1` then `s = z(-1) ∈ S(K)⁺`.
* **`localSpinKneserTits_of_spinKernel`**: `SpinLeviLiftStatement`,
  `SpinKernelGeneratorStatement` and `SpinKernelElementaryLiftStatement` together imply
  `LocalSpinKneserTitsStatement`. The two spin inputs are combined by
  `localSpinKneserTits_of_spinInputs` (module `LocalSpinKneserTitsReduction`). For spin
  input 2, a hyperbolic pair exists because the Witt index is `1`
  (`exists_hyperbolicPair_of_quadraticWittIndex_pos`).

## Status of the three statements

* Lifts: Worker 124's lift modules construct `mu` and `psi` assuming
  `DegreeTwoNormOneSimplyConnectedStatement`. They do not yet show `IsLeviLift` against
  `leviHom`.
* `SpinKernelGeneratorStatement` amounts to `π₁(O(q)⁰) = μ₂`, with the generator detected by
  the plane subgroup `SL₂ × SL₁(D)`. It is open.
* `SpinKernelElementaryLiftStatement` is automatic in characteristic `2`, where `-1 = 1`. In
  general it is open.

## Provenance

Internal (Task 5398). This is bookkeeping that assembles the published reduction
`localSpinKneserTits_of_spinInputs` with the descent theorem of `SpinKernelDescent` and the
Levi morphism of `LeviGroupScheme`.
