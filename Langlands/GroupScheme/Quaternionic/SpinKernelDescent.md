# Descent of the reduced norm along lifts of the Levi subgroup

Module `Langlands.GroupScheme.Quaternionic.SpinKernelDescent`, namespace
`Langlands.GroupScheme.Quaternionic.SpinKernel`.

The module states a kernel condition on a homomorphism `π : S ⟶ G` together with lifts of a
Levi morphism, and proves under it the reduced-norm obstruction that the Kneser–Tits reduction
calls spin input 1 (`SpinLeviReducedNormSquareStatement`, module
`LocalSpinKneserTitsReduction`). The module does not prove the kernel condition for spin covers,
and it does not construct the lifts.

## Setting

* `K` is a field. `D` is a finite-dimensional central division `K`-algebra, and
  `hdeg : reducedDegree K D = 2`.
* Points are taken over affine tests: for `A : CommAlgCat (CommRingCat.of K)`,
  `S.affinePoints A` is the group of points of `S` over `Spec A`. For `f : A ⟶ B`,
  `affinePointMap f` is extension of coefficients.
* `gmPoint A : Aˣ ≃* 𝔾_m(A)`, `unitPoint A : (A ⊗[K] D)ˣ ≃* GL₁(D)(A)` and
  `normOnePoint A : SL₁(D)(A) ≃* (normOne K D)(A)` are the inverses of the Library point
  equivalences `Gm.affineUnitsEquiv`, `FiniteAlgebraUnits.affinePointsEquiv` and
  `CentralSimpleUnits.normOneAffinePointsEquiv`. Here `GL₁(D)` is
  `CentralSimpleUnits.groupScheme K D` and `SL₁(D)(A)` is `reducedNormOne K D A`.
* The data are group-scheme homomorphisms `π : S ⟶ G`, `Λ : GL₁(D) ⟶ G`,
  `mu : 𝔾_m ⟶ S` and `psi : SL₁(D) ⟶ S`. `unitMap Λ A a = unitPoint A a ≫ Λ` is `Λ` on
  `A`-points.
* The hypotheses used are:
  - `hcent`: for every `A` and all points `x, y` of `S` over `A`, if `π(x) = 1` then `x` and
    `y` commute;
  - `hmu`: `π(mu(t)) = Λ(t · 1)` for every `A` and every `t ∈ Aˣ`;
  - `hpsi : psi ≫ π = normOneι ≫ Λ`.

## Definitions

* `QuadraticRoot c := AdjoinRoot (X ^ 2 - C c)` for `c : K`, with the unit
  `quadraticRootUnit hc` (the root `t`, a unit when `c ≠ 0`). `quadraticRootUnit_sq` states
  `t² = c`.
* `normOneMap f : SL₁(D)(A) →* SL₁(D)(B)` is extension of coefficients along `f : A ⟶ B`.
* `scalarNormOne hdeg A : μ₂(A) →* SL₁(D)(A)` sends `u` to `u ⊗ 1`. Here
  `μ₂(A) = rootsOfUnity 2 A`. The reduced norm of `u ⊗ 1` is `u² = 1` because the reduced
  degree is two.
* `kernelPoint hdeg mu psi A u = mu(u) · psi(u · 1)`. This is the map `z : μ₂ → ker π`.
* **`KernelGenerator hdeg π mu psi`** (a `Prop`): for every `A` and every point `k` of `S`
  over `A` with `k ≫ π = 1`, there is exactly one `u ∈ μ₂(A)` with `kernelPoint … A u = k`.

## Results

### Algebra

* `exists_algebraMap_eq_of_tmul_eq`: let `K` be a field and `R` a `K`-algebra. If
  `x ⊗ 1 = 1 ⊗ x` in `R ⊗[K] R`, then `x` is a scalar. Proof: otherwise `1, x` are linearly
  independent. Choose functionals `f` with `f(1) = 0`, `f(x) ≠ 0`
  (`Submodule.exists_dual_map_eq_bot_of_notMem`) and `g` with `g(1) ≠ 0`. Applying
  `a ⊗ b ↦ f(a) g(b)` gives `f(x) g(1) = f(1) g(x) = 0`, a contradiction.
* `exists_sq_of_tmul_relation`: let `c ≠ 0`, `R = QuadraticRoot c` with root `t`, and
  `w ∈ R` with `w² = 1`. If `1 ⊗ w = (1 ⊗ t)(t⁻¹ ⊗ 1)(w ⊗ 1)` in `R ⊗[K] R`, then `c` is a
  square in `K`. Proof: from the relation, `(1 ⊗ t)² = (t ⊗ 1)²` and
  `(t ⊗ 1)(t⁻¹ ⊗ 1) = 1`, a ring computation (`linear_combination`) gives
  `wt ⊗ 1 = 1 ⊗ wt`. So `wt = x` for some `x ∈ K`, and `x² = w² t² = c`.

### Points

* `gmPoint_naturality`, `unitPoint_naturality`, `normOnePoint_naturality`: the point
  equivalences commute with extension of coefficients. `normOnePoint_comp_normOneι` states
  that the inclusion `SL₁(D) ⟶ GL₁(D)` is the subtype map on points.
* `kernelPoint_naturality`: `f(z(u)) = z(f(u))` for `f : A ⟶ B`.
* `kernelPoint_comp`: under `hmu` and `hpsi`, `π(z(u)) = Λ(u²) = 1`.
* `kernelPoint_mul`: if all values of `z` over `A` are central, then `z(uv) = z(u) z(v)`.
  The two `psi`-factors commute because `u · 1` and `v · 1` do. Centrality of
  `z(v) = mu(v) psi(v)` then moves `psi(u)` past `mu(v)`.
* `rationalCoeffEquiv_comp_hom` restates the Library's `rationalCoeffEquiv_map` as a
  composite. `affinePointsEquiv_rationalCoeffEquiv_symm`: the rational point of `GL₁(D)`
  given by `a ∈ Dˣ` is `1 ⊗ a ∈ (K ⊗[K] D)ˣ`. `units_map_tensorMap_comp`,
  `normCoverScalarUnits_map` and `affinePointMap_comp_hom` are bookkeeping lemmas.

### Descent

* `descentPoint_comp_eq_one`: let `s` be a point of `S` over `A` with `π(s) = Λ(a)`,
  `t ∈ Aˣ`, and `b ∈ SL₁(D)(A)` with `b = t⁻¹ a`. Then `k = s⁻¹ mu(t) psi(b)` satisfies
  `π(k) = 1`, because `Λ(t) Λ(t⁻¹ a) = Λ(a)`.
* `descentPoint_map_eq`: assume `hcent`. Let `j₁, j₂ : A ⟶ B` with `j₁(s) = j₂(s)` and
  `j₁(a) = j₂(a)`, and let `u' ∈ μ₂(B)` with `j₂(t) = j₁(t) u'`. Then
  `j₂(k) = z(u') j₁(k)`. Proof: `j₂(b) = (u' · 1) j₁(b)`, since `u'⁻¹ = u'`. Expanding both
  images and using the centrality of `z(u')` gives the identity.
* **`exists_sq_eq_reducedNorm_of_comp_eq`**: assume `hcent`, `hmu`, `hpsi` and
  `KernelGenerator hdeg π mu psi`. Let `s` be a rational point of `S` and `a ∈ Dˣ` with
  `π(s) = Λ(a)` (as rational points, `a` viewed in `GL₁(D)(K)` through
  `FiniteAlgebraUnits.rationalPointsEquiv`). Then `reducedNorm K D K (1 ⊗ a) = x²` for some
  `x : K`.

  Proof. Put `c = Nrd(a) ≠ 0`, `R = K[t]/(t² - c)` and `b = t⁻¹ a ∈ SL₁(D)(R)`. By
  `descentPoint_comp_eq_one`, the point `k = s⁻¹ mu(t) psi(b)` over `R` lies in `ker π`.
  The kernel condition gives `w ∈ μ₂(R)` with `z(w) = k`. Let `j₁, j₂ : R ⟶ R ⊗[K] R` be the
  two inclusions and `u' = j₂(t) j₁(t)⁻¹`. Then `u'² = c/c = 1`. Both inclusions agree on
  `K`, so they agree on `s` and on `a`. `descentPoint_map_eq` gives
  `j₂(k) = z(u') j₁(k)`. By naturality and multiplicativity of `z`,
  `z(j₂(w)) = z(u' j₁(w))`. Both points lie in `ker π`, so uniqueness in the kernel condition
  over `R ⊗[K] R` gives `j₂(w) = u' j₁(w)`. This is the relation of
  `exists_sq_of_tmul_relation`, which shows that `c` is a square. No assumption on the
  characteristic is used.

## Use

For a spin cover `π : S ⟶ O(q)` and a hyperbolic pair, `Λ` is meant to be the Levi morphism
`a ↦ ℓ(a)`, and `mu`, `psi` lifts of `Λ` on the scalars and on `SL₁(D)`. `hcent` follows from
the centrality of the kernel of a central isogeny. Proving `KernelGenerator` for spin covers,
constructing the lifts, and identifying `Λ` on rational points with the Levi matrices of
`HyperbolicLevi` are separate tasks.

## Provenance

Internal (Task 5398). The descent argument is the standard computation of the connecting map
`O(q)(K) → H¹(K, μ₂) = K^×/K^{×2}` on the Levi element `ℓ(a)`, where the class is `Nrd(a)`.
Here it is written out with the explicit flat cover `K → K[t]/(t² - c)` and the equalizer of
`R ⇉ R ⊗ R`, so that it also covers characteristic two.
