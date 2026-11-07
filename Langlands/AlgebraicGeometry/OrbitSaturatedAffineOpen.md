# Saturated affine opens from finite group orbits

Author: Worker 1038.

Module `Langlands.AlgebraicGeometry.OrbitSaturatedAffineOpen`, namespace
`Langlands.AlgebraicGeometry.OrbitSaturatedAffineOpen`.

This is a scheme-level step for the task "AF representability from a finite
surjection with quasi-affine source" (Gross, *Tensor generators on schemes and
stacks*, Proposition 3.5). The route of that task does not use Gross's
normalization, conductor and pushout argument. It covers an algebraic space `Y`
by open subspaces whose preimages in a quasi-affine source `W` are affine and
saturated. The main theorem `exists_saturated_isAffineOpen` constructs such an
open in `W` from a combinatorial hypothesis on the fibres of `W → Y`. The
statement of that theorem is internal. Each fibre is either a single orbit of a
finite group acting on `W`, or lies in a closed part that already maps to a
scheme with finite affine neighbourhoods. The algebraic-space interface (which
relation, which group, which closed part) is not part of this module.

## Declarations

### Commutative algebra

- `exists_add_notMem_of_not_le I x s hp hI`: let `s` be a finite set of prime
  ideals of a commutative ring `A`, none of which contains the ideal `I`. Then
  for every `x : A` there is `e ∈ I` with `x + e ∉ p` for all `p ∈ s`. This is
  the coset form of prime avoidance (often credited to E. Davis). The proof is
  by strong induction on `s`. Pick a minimal element `q` of `s` (by
  `Finset.exists_minimal`) and apply the induction hypothesis to `s.erase q`,
  which gives `e'`. If `x + e' ∉ q` we are done. Otherwise `I * ∏_{p ≠ q} p` is
  not contained in `q`, because `q` is prime, `I ⊄ q`, and minimality rules out
  `p ≤ q`. An element `y` of that product outside `q` then gives `e = e' + y`.
- `exists_add_notMem_of_finite`: the same statement for a finite set `t` of
  indices and a family `p : ι → Ideal A`. It is derived from the previous lemma
  through `Finset.image`.

### Points and basic opens

- `exists_basicOpen_of_isAffineOpen hU hE hEV hVU`: let `U` be an affine open
  of a scheme `X`, `V ≤ U` an open, and `E ⊆ V` a finite set of points. Then
  some `f : Γ(X, U)` has `E ⊆ D(f) ≤ V`. The proof moves to
  `Spec Γ(X, U)` along `hU.fromSpec`. There it applies the Library's
  `GenericPointAvoidance.PrimeSpectrum.exists_basicOpen_of_finite` to the closed
  complement of the preimage of `V`. It returns using `fromSpec_preimage_basicOpen`
  and `range_fromSpec`.
- `exists_basicOpen_isAffineOpen_of_finite X hE`: every finite set of points of a
  quasi-affine scheme `X` lies in an affine basic open `D(s)` of a global
  section `s : Γ(X, ⊤)`. The proof applies the Library's
  `GenericPointAvoidance.exists_basicOpen_of_finite` in `Spec Γ(X, ⊤)` inside the
  open range of the open immersion `X.toSpecΓ`. It pulls back with
  `Scheme.preimage_basicOpen_top`; the argument is the one in the Library's
  `Picard.exists_isAffineOpen_of_finite_of_quasiAffine`, which records only an
  affine open and not a global basic open.
- `pointIdeal x hx` (definition): for `x ∈ U`, the kernel of Mathlib's evaluation
  `X.evaluation U x hx : Γ(X, U) ⟶ κ(x)`. It is a prime ideal (instance), and
  `mem_pointIdeal` says `f ∈ pointIdeal x hx ↔ x ∉ D(f)`.
- `mem_basicOpen_prod s f x`: `x ∈ D(∏_{i ∈ s} f i)` iff `x ∈ U` and `x ∈ D(f i)`
  for every `i ∈ s`. Proved by `Finset` induction from `Scheme.basicOpen_mul`.

### Norms along a finite family of endomorphisms

For `σ : G → (X ⟶ X)` with `G` a finite type:

- `norm σ r` (definition) is `∏_g (σ g)^* r` for a global section `r`.
- `appTop_norm hσ h r`: if `σ g ≫ σ h = σ (g * h)` for a group `G`, then
  `(σ h)^* (norm σ r) = norm σ r`. Pulling back by `σ h` reindexes the product by
  left multiplication by `h`.
- `mem_basicOpen_norm r x`: `x ∈ D(norm σ r)` iff `σ g x ∈ D(r)` for every `g`.

### Main theorem

`exists_saturated_isAffineOpen` takes the following data:

- a quasi-affine scheme `W`;
- a finite group `G` and maps `σ g : W ⟶ W` with `σ 1 = 𝟙 W` and
  `σ g ≫ σ h = σ (g * h)`;
- an equivalence relation `rel` on the points of `W` with finite classes and
  `rel w (σ g w)`;
- a closed immersion `i : Z ⟶ W` and a morphism `q : Z ⟶ P` that is a closed
  map, where `P` satisfies `PointTopology.HasFiniteAffineNeighborhoods`.

It assumes three things:

- the range of `i` is `rel`-saturated;
- on that range, `rel (i z) (i z')` holds iff `q z = q z'`;
- off that range, `rel`-related points differ by some `σ g`.

The conclusion is that every finite set `F` of points of `W` lies in an affine
open `V` that is `rel`-saturated: if `rel w w'` and `w ∈ V` then `w' ∈ V`.

No reducedness, noetherianity or flatness is assumed. The Lean proof runs as
follows.

1. Let `Fs` be the union of the classes of the points of `F`; it is finite and
   saturated. `exists_basicOpen_isAffineOpen_of_finite` gives `s` with
   `D(s)` affine and containing every `σ g` translate of `Fs`.
2. Let `X = D(norm σ s)`. It is contained in `D(s)` (use `g = 1`), so it is a
   basic open of the affine `D(s)` and hence affine (`Scheme.basicOpen_res`).
   It contains `Fs`. It is `G`-stable, `σ g ⁻¹ X = X`, by `appTop_norm` and
   `Scheme.preimage_basicOpen_top`.
3. `i ⁻¹ X` is affine (`IsAffineOpen.preimage`). Let `E = i ⁻¹ Fs` and let `V1` be
   an affine open of `P` containing `q(E)`. Choose `z : Γ(Z, i ⁻¹ X)` with
   `E ⊆ D(z) ≤ i ⁻¹ X ∩ q ⁻¹ V1`.
4. `B = q(Z ∖ D(z))` is closed and misses `q(E)`. A point of `Z` with the same
   image as a point of `E` is `rel`-related to it, hence lies in `E ⊆ D(z)`.
   Choose `c : Γ(P, V1)` with `q(E) ⊆ D(c) ≤ V1 ∖ B`; then `q ⁻¹ D(c) ≤ D(z)`.
5. The pullback `c' = q.appLE V1 (D z) c` has `D(c') = q ⁻¹ D(c)`
   (`Scheme.basicOpen_appLE`). `exists_eq_pow_mul_of_isAffineOpen` gives `n` and
   `y : Γ(Z, i ⁻¹ X)` with `y|_{D z} = z^n c'`. Since `z` is a unit on `D(z)`,
   `φ = z * y` satisfies `D(φ) = q ⁻¹ D(c)`.
6. `Scheme.Hom.app_surjective` (closed immersion, affine `X`) lifts `φ` to
   `h0 : Γ(W, X)`. Let `I` be the kernel of `i.app X`.
   - For each `w ∈ Fs ∩ X` outside the range of `i`, the ideal `I` is not
     contained in `pointIdeal w`. A basic open `D(a) ∋ w` missing the range
     makes `i.app X a` nilpotent
     (`Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact`), so a power of
     `a` lies in `I` but not in the prime `pointIdeal w`.
   - Davis avoidance then gives `e ∈ I` such that `h = h0 + e` is nonzero at
     each such `w`.
   - Then `i ⁻¹ D(h) = q ⁻¹ D(c)`, and `Fs ⊆ D(h) ≤ X`.
7. Let `V = D(∏_g (σ g).appLE X X h)`. It is a basic open of the affine `X`, so it
   is affine, and `w ∈ V` iff `w ∈ X` and `σ g w ∈ D(h)` for all `g`. It contains
   `F`, because each `σ g w` with `w ∈ F` lies in `Fs`.
8. Saturation. Let `w ∈ V` and `rel w w'`.
   - If `w` is off the range of `i`, then `w' = σ g w`. This point lies in `X`,
     and `σ k (σ g w) = σ (g * k) w ∈ D(h)`.
   - If `w = i x`, then `q x ∈ D(c)`. Every point `i x''` related to `i x`
     satisfies `q x'' = q x`, so it lies in `i ⁻¹ D(h) ⊆ X`. This applies to `w'`
     and to all `σ k w'`, which are related to `w`.

## Sources and provenance

Internal. The statement is designed for the route of the host task, which
replaces Gross's normalization/conductor induction (Gross 2017, proof of
Proposition 3.5, Steps 2–3) by an orbit-and-closed-part induction. Steps 1–2
(norms along a finite group to obtain an invariant affine open) follow the
classical argument for quotients of schemes by finite groups. The coset form of
prime avoidance is a standard commutative-algebra lemma. No proof is transcribed
from a source.
