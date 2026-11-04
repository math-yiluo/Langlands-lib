# Descent and specialization of solvable groups of points

Worker 1382.

This helper module is the algebraic core of the maximality part of the proof of
`Langlands.GroupScheme.BorelAlgClosedFieldExtensionStatement`. It is pure algebra: no schemes
occur. All declarations are in the namespace `Langlands.GroupScheme.BorelFieldExtension`.

Provenance: these are internal helper results, designed for this proof. They are not
transcriptions of a literature result. They replace the usual argument, which relies on
conjugacy of Borel subgroups or properness of `G/B`, neither of which is available in the
Library. Instead, a solvable group of points over the large field `K` is specialized to a
solvable group of points over the small field `k`.

## Conventions

- `k` is a field and `H` is a commutative Hopf algebra over `k`. Points of `H` with
  values in a commutative `k`-algebra `R` are `k`-algebra maps `H →ₐ[k] R`.
- `WithConv (H →ₐ[k] R)` is the group of points under convolution, from the Library
  instance `AlgHom.convGroupOfSemiring`:
  - the product is `(x * y) h = ∑ x h₁ * y h₂` over the comultiplication `Δ h = ∑ h₁ ⊗ h₂`;
  - the unit is `h ↦ ε h`, where `ε` is the counit;
  - the inverse is composition with the antipode.

  `toConv` and `ofConv` pass between a point and its element of this group.
- A `k`-algebra map `ψ : R → R'` acts on points by post-composition. This action is the
  group homomorphism `AlgHom.mapValue ψ`.
- `⁅a, b⁆` is the group commutator `a * b * a⁻¹ * b⁻¹`, from `open scoped commutatorElement`.

In the final proof, `H` is the coordinate Hopf algebra of `G`, `P` is the coordinate kernel
of the Borel subgroup `B`, and `Q` comes from a competing solvable subgroup over `K`.
Worker 1498's module `BorelFieldExtensionKSide` turns the conclusion of the main theorem
`exists_isPrime_lt_of_solvable` into `P ≤ 𝔭`, which contradicts `𝔭 < P`.

## Declarations

### Restriction (section `Res`; `k`, `K` fields, `C` a `K`-algebra)

- `resFun φ`: the restriction `h ↦ φ (1 ⊗ h)` of a `K`-algebra map
  `φ : K ⊗[k] H → C` to a `k`-algebra map `H → C`. Lemmas: `resFun_apply` and
  `resFun_injective`. Moreover, `resFun_mul` and `resFun_one` say that restriction respects
  convolution for the base-changed Hopf algebra `K ⊗[k] H` over `K`.
- `res k K H C`: restriction as an injective group homomorphism
  `WithConv (K ⊗[k] H →ₐ[K] C) →* WithConv (H →ₐ[k] C)` (`res_injective`).

### Basic maps (section `Basic`; `K` a commutative `k`-algebra)

- `extPoint x : K ⊗[k] M →ₐ[K] K` is the `K`-linear extension of a point `x : M →ₐ[k] K`.
  It sends `a ⊗ m` to `a * x m` (`extPoint_tmul`).
- `baseMap g : K ⊗[k] M →ₐ[K] K ⊗[k] N` is the base change of `g : M →ₐ[k] N`. It sends
  `a ⊗ m` to `a ⊗ g m` (`baseMap_tmul`).
- `extPoint_comp_baseMap` and `extPoint_baseMap`: `extPoint y ∘ baseMap g = extPoint (y ∘ g)`.
- `pairLift x y : M ⊗[k] M →ₐ[k] K` is the pair of points `(x, y)`, sending `a ⊗ b` to
  `x a * y b`. Lemmas: `pairLift_tmul`, and `pairLift_comp_includeLeft` /
  `pairLift_comp_includeRight` for its restrictions `x` and `y` to the two factors.
- `pairIdeal K I`: for an ideal `I` of `K ⊗[k] H`, the ideal of `K ⊗[k] (H ⊗[k] H)` generated
  by the images of `I` under `baseMap` of the two inclusions `H → H ⊗[k] H`.

### Separation (section `Separation`; `K` a field)

- `vanishingIdeal Γ`: for a set `Γ` of points, the ideal of all `f ∈ K ⊗[k] M` with
  `extPoint x f = 0` for every `x ∈ Γ`. Lemmas: `mem_vanishingIdeal` and the
  antitonicity `vanishingIdeal_anti`.
- `baseMap_mem_pairIdeal`: let `w : H →ₐ[k] H ⊗[k] H` (a "law") send every pair of points of
  `Γ₁` into `Γ₂`, that is, `(pairLift x y).comp w ∈ Γ₂` for all `x y ∈ Γ₁`. Then `baseMap w`
  maps `vanishingIdeal Γ₂` into `pairIdeal K (vanishingIdeal Γ₁)`.

  Proof. Write `I = vanishingIdeal Γ₁` and `N = pairIdeal K I`. Let
  `Φ : K ⊗[k] (H ⊗[k] H) → (K ⊗[k] H ⧸ I) ⊗[K] (K ⊗[k] H ⧸ I)` be the canonical map. Let `L`
  be the map back to `K ⊗[k] (H ⊗[k] H) ⧸ N` induced by the two inclusions. Then `L ∘ Φ` is
  the quotient map modulo `N`. For `x ∈ Γ₁`, the characters `χ_x` of `K ⊗[k] H ⧸ I` induced
  by `extPoint x` separate points, by the definition of `I`. Moreover, `(χ_x ⊗ χ_y) ∘ Φ` is
  `extPoint (pairLift x y)`, which kills `baseMap w f` for every `f ∈ vanishingIdeal Γ₂`. The
  Library lemma `RationalPointClosure.tensor_eq_zero_of_separating` therefore gives
  `Φ (baseMap w f) = 0`, so `baseMap w f ∈ N`.

### Universal laws (section `Words`)

- `univL` and `univR` are the universal points `h ↦ h ⊗ 1` and `h ↦ 1 ⊗ h` in
  `WithConv (H →ₐ[k] H ⊗[k] H)`.
- `wMul := univL * univR`, `wInv := univL⁻¹` and `wComm := ⁅univL, univR⁆`.
- `pairLift_comp_wMul`, `pairLift_comp_wInv` and `pairLift_comp_wComm`: for points `x` and
  `y` with values in a commutative `k`-algebra, `(pairLift x y).comp w` is `x * y`, `x⁻¹` and
  `⁅x, y⁆` respectively.

  Proof. `AlgHom.mapValue (pairLift x y)` is a group homomorphism. It sends `univL` to `x`
  and `univR` to `y` (`mapValue_pairLift_univL`, `mapValue_pairLift_univR`).

### Law systems (section `LawSystem`; `R` a commutative `k`-algebra)

- `pairFam v`: for a family `v : ι → R ⊗[k] H`, the family indexed by `ι ⊕ ι` of its two
  pullbacks under `baseMap` of the inclusions `H → H ⊗[k] H`.
- `IsLawSystem R n s g` (a structure in `Prop`): for families `g j : Fin (r j) → R ⊗[k] H`
  with `j : ℕ`, it records:
  - `one`: for `j ≤ n`, the unit point `(1 : WithConv (H →ₐ[k] R)).ofConv` kills each `g j i`
    under `extPoint`;
  - `mul`, `inv`: for `j ≤ n`, `baseMap wMul (g j i)` and `baseMap wInv (g j i)` lie in
    `Ideal.span (Set.range (pairFam (g j)))`;
  - `comm`: for `j < n`, `baseMap wComm (g (j + 1) i)` lies in
    `Ideal.span (Set.range (pairFam (g j)))`;
  - `fin`: for `h ∈ s`, `1 ⊗ h - algebraMap k _ (ε h)` lies in `Ideal.span (Set.range (g n))`.

  Informally, these are equations, with coefficients in `R`, for a descending chain of
  subgroups. Each is closed under the group laws, the commutators of the `j`-th lie in the
  `(j + 1)`-th, and the `n`-th has only the unit point, as tested on the elements of `s`.
- `extPoint_pairLift_eq_zero`: suppose `x` and `y` kill every `v i`, and
  `baseMap w t ∈ Ideal.span (Set.range (pairFam v))`. Then `(pairLift x y).comp w` kills `t`.

### Law systems of solvable groups over `K` (section `KSide`; `K` a field)

- `pairIdeal_span`: the `pairIdeal` of `Ideal.span (Set.range v)` is
  `Ideal.span (Set.range (pairFam v))`.
- `exists_isLawSystem`: let `H` be finitely generated, `S` a solvable subgroup of
  `WithConv (H →ₐ[k] K)` and `s` any set. Then some law system over `K` has its first
  family `g 0` vanishing at every point of `S`.

  Proof. Choose `n` with `derivedSeries S n = ⊥`. Let `Γ j` be the set of points in the
  `j`-th derived subgroup. Since `K ⊗[k] H` is Noetherian, `vanishingIdeal (Γ j)` is
  generated by a finite family `g j`. The unit lies in every `Γ j`. The fields `mul`, `inv`
  and `comm` follow from the separation lemma with the laws `wMul`, `wInv` and `wComm`,
  since the derived subgroups are subgroups and `⁅D_j, D_j⁆ = D_{j+1}`. For `fin`, `Γ n` is
  the unit alone, at which `1 ⊗ h - ε h` vanishes.

### Change of coefficients (section `Transfer`)

- `coeffMap ψ : R ⊗[k] M →ₐ[k] R' ⊗[k] M`, for `ψ : R →ₐ[k] R'` (`coeffMap_tmul`). Its
  properties:
  - `coeffMap_baseMap`: it commutes with `baseMap`;
  - `extPoint_coeffMap`: `ψ (extPoint x t) = extPoint (ψ ∘ x) (coeffMap ψ t)`;
  - `comp_one_ofConv`: `ψ` maps the unit point to the unit point;
  - `coeffMap_pairFam`: it commutes with `pairFam`;
  - `coeffMap_injective`: it is injective when `ψ` is, because every module over the field
    `k` is flat.
- `map_mem_span` and `mem_span_of_injective`: images of ideal-span memberships. In
  particular, if `f` is injective, `f t = ∑ c l * f (v l)` and every `c l` lies in the range
  of `f`, then `t ∈ Ideal.span (Set.range v)`.
- `IsLawSystem.map`: a law system over `R` maps along any `ψ : R →ₐ[k] R'` to a law
  system over `R'`.

### Descent to a finitely generated subalgebra (section `Descent`)

- `eventually_mem_range`: every `t ∈ K ⊗[k] M` lies in the image of
  `Algebra.adjoin k F ⊗[k] M` for all sufficiently large finite sets `F ⊆ K` (along
  `Filter.atTop` on `Finset K`).
- `eventually_coeffs`: if `t ∈ Ideal.span (Set.range v)` with `v` finite, then eventually
  the coefficients can be chosen in that image.
- `IsLawSystem.descend`: for finite `s`, every law system over `K` is the image under
  `coeffMap` of a law system over `Algebra.adjoin k F` for some finite `F ⊆ K`.

  Proof. Only finitely many elements and memberships are involved. So a single `F` works
  for all of them (`Filter.eventually_all_finite`, `Filter.Eventually.exists`). The
  descended families are chosen with `Function.invFun` of the injective `coeffMap`. The
  memberships descend by `mem_span_of_injective`, applied to the injective `coeffMap` on
  `H` and on `H ⊗[k] H`.

### Specialization (section `Specialization`; `A` a commutative `k`-algebra)

- `specMap φ : A ⊗[k] M →ₐ[k] M`, for a `k`-point `φ : A →ₐ[k] k`, sends `a ⊗ m` to
  `φ a • m` (`specMap_tmul`). Related lemmas:
  - `extPoint_eq_lid`: over `k`, `extPoint x` is `x` composed with `k ⊗[k] H ≃ H`;
  - `sub_specMap_mem`: `d - 1 ⊗ specMap φ d` lies in the extension of `ker φ` to
    `A ⊗[k] H`.
- `nonempty_algHom_of_finiteType`: a nontrivial finitely generated algebra over an
  algebraically closed field `k` has a `k`-point. The residue field at a maximal ideal is
  finite over `k` (Nullstellensatz, `finite_of_finite_type_of_isJacobsonRing`), hence equal
  to `k`.
- `exists_isPrime_lt_specMap`: the hypotheses are:
  - `A` is Noetherian and `H` is finitely generated;
  - `ι : A →ₐ[k] K` is injective and `φ` is a `k`-point of `A`;
  - `Q` is a prime of `K ⊗[k] H` and `P` is a prime of `H`;
  - every `q ∈ Q` maps to zero in `K ⊗[k] (H ⧸ P)`;
  - `1 ⊗ p ∉ Q` for some `p ∈ P`.

  Then there is a prime `𝔭 < P` of `H` with `specMap φ d ∈ 𝔭` whenever
  `coeffMap ι d ∈ Q`.

  Proof. In `A ⊗[k] H`, let:
  - `Q_A` be the preimage of `Q`;
  - `P_A` be the kernel of the map to `A ⊗[k] (H ⧸ P)`;
  - `M` be the preimage of `P` under `specMap φ`.

  Then `Q_A < P_A ≤ M`, `M` lies over `ker φ`, and `(A ⊗[k] H) ⧸ P_A ≅ A ⊗[k] (H ⧸ P)` is
  flat over `A`. So `exists_isPrime_lt_of_flat` (module `BorelFieldExtensionHeight`) gives
  a prime `q` with `Q_A + (ker φ) ≤ q < M`. By `sub_specMap_mem`, `d ∈ q` if and only if
  `1 ⊗ specMap φ d ∈ q`. Hence `𝔭 := q ∩ H` satisfies `𝔭 < P`, and it contains
  `specMap φ d` for `d ∈ Q_A`.

### Solvability over `k` (section `Rational`)

- `lawSubgroup hg j hj`: for a law system `hg` over `k` and `j ≤ n`, the subgroup of
  `WithConv (H →ₐ[k] k)` of points killing every `g j i`. Lemmas: `mem_lawSubgroup` and
  `commutator_mem_lawSubgroup` (commutators of the `j`-th subgroup lie in the `(j + 1)`-th).
- `exists_solvable_of_isLawSystem`: if `s` generates `H`, then some solvable subgroup
  `Γ` contains every point killing the first family.

  Proof. Take `Γ := lawSubgroup hg 0`. By induction, its `j`-th derived subgroup lies in
  the `j`-th law subgroup. A point of the `n`-th law subgroup agrees with the unit point
  on `s`, by the field `fin`. Since `s` generates `H`, it is the unit point
  (`AlgHom.ext_of_adjoin_eq_top`).

### Main theorem (section `Core`)

- `exists_isPrime_lt_of_solvable`: the hypotheses are:
  - `k` is algebraically closed, `K` is a field extension of `k`, and `H` is a finitely
    generated commutative Hopf algebra over `k`;
  - `S` is a solvable subgroup of `WithConv (H →ₐ[k] K)`;
  - `Q` is a prime of `K ⊗[k] H` that is exactly the vanishing ideal of `S`
    (`hSQ : ∀ q, q ∈ Q ↔ ∀ x, toConv x ∈ S → extPoint x q = 0`);
  - `P` is a prime of `H` with `Q` mapping to zero in `K ⊗[k] (H ⧸ P)`, and `1 ⊗ p ∉ Q` for
    some `p ∈ P`.

  Then there are:
  - a prime `𝔭 < P` of `H`;
  - a solvable subgroup `Γ` of `WithConv (H →ₐ[k] k)` containing every `k`-point `x` with
    `𝔭 ≤ RingHom.ker x`.

  Proof.
  1. Choose a finite generating set `s` of `H`.
  2. `exists_isLawSystem` gives a law system over `K` whose first family vanishes on `S`,
     so that family lies in `Q`.
  3. `IsLawSystem.descend` gives a law system over `A = Algebra.adjoin k F`, with `F` finite.
     This `A` is finitely generated and Noetherian. It is nontrivial as a subring of `K`,
     so it has a `k`-point `φ`.
  4. `exists_isPrime_lt_specMap` with `ι = A.val` gives `𝔭 < P`.
  5. `exists_solvable_of_isLawSystem`, applied to the law system mapped along `φ`, gives `Γ`.
  6. A `k`-point `x` with `𝔭 ≤ ker x` kills each specialized first-family element
     `specMap φ (g' 0 i)`, which lies in `𝔭`. By `extPoint_eq_lid`, these are the
     conditions defining `Γ`.
