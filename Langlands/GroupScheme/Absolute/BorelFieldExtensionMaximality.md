# Maximality of a Borel subgroup after an extension of algebraically closed fields

Worker 1498. The algebraic core used here
(`exists_isPrime_lt_of_solvable`, module `BorelFieldExtensionDescent`) is by Worker 1382.

This helper module proves the maximality field of `IsBorelSubgroup` for the base change of
a Borel inclusion along an extension `k → K` of algebraically closed fields. That field is
the hard part of the proof of `Langlands.GroupScheme.BorelAlgClosedFieldExtensionStatement`.
All declarations are in the namespace `Langlands.GroupScheme.BorelFieldExtension`.

Provenance: these are internal helper results, designed for this proof. They are not
transcriptions of a literature result. Milne, *Algebraic Groups* (2017), §17.66, states the
preservation of Borel subgroups under field extension and derives it from completeness of
`G/B` and conjugacy of Borel subgroups. Neither of these is available in the Library. Here,
maximality is instead reduced to the pure-algebra statement of `BorelFieldExtensionDescent`
and the statement over `k` of `BorelFieldExtensionKSide`. The present module supplies the
dictionary between schemes and Hopf algebras that connects them.

## Notation

- `k` and `K` are fields with `Algebra k K`, and `b = Spec.map (CommRingCat.ofHom (algebraMap k K))`.
- `G` is a group scheme over `Spec k` whose underlying scheme is affine, and
  `H = AffineCoordinates.hopfAlgebra G` is its coordinate Hopf algebra (Library module
  `AffineHopfCoordinates`). `G_K = (GroupScheme.baseChange b).obj G`.
- For a group scheme `B` over `Spec k`, `B_K` is its base change, and for `i : B ⟶ G`,
  `i_K = (GroupScheme.baseChange b).map i`.
- Rational points of `G` are morphisms `Over.mk (𝟙 (Spec k)) ⟶ G.X`, and `K`-points of
  `G_K` are morphisms `Over.mk (𝟙 (Spec K)) ⟶ G_K.X`.
- `extPoint x : K ⊗[k] H →ₐ[K] K` (`a ⊗ h ↦ a * x h`) and
  `baseMap g : K ⊗[k] M →ₐ[K] K ⊗[k] N` are from `BorelFieldExtensionDescent`.

## Declarations

### Global sections of spectra (section `Spec`)

- `specMap_appTop_inv`: for a ring map `f : R ⟶ S` and `r : R`, pulling back the global
  function `(ΓSpecIso R).inv r` along `Spec.map f` gives `(ΓSpecIso S).inv (f r)`. This is
  `Scheme.ΓSpecIso_inv_naturality`.
- `ΓSpecIso_inv_eq_zero_iff`: `(ΓSpecIso R).inv r = 0` if and only if `r = 0`.

### Points and coordinates (section `PointEquiv`; `k` a field, `G` affine)

- `hopfAlgebra_finiteType` (instance): if `G.X.hom` is locally of finite type, `H` is a
  finitely generated `k`-algebra (the Library's `AffineCoordinates.algebraFiniteType`).
- `hopfPointEquiv G A`: for a commutative `k`-algebra `A`, the multiplicative equivalence
  between `WithConv (H →ₐ[k] A)` (convolution group) and the group of morphisms from
  `Spec A` to `G` over `Spec k`. It composes Mathlib's `Spec.mapMulEquiv` with the
  isomorphism `AffineCoordinates.hopfSpecIso G` between `Spec H` and `G`.
- `schemeIso G : Spec H ≅ G.X.left`, the underlying scheme isomorphism. By
  `hopfPointEquiv_left`, the point attached to `x` is `Spec.map x ≫ (schemeIso G).hom`.
- `coordEquiv G : Γ(G.X.left, ⊤) ≃+* H`, the identification of global functions with `H`
  given by `schemeIso` and `ΓSpecIso` (`coordEquiv_apply`).
- `appTop_point`: pulling back a global function `g` along the point attached to `x` gives
  the constant `x (coordEquiv G g)`. Hence (`ker_appTop_point`) the global functions killed
  by that point are the preimage under `coordEquiv G` of `ker x`.
- `schemeIso_hom_comp` and `coordEquiv_symm_algebraMap`: constants from `k` correspond to
  global functions pulled back from `Spec k`.

### Rational points and `K`-points (section `Points`)

- `unitIso k` and `rationalPointEquiv G : WithConv (H →ₐ[k] k) ≃* rational points of G`
  (`rationalPointEquiv_left`: the point of `x` is again `Spec.map x ≫ (schemeIso G).hom`).
  It transports `hopfPointEquiv G k` along `pointsMulEquivOfIso`.
- `extIso k K` and `extPointEquiv G : WithConv (H →ₐ[k] K) ≃* K-points of G_K`. It is
  `hopfPointEquiv G K`, transported along `pointsMulEquivOfIso` and the inverse of the
  Library's `baseChangePointsEquiv`. Its compatibilities:
  - `baseChangePointsEquiv_extPointEquiv`: `baseChangePointsEquiv` sends the `K`-point of
    `x` to the point of `x` over `Spec k`.
  - `extPointEquiv_left_fst`: followed by the first projection `G_K → G`, it is
    `Spec.map x ≫ (schemeIso G).hom`.
  - `extPointEquiv_left_snd`: followed by the second projection to `Spec K`, it is the
    identity.

### Comparison map (section `Theta`)

- `scalarHom K G : K →+* Γ(G_K, ⊤)` pulls scalars back along the projection to `Spec K`.
  `coordHom K G : H →+* Γ(G_K, ⊤)` pulls coordinates back along the projection to `G`.
  They agree on `k` (`scalarHom_algebraMap`, from `pullback.condition`).
- `baseChangeAlgebra` (a local instance): the `k`-algebra structure on `Γ(G_K, ⊤)`
  through `coordHom`.
- `theta K G : K ⊗[k] H →+* Γ(G_K, ⊤)`, the product map of `scalarHom` and `coordHom`
  (`theta_tmul`: `a ⊗ h ↦ scalarHom a * coordHom h`). The proof never needs `theta` to be
  bijective. It only uses the evaluation formula below.
- `extPointEquiv_appTop_theta`: pulling `theta q` back along the `K`-point
  `extPointEquiv G x` gives the constant `extPoint x q`. Proof: by induction on tensors.
  On `a ⊗ h`, the two factors are computed by `extPointEquiv_left_snd` and
  `extPointEquiv_left_fst` together with `appTop_point`.

### Nullstellensatz (section `Nullstellensatz`; `K` algebraically closed)

- `exists_algHom_ne_zero`: in a finitely generated `K`-algebra `R` that is a domain, every
  `r ≠ 0` survives at some `K`-point `φ : R →ₐ[K] K`. Proof: `R` is a Jacobson ring, so
  the Jacobson radical of the prime `⊥` is `⊥`. Some maximal ideal `m` therefore misses
  `r`. The point is `pointOfMaximal K m`, from the Library's port
  `P2MW.S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed`.
- `eq_zero_of_forall_point`: on a reduced scheme `X` locally of finite type over `Spec K`,
  a global function `g` that vanishes at every `K`-point is zero. Proof: `X` is a Jacobson
  space. If `g ≠ 0`, then its basic open is nonempty because `X` is reduced
  (`basicOpen_eq_bot_iff`). So the basic open contains a closed point `x`
  (`nonempty_inter_closedPoints`). Mathlib's `pointOfClosedPoint` gives a `K`-point through
  `x`, and `g` does not vanish there.

### Maximality (section `Main`; `k` and `K` algebraically closed)

- `hopfKernel i`: for `i : B ⟶ G`, the ideal of `H` corresponding to the coordinate kernel
  `BorelExistence.coordinateKernel i` under `coordEquiv G`.
- `extPointEquiv_mem_range` (no algebraic closedness used): if `i` is a closed subgroup
  inclusion and `x : H →ₐ[k] K` kills `hopfKernel i`, then the `K`-point
  `extPointEquiv G x` of `G_K` lies in the range of `i_K`. Proof:
  `SubgroupFunctor.range_baseChangeHom` and `SubgroupFunctor.mem_baseChange` reduce this to
  the point of `x` over `Spec k`. On the affine scheme `G`, the ideal sheaf of `i` is
  contained in the kernel of that point (`ker_appTop_point`). So the point lifts through
  the closed immersion (`IsClosedImmersion.lift`).
- `maximal_baseChange`: let `G.X.hom` be affine and locally of finite type, and let `i` be
  a Borel inclusion (`IsBorelSubgroup i`). Let `B'` be a group scheme over `Spec K`,
  `i' : B' ⟶ G_K` a closed subgroup inclusion with `B'` smooth, connected and solvable,
  and `f : B_K ⟶ B'` with `f ≫ i' = i_K`. Then `f` is an isomorphism. Smoothness and
  connectedness of `G` are not assumed.

## Proof of `maximal_baseChange`

Write `P = hopfKernel i`. It is prime because `B` is smooth and connected
(`BorelExistence.coordinateKernel_isPrime`). The scheme `B'` is reduced, since it is smooth
over a field (`SmoothReducedProof.isReduced_of_smooth_over_field`).

1. **The solvable group `S`.** Let `S` be the subgroup of `WithConv (H →ₐ[k] K)` of those
   `x` whose `K`-point `extPointEquiv G x` lies in the range of `i'`. The `K`-points of `B'`
   form a solvable group (`isSolvableGroupScheme_iff_isSolvable_points`, as `K` is
   algebraically closed). The range of `i'` on `K`-points is its image, hence solvable, and
   `S` maps injectively into that range, so `S` is solvable.
2. **Points over `P` lie in `S`.** If `x` kills `P`, then by `extPointEquiv_mem_range` its
   `K`-point is `y ≫ i_K` for some `K`-point `y` of `B_K`. Since `i_K = f ≫ i'`, it is in
   the range of `i'`, so `x ∈ S`.
3. **The prime `Q`.** Let `Q ⊆ K ⊗[k] H` be the preimage under `theta` of the coordinate
   kernel of `i'`. That kernel is prime because `B'` is smooth and connected, so `Q` is
   prime. Moreover, `q ∈ Q` if and only if `extPoint x q = 0` for every `x ∈ S`:
   - If `q ∈ Q` and `x ∈ S`, write the `K`-point of `x` as `y ≫ i'`. Pulling back
     `theta q` gives `0` because `i'` kills it. By `extPointEquiv_appTop_theta`, the result
     is the constant `extPoint x q`.
   - Conversely, the pullback of `theta q` to `B'` vanishes at every `K`-point `z` of `B'`.
     Indeed, `z ≫ i'` is the `K`-point of some `x ∈ S`, and `extPointEquiv_appTop_theta`
     applies again. `B'` is reduced and locally of finite type, so
     `eq_zero_of_forall_point` shows the pullback is zero, that is, `q ∈ Q`.
4. **`Q` is contained in `K ⊗ P`.** Every `q ∈ Q` maps to zero in `K ⊗[k] (H ⧸ P)`. The ring
   `K ⊗[k] (H ⧸ P)` is a domain, because `H ⧸ P` is a domain and `k` is algebraically
   closed (the Library's `isDomain_tensorProduct_of_isAlgClosed`, after commuting the
   tensor factors). It is finitely generated over `K`. If the image of `q` were nonzero,
   `exists_algHom_ne_zero` would give a `K`-point `φ` not killing it. The composite
   `x : H → K ⊗[k] (H ⧸ P) → K` kills `P` and satisfies `extPoint x = φ ∘ baseMap`. By
   step 2, `x ∈ S`, and by step 3, `extPoint x q = 0`, a contradiction.
5. **Case 1: some `p ∈ P` has `1 ⊗ p ∉ Q`.** This case is impossible. Worker 1382's
   `exists_isPrime_lt_of_solvable` applies to `S`, `Q` and `P` (steps 1, 3 and 4). It gives
   a prime `𝔭 < P` of `H` and a solvable group `Γ` of `k`-points of `H` containing every
   `k`-point that kills `𝔭`. Transport `Γ` to rational points of `G` with
   `rationalPointEquiv`, and transport `𝔭` to global functions with `coordEquiv`. The
   result satisfies the hypotheses of `coordinateKernel_le_of_solvable_points` (module
   `BorelFieldExtensionKSide`), by `ker_appTop_point`. That lemma yields `P ≤ 𝔭`,
   contradicting `𝔭 < P`.
6. **Case 2: `1 ⊗ p ∈ Q` for every `p ∈ P`.** For each `K`-point `z` of `B'`, the point
   `z ≫ i'` is the point of some `x ∈ S`. By step 3, `x p = extPoint x (1 ⊗ p) = 0` for all
   `p ∈ P`. So by `extPointEquiv_mem_range`, `z ≫ i'` is in the range of `i_K`. Since `B'`
   is reduced and locally of finite type over the algebraically closed `K`, the Library's
   `UnipotentAllBorelsEnvelope.exists_factor_of_algClosed_points` gives a morphism
   `a : B'.X ⟶ B_K.X` over `Spec K` with `a ≫ i_K.hom.hom = i'.hom.hom`. Hence the
   coordinate kernel of `i_K` is contained
   in that of `i'`. The reverse containment is `BorelExistence.coordinateKernel_le`,
   applied to `f ≫ i' = i_K`. Equal coordinate kernels of two closed subgroup inclusions
   into the affine `G_K` force `f` to be an isomorphism
   (`BorelExistence.isIso_of_coordinateKernel_eq`).
