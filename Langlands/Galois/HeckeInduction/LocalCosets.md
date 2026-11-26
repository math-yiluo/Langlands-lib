# Right cosets of the image of a finite extension and the places above a base place

Module `Langlands.Galois.HeckeInduction.LocalCosets`, name space
`Langlands.GaloisRepresentation.HeckeInduction`. Let `E/K` be an extension of number fields,
`e : AlgebraicClosure K →ₐ[K] AlgebraicClosure E` a closure embedding and `H` the image of
`restrictionAlongClosure e` in `Gal(K̄/K)`. Let `v` be a finite place of `K`, `w` a finite place
of `E` above `v`, and `g = FiniteExtension.completionMap v w : K_v → E_w`. `LocalGroup`,
`localInertia`, `localResidueAction`, `IsGeometricFrobeniusLift` and `residueCardinality` are
those of `Langlands.Galois.CompatibleFamily`; `r_v` denotes
`Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v)`, the map used by
`atFinitePlace`, and similarly `r_w`; `ρ` denotes `Field.absoluteGaloisGroup.map g`.

## Closure maps and the comparison element

- `closureHom f` is Mathlib's chosen closure embedding `chosenClosureEmbedding f` over a field
  homomorphism `f`, as a ring homomorphism; `closureHom_algebraMap`, `closureHom_map`
  (it intertwines `Field.absoluteGaloisGroup.map f g` with `g`) and `closureHom_bijective`
  restate the published facts of `QuadraticFrobeniusPatching.Local` in this form.
- `exists_closureChange`: two embeddings of `AlgebraicClosure F` into a field that agree on `F`
  differ by an element of `Gal(F̄/F)` (`AlgHom.restrictNormal'`).
- `globalClosureMap e w : K̄ → Ē → \bar{E_w}` and `localClosureMap v w : K̄ → \bar{K_v} → \bar{E_w}`
  are composites of closure maps; both restrict on `K` to `K → E → E_w → \bar{E_w}`
  (`globalClosureMap_algebraMap`, `localClosureMap_algebraMap`, the latter by
  `completionMap_coe`). `placeConj e v w : Gal(K̄/K)` satisfies
  `globalClosureMap (placeConj x) = localClosureMap x` (`placeConj_spec`).
- `placeConj_relation`, `conj_placeConj_map`: for `a ∈ Gal(\bar{E_w}/E_w)`,
  `placeConj * r_v (ρ a) * placeConj⁻¹ = restrictionAlongClosure e (r_w a)`. Both sides are
  compared after applying the injective map `globalClosureMap`, using `placeConj_spec` and the
  intertwining properties of the three closure maps.
- `localClosureMap_placeConj_inv`: `placeConj⁻¹` moves the transported copy of `t ∈ E` to an
  element of `K̄` whose image in `\bar{E_w}` is `t` itself.
- `mem_range_of_conj_mem`, `conj_mem_iff_mem_range`: for `b ∈ Gal(\bar{K_v}/K_v)`,
  `placeConj * r_v b * placeConj⁻¹ ∈ H` if and only if `b` is in the image of `ρ`. The forward
  direction applies the published `mem_map_range_iff`: `b` is in the image when it fixes the
  copy of `E_w` in `\bar{K_v}`. The hypothesis shows that `b` fixes the copy of the image of `E`,
  so the two `K_v`-algebra maps `E_w → \bar{K_v}` agree on `E`; their equalizer is a
  `K_v`-subalgebra containing the image of `E`, hence everything
  (`subalgebra_eq_top_of_algebraMap_mem`). The backward direction is `conj_placeConj_map`.
- `completionMap_isAlgebraic`, `completionMap_norm_le_one_iff`: `E_w` is algebraic over `K_v`,
  and the completion map preserves and reflects the unit ball (from `local_finite` and
  `completionMap_mem_integers_iff`); these are the hypotheses of the published residue
  comparisons `closureIntegerEquiv`, `closureResidueEquiv`, `map_mem_inertia_iff` and
  `residueAction_map_eq_pow`.
- `absGal_apply_inv_apply`, `absGal_inv_apply_apply`: cancellation for the action of
  `Gal(K̄/K)` on `K̄`.

## The prime attached to a coset

- `cosetEmbedding e v x : E → \bar{K_v}` is `t ↦ closureHom (x⁻¹ (transportedEmbedding e t))`;
  `cosetIntegers e v x` is its restriction to `𝓞 E`, with values in the spectral integers of
  `\bar{K_v}` (integral elements lie there, `integral_iff_mem_spectralIntegers`), and
  `cosetPrime e v x` is the kernel of the reduction of `cosetIntegers e v x` to the residue field
  (`mem_cosetPrime_iff`).
- `cosetPrime_mul`: `cosetPrime (h * x * r_v b) = cosetPrime x` for `h ∈ H` and
  `b ∈ Gal(\bar{K_v}/K_v)`: `h⁻¹` fixes the transported copy of `E`, `r_v b` becomes the action
  of `b` on `\bar{K_v}`, and an automorphism acts on the spectral integers and their residues by
  ring automorphisms (`LocalGalois.residueHom_apply`). `cosetPrime_eq_of_coset_eq` is the form
  used for two elements `x * r_v b` and `x' * r_v b'` in the same right coset of `H`.
- `cosetPrime_placeConj`: `cosetPrime e v (placeConj e v w) = w.asIdeal`. By
  `localClosureMap_placeConj_inv` the published isomorphism `closureIntegerEquiv` of spectral
  integers carries `cosetIntegers (placeConj) t` to the image of the completion integer of `t`;
  being a ring isomorphism of local rings it preserves the maximal ideals, and the residue of the
  completion integer of `t` vanishes exactly when `t ∈ w`
  (`Global.CompletionResidue.residueMap_eq_zero_iff`).

## Frobenius and inertia

Let `γ` be a geometric Frobenius lift at `v` and `f = f(w|v)` the inertia degree.

- `residueAction_inv_pow`: `(γ⁻¹) ^ m` acts on the residue closure by `y ↦ y ^ (q_v ^ m)`.
- `residueCardinality_eq_pow`: `q_w = q_v ^ f` (`Ideal.absNorm_pow_inertiaDeg`);
  `one_lt_residueCardinality`: `1 < q_v`.
- `pow_not_mem_range`: for `0 < m < f`, `γ ^ m` is not in the image of `ρ`. If `γ ^ m = ρ a`,
  then by `closureResidueEquiv_action` the inverse `a⁻¹` acts on the residue closure of `E_w` by
  `z ↦ z ^ (q_v ^ m)`; it fixes the residue field of `E_w`, so every element `r` of that field,
  which has `q_w = q_v ^ f` elements, satisfies `r ^ (q_v ^ m) = r`. The polynomial
  `X ^ (q_v ^ m) - X` has at most `q_v ^ m` roots, so `q_v ^ f ≤ q_v ^ m`, contradicting `m < f`.
- `pow_inertiaDeg_mem_range`: if local inertia at `v` lies in the image of `ρ`, so does `γ ^ f`.
  For a geometric Frobenius lift `a` at `w`, `ρ a` and `γ ^ f` have the same residue action
  (`residueAction_map_eq_pow`), so they differ by an element of local inertia.
- `inertia_mem_range`: if, for every `i` in local inertia, `r_v i` fixes every conjugate
  `y (transportedEmbedding e t)`, then local inertia lies in the image of `ρ`, by
  `mem_range_of_conj_mem`.

## The normal closure

- `inducedPlace v M` is the Library's `inducedPrime v M` of a subextension `M` of `K̄`, as a
  finite place of `M`; `inducedPlace_liesOver`: it lies over `v`.
- `inertia_fixes_of_unramified`: if `M` is finite and normal over `K` and its induced place is
  unramified over `K`, then `r_v i` fixes `M` pointwise for every `i` in local inertia. Both
  `γ` and `γ * i` are geometric Frobenius lifts
  (`isGeometricFrobeniusLift_mul_of_mem_localInertia`); the inverses of their images restrict to
  arithmetic Frobenius elements at the induced prime (`arithmeticFrobeniusAt_inducedPrime`), which
  coincide at an unramified prime (`ClassFieldTheory.Global.Artin.eq_of_isArithFrobAt_mapAlgHom`),
  so `r_v i` restricts to the identity of `M`.
- `normalClosureField` is `IntermediateField.normalClosure K E K̄`. `inertia_fixes_conjugates`:
  if its induced place at `v` is unramified, `r_v i` fixes every conjugate
  `y (transportedEmbedding e t)`, which lies in the normal closure
  (`AlgHom.fieldRange_le_normalClosure`).

## Provenance

This is a derived, internal module. It formalizes, for the Library's explicit closure embeddings,
completion maps and residue actions, the classical comparison between the decomposition and
inertia groups of a place of `K̄` above `w` and the absolute Galois group of `E_w`, and the
description of the right cosets of `Gal(K̄/E)` by the embeddings of `E` into `\bar{K_v}`. It
builds on the Library's `QuadraticFrobeniusPatching.Local` residue comparisons, `FrobeniusDensity`
induced primes and the local degree results of `Global.AdelicFunctoriality.LocalDegree`. The
implemented proofs are those described above.
