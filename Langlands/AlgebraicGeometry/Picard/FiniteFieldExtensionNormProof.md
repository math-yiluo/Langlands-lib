# Norms of functions along the base change of a finite field extension (proof)

The theorem `finiteFieldExtensionNorm` proves the Library statement
`FiniteFieldExtensionNormStatement`. Let `L / K` be a finite field extension and let
`X` be a scheme with a morphism `p : X ⟶ Spec K`. Write
`π : X_L = X ×_{Spec K} Spec L ⟶ X` for the first projection of the actual pullback.
The proof gives a family of monoid homomorphisms `Γ(X_L, π⁻¹ U) →* Γ(X, U)`, one for
every open `U` of `X`, with the three required properties. The proof first constructs
the norm over affine opens of `X` as the determinant of multiplication. It then extends
these maps to all opens with the published construction `AffineNormGluing.norm` from
`Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNormGluing`. No hypothesis is
added. The fields may have any characteristic, the extension may be inseparable or
trivial, and the proof assumes nothing about `X` or `p`. All declarations except the
final theorem are in the namespace
`Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNorm`.

## Part A: norms of finite free algebras

These lemmas concern a commutative `A`-algebra `B` with a finite basis.

- `basis_repr_map` and `norm_map_of_basis`: take ring maps `σ : A →+* A'` and
  `φ : B →+* B'` that are compatible with the algebra maps and send a basis of `B` to a
  basis of `B'` indexed by the same finite type. Then `φ` sends coordinates to
  coordinates, so `σ (Algebra.norm A f) = Algebra.norm A' (φ f)`. The proof applies
  `RingHom.map_det` to the matrix of left multiplication.
- `dvd_algebraMap_norm`: in a finite free algebra, `f` divides the image of its norm in
  `B`. The proof uses Cayley–Hamilton (`Algebra.aeval_self_charpoly_lmul`). The constant
  coefficient of the characteristic polynomial of multiplication by `f` is `f` times an
  element of `B`. That coefficient equals the norm up to a sign
  (`LinearMap.det_eq_sign_charpoly_coeff`).
- `norm_mem_comap`: if `f` lies in an ideal `Q` of `B`, then `Algebra.norm A f` lies in
  the contraction of `Q`. This follows from the divisibility above.
- `exists_prime_over_of_norm_mem`: if `Algebra.norm A f` lies in a prime `P` of `A`,
  then some prime `Q` of `B` lying over `P` contains `f`. Suppose `a ∈ A` maps into the
  ideal `(f)`. Then `a ^ n` is the norm of `a` (`Algebra.norm_algebraMap_of_basis`), and
  this norm is a multiple of the norm of `f`, so `a ^ n ∈ P` and hence `a ∈ P`. So the
  contraction of `(f)` lies in `P`, and going-up for the integral extension
  `A → B` (`Ideal.exists_ideal_over_prime_of_isIntegral`) gives `Q ⊇ (f)` over `P`.

## Part B: the norm over an affine open

Here `bc K L` abbreviates `Spec.map (CommRingCat.ofHom (algebraMap K L))`. Also,
`coefX p V : K ⟶ Γ(X, V)` and `coefXL L p V : L ⟶ Γ(X_L, π⁻¹ V)` are the structure
maps that come from `p` and from the second projection, each followed by restriction.

- `isPushout_affine`: if `V` is affine, the square formed by `coefX`,
  `K ⟶ L`, `π.app V` and `coefXL` is a pushout of commutative rings. The open
  restriction `π⁻¹ V ⟶ V` is a pullback of `π` (`isPullback_morphismRestrict`). Pasting
  it with the defining pullback square shows that `π⁻¹ V` is the pullback of the affine
  scheme `V` along `Spec L ⟶ Spec K`. The lemma `isPushout_appTop_of_isPullback`
  then shows that global sections form a pushout. Finally `IsPushout.of_iso` transports
  this pushout to the sections over `V` and `π⁻¹ V` through `Scheme.ΓSpecIso` and
  `Scheme.Opens.topIso`. The helper lemmas `map_comp_map_eq` and `map_comp_map_self`
  simplify the resulting composites of presheaf restriction maps.
- `exists_basis`: the pushout is a base change of algebras
  (`CommRingCat.isPushout_iff_isPushout`). So the image of `Module.finBasis K L` under
  `coefXL` is a basis of `Γ(X_L, π⁻¹ V)` over `Γ(X, V)` (`IsBaseChange.basis`). This
  basis is indexed by `Fin (finrank K L)`.
- `normAff L p V` is `Algebra.norm Γ(X, V)` on `Γ(X_L, π⁻¹ V)`, where the algebra
  structure comes from `π.app V`. It is defined for every open `V`, but the proof uses
  it only on affine opens.
- `normAff_res`: for affine `V' ≤ V`, restriction commutes with `normAff`. Both
  restriction maps send the chosen basis over `V` to the chosen basis over `V'`, since
  both bases are images of the same `K`-basis of `L`. So `norm_map_of_basis` applies.
- `normAff_app`: `normAff` of `π.app V g` equals `g ^ finrank K L`. This is
  `Algebra.norm_algebraMap_of_basis`.
- `isAffineHom_fst`: `π` is affine because it is a base change of the affine morphism
  `bc K L`. Hence the preimage of an affine open is affine.
- `fromSpec_mem_basicOpen`: for an affine open `U`, a point `hU.fromSpec P` lies in the
  basic open of `a` exactly when `a ∉ P`.
- `mem_basicOpen_normAff`: let `V` be affine, `x ∈ V`, and `f` a section over `π⁻¹ V`.
  Then `x` lies in the basic open of `normAff L p V f` exactly when every point `y` with
  `π y = x` lies in the basic open of `f`. Points of `V` and of the affine open `π⁻¹ V`
  correspond to primes through `fromSpec`. Under this correspondence `π` is contraction
  of primes along `π.app V` (`IsAffineOpen.SpecMap_appLE_fromSpec`). The direction from
  left to right uses `norm_mem_comap`. The converse uses
  `exists_prime_over_of_norm_mem`. Both inclusions are proved.

## Part C: assembly

The final theorem `Langlands.AlgebraicGeometry.Picard.finiteFieldExtensionNorm` takes
`Nm := AffineNormGluing.norm π (fun V => normAff L p V) hN`, where `hN` is
`normAff_res`. The published lemmas then give the three clauses.

- `AffineNormGluing.naturality` gives clause 1.
- `AffineNormGluing.degree`, with `d = finrank K L` and `normAff_app`, gives clause 2.
- `AffineNormGluing.basicOpen` gives clause 3. Its affine input is the set equality
  `basicOpen (normAff L p V f) = {x ∈ V | ∀ y, π y = x → y ∈ basicOpen f}`. This
  equality follows from `mem_basicOpen_normAff`, together with
  `X.basicOpen_le` for the condition `x ∈ V`.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

This proof follows the local construction of Stacks Project Section 31.18 (tag 0BCX),
Lemma 31.18.6 (tag 0BD2, registered source
`stacks-norms-field-ample-descent-2026-10-26`, file `0BCX.html`). There the norm of a
finite locally free morphism is the determinant of multiplication on a local basis.
Here the basis over an affine open comes from a `K`-basis of `L`. The property about
zeros is proved directly through prime ideals and going-up, not through base change
to residue fields. The intermediate lemmas are internal to this proof.
