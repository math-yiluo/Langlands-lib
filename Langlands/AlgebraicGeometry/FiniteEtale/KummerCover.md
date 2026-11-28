# Kummer covers of a punctured spectrum after a finite étale base change

The module `Langlands.AlgebraicGeometry.FiniteEtale.KummerCover` fixes a ring
`R`, an element `t : R` and an `R`-algebra `R'`. When `R'` is a finite étale
`R`-algebra, it builds two finite étale covers of `U = Spec R[1/t]`: the
cover `Spec R'[1/t]` and, for a positive level `n` that is a unit of `R`, the
Kummer cover `Spec R'[1/t][X]/(X ^ n - t)`. On the Kummer cover it builds
the automorphisms `K c` that multiply the root by the powers `ζ ^ c` of an
`n`-th root of unity `ζ` of `R'`. For an `R`-algebra endomorphism `α` of `R'`
it builds the induced endomorphisms `AU α` of `Spec R'[1/t]` and `AX α` of
the Kummer cover; these need not be automorphisms. On geometric fibres the
root-scaling automorphisms realize the action of `μ_n` on the Kummer roots,
the finite-level form of the tame inertia action of SGA 7 I, Exposé I, 0.3
and 0.4. The intertwining relation `AX_comp_K`,
`AX α ≫ K c = K (q * c) ≫ AX α` when `α ζ = ζ ^ q`, is what computes this
finite Kummer action in the tame conjugation proof of the module
`Langlands.AlgebraicGeometry.FiniteEtale.TameConjugationProof`.

## Rings and morphisms

- `Loc t R'` is `Localization.Away (algebraMap R R' t)`, the ring `R'[1/t]`.
  `locHom t R' : R[1/t] →+* R'[1/t]` is the induced map, and `locHom_comp`
  says `R → R[1/t] → R'[1/t]` equals `R → R' → R'[1/t]`.
- `tt t R'` is the image of `t` in `R'[1/t]`, a unit (`isUnit_tt`).
  `kummerPoly t R' n = X ^ n - C (tt t R')` and
  `Kum t R' n = AdjoinRoot (kummerPoly t R' n)`. `root_pow` says
  `root ^ n = t` in `Kum t R' n`.
- `projU t R' : Spec R'[1/t] ⟶ Spec R[1/t]` and
  `projX t R' n : Spec (Kum t R' n) ⟶ Spec R'[1/t]` are `Spec.map` of
  `locHom` and of the algebra map. `projU_comp` says that the composite of
  `projU` with `Spec R[1/t] ⟶ Spec R` equals
  `Spec R'[1/t] ⟶ Spec R' ⟶ Spec R`.
- `isFinite_projU` (for `R'` finite over `R`) and `etale_projU` (for `R'`
  étale over `R`): finiteness is preserved by localization
  (`RingHom.localization_away_map_finite`). For étaleness, by `projU_comp`
  the composite with the open immersion `Spec R[1/t] ⟶ Spec R` is étale,
  and Mathlib's `Etale.of_comp` cancels the étale second factor.
- `isFinite_projX` (for `n ≠ 0`, since `X ^ n - t` is monic) and
  `etale_projX` (for `n ≠ 0` and `n` a unit of `R`): the latter is the
  package theorem `AdjoinRoot.etale_X_pow_sub_C`, which applies because `n`
  and `t` are units of `R'[1/t]`.
- `kappa t R' u hu`, for `u : R'` with `u ^ n = 1`, is the ring endomorphism
  of `Kum t R' n` that is the identity on `R'[1/t]` and sends the root to
  `u * root`. `kappa_comp_kappa` says `kappa u ∘ kappa v = kappa (u * v)`;
  `kappa_one` says `kappa 1` is the identity; `kappa_congr` transports along
  `u = v`. For `n ≠ 0` these relations make `kappa u` an automorphism with
  inverse `kappa (u ^ (n - 1))`; the module does not state this separately.
- `locEnd α`, for an `R`-algebra endomorphism `α` of `R'`, is the induced
  endomorphism of `R'[1/t]` (`locEnd_algebraMap`). It fixes `tt`
  (`locEnd_tt`) and is the identity on the image of `R[1/t]`
  (`locEnd_comp_locHom`). `kumEnd α` is the endomorphism of `Kum t R' n`
  that is `locEnd α` on `R'[1/t]` and fixes the root (`kumEnd_comp_of`,
  `kumEnd_root`). `kumEnd_comp_kappa` says
  `kumEnd α ∘ kappa u = kappa (α u) ∘ kumEnd α`; both sides agree on
  `R'[1/t]` and send the root to `α u * root`.
- `locHom_injective`: `R[1/t] → R'[1/t]` is injective if `R → R'` is.
  `of_injective`: if `R'[1/t]` is nontrivial and `n ≠ 0`, then
  `R'[1/t] → Kum t R' n` is injective (a monic polynomial of positive degree).

## Covers

Assume `R'` is finite and étale over `R`. Morphisms below are maps in the
Library's category `Cover (Spec R[1/t])` of finite étale schemes over
`Spec R[1/t]`.

- `coverU t R'` is `projU t R'`. `coverX t R' n hn0 hn`, for `n ≠ 0` and `n`
  a unit of `R`, is `projX t R' n ≫ projU t R'`. `proj t R' n hn0 hn` is the
  map `coverX ⟶ coverU` given by `projX`.
- `kumHom` turns a ring endomorphism of `Kum t R' n` that is the identity on
  the image of `R[1/t]` into an endomorphism of `coverX`. `kumHom_comp_proj`:
  if it is the identity on `R'[1/t]`, the map lies over the identity of
  `coverU`.
- `AX t R' n hn0 hn α` is `kumHom` of `kumEnd α`, and `AU t R' α` is the
  endomorphism of `coverU` given by `locEnd α`. `AX_comp_proj`:
  `AX α ≫ proj = proj ≫ AU α`.
- Fix `ζ : R'` with `ζ ^ n = 1`. `K t R' hn0 hn hζn c` is `kumHom` of
  `kappa (ζ ^ c)`: the root is multiplied by `ζ ^ c`. Then
  `K_comp_proj : K c ≫ proj = proj`, `K_comp_K : K c ≫ K d = K (c + d)`,
  `K_zero : K 0 = 𝟙`, and `AX_comp_K`: if `α ζ = ζ ^ q`, then
  `AX α ≫ K c = K (q * c) ≫ AX α`. These four relations are proved by
  comparing ring maps out of `AdjoinRoot` on `R'[1/t]` and on the root
  (`AdjoinRoot.ringHom_ext`). On spectra the composition order is reversed.
  Since `n ≠ 0` here, `K_comp_K` and `ζ ^ n = 1` make each `K c` an
  automorphism with inverse `K ((n - 1) * c)`; the module does not state
  this separately.

## Geometric fibres

- `exists_eq_comp_K`: suppose `ζ ^ l - 1` is a unit of `R'` for `0 < l < n`.
  Let `x : Spec Ω ⟶ Spec R[1/t]` be a point with values in a field. If two
  points `p₁ p₂ : Fiber x (coverX ...)` have the same image in `coverU`, then
  `p₂ = p₁ ≫ (K c).hom` for some `c`. Proof: write `pᵢ = Spec fᵢ` for ring
  maps `fᵢ : Kum t R' n → Ω`. They agree on `R'[1/t]`, so the images `rᵢ` of
  the root satisfy `r₁ ^ n = r₂ ^ n = t ≠ 0` in `Ω`. Thus `r₂ / r₁` is an
  `n`-th root of unity. The image of `ζ` in `Ω` is a primitive `n`-th root of
  unity, because the images of `ζ ^ l - 1` are units
  (`IsPrimitiveRoot.mk_of_lt`). Hence `r₂ / r₁` is a power `ζ ^ c`
  (`IsPrimitiveRoot.eq_pow_of_pow_eq_one`), and `f₂ = f₁ ∘ kappa (ζ ^ c)` by
  `AdjoinRoot.ringHom_ext`.
- `nonempty_fiber`: if `R'` is a domain, `R → R'` is injective and
  `t ≠ 0` in `R'`, then every point `x : Spec Ω ⟶ Spec R[1/t]` with `Ω`
  separably closed lifts to `coverX`. Proof: `R'[1/t]` is a domain, so the
  composite `R[1/t] → R'[1/t] → Kum t R' n` is finite and injective. Every
  prime of `R[1/t]` therefore has a prime above it (lying over,
  `RingHom.IsIntegral.comap_surjective`). The package lemma
  `Scheme.Hom.exists_lift_of_isSepClosed` then lifts `x` along the finite
  étale morphism `projX ≫ projU`.
