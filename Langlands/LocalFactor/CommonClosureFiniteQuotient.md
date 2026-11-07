# Finite-image representations of common-closure Weil subgroups

Helper module for the proof of
`Langlands.LocalFactor.CommonClosureDegreeZeroGenerationStatement`. In Tate's
proof of (2.3.1) (*Number theoretic background*, Corvallis 1979), a
representation of a Weil group with finite image is viewed as a representation
of a finite quotient. Brauer's theorem is applied to that quotient, and the
result is carried back to the Weil group. This module does this for the actual
common-closure Weil subgroups `W_E = weilSubgroup F E` of
`Langlands/LocalFactor/CommonClosure.lean`. The main result is
`finiteImage_sub_mem_span'`: for a continuous finite-image representation `B`
of `W_E`, the exact class `[B] - (dim B) · [1]` is an integral combination of
the generators `characterDifferenceInductionGenerators F E`, which are the
inductions `induce F E L h ([η] - [η'])` of differences of continuous character
lines of intermediate Weil subgroups `W_L`.

Throughout, `Γ = Field.absoluteGaloisGroup F.Carrier` and `localProjection F`
is the continuous projection `W_F → Γ`.

## A closed kernel (`Langlands.FiniteRepresentation`)

- `isClosed_ker_of_isContinuous A hc`: the kernel of a continuous
  finite-dimensional complex representation is closed. It is the preimage of
  the point `1` under the continuous map to continuous linear endomorphisms.

## Kernels and subgroups (`Langlands.LocalFactor.CommonClosure`)

- `exists_galois_kernel F E B hc hf`: if `B` is a continuous representation of
  `W_E` with finite image, then there is an open normal subgroup `U` of `Γ`
  such that `B w = 1` for every `w ∈ W_E` with `localProjection F w ∈ U`.

  Proof. The kernel `K` of `B` is open, by the Library lemma
  `Weil.open_kernel_of_finite_range_of_closed` together with
  `isClosed_ker_of_isContinuous`. It has finite index because `B` has finite
  image. Its image `M` in `W_F` is open of finite index, since `W_E` is open
  in `W_F`. The permutation representation `R` of `W_F` on functions on
  `W_F ⧸ M` is trivial on the normal core of `M`, which is open by Mathlib's
  `Subgroup.isOpen_of_isClosed_of_finiteIndex`. So `R` is continuous with
  finite image. The Library's `Weil.Local.localWeilGaloisTypeFor` then gives a
  continuous Galois representation `τ` of `Γ` with `R = τ ∘ localProjection F`.
  Its kernel `U` is open by
  `Weil.open_kernel_of_continuous_nonarchimedean_representation`, and it is
  normal. If `localProjection F w ∈ U`, then `R w = 1`. Applying this to the
  basis function at the coset of `1` gives `w ∈ M`, so `w ∈ K` and `B w = 1`.

- `exists_extension_of_le F E U hU H hH`: let `U` be an open normal subgroup
  of `Γ`, and let `H` be a subgroup of `W_E` that contains every `w` with
  `localProjection F w ∈ U`. Then there is an `L : Extension F` with
  `E.field ≤ L.field` and `w ∈ H ↔ w ∈ weilSubgroup F L` for all `w ∈ W_E`.

  Proof. Let `P : W_E → Γ` be the restricted projection and
  `K = P(H) ⊔ U`. Then `K` is open, hence closed. By infinite Galois theory
  (`InfiniteGalois.fixingSubgroup_fixedField`, `InfiniteGalois.isOpen_iff_finite`)
  its fixed field `L₁` is finite over `F` with fixing subgroup `K`. Take
  `L = L₁ ⊔ E.field`, whose fixing subgroup is `K ⊓ Gal(Fbar/E)`
  (`IntermediateField.fixingSubgroup_sup`). Since `w ∈ W_E` already projects
  into `Gal(Fbar/E)`, the condition `w ∈ W_L` reduces to `P w ∈ K`. Every
  element of `H` satisfies this. Conversely, if `P w ∈ K`, then because `U` is
  normal, `P w = P h · u` with `h ∈ H` and `u ∈ U`
  (`Subgroup.mem_sup_of_normal_right`). So `P (h⁻¹ w) = u ∈ U`, hence
  `h⁻¹ w ∈ H` and `w ∈ H`.

- `inflate_induce_oneDimensional F E L h π hπ hsurj S hS χ`: let `Q` be a
  finite group, `π : W_E →* Q` surjective with open kernel, `S ≤ Q` with
  `π w ∈ S ↔ w ∈ W_L` for all `w ∈ W_E`, and `χ : S →* ℂˣ`. Then there is a
  continuous character `η` of `W_L` such that the inflation along `π` (the map
  `ExactGrothendieckGroup.inflate` of `FiniteInflation`) of the finite induced
  class `Ind_S^Q χ` is `induce F E L h [η]`. Here `η` is `χ` composed with the
  map `W_L → S` induced by `π`. It is continuous because its kernel contains
  an open subgroup (`Weil.continuous_of_open_kernel`). The proof applies
  `ExactGrothendieckGroup.inflate_ofClass_induce` with `T = W_L ∩ W_E`. The
  matched representation of `T` is the character line of `η` restricted along
  the nested-Weil equivalence `nestedWeilEquiv F E L h`. Then
  `ExactGrothendieckGroup.restrict_ofRepresentation` identifies the result with
  the common-closure induction `induce F E L h`.

## The finite-image comparison (`Langlands.LocalFactor`)

- `finiteImage_sub_mem_span F hBrauer E B hc hf`: this is the conditional
  form. It assumes, as `hBrauer`, the finite degree-zero Brauer inclusion for
  every finite group `Q` in the universe `uF`: every virtual representation of
  `Q` whose character vanishes at `1` lies in the integral span of
  `FiniteRep.degreeZeroBrauerGenerators Q`. For `B`
  continuous with finite image on `W_E` (carrier universe `max uF uV`), it
  concludes

  `ofRepresentation (ContinuousPredicate F E) ⟨B, hc⟩ - (B.rank : ℤ) • characterClass 1
    ∈ span ℤ (characterDifferenceInductionGenerators F E)`.

  Proof. `exists_galois_kernel` gives `U`. Since `Γ` is compact, `U` has
  finite index. Let `N` be the preimage of `U` in `W_E`, which is normal,
  open and of finite index. Let `Q = W_E ⧸ N` and `π` the quotient map. Then
  `B` factors as `ρ ∘ π` (`QuotientGroup.lift`). The finite virtual class
  `x = [ρ] - (dim B) · [1]` has character value `0` at `1`, so by `hBrauer` it
  lies in the span of the finite generators. The inflation `Φ` along `π`
  sends `x` to `[B] - (dim B) · [1]`. This uses `inflate_ofClass` and the
  equivalence `FiniteRepresentation.inflateEquiv` between the inflation of the
  coordinate model of `ρ` and `B`. For the trivial line the two sides already
  agree definitionally. Finally, `Φ` maps each finite generator
  `Ind_S^Q (χ - χ')` into the span. Apply `exists_extension_of_le` to
  `H = π⁻¹(S)` (which contains `N`) to get `L` with `π w ∈ S ↔ w ∈ W_L`. Then
  `inflate_induce_oneDimensional`, applied to `χ` and to `χ'`, gives the
  generator `induce F E L h ([η] - [η'])`.

- `finiteImage_sub_mem_span' F E B hc hf`: the same conclusion without
  hypotheses. `hBrauer` is supplied by the Library's finite degree-zero Brauer
  theorem `FiniteRep.DegreeZeroBrauer.finiteDegreeZeroBrauer`, which states
  `degreeZeroBrauerSpan Q = degreeZeroVirtualReps Q`.
