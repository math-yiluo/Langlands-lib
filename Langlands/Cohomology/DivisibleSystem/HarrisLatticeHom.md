# Freeness of Harris's lattice and Harris's system Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DivisibleSystem.ReductionLattice`
(`mono_powSMul_action_iff`, `mono_powSMul_harrisLatticeAction`),
`Langlands.Cohomology.DivisibleSystem.IHomReduction`
(`ihomReductionSystem`, `reductionSystemIhomIso`,
`freeOverPowQuotient_permutation_ihom_reduction`,
`freeOverPowQuotient_subgroup_permutation_ihom_reduction`) and
`Langlands.Global.AdelicFunctoriality.LocalDegree` (the instance
`finitePlacesAbove_nonempty`: every finite place of `ℚ` lies under a finite
place of `L`). Through their imports it uses `powSMul`
(`Langlands.Cohomology.DivisibleSystem`), `reductionSystem` and
`mono_powSMul_one_iff_isSMulRegular`
(`Langlands.Cohomology.DivisibleSystem.Reduction`), `FreeOverPowQuotient`
(`Langlands.Cohomology.DivisibleSystem.FreeTorsionProjective`),
`Induction.permutation`
(`Langlands.Representation.Induction.PermutationModule`), `FinitePlacesAbove`
(`Langlands.Global.AdelicFunctoriality.Norm`), Worker 57's
`Langlands.Shimura.Coefficients.Lattice` (`CoefficientIntegers`,
`StableCoefficientLattice` with `carrier` and its finiteness and freeness
instances) and `Langlands.Shimura.Coefficients.HarrisLattice`
(`HarrisCoefficientIntegers`, `harrisLattice`, `harrisLatticeEquiv`,
`dependentProductSubmoduleEquiv`, `harrisLatticeAction`), and
`algebraicCompactCoefficientLattice`
(`Langlands.Shimura.Coefficients.AlgebraicCompactCoefficient`). From Mathlib
it uses `Module.Basis.equivFun`, `Module.Basis.ofEquivFun`,
`Module.Basis.coe_ofEquivFun`, `Module.Basis.ofEquivFun_equivFun`,
`Module.Basis.map`, `Pi.single_apply`, `Submodule.IsLattice.rank'`,
`Module.finrank_baseChange`, `Module.finBasisOfFinrankEq`,
`Module.Free.of_basis`, `Module.finrank_eq_card_basis`, `Pi.nontrivial_at`
and `Rep.trivial`.

## Conventions

`ℓ` and `m` are natural numbers. `powSMul ℓ m X` is the published
endomorphism "multiplication by `ℓ ^ m`" of an object `X` of a preadditive
category. For a commutative ring `R`, a group `G` and representations `A`,
`L` in `Rep R G`, `Hom_R(A, L)` is Mathlib's `(Rep.ihom A).obj L`, the
`R`-linear maps `A → L` with `g` acting by `φ ↦ L.ρ g ∘ φ ∘ A.ρ g⁻¹`. When
multiplication by `ℓ` is a monomorphism on `L`, the published
`reductionSystem ℓ L` is the `ℓ`-divisible system (Harris 1999, (2.1)) of
the cokernels `L / ℓ ^ m L` of `powSMul ℓ m L`, and the published
`ihomReductionSystem ℓ A L`, for `A` projective over `R`, is the
`ℓ`-divisible system `m ↦ Hom_R(A, L / ℓ ^ m L)`. The published predicate
`FreeOverPowQuotient ℓ m P` states that `P` is killed by `ℓ ^ m` and is free
over `(R ⧸ (ℓ ^ m))[G]`, where `(ℓ ^ m)` is the ideal
`Ideal.span {((ℓ : R) ^ m)}` and `k[G]` is `MonoidAlgebra k G`.
`Rep.trivial R G V` is Mathlib's representation of `G` on the `R`-module `V`
with the trivial action (an abbreviation for
`Rep.of (Representation.trivial R G V)`). `Induction.permutation R G X M` is
the published permutation representation on `M[X] = X →₀ M` for a `G`-set
`X` and an `R`-module `M`, with `G` permuting the points of `X`.

## Bases over a product of rings (namespace `Langlands.Cohomology.DivisibleSystem`)

`R i` is a commutative ring and `M i` an `R i`-module for each `i` in an
index type `ι`, and `κ` is a finite type. The product `∏ i, M i` is a module
over the product ring `∏ i, R i`, acting componentwise. Mathlib's
`Pi.basis` concerns products of modules over one ring; this section treats
the product ring.

- `piEquivFunOfBases R M b`: for bases `b i` of `M i` over `R i`, all indexed
  by `κ`, the linear equivalence over `∏ i, R i` between `∏ i, M i` and
  `κ → ∏ i, R i` whose `k`-th coordinate of `x` is the family of the `k`-th
  coordinates (`Module.Basis.equivFun`) of the components `x i`. The inverse
  sends `c` to the family whose `i`-th component has coordinates
  `k ↦ c k i` in the basis `b i`.
- `piBasisOfBases R M b`: the basis of `∏ i, M i` over `∏ i, R i` indexed by
  `κ` with these coordinates (`Module.Basis.ofEquivFun`).
- `piBasisOfBases_apply`: its `k`-th vector has `i`-th component `b i k`.
  Both sides are images of the `k`-th standard coordinate vector under the
  inverse coordinate maps (`Module.Basis.coe_ofEquivFun`,
  `Module.Basis.ofEquivFun_equivFun`), compared coordinatewise with
  `Pi.single_apply`.

## Stable lattices at one place

For the remaining sections, `A` is a finite-dimensional `ℚ`-algebra with
Worker 13's involution `σ : AlgebraInvolution ℚ A`, `L : Type u` a number
field, `W : Type u` an `L`-module and `ρ` an algebraic representation of
`σ.baseChange L` on `W`, as in the published `HarrisLattice`; `p` is a finite
place of `ℚ`. Here `l` is a finite place of `L` above `p`, `U` a subgroup of
`σ.FiniteAdelicPoints`, and `Λ` is Worker 57's
`StableCoefficientLattice ρ p l U`: a submodule `Λ.carrier` over the
valuation ring `CoefficientIntegers l` (written `𝒪_l`) of `L_l ⊗_L W`, where
`L_l` is the completion `FiniteCompletion L l`, that is a full lattice
(`Submodule.IsLattice` for `L_l`) and stable under `U`. The published
instances make `Λ.carrier` finite and free over `𝒪_l`.

- `finrank_stableCoefficientLattice Λ`: `Λ.carrier` has rank
  `Module.finrank L W` over `𝒪_l`. By Mathlib's `Submodule.IsLattice.rank'`,
  the rank of a full lattice over `𝒪_l` equals the dimension of the ambient
  space over its fraction field `L_l`, here `L_l ⊗_L W`, whose dimension is
  `Module.finrank L W` by `Module.finrank_baseChange`.
- `stableCoefficientLatticeBasis Λ`: a basis of `Λ.carrier` over `𝒪_l`
  indexed by `Fin (Module.finrank L W)` (`Module.finBasisOfFinrankEq`).

## Harris's lattice

From here on `W` is finite over `L` and `U` is a compact open level of
`σ.FiniteAdelicPoints`. Worker 57's `harrisLattice ρ p U` (written `𝓛`) is a
submodule of Harris's coefficient module `(L ⊗_ℚ ℚ_p) ⊗_L W` over
`HarrisCoefficientIntegers L p`, the product `∏_{l | p} 𝒪_l` of the valuation
rings at the places of `L` above `p`. The published `harrisLatticeEquiv ρ p U`
followed by `dependentProductSubmoduleEquiv` is a linear equivalence over
`∏_{l | p} 𝒪_l` from `𝓛` onto the product of the stable lattices
`(algebraicCompactCoefficientLattice ρ p l U).carrier` at the places `l`
above `p`.

- `harrisLatticeBasis ρ p U`: a basis of `𝓛` over `∏_{l | p} 𝒪_l` indexed by
  `Fin (Module.finrank L W)`: `piBasisOfBases` of the bases
  `stableCoefficientLatticeBasis` of the stable lattices at the places above
  `p`, all indexed by `Fin (Module.finrank L W)`, transported to `𝓛` along
  the inverse of this equivalence (`Module.Basis.map`).
- `harrisLattice_free` (instance): `𝓛` is free over `∏_{l | p} 𝒪_l`
  (`Module.Free.of_basis`).
- `finrank_harrisLattice`: `𝓛` has rank `Module.finrank L W` over
  `∏_{l | p} 𝒪_l`. The product ring is nontrivial because some place of `L`
  lies above `p` (`finitePlacesAbove_nonempty`, `Pi.nontrivial_at`), and the
  rank is the cardinality of the basis `harrisLatticeBasis`
  (`Module.finrank_eq_card_basis`).

The freeness depends on all stable lattices having the same rank: over a
product of rings, a product of free modules of different ranks over the
factors is not free (a remark, not formalized).

## Harris's system Hom(M[X], 𝓛 / ℓ ^ m 𝓛)

Here `ℓ` is nonzero (`[NeZero ℓ]`), `G : Type u` is a group, and
`R = HarrisCoefficientIntegers L p`.

- `isSMulRegular_harrisLattice`: `(ℓ : R)` is a non-zero-divisor on `𝓛`.
  The published instance `mono_powSMul_harrisLatticeAction` states that
  multiplication by `ℓ` is a monomorphism on the published action
  `harrisLatticeAction ρ p U` of `U.subgroup` on `𝓛`, which by the published
  `mono_powSMul_action_iff` means that `x ↦ ℓ • x` is injective on `𝓛`.
- `mono_powSMul_harrisLatticeTrivial` (instance): multiplication by `ℓ` is a
  monomorphism on `Rep.trivial R G 𝓛`, by the published
  `mono_powSMul_one_iff_isSMulRegular`.

Let `X : Type u` be a `G`-set and `M : Type u` a finite free `R`-module.

- `harrisPermutationIhomSystem ℓ ρ p U G X M` (the entry declaration) is the
  published `ihomReductionSystem ℓ` for the permutation representation
  `Rep.of (Induction.permutation R G X M)` (projective over `R`, being free)
  and `Rep.trivial R G 𝓛`: the `ℓ`-divisible system in `Rep R G` with level
  `m` equal to `Hom_R(M[X], 𝓛 / ℓ ^ m 𝓛)`.
- `reductionSystemHarrisPermutationIhomIso`: the reduction system of
  `Hom_R(M[X], 𝓛)` is isomorphic to `harrisPermutationIhomSystem`, by the
  published `reductionSystemIhomIso`.
- `freeOverPowQuotient_harrisPermutationIhomSystem_obj h m`: if `X` is finite
  and `G` acts on `X` with trivial stabilizers (`h`), level `m` of
  `harrisPermutationIhomSystem` satisfies `FreeOverPowQuotient ℓ m`. This is
  the published `freeOverPowQuotient_permutation_ihom_reduction`, whose
  hypothesis that the target lattice is free over `R` is the instance
  `harrisLattice_free`.
- `freeOverPowQuotient_harrisPermutationIhomSystem_subgroup_obj Q S m`: for a
  subgroup `S` of a finite group `Q : Type u`, acting on `Q` by left
  multiplication, level `m` of `harrisPermutationIhomSystem ℓ ρ p U S Q M`
  satisfies `FreeOverPowQuotient ℓ m` as a representation of `S`, by the
  published `freeOverPowQuotient_subgroup_permutation_ihom_reduction`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999) (Worker 61 read the rendered scanned pages):

- §3, printed p.306 (one-based PDF page 8): "`L_v = L ⊗_ℚ ℚ_v`" for a place
  `v` of `ℚ`, so `L_ℓ` is in general a finite product of finite extensions of
  `ℚ_ℓ`.
- §3, printed p.307 (one-based PDF page 9): "Let `𝒪` denote the ring of
  integers of `L_ℓ`, and let `𝓛_W` be a `K_ℓ`-stable `𝒪`-lattice in
  `W(L)`." (The published `harrisLattice` places it in
  `(L ⊗_ℚ ℚ_p) ⊗_L W`.)
- §4, printed p.311 (one-based PDF page 13): "Let the `K_ℓ`-modules `(ρ, W)`
  and `𝓛 = 𝓛_W` be as in §3; let `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m` for any `m`."
- proof of Proposition 4.10, printed p.312 (one-based PDF page 14): "Since
  `C^j_m(ẽ)^{H_p}` and `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free
  `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it follows that the maps (4.10.3) are
  surjective for all `m`."

Harris's `𝒪` is a product of the rings of integers of the factors of
`L_ℓ`, and Harris does not state that `𝓛_W` is free over `𝒪`. The published
`harrisLattice` represents `𝓛_W` over `∏_{l | p} 𝒪_l`, and the published
freeness result of IHomReduction requires the lattice to be free over the
coefficient ring; this module proves that freeness and the rank
`dim_L W` for the published lattice. With `R` in the role of `𝒪`,
`𝓛 / ℓ ^ m 𝓛` in the role of `𝓛_m` (reading `𝒪_m` as `𝒪/ℓ^m𝒪`, as in the
published ReductionLattice), `M[X]` in the role of `𝒪[C_p/H_p]^M` with
`M = R^M`, and `G` in the role of `S(ẽ)/H_p` acting freely on `X = C_p/H_p`,
`freeOverPowQuotient_harrisPermutationIhomSystem_obj` is Harris's second
freeness claim for the published lattice. That `S(ẽ)/H_p` acts trivially on
`𝓛` and freely on `C_p/H_p` is our reading of Harris's setting, as in the
published PermutationDual and IHomReduction modules. In Harris `ℓ` is a
rational prime and the coefficient place is the place `ℓ` of `ℚ`; here `p`
is any finite place of `ℚ` and `ℓ` any nonzero natural number, not tied to
`p`, as in the published ReductionLattice. The product basis, the rank and
freeness statements and all proofs are ours. The module is derived.

## Scope

The Lean modules are `Hom_R(M[X], 𝓛 / ℓ ^ m 𝓛)`, the `R`-linear maps from
`M[X]` into the reduction; as in the published IHomReduction, their
identification with Harris's `𝒪_m`-linear maps out of `𝒪_m[C_p/H_p]^M` is
not formalized, nor is the identification of `𝓛 ⊗_𝒪 𝒪_m` with
`𝓛 / ℓ ^ m 𝓛` beyond the published ReductionAdic. The group `G` acts
trivially on `𝓛`; the action of the level `U` on `𝓛`
(`harrisLatticeAction`) is not used in the Hom system. The module does not
treat `C^j_m(ẽ)^{H_p}` or Harris's identifications (4.7) and (4.8), and
makes no statement about cohomology. Everything concerns the categories
`Rep` of representations of abstract groups, with `G`, `X`, `M` and the
coefficient data in one universe `u`.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
