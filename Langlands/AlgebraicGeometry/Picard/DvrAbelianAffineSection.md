# An affine generation open meeting the special fibre

Author: Worker 171.

Module `Langlands.AlgebraicGeometry.Picard.DvrAbelianAffineSection`, namespace
`Langlands.AlgebraicGeometry.Picard.DvrAbelianGeometry`.

## Declarations

- `exists_maximal_generization`: in a noetherian quasi-sober `T₀` space, every point
  `z` of a closed set `E` has a generization `g ∈ E` with no proper generization in
  `E` (a generic point of an irreducible component of `E` through `z`, via
  `genericPoints.closure` and finiteness of components).
- `exists_generic_generization_not_mem`: for an abelian scheme over a DVR and an
  affine open `W` of the total space containing a point of the special fibre, every
  point outside `W` is a specialization of a point outside `W` lying over the generic
  point. Take a maximal generization `g` of the point outside `W`. If `g` were in the
  special fibre, the generic point `ξ` of the special fibre (which lies in `W`) and a
  generic-fibre generization `y₀` of `ξ` would give a chain `y₀ ⤳ ξ ⤳ g` with all
  proper generizations of `g` in `W`; stalks are domains and factorial
  (`smoothDVR_factorialStalks`), so
  `FactorialAffineComplement.false_of_generization_chain` rules this out.
- `exists_affine_section_meeting_closedFibre`: let `R` be a discrete valuation
  domain, `A` an abelian scheme over `Spec R` and `L` a line bundle on its total
  space whose pullback to the residue-field fibre at `⊥` is ample. Then for some
  `m ≥ 1` there is `τ : L.powSections m` with `IsAffineOpen (L.sectionOpen τ)` and a
  point `x ∈ L.sectionOpen τ` with `A.X.hom x = IsLocalRing.closedPoint R`.

## Proof of the last theorem as implemented

Fix a uniformizer `π` and let `D` be the principal open of `unifX A π`, the
complement of the special fibre.

1. *Generic section.* `isAmple_basicOpen` makes `L` ample on `D`; at a point of `D`
   choose a section of a power `L ^ n` on `D` with affine generation open, and
   globalize it with `exists_global_section_of_basicOpen` to `t₀` with
   `D ∩ L.sectionOpen t₀` that affine open.
2. *Division.* `not_forall_unifX_pow_smul` bounds the powers of `unifX` dividing `t₀`.
   Take the largest `j` with `t₀ = unifX ^ j • t`. If the generation open of `t` missed
   the special fibre, `exists_eq_unifX_smul` would divide once more; so
   `U := L.sectionOpen t` contains a special point `x₁`. Multiplying by a unit on `D`
   does not change generation opens, so `U ∩ D` is still the affine open of step 1.
3. *Affine shrinking.* Choose an affine open `W ⊆ U` containing `x₁`; it contains
   the generic point of the special fibre and a generic-fibre point `y₁`. In the
   affine `U ∩ D` choose `r₀` with `y₁ ∈ D(r₀) ⊆ W`. Since `U ∩ D` is the principal
   open of `unifRes A π U` in the quasi-compact quasi-separated `U`
   (`isLocalization_basicOpen_of_qcqs`), `r₀` is `r₁ / unifRes ^ k` with
   `r₁ ∈ Γ(U)`. Divide `r₁` by `unifRes` as often as possible
   (`eq_zero_of_forall_unifRes_pow_dvd`, `exists_eq_unifRes_mul`) to get `r` whose
   principal open meets the special fibre and agrees with `D(r₀)` on `U ∩ D`.
4. *`D(r) ⊆ W`.* A point of `D(r)` over the generic point lies in `D(r₀) ⊆ W`. A point
   of `D(r)` over the closed point outside `W` would, by
   `exists_generic_generization_not_mem`, have a generic-fibre generization outside
   `W`, still in the open `D(r)`, contradicting the first case. Hence `D(r)` is a
   principal open of the affine `W`, so it is affine.
5. *Back to sections.* The published `principalGenerationOpenLift` turns the
   function `r` on `U = L.sectionOpen t` into a global section of a positive power of
   `L ^ n` with generation open exactly `D(r)`; `tensorPowMulIso` rewrites it as a
   section of `L ^ (n * N)`.

## Provenance

The strategy is Raynaud's, as presented by N. Guo, *Ample sheaves on group
homogeneous spaces over Prüfer bases*, arXiv 2209.02443v1 (registered source
`guo-ample-sheaves-prufer-2209-02443-v1`): Corollary 3.6 (printed p.7) shrinks an
open with affine generic fibre to an affine principal open meeting the special fibre,
using Lemma 3.4 (printed pp.6–7) that the complement of an affine open containing the
maximal points of the fibres is flat of pure codimension one. Worker 171 read printed
pp.6–8 and 12–18. The implementation specializes to a discrete valuation ring and to
the generation open of a line-bundle section, replaces Lemma 3.4 by the factorial
argument of `FactorialAffineComplement`, and adds the division by the uniformizer
needed to make the section meet the special fibre.
