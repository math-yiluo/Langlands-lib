# A Čech model of the gauge complex

This is a helper module for the proof of
`Picard.ProperLineBundleHomRepresentabilityStatement` (task b792240c). Worker 1421
requested it with the exact statement of `exists_gauge_model` below. It is an
internal construction of that proof. It reduces the gauge complex of
`LineHom.GaugeComplex` to the Library's two-term complex theorem for the Čech
complex of a line bundle.

## Main theorem

`exists_gauge_model` has these hypotheses:

- `R` is a Noetherian commutative ring, and `p : Y ⟶ Spec R` is proper and flat;
- `𝒰` is an ordered affine cover of `Y` (`Scheme.OrderedAffineCover`);
- `α, β : ∀ i j, Γ(Y, 𝒰.U i ⊓ 𝒰.U j)ˣ` are unit cocycles
  (`CocycleGluing.IsCocycle`).

Under these hypotheses it gives:

- a two-term complex `G : CoherentBaseChange.TwoTermComplex R`, that is a linear
  map `G.d : G.C0 → G.C1` between finite free `R`-modules;
- `R`-linear maps `ψ0 : G.C0 → GaugeC0 p 𝒰` and `ψ1 : G.C1 → GaugeC1 p 𝒰`;
- a proof `comm` of `gaugeD p α β ∘ ψ0 = ψ1 ∘ G.d`.

The induced map `TwoChartCech.kerMapBaseChange G.d (gaugeD p α β) ψ0 ψ1 comm A`
goes from `ker (1_A ⊗ G.d)` to `ker (1_A ⊗ gaugeD p α β)`. It is bijective for
every commutative `R`-algebra `A` in the same universe.

## Construction and proof

The helper declarations live in the namespace `LineHom.CechModel`.

- `kerMapBaseChange_bijective_of_linearEquiv` is pure linear algebra. Suppose
  `ι0, ι1` map a complex `dK` into a complex `d`, and their kernel maps are
  bijective after base change to `A`. Suppose also that `e0, e1` are linear
  equivalences carrying `d` to `d'` (`d' ∘ e0 = e1 ∘ d`). Then the kernel maps of
  `e0 ∘ ι0, e1 ∘ ι1` into `d'` are also bijective after base change to `A`.
  Injectivity uses that `1_A ⊗ e0` is injective. For surjectivity, a kernel
  element `z` of `1_A ⊗ d'` is `(1_A ⊗ e0) w` for some `w`. Then `w` lies in the
  kernel of `1_A ⊗ d`, because `1_A ⊗ e1` is injective and the square commutes
  after base change.
- `gaugeCocycle α β i j = (α i j)⁻¹ * β i j`. `isCocycle_gaugeCocycle` shows that
  it is a cocycle when `α` and `β` are. The proof restricts all units to the
  triple intersection and computes in the commutative ring there.
- `coord g i hW m`, for a section `m` of the glued line bundle `glued g` over
  `W ≤ T i`, is the `i`-th component of `m`, restricted from `W ⊓ T i` back to
  `W`. `coord_smul_genSec_eq` says `coord g i hW m • genSec g hg i hW = m`; this is
  the Library lemma `eq_comp_smul_genSec`. Since `r ↦ r • genSec` is injective
  (`smul_genSec_bijective`), `coord_eq` characterises the coordinate. From it
  follow `coord_smul_genSec`, `coord_add`, `coord_neg`, `coord_smul`
  (`coord (a • m) = a * coord m`) and `coord_res` (compatibility with
  restriction).
- `idx0 i : 𝒰.Idx 0` is the one-element index `[i]`. `exists_eq_idx0` says every
  index of degree zero has this form, and `le_inter_idx0`, `inter_idx0_le`
  identify `𝒰.inter (idx0 i)` with `𝒰.U i`. `pair_le_inter` and `inter_le_pair`
  identify `𝒰.inter t` with `𝒰.U (t 0) ⊓ 𝒰.U (t 1)` for `t : 𝒰.Idx 1`.

From here on `γ` is a cocycle and `E = glued γ`. Write `OModulePresheaf.ofModules p E`
for the `R`-linear presheaf of sections of `E` used by the Library's Čech
complex.

- `cochain0Equiv p γ hγ` is an `R`-linear equivalence from the degree-zero Čech
  cochains of `E` on `𝒰` to `GaugeC0 p 𝒰`. It sends `c` to the family
  `i ↦ coord γ i (c [i])`, with the open `𝒰.inter [i]` replaced by `𝒰.U i`
  (`toGauge0`). The inverse `ofGauge0` sends `b` to `s ↦ b (s 0)| • genSec (s 0)`.
  `R`-linearity uses that `r • m` on sections is `scalarOn p r • m`, together with
  `res_scalarOn`.
- `res_idx0_eq_smul_genSec` and `res_eq_smul_genSec` give the restriction of a
  degree-zero cochain `c` at an index `s` with `s 0 = i`. Restricted to any
  `W ≤ U i`, it equals `(cochain0Equiv c i)| • genSec γ hγ i`.
- `cochain1Equiv p γ hγ α` is an `R`-linear equivalence from the degree-one
  cochains to `GaugeC1 p 𝒰`. It sends `x` to the family
  `t ↦ -α (t 0) (t 1) * coord γ (t 0) (x t)`, with `𝒰.inter t` replaced by
  `𝒰.U (t 0) ⊓ 𝒰.U (t 1)` (`toGauge1`). The inverse `ofGauge1` sends `y` to
  `t ↦ (-(α (t 0) (t 1))⁻¹ * y t)| • genSec (t 0)`. The lemmas
  `neg_units_inv_mul_neg_mul` and `neg_units_mul_neg_inv_mul` cancel the
  normalising factor.
- `gaugeD_comp_cochain0Equiv` is the commuting square
  `gaugeD p α β ∘ cochain0Equiv = cochain1Equiv ∘ d`, where `d` is the degree-zero
  Čech differential of `ofModules p (glued (gaugeCocycle α β))`. By
  `OModulePresheaf.d_apply`, `(d c) t = c [t 1]| - c [t 0]|`; the two faces of `t`
  are `[t 1]` and `[t 0]`. By `res_eq_smul_genSec` and `genSec_eq_smul_genSec`
  (`genSec (t 1) = γ (t 0) (t 1) • genSec (t 0)`), its coordinate at `t 0` is
  `b (t 1)| * γ (t 0) (t 1) - b (t 0)|`, where `b = cochain0Equiv c`. Multiplying
  by `-α (t 0) (t 1)` and using `α * α⁻¹ = 1` gives
  `b (t 0)| * α (t 0) (t 1) - β (t 0) (t 1) * b (t 1)|`, which is
  `gaugeD p α β b t`.

The proof of `exists_gauge_model` runs as follows.

1. Set `γ = gaugeCocycle α β` and `E = glued γ`.
2. `CocycleGluing.isLocallyFreeRankOne_glued` gives, around every point, an open
   `U` with `E.restrict U.ι ≅ unit`. Composing with
   `Scheme.Modules.restrictFunctorIsoPullback` gives the triviality hypothesis of
   `OModulePresheaf.exists_twoTermComplex_kerMapBaseChange_bijective_ofModules`.
   That theorem yields `G`, `ι0`, `ι1` into the Čech complex of `E` on `𝒰`, with
   bijective kernel maps after every base change.
3. Put `ψ0 = cochain0Equiv ∘ ι0` and `ψ1 = cochain1Equiv ∘ ι1`. Their commuting
   square follows from `gaugeD_comp_cochain0Equiv` and the square for `ι0, ι1`.
4. `kerMapBaseChange_bijective_of_linearEquiv` transfers the bijectivity.

## Provenance

The statement was fixed by Worker 1421 for task b792240c. The route follows
1421's suggestion: glue the cocycle `α⁻¹β`, apply the ported FLT two-term complex
theorem, and identify the Čech groups with the gauge groups through coordinates.
The normalisation by `-α (t 0) (t 1)` in degree one is the choice that makes the
square commute exactly. Identifying Čech cochains of a line bundle given by
transition functions with families of functions is the standard computation of
Čech cohomology through local trivialisations. All proofs here are internal.
