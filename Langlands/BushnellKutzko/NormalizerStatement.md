# The normalizer `𝔎(𝔄)` of a hereditary order (Bushnell–Kutzko 1993, §1.1, pp. 21–22)

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open
subgroups*, Annals of Math. Studies 129 (1993), `bushnell-kutzko-1993-admissible-dual-gln`,
§1.1, printed pp. 21–22 (PDF pp. 33–34; PDF page = printed page + 12). BK93 proves the
normalizer claim for `U^n(𝔄)`, `n ≥ 1`, on pp. 21–22. For `n = 0` it refers to the proof of
Bushnell–Fröhlich 1985 [BF2] (1.3.10) (`bushnell-frohlich-1985-nonabelian-congruence-gauss-sums`,
printed p. 220). The remaining claims are recalled without proof.

`NormalizerStatement : Prop` is an unproved statement. A later `lean.proof@1` task will prove
it. It uses the definitions of `Langlands.BushnellKutzko.LatticeChain` and
`Langlands.BushnellKutzko.UnitFiltration`.

## Quantifiers

For every nonarchimedean local field `F : Type u`, every `F`-vector space `V : Type v` and every
`𝔬_F`-lattice chain `𝓛 : LatticeChain 𝒪[F] F V`. The universes are independent. As in
`RadicalFiltrationStatement`, the existence of `𝓛` forces `V` to be finite-dimensional and
nonzero, so no further hypotheses are needed.

Notation: `A = Module.End F V`, `G = (Module.End F V)ˣ`, `𝔄 = 𝓛.order`,
`𝔓^n = 𝓛.endFiltration n`, `U^n(𝔄) = 𝓛.unitFiltration n`, `𝔎(𝔄) = 𝓛.stabilizer`, and for
`g ∈ 𝔎(𝔄)` the shift `𝓛.stabilizerValuation g`, the integer `d` with `g L_i = L_{i+d}`.

## Conclusions

The statement is a conjunction of four parts.

1. **For every `n ≥ 0`, `U^n(𝔄) ⊆ 𝔎(𝔄)` and `U^n(𝔄)` is normal in `𝔎(𝔄)`** (BK93 p. 21:
   "the `U^n(𝔄)`, for `n ≥ 0`, are normal subgroups of it"). Normality is
   `((𝓛.unitFiltration n).subgroupOf 𝓛.stabilizer).Normal`.
2. **`𝔎(𝔄)` is the `G`-normalizer of `𝔄`.** For every `g ∈ G`: `g ∈ 𝔎(𝔄)` if and only if
   `g 𝔄 g⁻¹ = 𝔄`, where `g 𝔄 g⁻¹` is the image of `𝔄` under `a ↦ g a g⁻¹`. BK93 (p. 21) writes
   `𝔎(𝔄) = {x ∈ G : x⁻¹ 𝔄 x = 𝔄}`. The task writes `{g : g 𝔄 g⁻¹ = 𝔄}`. The two sets agree
   because each is closed under inverses. The Lean version follows the task.
3. **For every `n ≥ 0`, `𝔎(𝔄)` is the `G`-normalizer of `U^n(𝔄)`** (BK93 p. 21: "`𝔎(𝔄)` is
   precisely the `G`-normaliser of `U^n(𝔄)`, for any given `n ≥ 0`"). Formally,
   `Subgroup.normalizer (𝓛.unitFiltration n) = 𝓛.stabilizer`.
4. **For `g ∈ 𝔎(𝔄)` with shift `d`:**
   - `𝓛.valuation g = d`. That is, BK93's valuation `v_𝔄(g) = max {n : g ∈ 𝔓^n}` of (1.1.3)
     equals the integer by which `g` shifts the chain.
   - `g 𝔄 = 𝔓^d` and `𝔄 g = 𝔓^d` as subsets of `A`, the images of `𝔄` under left and right
     multiplication by `g`.

   BK93 (p. 22): "if `x ∈ 𝔎(𝔄)`, it is easy to see that `v_𝔄(x) = n`, where `n` is given by
   `x𝔄 = 𝔄x = 𝔓^n`".

## Relation to the task

The task's S2 asks for the normality of `U^n(𝔄)` in `𝔎(𝔄)` (part 1), `𝔎(𝔄)` as the normalizer
of `𝔄` (part 2) and `g𝔄 = 𝔄g = 𝔓^{v_𝔄(g)}` (part 4). Part 4 also records that the two integers
called `v_𝔄(g)` agree: the shift `stabilizerValuation`, used in the task's definition item 5,
and the valuation of `g` as an element of `A`. Part 3, the normalizer of `U^n(𝔄)`, is the
remaining claim of the same BK93 paragraph and is included for completeness.
