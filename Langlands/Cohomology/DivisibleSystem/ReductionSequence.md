# Reduction sequences for inverse limits of ℓ-divisible systems

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DivisibleSystem.AdicLimit` (`powSMul_comp_π`,
`isCokernelOfFaithful`, `mono_powSMul_one_of_faithful`, and the instance
`rep_forget₂_preservesLimitsOfShape_nat`) and
`Langlands.Cohomology.DivisibleSystem.InverseLimit` (`inverseLimit`,
`inverseLimitHomologyComparison`, `inverseLimitHomologyComparison_π`,
`isIso_inverseLimitHomologyComparison_of_finite`,
`isIso_inverseLimitHomologyComparison_rep`). Through their imports it uses the
published `DivisibleSystem` with `tower`, `obj`, `powSMul_eq_zero` and
`degree`, together with `powSMul`, `comp_powSMul`, `map_powSMul` and
`shortComplex_exact_congr` (`Langlands.Cohomology.DivisibleSystem`);
`reductionπ` and `mono_powSMul`
(`Langlands.Cohomology.DivisibleSystem.Reduction`); and Worker 3's
`FiniteCohomologyInverseLimitStatement`
(`Langlands.Cohomology.InverseLimit.Statement`), which is used only as a
hypothesis.

From Mathlib it uses `ShortComplex`, `ShortComplex.Exact`,
`ShortComplex.ShortExact` with `ShortExact.δ`, `ShortExact.comp_δ`,
`ShortExact.δ_comp`, `ShortExact.homology_exact₁`, `homology_exact₂` and
`homology_exact₃` (the homology sequence of a short exact sequence of
complexes), `ShortComplex.exact_iff_of_epi_of_isIso_of_mono`,
`ShortComplex.Exact.mono_cokernelDesc`, `ShortComplex.Exact.epi_kernelLift`,
`ShortComplex.exact_of_g_is_cokernel`, `ShortComplex.exact_of_iso`,
`ShortComplex.shortExact_of_iso`, `ShortComplex.isoMk`,
`HomologicalComplex.shortExact_of_degreewise_shortExact`,
`HomologicalComplex.homologyMap` with `homologyMap_comp` and
`homologyMap_zero`, `HomologicalComplex.homologyFunctor`,
`HomologicalComplex.eval`, `cokernel.desc`, `kernel.lift`,
`epi_of_isColimit_cofork`, `isLimitOfPreserves`, `limit.cone`, `limit.π`,
`cancel_epi` and `asIso`.

All declarations are in the namespace `Langlands.Cohomology`; those after
`homologyMap_powSMul` are in `Langlands.Cohomology.DivisibleSystem`.

## Conventions

`C` is an abelian category, `ℓ` and `n` are natural numbers, and
`powSMul ℓ n X : X ⟶ X` is the published multiplication by `ℓ ^ n`. For an
object `M`, `M / ℓ ^ n` denotes the cokernel of `powSMul ℓ n M` (Mathlib's
`cokernel`; the published `reductionπ ℓ M n` is its projection) and
`M[ℓ ^ n]` the kernel of `powSMul ℓ n M` (Mathlib's `kernel`). In Milne's
notation these are `M^(ℓ^n)` and `M_{ℓ^n}`.

`T` is an `ℓ`-divisible system (the published `DivisibleSystem`), with levels
`T n = T.obj n` and inverse system `T.tower : ℕᵒᵖ ⥤ _`. For a system of
complexes `T : DivisibleSystem (HomologicalComplex C c) ℓ` (complex shape `c`
on an index type `ι`), `H^i(X)` is the homology `X.homology i` of a complex
`X` in degree `i`, and `c.Rel i j` says that the differential goes from
degree `i` to degree `j` (for cochain complexes indexed by `ℤ`, `j = i + 1`).
`L : Cone T.tower` is a cone with vertex `L.pt` and projections
`L.π.app (op n) : L.pt ⟶ T n`; `hL : IsLimit L` says that `L.pt` is the
inverse limit. The published `inverseLimit T` is `limit T.tower`, and
`inverseLimitHomologyComparison T q : H^q(limit T.tower) ⟶ lim_m H^q(T m)` is
the canonical comparison `limit.post` (Harris's Lemma 2.8 map).

## Four-term sequences and the homology sequence

- `cokernelKernelShortComplex f g δ h hfg hgδ hδh`: for maps
  `f : A ⟶ B`, `g : B ⟶ X`, `δ : X ⟶ D`, `h : D ⟶ E` with
  `f ≫ g = 0`, `g ≫ δ = 0` and `δ ≫ h = 0`, the short complex
  `coker f ⟶ X ⟶ ker h` whose maps are `cokernel.desc f g` and
  `kernel.lift h δ`.
- `cokernelKernelShortComplex_shortExact`: if the short complexes
  `A ⟶ B ⟶ X`, `B ⟶ X ⟶ D` and `X ⟶ D ⟶ E` are exact, then
  `0 ⟶ coker f ⟶ X ⟶ ker h ⟶ 0` is short exact. Proof: exactness of
  `B ⟶ X ⟶ D` transfers to `coker f ⟶ X ⟶ D` (morphism of short complexes
  with first component the epimorphism `cokernel.π f` and identities
  elsewhere), and then to `coker f ⟶ X ⟶ ker h` (identities and the
  monomorphism `kernel.ι h`); `cokernel.desc f g` is a monomorphism by
  exactness at `B`, and `kernel.lift h δ` an epimorphism by exactness at `D`.
- `homologyCokernelKernelShortComplex hS i j hij`: for a short exact sequence
  `hS` of complexes `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` and `c.Rel i j`, the short complex
  `coker (H^i X₁ ⟶ H^i X₂) ⟶ H^i X₃ ⟶ ker (H^j X₁ ⟶ H^j X₂)` built from the
  map induced by `X₂ ⟶ X₃` and Mathlib's connecting map `hS.δ i j hij`;
  `homologyCokernelKernelShortComplex_shortExact`: it is short exact (from the
  homology sequence).
- `homologyMap_powSMul`: the map induced on `H^i` by `powSMul ℓ n K` is
  `powSMul ℓ n (H^i K)` (the published `map_powSMul` for the homology
  functor).

## The reduction sequence of a cone

- `reductionShortComplex L n` (abbreviation): the short complex
  `L.pt ⟶ L.pt ⟶ T n` with maps `powSMul ℓ n L.pt` and the projection, for a
  cone `L` over `T.tower` in any abelian category (composite zero by the
  published `powSMul_comp_π`).
- `reductionShortComplex_shortExact_of_faithful hL F n`: if `L` is a limit
  cone and `F : C ⥤ ModuleCat R` is additive, faithful, preserves finite
  limits, finite colimits and limits indexed by `ℕᵒᵖ`, then
  `0 ⟶ L.pt ⟶ L.pt ⟶ T n ⟶ 0` is short exact. Proof: the projection is a
  cokernel of `ℓ ^ n` (published `isCokernelOfFaithful`), hence an
  epimorphism and the sequence is exact; `ℓ ^ n` is a monomorphism by the
  published `mono_powSMul_one_of_faithful` and `mono_powSMul`.

For a system of complexes `T : DivisibleSystem (HomologicalComplex C c) ℓ`:

- `reductionShortComplex_shortExact_of_degreewise hL F n`: if `C` has limits
  indexed by `ℕᵒᵖ`, `L` is a limit cone, and `F : C ⥤ ModuleCat R` is as
  above, then `0 ⟶ L.pt ⟶ L.pt ⟶ T n ⟶ 0` is a short exact sequence of
  complexes. Proof: degreewise, the evaluation of `L` in degree `q` is a limit
  cone over the published system `T.degree q`, and the previous result
  applies.
- `reductionShortComplex_shortExact_moduleCat T n`: for
  `T : DivisibleSystem (CochainComplex (ModuleCat R) ℤ) ℓ` (`R` commutative)
  and the limit cone `limit.cone T.tower`, with `F` the identity functor.
- `reductionShortComplex_shortExact_rep T n`: for
  `T : DivisibleSystem (CochainComplex (Rep k G) ℤ) ℓ` (`k` commutative, `G`
  a monoid) and `limit.cone T.tower`, with `F` the forgetful functor to
  `ModuleCat k`.

## Milne's sequence for the limit complex

For a system of complexes `T`, a cone `L` over `T.tower` and `n`, let
`hS : (reductionShortComplex L n).ShortExact`, and let `c.Rel i j`.

- `reductionSequence hS i j hij`: the short complex
  `H^i(L.pt) / ℓ ^ n ⟶ H^i(T n) ⟶ H^j(L.pt)[ℓ ^ n]`, the
  `cokernelKernelShortComplex` of
  `H^i(L.pt) ⟶ H^i(L.pt) ⟶ H^i(T n) ⟶ H^j(L.pt) ⟶ H^j(L.pt)` (maps `ℓ ^ n`,
  the map induced by the projection, the connecting map `hS.δ i j hij`, and
  `ℓ ^ n`).
- `reductionπ_reductionSequence_f`: `reductionπ ℓ (H^i(L.pt)) n` followed by
  the first map is the map `H^i(L.pt) ⟶ H^i(T n)` induced by the projection.
- `reductionSequence_g_ι`: the second map followed by the inclusion
  `H^j(L.pt)[ℓ ^ n] ⟶ H^j(L.pt)` is the connecting map.
- `reductionSequence_shortExact` (Milne, Lemma 1.11, for `H^r(L.pt)`):
  `0 ⟶ H^i(L.pt) / ℓ ^ n ⟶ H^i(T n) ⟶ H^j(L.pt)[ℓ ^ n] ⟶ 0` is short exact.
  Proof: the homology sequence of `0 ⟶ L.pt ⟶ L.pt ⟶ T n ⟶ 0`, whose maps on
  `H^i(L.pt)` and `H^j(L.pt)` are `ℓ ^ n` by `homologyMap_powSMul`, and
  `cokernelKernelShortComplex_shortExact`.

## Milne's form, with lim_m H^r(T m)

Here `C` has limits indexed by `ℕᵒᵖ`, `L` is `limit.cone T.tower` and
`hS : (reductionShortComplex (limit.cone T.tower) n).ShortExact`.

- `powSMul_homology_eq_zero T n i`: `ℓ ^ n` is zero on `H^i(T n)`.
- `inverseLimitReductionSequence hS i j hij hi`, for
  `hi : IsIso (inverseLimitHomologyComparison T i)`: the short complex
  `(lim_m H^i(T m)) / ℓ ^ n ⟶ H^i(T n) ⟶ (lim_m H^j(T m))[ℓ ^ n]`, the
  `cokernelKernelShortComplex` of the maps `ℓ ^ n`, the projection
  `lim_m H^i(T m) ⟶ H^i(T n)`, the connecting map followed by the comparison
  in degree `j`, and `ℓ ^ n`. The hypothesis `hi` is used to show that the
  projection followed by the connecting map vanishes (it is the map induced by
  the projection precomposed with the inverse of the comparison).
- `reductionπ_inverseLimitReductionSequence_f`,
  `inverseLimitReductionSequence_g_ι`: the first map after the projection to
  the cokernel is the projection `lim_m H^i(T m) ⟶ H^i(T n)`; the second map
  followed by the inclusion of the `ℓ ^ n`-torsion is the connecting map
  followed by the comparison in degree `j`.
- `inverseLimitReductionSequence_shortExact hS i j hij hi hj`: if the
  comparisons in degrees `i` and `j` are isomorphisms (`hi`, `hj`), then
  `0 ⟶ (lim_m H^i(T m)) / ℓ ^ n ⟶ H^i(T n) ⟶ (lim_m H^j(T m))[ℓ ^ n] ⟶ 0` is
  short exact. Proof: the three exact pieces of the homology sequence are
  transported along the comparison isomorphisms.
- `inverseLimitReductionSequence_shortExact_of_finite hF T hfin n q`: for
  `T : DivisibleSystem (CochainComplex (ModuleCat R) ℤ) ℓ` with finite
  cohomology in every level and degree (`hfin`), given
  `hF : FiniteCohomologyInverseLimitStatement R`,
  `0 ⟶ (lim_m H^q(T m)) / ℓ ^ n ⟶ H^q(T n) ⟶ (lim_m H^(q+1)(T m))[ℓ ^ n] ⟶ 0`
  is short exact (the comparisons are isomorphisms by the published
  `isIso_inverseLimitHomologyComparison_of_finite`).
- `inverseLimitReductionSequence_shortExact_rep hF T hfin n q`: the same for
  `T : DivisibleSystem (CochainComplex (Rep k G) ℤ) ℓ` with finite cohomology,
  given `hF : FiniteCohomologyInverseLimitStatement k`, as a short exact
  sequence of representations (published
  `isIso_inverseLimitHomologyComparison_rep`).

## Provenance and interpretation

Milne, *Étale Cohomology* (1980), Chapter V, §1 (Worker 61 read the scanned
pages; printed p.165 in the rendered image, the others in the text layer):

- printed p.165 (one-based PDF page 179), Lemma 1.11: "Let F = (F_n) be an
  l-adic sheaf on X_et such that each F_n is flat as a sheaf of
  Z/(l^n)-modules and H^r(X, F_n) is finite for all r and n. Then H^r(X, F) is
  finitely generated as a Z_l-module and there are exact sequences,
  0 → H^r(X_et, F)^(l^n) → H^r(X_et, F_n) → H^{r+1}(X_et, F)_{l^n} → 0 for
  all r and n." Milne's proof tensors
  `0 → Z/(l^n) → Z/(l^{n+s}) → Z/(l^s) → 0` with `F_{n+s}`, takes cohomology
  sequences and passes to the inverse limit, using that inverse limits of
  exact sequences of finite abelian groups are exact.
- printed p.164 (one-based PDF page 178): "The cohomology groups of an l-adic
  sheaf F are defined to be H^r(X, F) = lim H^r(X, F_n)."
- printed p.xiii (one-based PDF page 13), Notation: "The kernel and cokernel
  of multiplication by n, M → M, are denoted respectively by M_n and M^(n)."

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §2, printed p.306 (one-based PDF page 8):
"Lemma 2.8. For every q, there is a canonical isomorphism
H^q(lim C_m^•(U(ẽ)_F̄)) ≅ lim H_c^q(U(ẽ)_F̄, Z/ℓ^mZ)", for the inverse limit
of an `ℓ`-divisible system of complexes (published `InverseLimit`).

Interpretation. Our route differs from Milne's. We work with an
`ℓ`-divisible system of complexes `T` (standing for complexes computing the
cohomology of the `F_n`, as in Harris's `C_m^•`) and its limit complex
`L = lim_m T m`: the sequence `0 → L → L → T n → 0` (multiplication by
`ℓ ^ n`, then the projection) is short exact, and its homology sequence gives
`reductionSequence_shortExact` for `H^r(L)`. Milne's `H^r(X, F)` is
`lim_n H^r(X, F_n)`; the comparison `H^r(L) → lim_m H^r(T m)` is Harris's
Lemma 2.8, and `inverseLimitReductionSequence_shortExact` states the sequence
for `lim_m H^r(T m)` when this comparison is an isomorphism in degrees `r`
and `r + 1`. For complexes of modules or representations with finite
cohomology, this is derived from Worker 3's
`FiniteCohomologyInverseLimitStatement`, taken as a hypothesis and not
proved here. Milne's flatness hypothesis on the `F_n` corresponds to the
published `DivisibleSystem` axioms, which are assumed of `T`. The statements
and proofs are ours; the module is derived.

## Scope

Finite generation of `H^r(X, F)` over `ℤ_ℓ` is not formalized, nor is any
étale sheaf, `l`-adic sheaf, or identification of `T` with complexes computing
étale cohomology; the module is about `ℓ`-divisible systems of complexes in
abelian categories. Short exactness of `0 → L → L → T n → 0` is proved for
limit cones preserved by a faithful exact functor to modules (in particular
for complexes of modules and of representations); elsewhere it is the
hypothesis `hS`. The form with `lim_m H^r(T m)` assumes the comparison
isomorphisms (`hi`, `hj`), or `FiniteCohomologyInverseLimitStatement` with
finite cohomology. No topology, continuity, or `ℚ_ℓ`-coefficients are
treated.

Source registrations: Milne 1980, `milne-1980-etale-cohomology`, SHA-256
`0a2f02682f82db8385e4dc6c77c7113900b11d6c313f34f8b354a3a9a391d232`; Harris
1999, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
