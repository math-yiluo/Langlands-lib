# Proof that twisting by a large power of an ample line bundle is ample

`Langlands.AlgebraicGeometry.Picard.amplePowerTwist` proves the published
proposition `Langlands.AlgebraicGeometry.Picard.AmplePowerTwistStatement.{u}`
from module `Langlands.AlgebraicGeometry.Picard.AmplePowerTwistStatement`.
The theorem's type is that proposition itself, in an arbitrary universe `u`,
with no further hypotheses. For every scheme `X : Scheme.{u}`, every ample
`H : LineBundle X` and every `N : LineBundle X`, it produces `b₀ : ℕ` such
that every `P : LineBundle X` with
`Nonempty (P.obj ≅ tensorObj N.obj (tensorPow H.obj b))` and `b₀ ≤ b` is
ample. The statement pair and everything it imports are unchanged.

The helper declarations are in namespace
`Langlands.AlgebraicGeometry.Picard.AmplePowerTwist`. Like the Library module
`Modules.LineBundleSectionClearingProof`, whose public chart machinery
(namespace `Langlands.SchemeModule.SectionClearing`) it reuses, the module sets
`backward.isDefEq.respectTransparency false`.

## Overview

The proof has four steps.

1. **Gluing a family over an open** (`exists_global_of_charts_family`). This is
   a variant of the Library's `SectionClearing.exists_global_of_charts`. It
   starts from a compatible family of sections over an open `U`, not from
   global sections multiplied by a function on `U`.
2. **Extension along a twisted tower** (`exists_twist_section`). This is
   Stacks Lemma 18.2 (tag 01PW) for a twist. Let `X` be quasi-compact and
   quasi-separated, `s` a global section of a line bundle `L`, and `F` a line
   bundle trivial on `U = X_s`. Then some stage of the tower `F`, `L ⊗ F`,
   `L ⊗ (L ⊗ F)`, … has a global section generating on all of `U`.
3. **Pointwise generation** (`exists_twist_section_mem`). For ample `H`,
   every point `x` lies in the generation open of a global section of
   `tensorObj N.obj (tensorPow H.obj c)` for some `c` depending on `x`.
4. **Pointwise Lemma 27.5 and compactness**
   (`exists_affine_section_of_ample_tensor`, `amplePowerTwist`). If `A` is
   ample and `y` lies in the generation open of a section of `M`, then `y`
   lies in an affine generation open of a section of a positive power of any
   `P ≅ A ⊗ M`. Finitely many of the opens from step 3 cover `X`. Above the
   largest exponent `c` used, `A = H^{⊗(b - c)}` is ample, which proves the
   theorem.

## Step 1: gluing a family over an open

Fix module sheaves `N m` with morphisms `μ m : N m ⟶ N (m + 1)` and an open
`U`. A family `p m : Γ(N m, U)` is *compatible* if
`(μ m).app U (p m) = p (m + 1)`.

- `powMul_app_family`: the Library's iterated multiplication
  `powMul N μ n k` sends `p n` to `p (n + k)`. This is induction on `k`.
- `powMul_extends`: suppose `b : Γ(N n, V)` agrees with `p n` on `V ⊓ U`.
  Then `(powMul N μ n k).app V b` agrees with `p (n + k)` on `V ⊓ U`. The
  proof uses naturality of `powMul` under restriction (`hom_app_map`).
- `chart_E_family`: take a Library `LocalChart N μ T c` and an open
  `W ≤ T ⊓ U`. In the chart coordinates, `p m` restricted to `W` is
  `p 0` restricted to `W`, times the `m`-th power of the restriction of `c`.
  This is induction on `m` with the chart axiom `mul`.
- `chart_exists_local_family`: suppose `X.basicOpen c = T ⊓ U` and `V ≤ T`
  is affine. Then some `n` and some `b : Γ(N n, V)` satisfy
  `b|_{V ⊓ U} = (p n)|_{V ⊓ U}`. On `V`, `V ⊓ U` is the basic open of `c|_V`.
  Mathlib's `exists_eq_pow_mul_of_isAffineOpen` gives `y` on `V` with
  `y|_{V ⊓ U} = (c|_{V ⊓ U})^n · f`, where `f` is the coordinate of
  `(p 0)|_{V ⊓ U}`. Let `b` be the section with coordinate `y`; the chart
  coordinate is surjective. By injectivity of the coordinates on `V ⊓ U` and
  `chart_E_family`, `b` and `p n` agree on `V ⊓ U`.
- `exists_global_of_charts_family`: let `X` be quasi-compact and
  quasi-separated, and let every point have a chart `LocalChart N μ T c`
  with `x ∈ T` and `X.basicOpen c = T ⊓ U`. Then some `m` and some global
  `a : Γ(N m, ⊤)` satisfy `a|_U = p m`. The proof copies the Library proof
  of `exists_global_of_charts`, replacing the local solutions of the form
  `r • p` by `chart_exists_local_family`. First, choose finitely many affine
  opens `V_i`, each inside a chart, covering `X`. Next, find one exponent `e`
  with local extensions `b_i` on every `V_i`. Their differences on
  `V_i ⊓ V_j` vanish on `V_i ⊓ V_j ⊓ U`. Because `V_i ⊓ V_j` is compact by
  quasi-separatedness, the Library's `LocalChart.exists_powMul_eq_zero`
  kills each difference after `k` further multiplications, for one common
  `k`. The sheaf property glues the sections `powMul e k (b_i)` to a global
  `a`, and `a|_U = p (e + k)` is checked locally on the `V_i ⊓ U` with
  `powMul_extends`.

## Step 2: the twisted tower

For module sheaves `L` and `F`:

- `twistPow L F : ℕ → X.Modules` is `F` at `0` and
  `tensorObj L (twistPow L F m)` at `m + 1`.
- `twistMul L F s m` is the Library's
  `sectionMul L s (twistPow L F m) : twistPow L F m ⟶ twistPow L F (m + 1)`,
  that is, `(tensorLeftUnitor _).inv ≫ tensorMap (sectionHom L s) (𝟙 _)`.
- `twistFamily L F s q` is the compatible family over `U` generated by
  `q : Γ(F, U)`: `q` at `0`, and `(twistMul L F s m).app U` of the previous
  term at `m + 1`. Compatibility holds by definition.
- `nonempty_twistPow_iso`: `twistPow L F m ≅ tensorObj F (tensorPow L m)`.
  This is induction on `m`, using `tensorRightUnitor` at `0` and the
  published `tensorAssociator` and `tensorComm` at successors. Only the
  existence of the isomorphism is used.
- `twistPow_isLocallyFreeRankOne`: for line bundles `L` and `F`, every stage
  is locally free of rank one. This uses `IsLocallyFreeRankOne.tensor` with
  the published `pullbackTensorComparisonIsIso`.

Charts. Let `e : L.restrict T.ι ≅ 𝒪_T` and `eF : F.restrict T.ι ≅ 𝒪_T` be
trivializations. `twistTriv` trivializes the pulled-back stages. At `0` it is
the Library's `pullbackTriv T F eF`. At `m + 1` it is
`pullbackTensorIso`, then the tensor of `pullbackTriv T L e` with the
previous trivialization, then `tensorLeftUnitor`. This is exactly the
Library's `powTriv`, with `F` in place of the structure sheaf at `0`.
`twistChartIso` composes with `restrictFunctorIsoPullback`.
`twistChartIso_succ` shows that `twistMul` becomes the endomorphism
`chartMulOf T L e (sectionHom L s)` in these trivializations. The proof is
that of the Library's `chartIso_succ`, applying the Library lemma
`pullback_mul_comp` to `twistPow L F m` and `twistTriv … m`. The Library's
`localChartOf` then gives a `LocalChart` on `T` whose coefficient `c`
satisfies `X.basicOpen c = T ⊓ X_s`, by the Library's
`basicOpen_chartCoeff`.

`exists_twist_section`. Let `X` be quasi-compact and quasi-separated, let
`L` and `F` be line bundles, let `s` be a global section of `L`, and let
`eFU` trivialize `F` on `U = trivializationOpen L.obj s`.

- `L` is trivial on `U` through `(trivializationOpenIso L.obj s).symm`. With
  `eFU`, this gives a chart `CU` on `U` itself. Let `q` be the section of `F`
  over `U` whose stage-`0` coordinate in `CU` is `1`, namely
  `chartF (twistChartIso … 0) U le_rfl 1`.
- Every point `x` has trivializing opens `T₁` of `L` and `T₂` of `F`. The
  Library's `restrictTrivializationOfLE` restricts both trivializations to
  `T₁ ⊓ T₂`, which gives the charts required in Step 1.
- `exists_global_of_charts_family` yields `m` and a global section `a` of
  `twistPow L F m` with `a|_U = twistFamily L F s q m`.
- Let `cU` be the coefficient of `CU`. By `basicOpen_chartCoeff`,
  `X.basicOpen cU = U ⊓ U`, so `D = X.basicOpen cU` equals `U`. By
  `chart_E_family` and the chart axiom `res`, the coordinate of `a|_D` in
  `CU` is `(cU|_D)^m`. This is a unit by
  `RingedSpace.isUnit_res_basicOpen`. The Library's
  `QuasiAffineSectionBasis.le_trivializationOpen_of_chart_unit` then gives
  `D ≤ trivializationOpen (twistPow L.obj F.obj m) a`, hence `U ≤` the same
  open.

## Step 3: pointwise generation

`exists_twist_section_mem X H N hH x`:

- `X` is quasi-compact (`hH.compactSpace`) and quasi-separated (the Library's
  `LineBundle.IsAmple.quasiSeparatedSpace`).
- Choose a trivializing open `T ∋ x` of `N`. The Library's
  `ampleSectionOpenBasis` gives `d` and `s : H.powSections d` with
  `x ∈ X_s ≤ T`.
- Apply `exists_twist_section` to the line bundle `H^{⊗d}` (rank one by
  `tensorPow_isLocallyFreeRankOne`), the section `s`, and `F = N`
  trivialized on `X_s` by `restrictTrivializationOfLE`. This gives `m` and
  `a` with `X_s ≤ X_a`.
- Transport `a` along `nonempty_twistPow_iso` followed by `tensorPowMulIso`
  in the second factor:
  `twistPow (H^{⊗d}) N m ≅ tensorObj N.obj (tensorPow H.obj (d * m))`.
  The published `trivializationOpen_mapIso` shows that the transported
  section has the same generation open, which contains `x`.

## Step 4: pointwise Lemma 27.5 and the bound

`exists_affine_section_of_ample_tensor A M P e hA t hy` takes
`e : P.obj ≅ tensorObj A.obj M.obj` and `y ∈ trivializationOpen M.obj t`.
It is the body of the Library proof of `ampleTensor`, specialized to an
exponent of `1` for `M`.

- Ampleness of `A` gives `n ≥ 1` and `s` with `y ∈ X_s` and `X_s` affine.
- The section `tensorSection (A^{⊗n}) (M^{⊗n}) s (sectionPow M t n)` is
  transported to `tensorPow P.obj n`. The transport is the inverse of
  `tensorPowTensorIso A.obj M.obj n`, followed by `tensorPowIso e.symm n`.
- By `trivializationOpen_mapIso`, `tensorSectionGenerationLocus` and
  `trivializationOpen_sectionPow`, the generation open of the result `r` is
  `X_s ⊓ X_t`.
- This open contains `y`. It is affine by `affineGenerationLocusIntersection`
  applied to `M`, `t` and the affine `X_s`.

`amplePowerTwist`. By Step 3, choose for each point `x` an exponent `c x`
and a section `t x` of `tensorObj N.obj (tensorPow H.obj (c x))` generating
at `x`. Compactness of `X` gives a finite set `S` of points whose opens
cover `X`. Set `b₀ = S.sup c + 1`.

Let `b ≥ b₀`, let `eP : P.obj ≅ tensorObj N.obj (tensorPow H.obj b)`, and let
`y` be a point. Then `y` lies in the open of some `x ∈ S`, and `c x < b`.

- `A = tensorPow H.obj (b - c x)` is a line bundle, ample by the published
  `positiveTensorPowerAmple`, since `0 < b - c x`.
- `M = tensorObj N.obj (tensorPow H.obj (c x))` is a line bundle by
  `IsLocallyFreeRankOne.tensor`.
- An isomorphism `P.obj ≅ tensorObj A.obj M.obj` composes `eP` with
  `eqToIso` for `b = (b - c x) + c x` and the inverse of `tensorPowAddIso`
  (in the second factor). It is followed by the inverse of
  `tensorAssociator`, then `tensorComm` in the first factor, then
  `tensorAssociator`.

`exists_affine_section_of_ample_tensor` gives the required data at `y`.
Quasi-compactness comes from `hH`, so `P.IsAmple` holds. The construction
covers the empty scheme. It uses no hypothesis on `X` beyond ampleness of
`H`.

## Provenance and authorship

The source is The Stacks Project, chapter *Properties of Schemes*
(tag 01OH), registered as `stacks-properties-chapter-2026-10-28`. The file is
`literature/Stacks Project — Properties of Schemes chapter (PDF compiled July 14, 2026).pdf`
with SHA-256
`2f5b9ba41e07dd3a888da40496e07afae6caedd550597d96313ab16db4380316`. Step 2
is Lemma 18.2 (tag 01PW, PDF p.22) for the twisted tower: sections over `X_s`
extend after multiplication by a power of `s`. Step 1 follows the Library's
gluing proof of `lineBundleSectionClearing`. Steps 3 and 4 implement the
derivation in the statement Markdown (Proposition 27.13 (1) ⇒ (7), tag 01QA,
PDF pp.44–45, for `F = N`, then Lemma 27.5, tag 0890, PDF p.42) in pointwise
form. The proof does not establish global generation for one uniform
exponent. For each point it uses some exponent `c`, and it applies Lemma 27.5
with the ample bundle `H^{⊗(b - c)}` and `M = N ⊗ H^{⊗c}`.

Worker 770 wrote the proof. It imports the published Library modules by Lean
name and reuses no unaccepted draft.
