# The uniform standard canonical Jacquet section for an Iwahori decomposition (proof)

Module `Langlands.Representation.Jacquet.StandardIwahoriCanonicalSectionProof`.
Namespace `Langlands.Jacquet`.

`Langlands.Jacquet.standardIwahoriCanonicalSection` proves the exact published
proposition `Langlands.Jacquet.StandardIwahoriCanonicalSectionStatement.{uF, uV}`
of `Langlands.Representation.Jacquet.StandardIwahoriDecompositionStatements`. Its
level parameters are `uF` (field and group schemes) and `uV` (representation
space), in that order. It covers both parameters, and the theorem adds no
hypothesis. The module was written against Library commit
`fcb85a7ef43356fec01e6ccf1605f08568c08cb0`. The general helper lemmas are copied
from the published proof `Langlands.Jacquet.standardCanonicalSection`
(module `Langlands.Representation.Jacquet.StandardCanonicalSectionProof`), where
they are private and cannot be imported. The Iwahori-contraction construction
for an arbitrary compact open `K` is new.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`: VI.6.1,
(VI.6.1.2), the single-image isomorphism and decomposition, and the
Proposition, printed pp.176–177 / PDF pp.182–183. The hypothesis on `K` is the
Iwahori decomposition of V.5.2 (ii), printed p.123 / PDF p.129. The target's
Markdown gives the source passages and the exact meaning of every datum and
conclusion.

## What is proved

The data are as in the target. `F` is a nonarchimedean local field of either
characteristic and `G` an actual connected reductive group over `Spec F`, with
the canonical rational-point topology. There is a maximal split torus `i`, a
generic cocharacter `ν`, a standard index `J ⊆ simpleRelativeRoots i ν` with a
standard cocharacter, and a compatible split component `q : A → S`. Then
`M`, `N` and `N̄` are the actual standard Levi, unipotent radical and opposite
radical. `K` is a compact open subgroup of `G(F)` with the ordered Iwahori
decomposition `HasIwahoriIntersectionDecomposition K M N N̄`, and `ρ` is an
admissible complex representation. Nothing else is assumed of `K`. In
particular, the theorem does not assume the published
`StandardParabolicBasisMember` or its `WeakChamberContraction` clause.

Write `j : V^K → (V_N)^{K ∩ M}` for the fixed-vector Jacquet map and `C_t` for
the compression `compressedAction ρ hρ.1 K hK t`. The theorem gives
`0 < ε ≤ 1`, a point of the epsilon chamber `standardComponentCAepsilon i ν J q ε`,
and one linear map `s` with `j ∘ s = id`, such that for every `t` in that chamber
all of the following hold:

- `ker j ≤ ker C_t` and `ker C_t = ker j`;
- `ker C_t` and `range C_t` are complementary;
- the restriction of `j` to `range C_t` is bijective;
- `range C_t` is the stable image, and the generalized kernel is `ker j`;
- `range s = range C_t`, and `s` equals the inverse restricted quotient
  `compressedImageLift` for every proof of that bijectivity.

## The implemented proof

The only change from the basis-member route is how the Iwahori contraction data
are obtained for the chamber points. A weak-chamber point need not contract an
arbitrary compact open `K`. Instead, the proof shrinks `ε` until every point of
the small chamber contracts `K ∩ N` and `K ∩ N̄`.

1. **Published uniform clauses for every compact open `K`.**
   `IsCompatibleStandardSplitComponent.uniform_containment_and_cofinality`
   gives `UniformCompactContainment` and `UniformCompactOpenCofinality` for `K`
   and the epsilon chambers.
   `IsCompatibleStandardSplitComponent.strictChamber_power_basis_and_exhaustion`
   gives `StrictChamberExhaustion` and `StrictChamberNeighborhoodBases` on the
   strict chamber. `IsCompatibleStandardSplitComponent.leviIntersectionNormalization`
   gives `LeviIntersectionNormalization`: component points commute with the
   Levi, so they normalize `K ∩ M`. All three hold for any compact open `K`.

2. **Weak contraction on a small chamber**
   (`actual_epsilon_weakChamberContraction`). `N` and `N̄` are closed in
   `G(F)`, because they are the rational points of closed subgroup schemes
   (`isClosed_rationalPoint_subgroup`, as in the published uniform-chamber
   module). So `K ∩ N` and `K ∩ N̄`, as preimages of compact `K` under the
   closed embeddings `N → G(F)` and `N̄ → G(F)`, are compact open subgroups of
   `N` and `N̄`. Apply uniform compact-open cofinality to these two subgroups.
   It gives `ε_N, ε_N̄ > 0` with `t (K ∩ N) t⁻¹ ⊆ K ∩ N` for
   `t ∈ C_A^+(ε_N)` and `t⁻¹ (K ∩ N̄) t ⊆ K ∩ N̄` for `t ∈ C_A^+(ε_N̄)`. By
   monotonicity of the epsilon chambers, `min(ε_N, ε_N̄)` gives
   `WeakChamberContraction` with the small epsilon chamber in place of the weak
   chamber.

3. **Iwahori contraction data** (`actual_epsilon_isIwahoriContraction`).
   Suppose `ε ≤ 1` and the weak contraction of step 2 holds on `C_A^+(ε)`. Then
   `ContractionAndCofinality` holds for `K`, with `C_A^+(ε)` in the weak-chamber
   slot and the actual `C_A`, strict chamber and epsilon family elsewhere. The
   six clauses come from steps 1 and 2. A point `t ∈ C_A^+(ε)` lies in the
   Levi, in `C_A`, in that slot and, since `ε ≤ 1`, in the strict chamber. The
   published `isIwahoriContraction_of_contractionAndCofinality` therefore
   gives `IsIwahoriContraction K N M N̄ t`, using the hypothesis `_hIwahori`
   for the factorization.

4. **Uniform annihilation of the Jacquet kernel.** This step is copied from the
   published proof. Span induction on the actual Jacquet relations, using the
   uniform compact containment of step 1 for singletons `{n} ⊆ N`, gives each
   relation a threshold beyond which compact averaging kills its translate.
   A finite spanning set of `ker j` (the space `V^K` is finite dimensional by
   admissibility) then gives one threshold `ε₀` with `ker j ≤ ker C_t` for all
   `t ∈ C_A^+(ε₀)`.

5. **Choice of `ε`.** Take `ε = min(min(ε₀, ε_1), 1)`, where `ε_1` comes from
   step 2. Then `0 < ε ≤ 1`, and by monotonicity every `t ∈ C_A^+(ε)` satisfies
   step 4, the weak contraction of step 2 and hence the Iwahori contraction of
   step 3.

6. **Single-image consequences**, copied from the published proof. For each
   such `t`, the published generalized-kernel equality
   `powerKernelSup_eq_ker_of_iwahoriContraction` and the Fitting complement
   `powerKernelSup_isCompl_stableImage` identify `ker C_t` with `ker j`, and
   `range C_t` with the stable image. They also make `ker C_t` and `range C_t`
   complementary. The published stable-image bijection
   `stableImageJacquetMap_bijective_of_iwahoriContraction` then gives the
   bijectivity of `j` on `range C_t`.

7. **Nonemptiness, products and the common section**, copied from the
   published proof. The chamber is nonempty: lift a standard cocharacter
   through the compatible component and take a large power of its
   common-uniformizer image. Since `ε ≤ 1`, the chamber is closed under
   multiplication, and its points commute. Compression multiplicativity
   (`compressedAction_mul_of_factor`, using the `upper`, `lower` and `levi`
   fields of step 3) places `range C_{tt'}` inside `range C_t` and
   `range C_{t'}`. Surjectivity of `j` on the smaller image and injectivity on
   the larger one force equality, so all images agree. The section is
   `compressedImageLift` at one chosen chamber point. The published inverse,
   range and equal-range lemmas give `j ∘ s = id`, `range s = range C_t` and
   equality with every lift.

Renard proves (VI.6.1.2) with a compact open `Γ ⊆ N` and V.5.2 (iv), and the
independence from dimension counts. The Lean proof instead uses span induction,
the published Fitting results and the nested-image argument above. It
introduces no structural or representation-theoretic assumption beyond those of
the target.

## Imports

- `Langlands.Representation.Jacquet.StandardIwahoriDecompositionStatements` (the target);
- `Langlands.Representation.Jacquet.IwahoriContractionAdmissibility` (the
  single-contraction Fitting and bijectivity results);
- `Langlands.BruhatTits.SpecialCompact.JacquetContractionAssembly`
  (`isIwahoriContraction_of_contractionAndCofinality`);
- `Langlands.BruhatTits.SpecialCompact.JacquetStrictElement` (Levi membership of
  component points and the cocharacter lift);
- `Langlands.BruhatTits.SpecialCompact.WeakIwahoriBasisReduction` (Levi
  normalization; it imports the uniform-chamber and strict-power modules).

Because the last import contains a namespace `Langlands.CategoryTheory`, the
module opens `_root_.CategoryTheory` explicitly.

## Scope

The theorem proves independence of the contracting point within one chosen
nonempty epsilon chamber, for the specified data and `K`. It does not prove the
arbitrary-parabolic section. It does not prove independence from the torus,
split component, uniformizer or `K`, nor the VI.9.4 statements. It also does
not prove `StandardCanonicalSectionStatement` independently: that follows from
this theorem through the published comparison
`standardCanonicalSectionStatement_of_standardIwahori`, which this module does
not restate.
