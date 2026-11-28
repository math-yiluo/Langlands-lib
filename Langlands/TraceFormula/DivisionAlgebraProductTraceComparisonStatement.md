# The trace comparison between `GL_n` and the units of a division algebra for restricted tensor products (statement)

The module defines the proposition
`Langlands.TraceFormula.DivisionAlgebraProductTraceComparisonStatement` and three supporting
definitions. The proposition is not proved in this module.

It is the global trace identity of Deligne–Kazhdan–Vignéras between `G = GL_n` and the unit
group `G' = Aˣ` of a central division algebra `A` of dimension `n²` over a number field `E`,
written for restricted tensor products of local test functions. The algebra `A` is a division
algebra at two distinct finite places `p₁`, `p₂` and split at every other place, finite and
infinite. After a choice of matrix charts of `E_p ⊗ A` at the split places, of integral
subgroups of `G'(E_p)` and of a constant `c > 0`, the statement says: if the components of
`f` and `f'` at `p₁`, `p₂` are matching functions with regular support, and the other components
of `f'` are those of `f` read through the charts, then `R'(f')` on `L²([G'])` and `R_disc(f)` on
`L²_disc([G])` are trace class and `tr R'(f') = c · tr R_disc(f)`. The constant `c` is chosen
before the test functions and serves for all of them.

## Notation from the Library

- `E : Type` is a number field and `A : Type` carries `[Ring A] [Algebra E A]
  [FiniteDimensional E A] [Algebra.IsCentral E A]`, with `Module.finrank E A = n ^ 2`. That `A`
  is a division algebra is not a separate hypothesis: it follows from the division model at
  `p₁` (see the remarks below).
- `Gₐ` is a local notation for `FiniteAlgebraUnits.groupScheme (Module.finBasis E A)`, the group
  scheme of units of `A` (the group scheme `Langlands.Shimura.HarrisClozel.divisionGroup`).
  `GLₙ` is a local notation for `GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of E)`.
  The module installs local `IsAffine` and `Smooth` instances for `GLₙ`, as
  `DivisionAlgebraSimpleTraceComparisonStatement` does, and the Borel σ-algebra (with its
  `BorelSpace` instance) on `GeneralLinear n (FiniteCompletion E p)` for every finite place `p`.
- `FiniteCompletion E p` is the completion `E_p = p.adicCompletion E` at a finite place `p`, with
  its completion topology, and `p.adicCompletionIntegers E` is its ring of integers `O_p`.
  `InfiniteAdeleRing E` is `E_∞ = E ⊗ ℝ`, the product of the archimedean completions.
- `AdelicGroupPoints E G` is `G(𝔸_E)`, `PlaceGroupPoints E G (.inr p)` is `G(E_p)`,
  `InfiniteAdelicGroupPoints E G` is `G(E_∞)`; `AdelicGroupPoints.atPlace E G (.inr p)` is the
  projection `x ↦ x_p` and `AdelicGroupPoints.infinite E G` the projection `x ↦ x_∞`.
- On the `GL_n` side, `localGLEquiv E n (.inr p) : G(E_p) ≃* GL_n(E_p)` and
  `GeneralLinearGroupPoints.infiniteEquiv E n : G(E_∞) ≃* GL_n(E_∞)` are the Library's
  identifications of the points of `GLₙ` with invertible matrices, and `glIntegralSubgroup E n p`
  is the subgroup `GL_n(O_p)` of `G(E_p)` (all from
  `Langlands/TraceFormula/GeneralLinearBaseChangeLocal.lean` and `Langlands/Global`).
  `Langlands.GeneralLinearGroup.integralSubgroup (Fin n) O_p` is `GL_n(O_p)` inside
  `GL_n(E_p)`: invertible matrices whose entries and whose inverse's entries lie in `O_p`.
- `ArchimedeanGL.SmoothCompactKernel E n` is the space of smooth compactly supported functions on
  `GL_n(E_∞)` (`InfiniteAdelicGL E n`); `fInf.1.1` is the underlying function.
  `SchwartzBruhat X` is the space of locally constant compactly supported functions on a
  topological space `X`.
- `IsEllipticSupported f` (`Langlands.BaseChange`) says that `f` on `GL_n(F)` vanishes off the
  regular elliptic set (separable irreducible characteristic polynomial).
  `IsDivisionRegularSupported F D f'` says that `f'` on `Dˣ` vanishes off the regular set
  (separable reduced characteristic polynomial). `AreMatching μ μ' f f'`
  (`Langlands.JacquetLanglands.DivisionMatching`) says that the orbital integrals of `f` vanish at
  the regular semisimple elements that are not elliptic and that the orbital integrals of `f` at
  `γ` and of `f'` at `γ'` agree, for the measures `μ` on `GL_n(F)` and `μ'` on `Dˣ`, at every
  pair of regular elements with the same (reduced) characteristic polynomial and for all
  associated Haar measures on their centralizers. No sign is built in.
- `IsUniformlyIntegral E G U` says that for every regular function `a` on `G`, at almost every
  finite place `p`, `a` takes values in `O_p` on the whole subgroup `U (.inr p)`.
- `IsAdelicTestFunction E G h` is the Library's notion of a smooth compactly supported test
  function on `G(𝔸_E)`: continuous with compact support, with plot-smooth archimedean slices, and
  invariant on both sides under an open subgroup of `G(𝔸_{E,f})`.
- `canonicalIntegratedAction E G hG h hh` is `R(h)` on the canonical `L²([G])`,
  `[G] = A_G G(E) \ G(𝔸_E)`, for `Measure.haar` on `G(𝔸_E)`, and
  `canonicalDiscreteIntegratedAction E G hG h hh` is its compression `R_disc(h)` to the discrete
  spectrum `L²_disc([G])`; both are defined in `DivisionAlgebraSimpleTraceComparisonStatement`.
  `IsTraceClass` and `operatorTrace` are the Library's trace-class predicate and trace.

## Supporting definitions

- `IsAdelicInfiniteFactorization F G S φInf φ U f`, for a finite set `S` of finite places, a
  function `φInf` on `G(F_∞)`, local functions `φ p` on `G(F_p)` and subgroups `U p` of `G(F_p)`
  (`p` finite): for every `x ∈ G(𝔸_F)`,
  `f(x) = φInf(x_∞) · ∏_{p ∈ S} φ p (x_p)` if `x_p ∈ U p` for every finite `p ∉ S`, and
  `f(x) = 0` otherwise. It is the restricted tensor product
  `f = φInf ⊗ ⊗_{p ∈ S} φ p ⊗ ⊗_{p ∉ S} 1_{U p}`. It differs from the Library's
  `IsAdelicFactorization` in that the archimedean factor is one function on the whole group
  `G(F_∞)` rather than a product over the archimedean places, so that smooth compactly supported
  functions on `G(F_∞)` that are not products are allowed.
- `finiteAlgebraPlaceUnitEquiv F A p : G'(F_p) ≃* (F_p ⊗[F] A)ˣ` is
  `FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis F A)` over the completion
  `placeCompletion F (.inr p)`, for a finite-dimensional `F`-algebra `A`.
- `finiteAlgebraInfiniteUnitEquiv F A : G'(F_∞) ≃* (F_∞ ⊗[F] A)ˣ` is the same equivalence over
  `InfiniteAdeleRing F`.

These are the charts used in `Langlands.Shimura.HarrisClozel.IsSplitLocalTransfer`,
`IsDivisionLocalTransfer` and `IsInfiniteTransfer`, composed there with an algebra isomorphism in
the same way as here.

## Statement

Fix `E`, `A`, `n` as above, connected-reductivity witnesses `hD : IsConnectedReductive Gₐ` and
`hG : IsConnectedReductive GLₙ`, and finite places `p₁ ≠ p₂` of `E`.

**Division models.** For `j = 1, 2` let `Δ_j : Type` be a central division algebra over
`E_{p_j}` (`[DivisionRing Δ_j] [Algebra E_{p_j} Δ_j] [FiniteDimensional E_{p_j} Δ_j]
[Algebra.IsCentral E_{p_j} Δ_j]`) with a topology that is its module topology
(`[TopologicalSpace Δ_j] [IsModuleTopology E_{p_j} Δ_j]`), and let
`t_j : E_{p_j} ⊗[E] A ≃ₐ[E_{p_j}] Δ_j` be an algebra isomorphism. Then `Δ_j` is a topological
ring (`IsModuleTopology.isTopologicalRing`), and `Δ_jˣ` gets its units topology and its Borel
σ-algebra.

**Measures.** Let `μ_j` be a Haar measure on `GL_n(E_{p_j})` and `μ'_j` a Haar measure on
`Δ_jˣ`, `j = 1, 2`. These measures are arbitrary.

**Hypotheses.**

1. For every finite place `p ≠ p₁, p₂` there is an `E_p`-algebra isomorphism
   `E_p ⊗[E] A ≃ M_n(E_p)`.
2. There is an `E_∞`-algebra isomorphism `E_∞ ⊗[E] A ≃ M_n(E_∞)`.

**Conclusion.** There exist

- a finite set `S₀` of finite places,
- for every finite place `p` with `p ≠ p₁` and `p ≠ p₂` an `E_p`-algebra isomorphism
  `s p : E_p ⊗[E] A ≃ M_n(E_p)`,
- an `E_∞`-algebra isomorphism `sInf : E_∞ ⊗[E] A ≃ M_n(E_∞)`,
- a subgroup `U' i` of `G'(E_i)` for every place `i`,
- a real number `c`,

such that

1. `p₁ ∈ S₀`, `p₂ ∈ S₀` and `0 < c`;
2. the family `U'` is uniformly integral (`IsUniformlyIntegral E Gₐ U'`);
3. for every `x ∈ G'(𝔸_E)`, `x_p ∈ U' p` for all but finitely many finite places `p`;
4. `U' p` is open and compact in `G'(E_p)` for every finite place `p`;
5. for every finite place `p ∉ S₀` (so `p ≠ p₁, p₂`),
   `U' p = {x ∈ G'(E_p) : s p (x) ∈ GL_n(O_p)}`, where `x` is read in `(E_p ⊗[E] A)ˣ` through
   `finiteAlgebraPlaceUnitEquiv` and sent to `GL_n(E_p)` by `s p`;
6. for every finite set `S ⊇ S₀` of finite places and all local data
   - `fInf ∈ SmoothCompactKernel E n`,
   - `floc p ∈ SchwartzBruhat (GL_n(E_p))` for every finite place `p`,
   - `f'_j ∈ SchwartzBruhat (Δ_jˣ)`, `j = 1, 2`,

   such that, for `j = 1, 2`, `floc p_j` is supported in the regular elliptic set
   (`IsEllipticSupported`), `f'_j` is supported in the regular set
   (`IsDivisionRegularSupported E_{p_j} Δ_j`), and `AreMatching μ_j μ'_j (floc p_j) f'_j`; for
   all functions `φ' p` on `G'(E_p)` (`p` finite) with
   - `φ' p_j (x) = f'_j (t_j (x))` for `x ∈ G'(E_{p_j})`, `j = 1, 2`,
   - `φ' p (x) = floc p (s p (x))` for `p ∈ S`, `p ≠ p₁, p₂` and `x ∈ G'(E_p)`

   (points read through `finiteAlgebraPlaceUnitEquiv`, units mapped by `Units.mapEquiv`); and for
   all functions `f` on `G(𝔸_E)` and `f'` on `G'(𝔸_E)` with
   - `IsAdelicInfiniteFactorization E GLₙ S (fInf ∘ infiniteEquiv) (p ↦ floc p ∘ localGLEquiv)
     (p ↦ GL_n(O_p)) f`, that is
     `f = fInf ⊗ ⊗_{p ∈ S} floc p ⊗ ⊗_{p ∉ S} 1_{GL_n(O_p)}`,
   - `IsAdelicInfiniteFactorization E Gₐ S (fInf ∘ sInf ∘ finiteAlgebraInfiniteUnitEquiv) φ'
     (p ↦ U' p) f'`, that is `f' = (fInf ∘ sInf) ⊗ ⊗_{p ∈ S} φ' p ⊗ ⊗_{p ∉ S} 1_{U' p}`,

   the functions `f` and `f'` are test functions (`IsAdelicTestFunction`), and there are
   witnesses `hf'`, `hf` that `f'` and `f` are integrable for `Measure.haar` such that
   `R'(f') = canonicalIntegratedAction E Gₐ hD f' hf'` is trace class on `L²([G'])`,
   `R_disc(f) = canonicalDiscreteIntegratedAction E GLₙ hG f hf` is trace class on
   `L²_disc([G])`, and

   `operatorTrace R'(f') = c · operatorTrace R_disc(f)`.

### Remarks on the formulation

- *Division at `p₁` and `p₂`.* For `n ≥ 1`, a division model `(Δ_j, t_j)` exists exactly when
  every nonzero element of `E_{p_j} ⊗[E] A` is a unit, the hypothesis
  `Langlands.Shimura.FiniteUnitary.IsDivisionAt E A p_j`: then `E_{p_j} ⊗[E] A` itself, with the
  division ring structure `DivisionRing.ofIsUnitOrEqZero`, its module topology and the identity,
  is a model (it is central over `E_{p_j}` because `A` is central over `E`). The models are taken
  as data because the local predicates `IsDivisionRegularSupported` and `AreMatching` are stated
  for a type with a `DivisionRing` instance. The statement holds for every choice of models, in
  the form used by `IsDivisionLocalTransfer`. The model at `p₁` also makes `A` a division
  algebra: `A → E_{p₁} ⊗[E] A` is injective, so a nonzero `a ∈ A` becomes a unit there, left
  multiplication by `a` on `A` is injective, hence bijective since `A` is finite-dimensional (the
  argument of `FiniteUnitary.isDivision_of_isDivisionAt`).
- *Splitting.* Hypothesis 1 at `p` is, by definition, `Langlands.Shimura.FiniteUnitary.IsSplitAt
  E A p n`; it is written out so that this module does not depend on the unitary Shimura
  modules. Hypothesis 2 is splitting at every archimedean place at once, in the form used by
  `IsInfiniteTransfer`.
- *Measures.* The Haar measures at `p₁` and `p₂` are universally quantified and the constant `c`
  is chosen after them; this is stronger than fixing one pair of measures. Rescaling `μ_j` or
  `μ'_j` rescales the condition `AreMatching` and is absorbed by `c`.
- *Topologies.* `SchwartzBruhat`, `IsEllipticSupported`, `IsDivisionRegularSupported` and
  `AreMatching` use only the topologies and the Borel σ-algebras; the topology of
  `FiniteCompletion E p` is the completion topology, which is the topology of
  `CompletionPadic.topologicalData p` (`CompletionPadic.topologicalData_topology`). So the local
  statements `DivisionRegularTransferStatement` and `JacquetLanglandsMatchingTraceStatement` apply
  to these data after installing the valuative relation and the local field instance of
  `CompletionPadic.topologicalData`, as `completionJacquetLanglandsPair` does.
- *The local functions on `G'`.* The family `φ'` is constrained only at `p₁`, `p₂` and at the
  places of `S`; outside `S` it does not enter `f'`. The family `floc` is indexed by all finite
  places; only its members at the places of `S` enter `f`. Since `S ⊇ S₀ ∋ p₁, p₂`, the
  subgroups `U' p₁`, `U' p₂`, the subgroups `U' p` for `p ∈ S₀` and the archimedean members of
  `U'` never enter `f'`; they are constrained only by conclusions 2–4.
- *The constant.* `c` depends only on the data chosen before the test functions: the measures
  `Measure.haar` on `G(𝔸_E)`, `G'(𝔸_E)` and their norm-one subgroups, `μ_j`, `μ'_j` and the charts.
  It compares `Measure.haar` with products of local Haar measures (see below). There is no sign:
  the matching `AreMatching` has no sign built in, and the comparison is between geometric sides.

## Why it is true

1. *Charts and integral subgroups.* Let `Λ ⊆ A` be the `O_E`-span of the basis
   `Module.finBasis E A`. For almost every finite `p` the structure constants and the coordinates
   of `1` are `p`-integral and the discriminant of `Λ` is a `p`-unit, so `Λ_p = O_p ⊗ Λ` is a
   maximal `O_p`-order of `E_p ⊗[E] A`. At a split place every maximal order of `M_n(E_p)` is
   conjugate to `M_n(O_p)`, so for almost every `p ≠ p₁, p₂` an isomorphism `s p` with
   `s p (Λ_p) = M_n(O_p)` can be chosen; at the remaining split places `s p` is any isomorphism
   given by hypothesis 1, and `sInf` is given by hypothesis 2. Take `S₀ = {p₁, p₂}`,
   `U' p = (s p)⁻¹(GL_n(O_p))` for `p ≠ p₁, p₂`, any compact open subgroup at `p₁`, `p₂`
   (for example the preimage of the units of the maximal order of `Δ_j`) and the whole group at
   the archimedean places. The regular functions on `G'` are the polynomials in the coordinates
   with respect to the basis and the inverse of the norm `N` of left multiplication. Where
   `s p (Λ_p) = M_n(O_p)`, `U' p = Λ_pˣ`, on which the coordinates are integral and `N` is a unit
   of `O_p`: this gives uniform integrality. Conversely, an adelic point `x` has integral
   coordinates and `N(x_p)⁻¹ ∈ O_p` for almost every `p`; then `x_p ∈ Λ_p` and, by the
   Cayley–Hamilton theorem for left multiplication, `x_p⁻¹ ∈ Λ_p`, so `x_p ∈ U' p`. Each `U' p`
   is compact and open because the charts are homeomorphisms and `GL_n(O_p)` is compact and open.
2. *Test functions.* By conclusions 2–4 the set `{y : y_p ∈ U' p for all p ∉ S}` is the open
   subset `G'(E_∞) × ∏_{p ∈ S} G'(E_p) × ∏_{p ∉ S} U' p` of `G'(𝔸_E)`, whose last factor is
   compact, and similarly for `GL_n(O_p)`. The
   functions `floc p`, `φ' p` are locally constant with compact support, hence bi-invariant under
   compact open subgroups, and the archimedean factors are smooth with compact support (the
   charts are algebraic). So `f` and `f'` are test functions, and `c · f` is one too.
3. *Reduction to the simple comparison.* `DivisionAlgebraSimpleTraceComparisonStatement` applied
   to `f'` and `c · f` (with `A` made a division ring by `DivisionRing.ofIsUnitOrEqZero`, the
   first remark) gives the conclusion, since `R_disc(c f) = c R_disc(f)`. Its four hypotheses are
   checked as follows.
   - *Support at two places.* If `f(g) ≠ 0` then `floc p_j (g_{p_j}) ≠ 0`, so `g_{p_j}` is regular
     elliptic. The support of the locally constant `floc p_j` is closed, so this holds on
     `tsupport f` too.
   - *No inseparable classes for `f'`.* The positive split centre `A_{G'}` has trivial components
     at the finite places, so the component at `p₁` of `a x⁻¹ r' x` is a conjugate of `r'`. Its
     reduced characteristic polynomial in `Δ₁` is that of `r'` in `A`, which is inseparable, so
     `f'₁` vanishes there, and `f'¹` vanishes on the conjugates of `r'`.
   - *Classes that do not transfer.* Let `r ∈ GL_n(E)` be regular elliptic, with characteristic
     polynomial `P` and `L = E[X]/(P)`. If `r` is elliptic at `p₁` and at `p₂`, then `L ⊗ E_{p_j}` is
     a field of degree `n`, so `L` splits `A` at `p₁` and `p₂`; at the other places `A` is split.
     By the criterion for maximal subfields (Platonov–Rapinchuk §1.5.1), `L` embeds in `A`, and
     the image of a root of `P` has reduced characteristic polynomial `P`. So if `P` is the
     reduced characteristic polynomial of no element of `A`, then `r` is not elliptic at `p₁` or
     at `p₂`, `floc p_j` vanishes on the conjugates of `r` there, and the orbital integrals of
     `f¹` at `r` vanish.
   - *Matching of global orbital integrals.* Let `r ∈ GL_n(E)` be regular elliptic and `r' ∈ Aˣ`
     with the same (reduced) characteristic polynomial. As `t_j(r')` lies in the commutative
     subfield `E_{p_j}[t_j(r')]` of the division algebra `Δ_j`, `r` is elliptic at `p₁` and `p₂`,
     and `(r, t_j(r'))` is a corresponding pair. Choose Haar measures `μ_v` on `GL_n(E_v)` for
     every place `v` with `μ_p(GL_n(O_p)) = 1` for `p ∉ S₀`, `μ_{p_j}` the given ones, and on
     `G'(E_v)` the measures `μ'_{p_j}` and, for `v ≠ p₁, p₂`, the transports of `μ_v` by the
     charts. Their restricted products are `α · Measure.haar` on `G(𝔸_E)` and
     `α' · Measure.haar` on `G'(𝔸_E)` for some `α, α' > 0` independent of the test functions and
     of `S`. For product measures on the centralizers `(L ⊗ 𝔸)ˣ`, the global orbital integrals of
     `f` and `f'` factor into local ones (Getz–Hahn, Lemma 17.8.3). The local factors agree at
     every place: at `p_j` by `AreMatching`; at the other finite places and at infinity because
     the local factor of `f'` is that of `f` read through an algebra isomorphism that sends `r'` to
     an element with the same separable characteristic polynomial as `r`, hence to a conjugate
     of `r`; outside `S` because both factors are indicator functions of corresponding integral
     subgroups. Translating `r`, `r'` by the positive split centre (which the charts fix) and
     integrating over it gives the same identity for the norm-one averages `f¹`, `f'¹`. With the
     ratio of the intrinsic measures on the two positive split centres, this produces one
     constant `c > 0`, independent of the test functions and of `S`, with
     `O_{r'}(f'¹) = c · O_r(f¹)` for associated centralizer measures, which is hypothesis 3 for
     `f'` and `c · f`.

## Sources and provenance

- Deligne–Kazhdan–Vignéras, *Représentations des algèbres centrales simples `p`-adiques*, in
  Bernstein–Deligne–Kazhdan–Vignéras, *Représentations des groupes réductifs sur un corps local*
  (1984), registered `bdkv-1984-representations-local-field` (printed page = PDF page − 4).
  §B.1.a, printed p. 78: for `G = GL(n, F)` and `G' = GL(m, D)`, functions `φ`, `φ'` in the
  Hecke algebras of `L²(G, ω)` whose local components are equal outside the finite set `S` of
  places where `D` ramifies, with a supercuspidal component at one place outside `S`, components
  supported in the regular elliptic elements at a place of `S`, and orbital integrals of `φ_S`
  equal to the extension by `0` of those of `φ'_S`; then `trace ρ(φ) = trace ρ'(φ')` for
  compatible measures on `G(𝔸)`, `G'(𝔸)` and on the centralizers. §C.1, printed pp. 90–91: the
  simple trace formula on the discrete part `L²_d(G, ω)` when two local components have
  vanishing orbital integrals at every non-elliptic `γ ∈ G(F)` (Théorème (?)), the correspondence
  of orbital integrals at all places (C.1.a), the lemma that a non-elliptic `γ` is not conjugate
  into `G'` at two places (C.1.b), and the identity `trace ρ_d(φ) = trace ρ'(φ')` (C.1.c).
- Arthur–Clozel, *Simple algebras, base change, and the advanced theory of the trace formula*
  (1989), registered `arthur-clozel-1989-base-change`, Chapter 1, §4, printed pp. 42–44: the
  global argument with product functions `φ = ⊗ φ_v`, `f = ⊗ f_v` whose local components are
  associated at every place and are unit elements of the Hecke algebras at almost all places;
  the global orbital integrals are products of local ones formed with Tamagawa measures, which
  gives the comparison (4.4)–(4.6) of the two trace formulas.
- Getz–Hahn, *An introduction to automorphic representations* (2024), registered
  `getz-hahn-2024-automorphic-representations`, §17.8: the restricted tensor products
  `C_c(X(𝔸^∞)) = ⊗' C_c(X(F_v))` with respect to the characteristic functions of the integral
  points (printed p. 462), and Lemma 17.8.3 (printed p. 464; the setting on p. 463): global
  orbital integrals of product functions are products of local orbital integrals for product
  measures, and the local factor is `1` at almost all places.
- Platonov–Rapinchuk, *Algebraic groups and number theory* (1994), registered
  `platonov-rapinchuk-1994-algebraic-groups-number-theory`, §1.5.1, printed p. 38: a field
  extension of degree `n` equal to the index of a division algebra `D` over a number field is a
  maximal subfield of `D` exactly when it splits `D` locally at every place.

This is derived content. The proposition combines the comparison of the simple trace formulas,
stated in the Library as `DivisionAlgebraSimpleTraceComparisonStatement`, with the passage from
local to global matching for restricted tensor products. It relates to the sources as follows.

- *Product test functions.* The sources take factorizable functions in the Hecke algebras with a
  fixed central character. Here the archimedean factor is an arbitrary smooth compactly supported
  function on `GL_n(E_∞)`, not necessarily a product over the archimedean places or `K`-finite,
  the finite factors are arbitrary locally constant compactly supported functions, and the
  quotient is the canonical `A_G G(E) \ G(𝔸_E)` of the Library, without central character.
- *Matching.* Deligne–Kazhdan–Vignéras ask for equal local components outside the ramified
  places. Here equality is expressed through algebra isomorphisms `s p`, `sInf` (the groups
  `G'(E_v)` and `GL_n(E_v)` are different types), which are part of the conclusion together with
  the integral subgroups `U' p` they determine. At the two ramified places the local hypothesis
  is `AreMatching` (DKV B.2.a, Badulescu §5, as in `DivisionMatching`). For `floc p_j` with
  regular elliptic support it is condition 4 of §B.1.a on the regular set: the orbital integrals
  of `floc p_j` vanish at the regular semisimple elements that are not elliptic and agree with
  those of `f'_j` at corresponding regular elements; every regular elliptic element of
  `GL_n(E_{p_j})` has a partner in `Δ_jˣ`, since every field extension of degree `n` of
  `E_{p_j}` embeds in `Δ_j`.
- *The simple form.* Instead of a supercuspidal component at an unramified place (§B.1.a), the
  simple form comes from regular elliptic support at the two ramified places, as in §C.1, and the
  conclusion concerns the whole discrete spectrum of `GL_n`.
- *The constant `c`.* The sources normalize the measures (compatible or Tamagawa measures) so
  that no constant appears. Here the adelic operators are formed with `Measure.haar`, and the
  constant `c > 0` absorbs the comparison of `Measure.haar` with products of local measures; it
  is fixed before the test functions and is the same for all `S ⊇ S₀`.
- *Division models and universal measures.* The local data at `p₁`, `p₂` are arbitrary division
  models `(Δ_j, t_j)` and arbitrary Haar measures, as explained in the remarks above.
