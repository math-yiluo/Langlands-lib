# The global functional equation for twisted pairs of relative Weil representations

Author: Worker 84. Statement contribution to task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1, for the Galois-side global
functional equation used by Henniart (2000), §2.3. All four declarations are
proposition definitions in the namespace
`Langlands.Global.FunctionalEquationComparison`. Defining them proves nothing and
assumes nothing. In particular no local map, local-constant system, additive
component, local factor or partial L-function is constructed, and no existence
theorem is proved.

The target is `RelativeWeilTwistFunctionalEquationStatement`. It is Tate (1979),
Theorem 3.5.3, with (3.5.1)–(3.5.4), applied to the representation
`V = ((χ ∘ τ_F) ⊗ S) ⊗ S'` of the relative Weil group `W_{E/F}`, where `S` and
`S'` are continuous and `χ` is a finite-order Hecke character that is trivial on the
archimedean ideles. Every finite local factor is the actual arithmetic pair factor.
The archimedean block is existential and independent of the twist. The section
"Relation to the source" lists every way the target differs from Tate's theorem.

## Objects

- **Class family and Weil group.** `c : FundamentalClass.ClassFamily.{u}` with the
  published `IsArithmeticClassFamily c`, number fields `F E : Type u` with
  `[Algebra F E]` and `[IsGalois F E]`, and the published
  `RelativeWeilGroup c F E`. As in the published `AssociatedFactorStatement`,
  `IsArithmeticClassFamily c` makes `W_{E/F}` the Weil group of the actual
  fundamental class.
- **Representations.** `S S' : FiniteRepresentation.{0, u, uV} ℂ
  (RelativeWeilGroup c F E)` with `S.IsContinuous` and `S'.IsContinuous`. These are
  finite-dimensional complex representations, continuous for the usual topology on
  endomorphisms (published `FiniteRepresentation.IsContinuous`). Semisimplicity is
  not assumed; see below.
- **Global additive character.** `ψ : HarmonicAnalysis.UnitaryAdditiveCharacter
  (Adeles F)` with `∃ x, ψ x ≠ 1` and `ψ (diagonal F x) = 1` for every `x : F`. The
  nontriviality hypothesis is also implied by the structure field `nontrivial`. It
  is kept so that the hypotheses read as in the published
  `HeckeGlobalFunctionalEquationStatement`.
- **Twisting characters.** `χ : HeckeCharacter F` with `χ.HasFiniteOrder`
  (`χ ^ n = 1` for some `n > 0`) and `χ.HasPrescribedInfinityComponent 1`
  (`χ.atInfinity = 1`, i.e. `χ` is trivial on the archimedean ideles).
  `χ.IsUnramifiedAt z` says that `χ.finiteComponent z` is trivial on the local
  integral units. The twist is the published
  `FiniteRepresentation.twist (reciprocityCharacter c F E χ) S`, where
  `reciprocityCharacter c F E χ` is `χ ∘ τ_F` and `τ_F` is the pointwise inverse
  of the transfer `W_{E/F} → C_F`. This twist is the same as the one in the published
  `AssociatedDeterminantTwistStatement` and `FiniteTwistGammaRealizations`.
- **Local maps.** For a finite place `z` of `F`, `w : FinitePlacesAbove E z`, a
  reciprocity candidate `e` of `E_w`, and a continuous homomorphism
  `ι : W_{F_z} →ₜ* W_{E/F}` with the published `IsLocalRelativeWeilMap z w.1 e ι`.
  `localPairClass S ι` is the published zero-monodromy Weil–Deligne class of
  `S ∘ ι`, in `Correspondence.LocalPairClass (padicField z)`.
- **Local additive characters.** `ψz : Correspondence.NontrivialAdditiveCharacter
  (padicField z)` with the published `IsCanonicalFiniteAdditiveComponent ψ z ψz`,
  i.e. `ψz x = ψ (0, single z x)` for all `x`.
- **Local constants.** A local-constant system at `F_z` is a triple
  `(eCz, εz, hεz)`: a common-closure reciprocity family
  `eCz : LocalFactor.CommonClosure.ReciprocityFamily (padicField z)`, an assignment
  `εz : LocalFactor.NonabelianSystem.Assignment.{u, uE} (padicField z)`, and
  `hεz : LocalFactor.NonabelianSystem.IsSystem (padicField z) eCz εz`. `IsSystem`
  includes `NormalizedReciprocity` for `eCz` together with the additivity,
  Haar-scaling, induction and rank-one relations. These are the system parameters
  of the published arithmetic epsilon factors.
- **Euler data.** The published `LocalFactors` (three functions `ℂ → ℂ`: L,
  dual L, epsilon), `FiniteEulerData (AllPlaces F)` with
  `AllPlaces F = InfinitePlace F ⊕ FinitePlace F`, and
  `exceptionalPlaces F B`, the finite set of all infinite places together with
  the finite places in `B`. The published predicates are:
  - `Admissible D S`: both partial L-functions are nonzero meromorphic, and so are
    the three local factors at each place of `S`. Here nonzero meromorphic means
    meromorphic with no identically zero germ.
  - `HasEulerProductsOutside D S σ`: for `Re s > σ`, both partial L-functions are
    the unconditional products (`HasProd`) of the local L-factors, respectively
    dual L-factors, over the places outside `S`.
  - `FunctionalEquation D S`:
    `L_S(s) ∏_{v ∈ S} L_v(s)` and
    `(∏_{v ∈ S} ε_v(s)) · L^∨_S(1 - s) ∏_{v ∈ S} L^∨_v(1 - s)` have equal punctured
    germs at every point (`MeromorphicEq`).

## Declarations

### `IsArithmeticPairLocalFactors K eC ε hε ψ X Y Xd Yd f`

Section `Local`, for a p-adic field `K : PadicField.{u} p`, a local-constant
system `(eC, ε, hε)`, `ψ : Correspondence.NontrivialAdditiveCharacter K`, pair
classes `X Y Xd Yd : Correspondence.LocalPairClass.{u, uV} K` and
`f : LocalFactors`. It is the conjunction of:

1. `f.lFactor s = RatFunc.eval (RingHom.id ℂ) (q^(-s))
   (Correspondence.arithmeticPairLFactor K X Y)` for every `s`, where `q` is the
   residue cardinality of `K` and `q^(-s)` is the published
   `RankinSelberg.spectralPoint q s`;
2. the same for `f.dualLFactor` and the pair `(Xd, Yd)`;
3. some `c : ℂˣ` and `m : ℤ` satisfy the published
   `Correspondence.IsArithmeticPairEpsilonFactor K eC ε hε ψ X Y c m`, and
   `f.epsilonFactor s = c q^(-ms)` for every `s` (published
   `RankinSelberg.epsilonMonomial q c m s`).

`arithmeticPairLFactor K X Y` is the published Euler factor
`det(1 - Φ X | (X ⊗ Y)^I)^(-1)` of the actual tensor product on `(ker N)^I`, at the
published geometric Frobenius lift, as a rational function of `X = q^(-s)`.
`IsArithmeticPairEpsilonFactor` asserts that admissible base data exist. Such data
consist of the transported character, a measure self-dual for it, and continuous
pairs restricting `X` and `Y`, together with a geometric Frobenius. It also
asserts that every admissible choice of these data gives the value `c q^(-ms)` at
every `s`. The self-dual measure is therefore built into the epsilon factor.

Values at poles are those of the totalized `RatFunc.eval`. This does not affect the
target: `Admissible` and `FunctionalEquation` depend only on germs at punctured
neighbourhoods. `HasEulerProductsOutside` uses only `Re s > σ`, where for
`σ` large no factor outside the exceptional set has a pole.

### `IsTwistedRelativePairFactorsAt c E ψ S S' χ z f`

For a finite place `z` of `F` and `f : LocalFactors`, this holds when there exist
`w`, `e` and `ι` with `IsLocalRelativeWeilMap z w.1 e ι`, and there exist `ψz`
and a local-constant system `(eCz, εz, hεz)` at `F_z` with
`IsCanonicalFiniteAdditiveComponent ψ z ψz`, such that
`IsArithmeticPairLocalFactors (padicField z) eCz εz hεz ψz X Y Xd Yd f` holds for

- `X = localPairClass (twist (χ ∘ τ_F) S) ι` and `Y = localPairClass S' ι`;
- `Xd = localPairClass (twist (χ ∘ τ_F) S).dual ι` and
  `Yd = localPairClass S'.dual ι`,

where `dual` is the published contragredient of a finite representation. So `f` is
the factor triple of `V_z = ((χ ∘ τ_F) ⊗ S ⊗ S') ∘ ι`. Its dual L-factor is that of
`V_z^∨ = (χ ∘ τ_F ⊗ S)^∨ ⊗ S'^∨`, and its epsilon factor is `ε(s, V_z, ψz)`.

### `assembledEulerData arch f Lp Lpd`

The published `FiniteEulerData (AllPlaces F)` with local factors
`Sum.elim arch f`, i.e. `arch v` at an infinite place `v` and `f z` at a finite
place `z`, and with partial L-functions `Lp` and `Lpd`. It is data only.

### `RelativeWeilTwistFunctionalEquationStatement`

The quantifiers, in order:

1. every `c` with `IsArithmeticClassFamily c`, every Galois pair of universe-`u`
   number fields `F ⊆ E`, and every `ψ` as above;
2. every pair `S`, `S'` of continuous representations of `W_{E/F}`, in carrier
   universe `uV`;
3. **there exist** a finite set `T₀` of finite places of `F` and an archimedean
   block `arch : InfinitePlace F → LocalFactors`;
4. for every `χ` of finite order with `χ.atInfinity = 1`;
5. for every finite set `B` of finite places with `T₀ ⊆ B` and `χ` unramified at
   every `z ∉ B`;
6. for every `f : FinitePlace F → LocalFactors` with
   `IsTwistedRelativePairFactorsAt c E ψ S S' χ z (f z)` at every finite place `z`;
7. **there exist** `σ : ℝ` and `Lp Lpd : ℂ → ℂ` such that, writing
   `D = assembledEulerData arch f Lp Lpd` and `Σ = exceptionalPlaces F B`,
   - `Admissible D Σ`,
   - `HasEulerProductsOutside D Σ σ`, and
   - `FunctionalEquation D Σ`.

Spelled out, the conclusion says the following. For `Re s > σ`,
`Lp(s) = ∏_{z ∉ B} L(s, V_z)` and `Lpd(s) = ∏_{z ∉ B} L(s, V_z^∨)` as convergent
products. `Lp`, `Lpd` and every factor at the infinite places and at the places of
`B` are nonzero meromorphic. Finally

`Lp(s) ∏_{v | ∞} L_v(s) ∏_{z ∈ B} L(s, V_z)
  = ∏_{v | ∞} ε_v(s) ∏_{z ∈ B} ε(s, V_z, ψz) · Lpd(1 - s) ∏_{v | ∞} L^∨_v(1 - s) ∏_{z ∈ B} L(1 - s, V_z^∨)`

as meromorphic functions. Here `(L_v, L^∨_v, ε_v) = arch v` does not depend on `χ`,
on `B` or on `f`.

Two properties of the hypothesis on `f` matter for how the target can be used:

- **Every choice.** The hypothesis lets each `f z` come from any local map, place
  above, reciprocity candidate, additive component and system. Each realized
  triple is a function of these local choices, so `∀ f` with this hypothesis says
  the same as: for every choice of local data at every finite place, the factors
  built from those choices satisfy the conclusion. The conclusion therefore holds
  for whatever choices a consumer makes, and no comparison between choices is
  needed.
- **Vacuity boundary.** The target does not assert that local maps, systems or
  admissible epsilon data exist. If at some finite place no realization exists, no
  `f` satisfies the hypothesis, and the target says nothing. Existence of local
  maps is the separately published `LocalRelativeWeilMapExistenceStatement`.
  Existence of systems is `LocalFactor.NonabelianSystem.Exists`, the
  Langlands–Deligne existence of local constants. Tate, printed p.15, notes that
  Deligne's proof of that existence uses the global functional equation in the form
  of (3.5) itself. Making the target conditional keeps the two results separate.

## Relation to the source

Tate (1979), §3.5, fixes a nontrivial character `ψ` of `A_F/F` and the Tamagawa
measure `dx` on `A_F`. He factors `dx = ∏ dx_v` with the integers of measure one
for almost all `v`. For a representation `V` of the global Weil group `W_F` he
defines `L(V, s) = ∏_v L(V_v ω_s)` (3.5.1) and
`ε(V, s) = ∏_v ε(V_v ω_s, ψ_v, dx_v)` (3.5.2). Theorem 3.5.3 states that (3.5.1)
converges in a right half-plane, is meromorphic in the whole plane, and satisfies
`L(V, s) = ε(V, s) L(V^*, 1 - s)` (3.5.4). By "representation" Tate means a
continuous homomorphism to `GL(V)` with `V` finite-dimensional complex (§2.1,
printed p.9). Every such representation factors through some `W_{E/F}` (same
page). Henniart (2000), §2.1, fixes such a `ψ`. His §2.3 Théorème concerns
continuous representations `S`, `S'` of `W_F` and their twists by characters of
`A_F^×/F^×`, and his proof uses the global functional equations of the pair
L-functions. The target differs from Tate's theorem in the following derived
respects.

- **Relative Weil group.** The target is stated on `W_{E/F}` for an arithmetic
  class family. A representation of `W_F` that factors through `W_{E/F}` is a
  representation of `W_{E/F}`, and its local components are its compositions with
  the local maps `W_{F_z} → W_{E/F}`.
- **Pairs and twists.** `V` is the tensor product of `(χ ∘ τ_F) ⊗ S` with `S'`.
  The dual is taken factor by factor, `V^* = ((χ ∘ τ_F) ⊗ S)^∨ ⊗ S'^∨`. The
  characters `χ` are the finite-order characters trivial at infinity that
  Henniart's twisting argument uses. They are also the characters quantified in the
  published consumer `CommonTwistEulerInputs`.
- **Finite L-factors.** Tate's `L(V_z ω_s)` is `det(1 - Φ q^(-s) | V_z^I)^(-1)` for
  an inverse (geometric) Frobenius `Φ` ((3.3.2), printed p.14). This is
  `arithmeticPairLFactor` evaluated at `q^(-s)`, because the zero-monodromy class
  has `ker N` equal to the whole space. Tate's convention that uniformizers
  correspond to inverse Frobenius elements ((1.4.1), printed p.6) is the geometric
  normalization. The published `IsLocalRelativeWeilMap` imposes the same
  normalization through `GeometricWeilReciprocityRelation`, as does
  `NormalizedReciprocity` inside `IsSystem`. The local maps are normalized
  compatibly with the arithmetic normalization of the class family. With these
  conventions `(χ ∘ τ_F) ∘ ι` is the local component of `χ` composed with local
  reciprocity. That is a property of the published objects and is not restated
  here.
- **Finite epsilon factors and measures.** The target uses at every finite place
  a measure self-dual for `ψz`, built into `IsArithmeticPairEpsilonFactor`. The
  product of the local self-dual measures is the Tamagawa measure (Tate, §3.6,
  printed p.17), and the global `ε(V, s)` depends only on the product measure by
  (3.4.3). So this specializes the source's choice, exactly as in the published
  `HeckeGlobalFunctionalEquationStatement`. The form `c q^(-ms)` is (3.4.5).
- **Exceptional set.** The source asserts implicitly that (3.5.2) is a finite
  product. The target places every epsilon factor in `exceptionalPlaces F B` and
  omits the others. That is correct exactly when `ε(s, V_z, ψz) = 1` for `z ∉ B`.
  By (3.4.6) and (3.2.6.1) this holds when `V_z` is unramified, `n(ψz) = 0`, and
  the self-dual measure gives the integers measure one. The last condition follows
  from `n(ψz) = 0`. The existential `T₀` is meant to contain the finite places
  where `S` or `S'` ramifies or the component of `ψ` has nonzero conductor. Every
  `B ⊇ T₀` outside which `χ` is unramified is then admissible. `B` is universally
  quantified, so any such enlargement chosen later by a consumer is covered.
- **Separated Euler product.** The partial L-functions `Lp`, `Lpd` are the Euler
  products over the finite places outside `B`. The remaining factors are written
  out separately. By `HasEulerProductsOutside` they are the limits of those
  products on the half-plane, hence uniquely determined there.
- **Nonvanishing.** `Admissible` asks for nonzero meromorphic functions, which is
  slightly more than Tate's meromorphy. For the partial L-functions it follows
  from the nonvanishing of a convergent Euler product of nonzero factors on the
  half-plane. For the finite exceptional factors it holds because they are
  reciprocals of polynomials in `q^(-s)` with constant term one, and nonzero
  monomials.
- **Archimedean block.** The archimedean factors are not identified with Tate's
  archimedean `L(V_v ω_s)` and `ε(V_v ω_s, ψ_v, dx_v)`. The Library has no maps from
  archimedean local Weil groups into `W_{E/F}`: the published
  `IsLocalRelativeWeilMap` is stated only at finite places, so the archimedean
  components of `V` cannot yet be formed. The target therefore asserts only that
  some nonzero meromorphic archimedean block, chosen after `S`, `S'` and `ψ`,
  makes the functional equation hold for every `χ`. Tate's factors are such a
  block, because `χ` is trivial on the archimedean ideles. The archimedean
  components of `χ ∘ τ_F` are then trivial, so the archimedean components of `V`
  are those of `S ⊗ S'` for every `χ`. The block is chosen before `χ`, so the
  target asserts more than meromorphy. For any two admissible `χ` it says that the
  quotient `ε_∞(s) L^∨_∞(1 - s) / L_∞(s)` of the archimedean contributions is the
  same function. That is the archimedean input of Henniart's twisting comparison
  and of the published `InfinityGammaPreservation`. The target does not say that
  the block is Tate's.
- **No semisimplicity.** Tate's representations, and Henniart's in §2.2, are only
  continuous, and so are `S` and `S'`. Nothing in the target needs more. The image
  of inertia under `ι` is compact, so `(-)^I` is exact on continuous
  representations and `det(1 - Φ X | V^I)` depends only on the class of `V` in the
  Grothendieck group. The published local-constant assignments are defined on the
  exact Grothendieck group (`LocalFactor.CommonClosure.Virtual`).

The target is the Galois-side input of the published conditional
`RelativeGammaComparisonStatement`. That statement retains `CommonTwistEulerInputs`,
`InfinityGammaPreservation` and `FiniteTwistGammaRealizations` as hypotheses, and
the arithmetic halves of those hypotheses are of the shape asserted here. The
adapter that packages this target as a `HeckeEulerFamily` is separate work.

## Original sources

- John Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II
  (1979), 3–26. Printed page `p` is PDF page `p + 9`. The pages read and used
  here are:
  - (1.4.1), printed p.6, for the normalization of uniformizers to inverse
    Frobenius elements;
  - §2.1, printed p.9, for representations as continuous homomorphisms
    factoring through some `W_{E/F}`;
  - (3.2.6.1), printed pp.13–14, for the unramified epsilon factor;
  - (3.3.2), printed p.14, for the local L-factor at an inverse Frobenius;
  - (3.4.3)–(3.4.6), printed p.15, for the measure dependence, the form of
    `ε(V ω_s)` in `s`, and the unramified case. The same page notes that
    Deligne's existence proof of the local constants uses the global functional
    equation.
  - §3.5, (3.5.1)–(3.5.4) and Theorem 3.5.3, printed pp.15–16;
  - §3.6, printed p.17, for self-dual measures and the Tamagawa measure.

  Source `tate-1979-number-theoretic-background`, SHA256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
- Guy Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
  corps p-adique*, Invent. Math. 139 (2000), 439–455. §2.1 and §2.2, p.444, for the fixed
  global additive character and continuous representations of `W_F`. §2.3,
  pp.444–445, for the Théorème on pairs of continuous representations and the use
  of the global functional equations of pair L-functions. Source
  `henniart-2000-simple-proof`, SHA256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

## Dependencies and acceptance boundary

The module imports `Langlands.Global.Factors.HeckeTwistComparisonStatement`
(Lean SHA256 `6b109c36b8fb0183fa9ed6d398b4b7393cb0b2b8c972b93ca46945e98c15e9f5`)
and `Langlands.Automorphic.AssociatedDeterminantTwistStatement` (Lean SHA256
`5bd3c3547958db145b004cafaf39273605466193a3c02b52996e78b7c2cb0df4`). Both are
published at Library commit `63d0c9b9d2720e646aa7abb360a08988aee052bf`, and every
other declaration used comes through them.

The module compiled with no errors or warnings in the project environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, as a draft (check `dc1a1f10`) and in the
workspace (check `d70ad05d`). Inspection of
`RelativeWeilTwistFunctionalEquationStatement` reports a `Prop`-valued definition
with level parameters `u`, `uV`, `uE` and only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

These development checks provide neither independent semantic acceptance nor a
proof of the functional equation.
