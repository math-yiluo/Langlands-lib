# The cubic bundle determines the polarization (proof)

`Langlands.AbelianScheme.PolarizedFiniteLevel.cubicBundlePolarizationDetermination`
proves the published statement
`CubicBundlePolarizationDeterminationStatement` (universe `u`), exactly as stated
and with no added hypotheses. Fix `P`, a locally noetherian `S`, data `a b`,
an isomorphism `e : a.abelian ≅ b.abelian`, a line bundle `N` on `S` and an
isomorphism `I : (hom e.hom)^* b.cubicBundle ≅ a.cubicBundle ⊗ π_a^* N`. The
theorem concludes `a.polarization = e.hom ≫ b.polarization ≫ e^∨`, where
`e^∨ = a.dualWitness.map P b.dualWitness e.hom`.

The proof works relatively over `S`, with all points `Z ⟶ A.X` of `Over S`. It
does not compare geometric fibres and does not use rigidity. The only use of
"locally noetherian" is the derived instance `QuasiSeparatedSpace S`, which the
relative diagonal Mumford theorem needs.

## Classes and the four-term class

Line-bundle classes are elements of the commutative group
`IsoClasses P.preservation X` of isomorphism classes, with `pullbackHom` the
pullback homomorphism. For a Poincaré family on `T ×_S A`, the published
`familyPointClass` is the class at `Z` of its pullback along the point
`(z, x) : Z ⟶ T ×_S A`.

For a class `q` on `A.X.left` and points `x y : Z ⟶ A.X`, the private
`bundleCoboundary` is the four-term class on `Z.left`

`[(x y)^* q] · [x^* q]⁻¹ · [y^* q]⁻¹ · [1^* q]`,

where `x y` is the group-law product of points and `1 : Z ⟶ A.X` is the unit
point. The unit term makes it insensitive to bundles from the base, which need
not be trivial here. Three elementary properties are proved:

- `bundleCoboundary_twist`: replacing `q` by `q · π^* r` for a class `r` on `S`
  does not change it. Each of the four points composes with `π` to the structure
  morphism of `Z` (`Over.w`), so the four pullbacks of `π^* r` are equal and cancel
  (signs `+ − − +`). The cancellation is a commutative-group calculation
  (`abel` after `Additive.ofMul`).
- `bundleCoboundary_pow`: the four-term class of `q^k` is the `k`-th power of
  that of `q`, because pullback maps are group homomorphisms and the class group
  is commutative.
- `bundleCoboundary_pullback`: for a homomorphism `f : A ⟶ B` and a class `q` on
  `B`, the four-term class of `(hom f)^* q` at `(x, y)` is that of `q` at
  `(x ≫ f, y ≫ f)`. This uses that `f` respects the product of points and the
  unit (`MonObj.mul_comp`, `MonObj.one_comp`).

## The Mumford map in terms of the four-term class

`familyPointClass_mumford_eq_coboundary`: let `L` be a line bundle on `A` with any
normalization data `(N, evN, M, evM)` for the published
`mumfordSchemeMapOfLineBundle`, and write `φ_L` for that Mumford scheme map
`A.X ⟶ A^∨`. Then the class of the Poincaré family at `(x ≫ φ_L, y)` is the
four-term class of `[L]` at `(x, y)`.

Proof: by `familyPointClass_relativePullback` the left side is the class of the
relative pullback of the Poincaré family along `φ_L`, and
`mumfordSchemeMapOfLineBundlePullbackIso` with `familyPointClass_eq_of_iso`
replaces it by the Mumford family of `L`. `familyPointClass_mumfordFamily`
evaluates that class as `[(x y)^*(L ⊗ π^* N)] · [x^* M] · [y^* M]`. The
evaluations `evN` and `evM` give `[N] = [ε^* L]⁻¹` and
`[M] = ([L] · [π^* N])⁻¹`, where `ε` is the unit section. Since every point composes
with `π` to the structure map of `Z`, and the unit point has underlying map `π_Z ≫ ε` (`unitPoint_left`), each
`π^* N` term becomes `[1^* L]⁻¹`. Collecting terms gives the four-term class (the
same `abel` calculation).

## The Mumford map of the cubic bundle

`familyPointClass_cubic`: for a datum `a` over a quasi-separated base, the class of
the Poincaré family at `(x ≫ (6λ_a), y)` is the four-term class of
`[a.cubicBundle]`. Here `(6λ_a)` denotes the underlying scheme map of
`6 • a.polarization`.

The published relative theorem `polarizationDiagonalMumford` (GIT
Proposition 6.10) supplies normalization data for `a.canonicalBundle = (1, λ_a)^* 𝒫`
whose Mumford scheme map is that of `2 • a.polarization`. The previous lemma
then gives the claim with exponent `2` and `a.canonicalBundle`. The cubic bundle has
class `[a.canonicalBundle]^3` (`isoClass_tensorPow`). By `bundleCoboundary_pow` its
four-term class is the cube. On the other side, `groupHom_nsmul_hom`
identifies the scheme map of `k • λ` with the `k`-th pointwise power of `λ`, and
`MonObj.comp_pow` with `familyPointClass_poincareFamily_pow_left` turns powers
in the dual variable into powers of classes. Thus `6 = 2 · 3` matches both sides.
`isoClass_tensorPow`, `groupHom_nsmul_hom` and
`familyPointClass_poincareFamily_pow_left` are published in
`CubicBundleMumfordProof` without any field hypothesis.

## Dual maps and detection by classes

`familyPointClass_dualMap`: for `f : A ⟶ B`, a point `z : Z ⟶ B^∨` and
`x : Z ⟶ A.X`, the class of `A`'s Poincaré family at `(z ≫ f^∨, x)` equals the
class of `B`'s Poincaré family at `(z, x ≫ f)`. The dual map has underlying map
`dualSchemeMap homPicardZeroPullback f` (definitional unfolding of
`DualWitness.map`). Its defining isomorphism `dualSchemeMapPullbackIso` identifies
the relative pullback of `A`'s Poincaré family with the pullback of `B`'s family
along `1 × f` (`homFamilySpaceMap f`). The points satisfy
`(z, x) ≫ (1 × f) = (z, x ≫ f)`, which is checked on both projections
(`homFamilySpaceMap_fst`, `homFamilySpaceMap_snd`), and
`isoClass_pullback_pullback` concludes.

`eq_of_familyPointClass_eq`: two scheme maps `p q : A.X ⟶ A^∨` are equal if the
Poincaré classes at `(x ≫ p, y)` and `(x ≫ q, y)` agree for all test points. Take
the tautological points `relativeFst`, `relativeSnd` on `A ×_S A`. Then the hypothesis
is an equality of classes of the underlying bundles of the two relative pullbacks of
the Poincaré family (`familyPointClass_relativePullback`,
`isoClass_forget_eq_familyPointClass`), hence an isomorphism of underlying line
bundles (`LineBundle.isoClass_eq_iff`). Since the rigidification section has a
retraction, `RigidifiedLineBundle.nonempty_iso_of_forget_iso` upgrades it to an
isomorphism of rigidified bundles. Then the published
`eq_of_nonempty_relativePullback_poincareFamily_iso` (injectivity of Poincaré
classification) gives `p = q`.

## The main argument

Put `λ' = e.hom ≫ b.polarization ≫ e^∨`. The hypothesis `I` gives
`(hom e.hom)^*[b.cubicBundle] = [a.cubicBundle] · π_a^*[N]`.

1. The scheme maps of `6 • a.polarization` and `6 • λ'` are equal, by
   `eq_of_familyPointClass_eq`. The scheme map of `6 • λ'` is
   `e ≫ (6λ_b) ≫ e^∨` (`Preadditive.comp_nsmul`, `Preadditive.nsmul_comp`). For
   test points `x, y`, `familyPointClass_dualMap` turns the class at
   `(x ≫ e ≫ (6λ_b) ≫ e^∨, y)` into `b`'s class at `(x ≫ e ≫ (6λ_b), y ≫ e)`.
   `familyPointClass_cubic` for `b` gives the four-term class of `[b.cubicBundle]`
   at `(x ≫ e, y ≫ e)`. `bundleCoboundary_pullback` gives that of
   `(hom e.hom)^*[b.cubicBundle]` at `(x, y)`. By the hypothesis and
   `bundleCoboundary_twist` this is the four-term class of `[a.cubicBundle]`, which
   is the class at `(x ≫ (6λ_a), y)` by `familyPointClass_cubic` for `a`.
2. Multiplication by `6` on `a.abelian` is an isogeny (published
   `GroupScheme.multiplicationIsogeny`: smooth, proper, geometrically connected, and
   `6 ≠ 0`). Its underlying scheme morphism is therefore an effective epimorphism
   (`IsIsogeny.effectiveEpi`), hence an epimorphism in `Over S`
   (`Over.epi_of_epi_left`). For every homomorphism `v`, `[6] ≫ v` has the same
   scheme map as `6 • v` (`GroupScheme.multiplication_hom`, `GrpObj.zpow_comp`,
   `groupHom_nsmul_hom`). Cancelling `[6]` gives equal scheme maps for
   `a.polarization` and `λ'`. `Grp.hom_ext` and injectivity of `Additive.toMul`
   make them equal homomorphisms of abelian schemes.

## Relation to the literature

The statement is the step in Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*,
3rd ed. (1994), §7.2, printed p.131 (PDF p.144), registered source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`:
`L_Δ(ω)^3` is determined up to a bundle from the base, and since the group of
`S`-homomorphisms from `X` to `X̂` has no torsion, `ω` is determined. The proof above
follows this argument. The Mumford map of `L_Δ(λ)^3` is `6λ`. A base twist does not
change it, and pullback along `e` conjugates it by `e` and its dual. The torsion-freeness
input is used only for `6`, as the fact that `[6]` is an epimorphism of
`S`-schemes, so it holds over any base. The fibrewise route via geometric fibres and rigidity
(GIT Corollary 6.2) mentioned in the task context is not needed.
