# Rational Levi conjugacy from dynamic parabolics

Author: Worker 1491.

This module reduces the published `RationalLeviConjugacyStatement` to three
inputs. Two of them are published statements about connected reductive groups.
The third is a conjugacy statement for cocharacters, supplied as an explicit
hypothesis. Nothing in the module is conditional beyond these hypotheses. In
particular, the radical comparison, the source isomorphism and the uniqueness of
the conjugating point are all proved here for actual scheme morphisms.

The inputs of `rationalLeviConjugacy_of_dynamic` are:

- `ParabolicDynamicStatement`: every rational parabolic `j : P → G` of a
  connected reductive `G` has `range j = P_G(χ)` for some cocharacter `χ`.
- `DynamicGeometricUnipotentRadicalStatement`: a closed representative of
  `U_G(χ)`, factored through a representative of `P_G(χ)`, is a geometric
  unipotent radical in the semistandard sense (`IsGeometricUnipotentRadical`).
- `hlift`: over a field, for an affine group `G` and cocharacters `χ`, `ψ` with
  `ψ · χ⁻¹ ∈ U_G(χ)(𝔾_m)` (a statement about the universal point of `𝔾_m`), there
  is a rational point `u ∈ U_G(χ)(k)` with `χ ≫ Int(u) = ψ`.

## Mathematical source and provenance

The target is Borel–Tits, *Groupes réductifs* (1965), Corollary 3.14 (printed
p.80, PDF p.27), specialized to parabolics as recorded in the target statement's
Markdown. The route here is derived: it is the dynamic description of
parabolics, not the argument of Borel–Tits. It uses the semidirect decomposition
`P_G(χ) = Z_G(χ) ⋉ U_G(χ)` of Conrad–Gabber–Prasad, *Pseudo-reductive groups*
(2nd ed., 2015), Proposition 2.1.8(2), printed p.53 / PDF p.79. In the Library
this is `Dynamic.limit` with `Dynamic.limit_mem_centralizer`,
`Dynamic.mul_inv_limit_mem_unipotent` and the uniqueness of limits
`Dynamic.HasLimit.unique` for separated `G`.

## Declarations over an arbitrary base scheme

Fix `χ : 𝔾_m → G` with `G` separated, a representative `j : P → G` of `P_G(χ)`
(`hj : (Dynamic.parabolic χ).IsRepresentedBy j`), a homomorphism `l : L → P`,
and a retraction `q : P → L` with `l ≫ q = 𝟙` whose kernel on every test scheme
is `U_G(χ)`. That is, `hker : x ≫ q = 1 ↔ x ≫ j ∈ U_G(χ)(T)` for every point `x`
of `P`.

- `range_le_parabolic χ`: the points of `χ` lie in `P_G(χ)`.
- `parabolicCocharacter χ hj`: the factorization of `χ` through `j`
  (`SubgroupFunctor.IsRepresentedBy.factorHom`). Its defining property is
  `parabolicCocharacter_comp`. `mem_parabolic_comp` and
  `exists_comp_eq_of_mem_parabolic` translate between points of `P` and points of
  `P_G(χ)`.
- `hom_hom_comp_hom_hom`: `l ≫ q = 𝟙` on underlying morphisms.
- `centralizer_leviCocharacter_eq_top`: the Levi cocharacter
  `χ_L = parabolicCocharacter χ hj ≫ q` is central in `L`, that is,
  `Z_L(χ_L)` is all of `L`. Proof: for a point `y` of `L`, let `z` be the limit
  of `l(y)` in `Z_G(χ)`, and write `z = zP ≫ j`. Then `l(y) zP⁻¹` maps into
  `U_G(χ)`, so `q` kills it, and `y = q(l(y)) = q(zP)`. The point `zP`
  centralizes `parabolicCocharacter χ hj` (`Dynamic.centralizer_eq_comap_of_mono`).
  Hence `q(zP)` centralizes `χ_L` (`Dynamic.centralizer_le_comap`).
- `leviCocharacter_mul_inv_mem`: `(χ_L ≫ l ≫ j) · χ⁻¹ ∈ U_G(χ)(𝔾_m)`. Writing
  `x` for the universal point of `parabolicCocharacter χ hj`, the point
  `q(l(q(x))) · q(x)⁻¹ = 1` shows that `l(q(x)) · x⁻¹` lies in the kernel of `q`.
- `range_comp_innerIso_inv_eq_centralizer`: let `u ∈ U_G(χ)(S)` satisfy
  `χ ≫ Int(u) = χ_L ≫ l ≫ j`. Then the image of `l ≫ j ≫ Int(u)⁻¹` is exactly
  `Z_G(χ)` on every test scheme.
  - Inclusion: `Z_G(χ)` is the preimage of `Z_G(χ_L ≫ l ≫ j)` under `Int(u)`
    (`Dynamic.centralizer_eq_comap_of_iso`), and centrality of `χ_L` sends every
    point of `L` into `Z_G(χ_L ≫ l ≫ j)`.
  - Reverse inclusion: for `z ∈ Z_G(χ)(T)`, the point `u z u⁻¹` lies in
    `P_G(χ)`; write it as `pz ≫ j`. Then `w = l(q(pz))⁻¹ pz` lies in the kernel
    of `q`, so its conjugate by `u⁻¹` lies in `U_G(χ)`. That conjugate is also
    `b⁻¹ z` with `b` in the image, which lies in `Z_G(χ)` by the inclusion. As
    `Z_G(χ) ∩ U_G(χ) = 1` (`Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent`),
    `z = b`.
- `eq_one_of_comp_innerIso`: with `u` as above, let `g` be a base point of `P`
  with `g ≫ j ∈ U_G(χ)` and `l ≫ Int(g) = σ ≫ l` for an automorphism `σ` of `L`.
  Then `g = 1`. Composing with `q` gives `σ = 𝟙`, because `Int(g) ≫ q = q ≫ Int(q(g))`
  (`innerIso_hom_comp`) and `q(g) = 1`. Hence `Int(g ≫ j)` fixes `l ≫ j`. So
  `u⁻¹ (g ≫ j) u` fixes `χ` (`mem_torusCentralizer_base_iff`), and lies in
  `Z_G(χ) ∩ U_G(χ) = 1`.

## Declarations over a field

- `mem_range_radical_iff`: let `G` be connected reductive, `j` a closed
  representative of `P_G(χ)` and `r : U → P` a radical satisfying
  `LeviSubgroup.IsGeometricUnipotentRadical`. Given
  `DynamicGeometricUnipotentRadicalStatement`, a point `x` of `P` lies in the
  image of `r` if and only if `x ≫ j ∈ U_G(χ)`. Proof: the Library's closed
  representative `Dynamic.Affine.unipotentHom χ` of `U_G(χ)` factors through `j`
  as `r'`, and the published statement makes `r'` a semistandard geometric
  unipotent radical. The ground-field greatestness of `r` gives
  `range r' ≤ range r`. The algebraic-closure greatestness of `r'`, applied to
  the base change of `r`, gives the reverse inclusion after base change. It
  descends along the fpqc map `Spec k̄ → Spec k`
  (`SubgroupFunctor.le_range_of_baseChange_le`).
- `rationalLeviConjugacy_of_dynamic`: the reduction.
  1. Choose `χ` with `range j = P_G(χ)`.
  2. For each Levi, the Library retraction
     (`IsRationalLeviSubgroup.exists_unipotentRadical_retraction`) has kernel
     the image of a radical `r₀`. Since `range r₀ = range r`
     (`IsUnipotentRadical.range_eq`), its kernel is `U_G(χ)` by
     `mem_range_radical_iff`.
  3. `hlift`, applied to `leviCocharacter_mul_inv_mem`, gives `u₁` and `u₂`.
     `range_comp_innerIso_inv_eq_centralizer` shows that the two conjugated
     Levis both have image `Z_G(χ)`.
  4. `SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` gives `e : L ≅ L'`.
     Write `u_i = v_i ≫ j`. Cancelling the monomorphism `j` shows
     `l ≫ Int(v₂ v₁⁻¹) = e ≫ l'`. Since `v₂ v₁⁻¹` maps into `U_G(χ)`, it is
     `q ≫ r` for a rational point `q` of `U`.
  5. Uniqueness: let `q'` and `e'` be another solution. Then
     `g = (q ≫ r)⁻¹ (q' ≫ r)` satisfies `l ≫ Int(g) = (e' ≪≫ e⁻¹) ≫ l`, so
     `eq_one_of_comp_innerIso` gives `g = 1`. As `r` is a monomorphism, `q' = q`.

The equalities are equalities of group-scheme morphisms. So the conclusion
compares the actual morphisms on every test scheme, as the target requires.
