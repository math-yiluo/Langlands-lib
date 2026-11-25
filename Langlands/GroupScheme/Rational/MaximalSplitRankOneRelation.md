# The rank-one relation for an equivariant line in a nonmultipliable root group

This module is an interface of the proof of Borel–Tits 1965, Théorème 7.2. Its input is the
output of `MaximalSplitSubgroup.exists_line_through_rootPoint`
(`Rational.MaximalSplitRankOneLine`). Its output is the rank-one relation that the
generated-subgroup argument of that proof consumes (`MaximalSplitSubgroupLines`,
`MaximalSplitGeneratedWeyl`).

Throughout, `k : Type u` is a field and `G` is a group scheme over `Spec k`. `S` is a
commutative group scheme over `Spec k`, and `i : S.toGrp ⟶ G` is a homomorphism. Notation:

- `RootCell.Ga k` is `𝔾ₐ`.
- For `u : 𝔾ₐ ⟶ G`, `rootPoint u Z c` is the point `u(c)` over a test scheme `Z`, for a
  global function `c`. This is the published `LocalSplitCell.rootPoint`.
- `G.constantPoint n Z` is the pullback to `Z` of a rational point `n`.
- `VectorGroup.IsTorusEquivariant i x a` is the published all-test conjugation law
  `t x(c) t⁻¹ = x(a(t) c)`.
- `latticeReflectionIso a ν h` is the published involution `1 - a ⊗ ν` of `S`, for
  `⟨a, ν⟩ = 2`.
- `RootCell.RelationOver i ν x y Z` is the published rank-one relation over `Z`: for points
  `X`, `Y` with `u = 1 + XY` a unit, `x(X) y(Y) = y(u⁻¹Y) · i(ν(u)) · x(u⁻¹X)`.

## Main theorem

`MaximalSplitSubgroup.exists_rankOneRelation`. Assume:

- `G` is affine (`[IsAffineHom G.X.hom]`) with `IsConnectedReductive G`;
- `i` is a maximal split torus (`IsMaximalSplitTorus i`);
- `a ∈ roots i` and `(2 : ℤ) • a ∉ roots i`;
- `x : 𝔾ₐ ⟶ G` is a monomorphism with `IsTorusEquivariant i x a` and
  `range x ≤ RelativeRoot.subgroup i a`.

Then there are a cocharacter `ν`, a proof `hpair : ⟨a, ν⟩ = 2` and a rational point `n` with:

1. `IsTorusEquivariant i (oppositeLine x n) (-a)`;
2. `oppositeLine x n` is a monomorphism;
3. `range (oppositeLine x n) ≤ RelativeRoot.subgroup i (-a)`;
4. `n = y(-1) * x(1) * y(-1)`, where `y = oppositeLine x n`, an explicit word in the two
   lines;
5. `IsNormalizingPoint i n (latticeReflectionIso a ν hpair)`, so `n i(t) n⁻¹ = i(s_a t)`;
6. `RootCell.RelationOver i ν x (oppositeLine x n) Z` for every test scheme `Z`.

The entry definition `oppositeLine x n` is `scaleHom (-1) ≫ x ≫ (G.innerIso n⁻¹).hom`.
Pointwise it is `t ↦ n⁻¹ x(-t) n` (`rootPoint_oppositeLine`), and `mono_oppositeLine` shows it
is monic when `x` is.

The section `Reflection` gives the reflection formulas in the form the generated-subgroup
argument uses:

- `cocharacter_comp_reflection`: `ξ ≫ s_a = ξ - ⟨a, ξ⟩ • ν`;
- `groupHom_comp_reflection_of_pairing_eq_zero`: `s_a` fixes every cocharacter `ξ` with
  `⟨a, ξ⟩ = 0`;
- `reflection_inv_comp_character`: `s_a⁻¹ ≫ χ = χ - ⟨χ, ν⟩ • a`.

## Proof

1. **Rank-one data.** Let `u = x(1)`. It lies in `U_(a)` and is nontrivial, since `x` is
   monic and `1 ≠ 0` in `Γ(Spec k)` (`rootPoint_one_ne_one`). The published
   `rootRankOneFactorization` gives a normalizing opposite factor pair `p` with
   `n = p.1 u p.2`. Since `2a` is not a root, it also gives `p.1 = p.2` and `p.1 = n⁻¹ u n`.
   The published `IsOppositeFactorPair.coroot_spec` gives `ν` with `⟨a, ν⟩ = 2` and Weyl
   action `χ ↦ χ - ⟨χ, ν⟩ a`. By `IsSplitTorus.iso_ext_of_character_congr` and
   `characterAut_latticeReflectionIso`, the normalizing automorphism of `n` is
   `latticeReflectionIso a ν hpair`, which proves clause 5. Then `y(-1) = n⁻¹ x(1) n = p.1`,
   which proves clause 4.
2. **The opposite line** (clauses 1–3). `isTorusEquivariant_oppositeLine` conjugates
   `n⁻¹ x(-c) n` by `t` and uses `n t n⁻¹ = s_a(t)` together with `s_a ≫ a = -a`
   (`reflection_comp_root`). For clause 3, the published `RelativeRoot.normalizer_conj_mem`
   applied to `n⁻¹` moves `U_(a)` to `U_(weylAction n⁻¹ a) = U_(-a)`.
3. **The Weyl identity at character values** (`weyl_cu`). For a torus point `t` with
   `e = a(t)`, conjugating `n = y(-1) x(1) y(-1)` by `t` gives
   `y(-e⁻¹) x(e) y(-e⁻¹) = t n t⁻¹`. The reflection formula `s_a(t) = t · ν(a(t))⁻¹`
   (`comp_reflection`) gives `t n t⁻¹ = n ν(e)⁻¹` (`conj_constantPoint_eq`).
4. **Descent** (`weylWord_eq`). Write `W(c) = y(-c⁻¹) x(c) y(-c⁻¹) ν(c)`. `W` is natural in
   the test scheme (`comp_weylWord`). At the universal unit on `𝔾_m`, the identity `W = n`
   holds after pulling back along `a : S → 𝔾_m`, by step 3 at the universal torus point.
   The published `RelativeRoot.characterFpqc` makes `a` flat and surjective, hence an
   epimorphism, so `W = n` holds on `𝔾_m`. Pulling back along the classifying map of an
   arbitrary unit gives `W(c) = n` for every unit `c` on every test scheme.
5. **Group algebra.**
   - `coroot_mul_constantPoint`: `ν(c) n = n ν(c)⁻¹`, since `s_a(ν(c)) = ν(c)⁻¹`.
   - `constantPoint_mul_self`: `n² = ν(-1)`, from step 4 at `c = ±1`.
   - `coroot_conj_line` and `coroot_conj_oppositeLine`: `ν(c)` scales `x` by `c²` and `y` by
     `c⁻²`.
   - `relation_of_isUnit`: let `X` be a unit and `u = 1 + XY`. Step 4 at `c = X` gives
     `x(X) = y(X⁻¹) n ν(X)⁻¹ y(X⁻¹)`. Step 4 at `d = -X u⁻¹` gives
     `y(X⁻¹ + Y) = n ν(d)⁻¹ y(d⁻¹) x(-d)`. The previous facts give
     `n ν(X)⁻¹ n ν(d)⁻¹ = ν(u)`. Moving `ν(u)` past `y(d⁻¹)` then yields
     `x(X) y(Y) = y(u⁻¹Y) ν(u) x(u⁻¹X)`.
6. **All test schemes.** Over the spectrum of a field, every global function is zero or a
   unit (`eq_zero_or_isUnit_of_field`). If `X = 0`, then `u = 1` and the relation is
   trivial. Otherwise step 5 applies (`relationOver_field`). The published
   `RootCell.relationOver_of_isAlgClosed` (it needs `G` separated) extends the relation from
   algebraically closed fields to every test scheme (`relationOver`).

## Scope and sources

The field is arbitrary: any characteristic, perfect or not, finite or infinite. The proof
does not use Zariski density of rational points, and it does not use Borel–Tits 3.22. The
mathematics follows Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015):

- Proposition C.2.24, printed p.620 (PDF p.646): the rank-one factorization
  `m(u) = v u v` with `v = m(u)⁻¹ u m(u)`;
- the proof of Theorem C.2.30, Steps 1–2, printed pp.631–632 (PDF pp.657–658): the opposite
  line `E_{-a} = n⁻¹ E_a n` and the rank-one relations.

CGP use density of rational points over an infinite field in Step 2. Here that is replaced by
fpqc descent along `a` and the field case analysis above, which work over every field.
