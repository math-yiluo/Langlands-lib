# Axioms V 2 and V 5 for the Chevalley root function family

This internal unit proves the rank-one axioms V 2 and V 5 of a valuation of the
root datum (Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, Definition
6.1.2; Lemma 6.1.1 for the split case) for the published Chevalley root function
family `ChevalleyRootFamily.family G omega`. Here `G` is a Chevalley group of
the split existence construction, for Chevalley data of a finite reduced root
datum with finite free weight lattice, and `G.H` is affine and locally of finite
type. The function `omega` is an additive valuation of the field. The V 2 and V 5
theorems also assume the instances `IsAffineHom G.H.X.hom` and
`Mono G.t.hom.hom.left`.

## Values on root points

- `family_rootPt`: on the root point `u_j(s)` (the published `rootPt`), the
  family at the root character of `j` takes the value `omega s`.
- `omega_sign`: the valuation of an integral sign `±1` is zero.

## Axiom V 5

`opposite` is exactly the V 5 field of the published `IsRootDatumValuation`.
Let `u` be a nonidentity point of a root group, and `u', u''` points of the
opposite root group with `u' u u''` in the normalizer. Then
`φ_{-a}(u') + φ_a(u) = 0`.

The proof writes `u = u_j(S)` with `S ≠ 0`. The published
`exists_isOppositeFactorPair_rootPt` gives the explicit pair
`(u_{-j}(ε S⁻¹), u_{-j}(ε S⁻¹))` with a sign `ε`. The published uniqueness
`IsOppositeFactorPair.eq` identifies the given pair with it. Hence
`φ_{-a}(u') = omega(ε S⁻¹) = -omega(S)`.

## Reflection elements

- `ActsByReflection G α m` states that the Weyl action of a normalizer point `m`
  on characters is the reflection `s_α` on the published characters
  `charOf k x`.
- `ConjToNeg G α m` states that conjugation by `m` sends each root point
  `u_α(s)` to `u_{-α}(ε s)` for a fixed sign `ε`. Here `-α` is the index
  `P.reflectionPerm α α`.
- `HasReflectionElement G α` states that some normalizer point has both
  properties.
- `weylNormalizer G i` is the published simple Weyl point `n_i` as a normalizer
  point. `weylNormalizer_actsByReflection` states that it acts by `s_i`. The
  proof uses uniqueness of the normalizing automorphism and the published
  `torusAut_inv_comp_charOf`.
- `ActsByReflection.inv` and `ActsByReflection.conj` state that the property
  passes to inverses and to conjugates by simple Weyl points, with the reflected
  root. The latter uses Mathlib's
  `reflection_reflectionPerm : s_{s_j α} = s_j s_α s_j`.
- `hasReflectionElement_simple`, `HasReflectionElement.neg` and
  `HasReflectionElement.reflect` give the base case and closure under negation
  and simple reflections. `hasReflectionElement_all` concludes for every root
  and its negative, by `RootPairing.Base.induction_reflect`.
- `realizesReflection_of_actsByReflection`: a point acting by `s_α` realizes
  the reflection along the root character. On characters,
  `s_α(χ) = χ - ⟨χ, α^∨⟩ a`, so `χ(m v) = χ(v)` whenever `a(v) = 0`. The
  separation lemma `eq_zero_of_forall_eval_eq_zero` then gives `m v = v`.

## Axiom V 2

- `exists_eq_of_mem_centralizerPoints`: a centralizer point of a Chevalley
  group is the image of a rational torus point. It uses the published
  `centralizerPoints_le_torusCentralizer` and `torusCentralizer_eq`.
- `conj_torus_rootPt`: conjugation by the image of a rational torus point `τ`
  multiplies root coordinates by the root value at `τ`.

`reflection` is exactly the V 2 field of `IsRootDatumValuation`. Let `n` realize
the reflection along the root character `a` of `α`, and take the reflection
element `m` of `α`. By the uniqueness theorem
`RealizesReflection.inv_mul_mem_centralizerPoints` of the companion unit
`ReflectionRealizationUniqueness`, `m⁻¹ n` is a torus point `τ`. So
`n u_α(s) n⁻¹ = u_{-α}(ε α(τ) s)`, and `φ_{-a}(n u n⁻¹) = φ_a(u) + omega(α(τ))`.
The constant is `c = -omega(α(τ))`, which is finite because `α(τ)` is a unit.
Its hypotheses for the uniqueness theorem come from
`IsConnectedReductive.finite_relativeWeylGroup`,
`IsConnectedReductive.relativeWeylAction_injective`, and maximality of the split
torus.

## Scope

The unit proves V 2 and V 5 only. V 3 (commutators) and normalizer stability
are not treated, and nothing is transported to other split groups. All results
are uniform in the universe and the characteristic.
