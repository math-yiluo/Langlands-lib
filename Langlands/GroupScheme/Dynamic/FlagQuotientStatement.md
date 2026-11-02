# Proper dynamic flag quotient existence

`Langlands.GroupScheme.DynamicFlagQuotientExistenceStatement` is a proposition
about every field `k : Type u`, every actual connected reductive group scheme
`G` over `Spec k`, and every cocharacter `χ : 𝔾_m → G` defined over `k`.
Connected reductivity means the existing `IsConnectedReductive G`, and the
parabolic is the existing orbit-extension subgroup functor `Dynamic.parabolic χ`.

The proposition asks for an actual relative scheme `Q` and a relative scheme
morphism `π : G.X → Q` satisfying three conditions:

1. The structure morphism `Q → Spec k` is proper.
2. On every test scheme `T` over `k`, two points `g,h : T → G.X` have the same
   composite with `π` exactly when `g⁻¹h` belongs to `Dynamic.parabolic χ(T)`.
   Thus the fibers have the orientation of the usual right cosets `gP`.
3. Every rational point `p : RingPoint k Q k` has an open subscheme `U` containing
   its entire image on underlying scheme points and a relative morphism
   `s : openOver k Q U → G.X` for which `s ≫ π = openOverι k Q U`.
   This is an algebraic section of `π` over a neighborhood of `p`.

Here containment of the entire image is literally `Set.range p.left ⊆ U`;
`openOver` and `openOverι` are the existing actual open subscheme and its
inclusion over `Spec k`. No topology on `k` or on the point sets is assumed.
The quotient scheme is not supplied as an input, and neither its properness nor
the local sections are encoded in a replacement notion of reductivity.
The proposition includes the trivial cocharacter and the case `P(χ)=G`.

This is a derived consequence of the algebraic quotient results in J. S. Milne,
*Algebraic Groups: The Theory of Group Schemes of Finite Type over a Field*
(2017), rather than a definition of a quotient or of a parabolic:

- Definition 5.20, Propositions 5.21–5.25 and Theorem 5.28, printed pages 104–105,
  give the quotient construction and its coset fibers.
- Definition 17.15 and Theorem 17.16, printed page 356, identify parabolics with
  the subgroups having complete quotient.
- Theorem 25.1, printed page 544, identifies the dynamic subgroups `P(χ)` as
  parabolic over every field.
- Theorem 25.9 and its proof, printed page 546, provide the opposite-cell local
  section at the identity coset and surjectivity `G(k) → (G/P)(k)`. Translating
  that cell by a rational lift provides a section near each rational point.
  The global Zariski local-section assertion in part (a) assumes that `k` is
  infinite. The present statement only asks for neighborhoods of rational points,
  using the rational-point surjectivity in part (b), which holds for every field.
- Appendix A.75–A.76, printed page 583, relates completeness to the proper
  structure morphism used in the Lean statement.

The registered source is `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The author's registered errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was consulted; its Chapter 25
corrections do not alter Theorems 25.1 or 25.9.

The statement records the specific consequences needed for the compactness
argument. It does not state a universal property or general representability of
the quotient sheaf. It asserts no formal proof of existence, continuity or
compactness of local-field points. Proving this proposition, transporting its
algebraic sections to the canonical point topology, and proving compactness of
proper schemes' local-field points remain separate obligations.
