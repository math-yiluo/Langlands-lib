# Rank-cast normal forms for the mirabolic restriction sequence

Author: Worker 1163.

This helper module of the proof of
`Langlands.Derivative.MirabolicProductRestrictionStatement` rewrites the three
published helper functors of the statement into normal forms in which all three
end with the same mirabolic rank cast along `(m + 1) + n = m + n + 1`, and it
transports exactness data through that cast. It states no new mathematics about
representations; every result is an equality of functors or a transport along
an equality of natural numbers. The content is internal to the proof and has no
separate literature source.

## Declarations

All declarations are in namespace
`Langlands.Derivative.MirabolicProductRestriction`.

- `ExactAt f g` is the conjunction used at every object in the statement:
  `SmoothRep.hom f` is injective, the range of `f` equals the kernel of `g`
  (as linear maps), and `SmoothRep.hom g` is surjective.
- `generalLinearRankCast_comp_restriction`: for `h : c = d` and any proof
  `h' : c + 1 = d + 1`, the published `generalLinearRankCast T h'` followed by
  `generalLinearRestriction T d` equals `generalLinearRestriction T c` followed
  by the published `mirabolicRankCast T h`. Proof: `subst h`, after which both
  casts are the identity functor.
- `mirabolicRankCast_comp`: two successive mirabolic rank casts are the cast
  along the composite equality (proof by `subst`).
- `exists_exact_comp_mirabolicRankCast`: if three functors `F₁, F₂, F₃` into
  smooth representations of `P_(c+1)` carry natural maps `F₁ ⟶ F₂ ⟶ F₃` that are
  `ExactAt` at every object, then so do `Fᵢ ⋙ mirabolicRankCast T h`. Proof:
  `subst h`, after which the cast is the identity.
- `mirabolicCast h : mirabolic c K ≃ₜ* mirabolic d K` is the identification of
  topological groups along `h : c = d` (the identity after `subst h`), and
  `mirabolicCast_apply` records that its matrix entries are those of the input at
  the cast indices.
- `mirabolicRankCast_eq_pullback`: the published `mirabolicRankCast T h` equals
  the published pullback functor `MixedProductTensor.pullbackFunctor` along
  `mirabolicCast h.symm` (proof by `subst h` and `rfl`).
- `restrictedProduct_eq`: `restrictedProduct T m n` equals
  `(binaryNormalizedProductFunctor (m+1) (n+1) ⋙ generalLinearRestriction T ((m+1)+n)) ⋙ mirabolicRankCast T h₁`
  with `h₁ : (m + 1) + n = m + n + 1`. The group `GL_((m+1)+(n+1))` is
  definitionally `GL_(((m+1)+n)+1)`, so the restriction is to the mirabolic
  subgroup `P_((m+1)+(n+1))` of the same group.
- `restrictionSubobject_eq`: `restrictionSubobject T m n` equals the restriction
  of the first input, the published right mixed product `rightMixedProductFunctor (n+1) m`,
  the pullback along `mirabolicCast` for `(n + 1) + m = (m + 1) + n`, and finally
  `mirabolicRankCast T h₁`. Proof: split the statement's cast along
  `(n + 1) + m = m + n + 1` as two casts (`mirabolicRankCast_comp`) and replace
  the first by the pullback (`mirabolicRankCast_eq_pullback`).
- `restrictionQuotient_eq`: `restrictionQuotient T m n` is already
  `((𝟭 × generalLinearRestriction T n) ⋙ leftMixedProductFunctor (m+1) n) ⋙ mirabolicRankCast T h₁`
  (proof `rfl`).

All rank transports of the statement are retained: no cast is discarded, the
inner cast is replaced by the equal pullback functor, and the outer cast is kept
and handled by `exists_exact_comp_mirabolicRankCast`.

## Imports

The only project import is the published statement module
`Langlands.Representation.Derivative.MirabolicProductRestrictionStatement`,
whose definitions are used; its proposition is not used as a hypothesis.
