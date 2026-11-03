# Lang's theorem for corepresented group functors over a finite field

Author: Worker 1387.

Lang's theorem says that for a connected algebraic group `G` over a finite field
`k` the map `g ↦ g⁻¹ · Frob(g)` is surjective on points over an algebraic
closure. This
module proves the form needed for
`Langlands.GroupScheme.FiniteFieldTorsorPointStatement`, for a group functor
corepresented by a finitely generated domain. The proof is the one implemented
here, by integrality and Krull dimension; it uses no étaleness or differentials.
It relies on the commutative algebra of [`LangAlgebra`](LangAlgebra.md) and on the
Library's corepresented-functor framework
`Langlands.GroupScheme.Corepresented.LinearEmbedding`
([`CorepresentedLinearEmbedding`](../CorepresentedLinearEmbedding.md)).

All declarations live in `Langlands.GroupScheme.FiniteFieldTorsorPoint`. Fix a
finite field `k : Type u` (with `[Fintype k]`), a functor
`F : CommAlgCat (CommRingCat.of k) ⥤ GrpCat` and a corepresentation
`e : (F ⋙ forget GrpCat).CorepresentableBy B` by `B : CommAlgCat (CommRingCat.of k)`.
Write `q = Fintype.card k`. The framework provides `pt e : (B ⟶ S) → F.obj S` and
its inverse `cls e`, with `pt` natural (`pt_comp`), `cls` multiplicative
(`cls_mul`) and natural (`cls_map`).

## Frobenius

- `frob k S : S ⟶ S` is `CommAlgCat.ofHom (FiniteField.frobeniusAlgHom k S)`, the
  `k`-algebra endomorphism `x ↦ x ^ q`; `frob_apply` records this formula.
- `frob_naturality`: `frob k S ≫ g = g ≫ frob k T` for every `g : S ⟶ T`, since
  algebra maps commute with powers.

## The universal Lang point

- `univ e = pt e (𝟙 B)` is the universal point.
- `langUniv e = (univ e)⁻¹ * F.map (frob k B) (univ e)` is the Lang map applied to
  it.
- `langCo e = cls e (langUniv e) : B ⟶ B` is the algebra endomorphism that
  classifies it, the comorphism of the Lang map.
- `map_langUniv`: for `g : B ⟶ S`,
  `F.map g (langUniv e) = (pt e g)⁻¹ * F.map (frob k S) (pt e g)`. This follows from
  `pt_comp` and `frob_naturality`.
- `exists_lang_eq_of_factor`: if `y : F.obj S` and `g : B ⟶ S` satisfy
  `langCo e ≫ g = cls e y`, then `y = x⁻¹ * F.map (frob k S) x` for `x = pt e g`.
  Indeed `y = pt e (langCo e ≫ g) = F.map g (langUniv e)`, by `cls_map` and
  `pt_cls`, and `map_langUniv` applies.

## Integrality

`isIntegral_langCo_range`: if `B` is finitely generated over `k`, then `B` is
integral over the subalgebra `(langCo e).hom.range`. Write `ψ = (langCo e).hom`.
Let `s` be a finite generating set. The Library's `Comodule.exists_matrix`
(applied with `coassoc e`, `leftCounit e`, `rightCounit e`) gives a square matrix
`a` over `B` whose entries span a subspace containing `s`, with
`comulL e (a i j) = ∑ l, a i l ⊗ a l j` and `counitL e (a i j) = δᵢⱼ`. Then
`coeffHom e a … B : F.obj B →* Matrix _ _ B`, `x ↦ (cls e x).hom.mapMatrix a`, is
a monoid homomorphism. Applying it to
`univ e * langUniv e = F.map (frob k B) (univ e)` and using `cls_pt` and `cls_map`
gives the matrix identity `a * ψ.mapMatrix a = (frob k B).hom.mapMatrix a`. In
entries,

`a i j ^ q = ∑ l, a i l * ψ (a l j)`.

So the entries `v (i, j) = a i j` generate `B` over `ψ.range` (they generate it
over `k`, and `Algebra.adjoin_adjoin_of_tower` passes to the larger base), and each
`v p ^ q` is a `ψ.range`-combination of entries. As `q ≥ 2`,
`finite_of_pow_mem_span` shows that `B` is a finite `ψ.range`-module, hence
integral.

## Lang's theorem

`exists_lang_eq`: if `B` is a domain finitely generated over `k`, `K` is an
algebraically closed field with `[Algebra k K]` and
`y : F.obj (CommAlgCat.of (CommRingCat.of k) K)`, then there is `x` with
`y = x⁻¹ * F.map (frob k _) x`. By `isIntegral_langCo_range` and
`exists_comp_eq_of_isIntegral_range` there is `g : B →ₐ[k] K` with
`g.comp ψ = (cls e y).hom`, which is the hypothesis of `exists_lang_eq_of_factor`.
The statement does not mention `e`, so it holds for every functor that is
corepresented by such an algebra.
