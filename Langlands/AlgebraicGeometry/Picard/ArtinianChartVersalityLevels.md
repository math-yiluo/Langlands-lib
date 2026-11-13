# Pointed Picard versality along towers of Artinian levels

This module transfers formal versality of an actual Picard family from one chart
to another. It is the Picard-stack counterpart of two steps in the proof of
Stacks Project Lemma 98.12.7 (Tag 07XH, `artin.pdf` printed pp. 20–21):

- the successive lifting `ξ → η₃ → η₄ → …` by versality (Formal Deformation
  Theory, Remark 8.10);
- the conclusion "η is isomorphic to a versal object, hence versal itself", via
  Lemma 98.12.3 (Tag 0CXK).

No isomorphism of formal objects is constructed. Instead, a lifting problem for the
new family is moved to the old family through a single Artinian level, solved
there, and moved back. The provenance is derived.

## Moving a lifting problem through a level

In namespace `Langlands.CategoryTheory.PseudofunctorPointFiber`, `F` is an
arbitrary category-valued pseudofunctor on `Cᵒᵖ`.

- `points_eq_of_pullIso` and `pullIso_eq_of_points_eq` express equality of actual
  points `⟨a₁, e₁⟩ = ⟨a₂, e₂⟩` through the transport `pullIso e₁ (𝟙 _) a₂ …` of the
  isomorphism along the identity.
- `exists_restrict_eq_of_factor` takes objects `ξ` over `V`, `ξ'` over `U` and `M`
  over `T`, together with a point `x` of `ξ` with values in `ξ'` over a level
  `c : Z ⟶ U`, whose chart map `x.1 : Z ⟶ V` is a monomorphism. Let `y` be a point of
  `ξ'` with values in `M` over `b = g ≫ a`, with `y.1 = j ≫ c`. Restricting `x`
  along `j` and composing with `y.2` gives a point `yL` of `ξ`. Suppose `yL` lifts
  along `g` to a point `xL` over `a` with `xL.1 = j' ≫ x.1`. Then `y` lifts along
  `g` to the point `⟨j' ≫ c, (x restricted along j').2⁻¹ ≪≫ xL.2⟩`.

  Monicity of `x.1` gives `g ≫ j' = j`. The second components are compared with
  `pullIso_pullIso`, `pullIso_trans` and `pullIso_congr` from
  `PseudofunctorParallelIsomorphisms`, and `pullIso_symm` from `AtlasArrowInversion`.

## Versality along levels

In namespace `PicardGroupoid.ArtinianChartVersality`, `f : X ⟶ Spec k` is a scheme
over `k`, `L` is a line bundle on `V ×_k X`, and `pV` is a `K`-point of `V`.

`towerDown T π n : T n ⟶ T 0` composes a tower of test arrows
`π n : T (n + 1) ⟶ T n` down to its bottom level.

`exists_tower_points` assumes that `L` is formally versal at `pV`. It also takes a
second chart `U` with line bundle `L'`, surjective test arrows `π n`, maps
`c n : base (T n) ⟶ U` with `baseMap (π n) ≫ c (n + 1) = c n`, and a fibre point
`x₀` over `c 0` whose residue map is `pV`. For every `n` it gives a fibre point `x`
over `c n` with residue map `pV` and with
`baseMap (towerDown T π n) ≫ x.1 = x₀.1`. The proof is induction using
`exists_lift_at` on the test arrow `π n`, with the test family `(U, L')`.

`isFormallyVersalAt_of_levels` assumes that `L` is formally versal at `pV`, and
takes a chart `U` with line bundle `L'` and a point `pU`. It also takes levels
`c n : Z n ⟶ U` and fibre points `x n` of `L` with values in `L'` over `c n`, such
that:

- every chart map `(x n).1` is a monomorphism;
- every `K`-point `r` of `Z n` with `r ≫ c n = pU` has `r ≫ (x n).1 = pV`;
- for every test `B`, there is `n₀` such that every pointed map `base B ⟶ U`
  factors through `c n` for all `n ≥ n₀`;
- for every test `A`, there is `n₀` such that every pointed map `base A ⟶ V`
  factors through `(x n).1` for all `n ≥ n₀`.

Then `L'` is formally versal at `pU`. Given a surjective test arrow `q : A ⟶ B` and a
lifting problem for `L'`, choose one level `n` large enough for both `A` and `B`.
Factor the given point through `c n`, transport it to a pointed problem for `L`,
and solve it by versality. The solution factors through `(x n).1`, and
`exists_restrict_eq_of_factor` transports it back. Using a single level for both
test rings avoids any compatibility condition between different levels.
