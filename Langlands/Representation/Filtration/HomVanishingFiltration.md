# The vanishing filtration on maps out of a filtered functor value

Author: Worker 5226. This is an internal construction with supporting lemmas, derived for the planned proof of the first lemma of Renard VI.10.4 (printed pp.209–212 / PDF pp.215–218). Reference: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Renard does not state these lemmas.

The planned use runs as follows. By Frobenius reciprocity, `End(i_P^G Π_D)` is identified with `Hom(r_P i_P Π_D, Π_D)`. The geometric lemma (`representedGeometricLemma`) provides a natural filtration of `r_P i_P`. This file supplies the filtration of the Hom space induced by such a natural filtration, and its comparison with Hom spaces out of the graded pieces. Everything is unconditional and works for an arbitrary filtered functor.

## Setting

Throughout:
- `R` is a commutative ring and `G` a monoid;
- `C` is a category and `F : C ⥤ Rep R G` a functor;
- `s : RepFunctorFiltration F n` is a published natural filtration (`Langlands/Representation/Filtration/Definitions.lean`). It has steps `s.step i` for `i : Fin (n + 1)` with `step 0 = 0` and `step n = F`. Its graded functors are `s.graded j = step (j + 1) / step j` for `j : Fin n`.
- `X : C` is an object and `Y : Rep R G` a target.

## Declarations

### The filtration of the Hom space

- `homVanishing s X Y i` is the additive subgroup of `F.obj X ⟶ Y` consisting of the maps that vanish on `(s.step i).obj X`. `mem_homVanishing` unfolds membership.
- `homVanishing_zero`: the filtration starts at `⊤`, because step `0` is zero.
- `homVanishing_last`: the filtration ends at `⊥`, because step `n` is everything.
- `homVanishing_succ_le`: the filtration is decreasing, `homVanishing (j + 1) ≤ homVanishing j`.
- `map_comp_mem_homVanishing`: precomposition with `F.map a`, for `a : X' ⟶ X`, preserves vanishing on step `i`. This holds because the steps are subfunctors.

### Descent to graded pieces

- `gradedProjection s X j` is the published quotient projection of step `j + 1` onto the graded piece `(s.graded j).obj X`, with the graded functor as its declared codomain.
  - `gradedProjection_surjective`: the projection is surjective.
  - `gradedProjection_eq_zero_iff`: its kernel consists of the elements of step `j`.
- `gradedDescent s X Y j f hf` takes a map `f` vanishing on step `j` and gives the induced map `(s.graded j).obj X ⟶ Y`. It is built with `Submodule.liftQ` from the restriction of `f` to step `j + 1`.
  - `gradedDescent_projection` (by `rfl`): the descent composed with the graded projection is `f` on step `j + 1`.
  - `gradedDescent_ext`: two maps out of a graded piece are equal if they agree after the graded projection.
  - `gradedDescent_eq_zero_iff`: the descent is zero exactly when `f` also vanishes on step `j + 1`.
  - `gradedDescent_sub`: descent is additive.
  - `gradedDescent_map_comp`: the descent of `F.map a ≫ f` is `(s.graded j).map a ≫ gradedDescent f`.

### Lifting maps out of graded pieces when the projections split

- `toLastStep` identifies `F.obj X` with its last step, using `s.top`.
- `stepRetraction k σ hσ` takes a section `σ` of the graded projection at step `k`, meaning `σ ≫ gradedProjection k = 𝟙`. It is the retraction of step `k + 1` onto step `k` given by `w ↦ w - σ (p w)`.
  - The value lies in step `k` because its projection is `p w - p w = 0`.
  - It is intertwining because `σ` and `p` are.
- `stepRetraction_apply_of_mem`: the retraction fixes the elements of step `k`, because they project to `0`.
- `exists_extension_of_sections` assumes that every graded projection has a section. It concludes that every map out of a step `(s.step m).representation X ⟶ Y` extends to a map `F.obj X ⟶ Y` with the same values on step `m`. The proof is downward induction on `m` (`Fin.reverseInduction`):
  - at the last step, precompose with `toLastStep`;
  - at step `k`, extend the composite `stepRetraction k σ hσ ≫ h` from step `k + 1`. It agrees with `h` on step `k` by `stepRetraction_apply_of_mem`.
- `exists_gradedDescent_eq_of_sections` has the same hypothesis. It concludes that every map `g : (s.graded j).obj X ⟶ Y` equals `gradedDescent f hf` for some `f` vanishing on step `j`. The proof extends `gradedProjection j ≫ g` from step `j + 1`.
  - The extension vanishes on step `j`, because the projection kills it.
  - Its descent is `g`, by `gradedDescent_ext` and `gradedDescent_projection`.

The section hypothesis is stated objectwise at `X`. It holds, for example, when every graded piece `(s.graded k).obj X` is projective in a category in which the graded projections are epimorphisms. That projectivity is not proved here.
