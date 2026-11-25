/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DensePoints
public import WeilConjectures.AlgebraicGeometry.Picard.Defs

/-!
# The section `σ_T` induced by a rational point

A `k`-rational point of a `k`-scheme `X` is a section `σ : Spec k ⟶ X` of the structure morphism
`f : X ⟶ Spec k` (an element of `AlgebraicGeometry.Scheme.Hom.fieldPoints`). For every
`k`-scheme `T` it induces the section `σ_T : T ⟶ X_T = X ×_k T` of the projection
`X_T ⟶ T` (`AlgebraicGeometry.Scheme.Hom.fieldPointBaseChange`), the base change of `σ`
(`AlgebraicGeometry.sectionBaseChange`). For `T = Spec K` it is the `K`-rational point
`AlgebraicGeometry.Scheme.Hom.baseChangeFieldPoint` of `X_K`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {k : Type u} [Field k]

/-- A `k`-rational point of `X` is a section of the structure morphism. -/
lemma Hom.fieldPoints_comp_eq_id (f : X.Hom (Spec (.of k))) (p : f.fieldPoints k) :
    p.1 ≫ f = 𝟙 _ := by
  rw [p.2, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

/-- **The section `σ_T` induced by a rational point.** For a `k`-rational point
`σ: Spec k ⟶ X` of a `k`-scheme `X` and a `k`-scheme `T`, the induced section
`σ_T: T ⟶ X_T = X ×_k T` of the projection `X_T ⟶ T`, i.e. `σ_T = (σ ∘ (T ⟶ Spec k), id_T)`. -/
noncomputable def Hom.fieldPointBaseChange (f : X.Hom (Spec (.of k))) (p : f.fieldPoints k)
    (T : Over (Spec (.of k))) : T.left ⟶ pullback f T.hom :=
  sectionBaseChange f p.1 (f.fieldPoints_comp_eq_id p) T

/-- **`σ_T` is a section of the projection `X_T ⟶ T`.** -/
@[reassoc (attr := simp)]
lemma Hom.fieldPointBaseChange_snd (f : X.Hom (Spec (.of k))) (p : f.fieldPoints k)
    (T : Over (Spec (.of k))) : f.fieldPointBaseChange p T ≫ pullback.snd f T.hom = 𝟙 T.left :=
  sectionBaseChange_snd _ _ (f.fieldPoints_comp_eq_id p) _

/-- The composite of `σ_T` with the projection `X_T ⟶ X` is `T ⟶ Spec k ⟶ X`. -/
@[reassoc (attr := simp)]
lemma Hom.fieldPointBaseChange_fst (f : X.Hom (Spec (.of k))) (p : f.fieldPoints k)
    (T : Over (Spec (.of k))) : f.fieldPointBaseChange p T ≫ pullback.fst f T.hom = T.hom ≫ p.1 :=
  pullback.lift_fst _ _ _

/-- The sections `σ_T` are compatible with base change: for `i : V ⟶ U` over `k`,
`σ_U ∘ i = (X ×_k i) ∘ σ_V`. -/
lemma Hom.fieldPointBaseChange_comp_baseChangeMap (f : X.Hom (Spec (.of k)))
    (p : f.fieldPoints k) {U V : Over (Spec (.of k))} (i : V ⟶ U) :
    f.fieldPointBaseChange p V ≫ baseChangeMap f i = i.left ≫ f.fieldPointBaseChange p U :=
  sectionBaseChange_comp_baseChangeMap _ _ (f.fieldPoints_comp_eq_id p) i

/-- For `T = Spec K`, the section `σ_T` is the `K`-rational point `x_K` of `X_K`
(`AlgebraicGeometry.Scheme.Hom.baseChangeFieldPoint`). -/
lemma Hom.fieldPointBaseChange_spec (f : X.Hom (Spec (.of k))) (p : f.fieldPoints k)
    (K : Type u) [Field K] [Algebra k K] :
    f.fieldPointBaseChange p (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))) =
      (f.baseChangeFieldPoint K p).1 :=
  rfl

end AlgebraicGeometry.Scheme
