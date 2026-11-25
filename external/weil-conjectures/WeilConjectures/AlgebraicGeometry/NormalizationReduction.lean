/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.AlgebraicGeometry.NormalizationCover
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!

# The normalization of an irreducible scheme of finite type over a field

Let `X` be an irreducible scheme locally of finite type over a field `k`. Its reduction
`X_red` is integral and has a nonempty normal open `W`
(`AlgebraicGeometry.Scheme.exists_nonempty_forall_isIntegrallyClosed_stalk`); the normalization
of `X_red` in `W` is a normal scheme, finite over `X_red`, containing `W` as an open subscheme
(`AlgebraicGeometry.Scheme.normalization_comp_of_finite_etale`).

## Main results

- `AlgebraicGeometry.Scheme.exists_isNormalScheme_isFinite_of_irreducibleSpace`: a normal scheme
  `X'` with a finite morphism `f : X' ⟶ X` and an open immersion of a nonempty open `W` of
  `X_red` into `X'` lying over `X_red ⟶ X`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The inclusion of the reduction `X_red ⟶ X` is surjective, hence a universal homeomorphism. -/
instance Scheme.surjective_nilradical_subschemeι (X : Scheme.{u}) :
    Surjective X.nilradical.subschemeι := ⟨by
  rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι, Scheme.support_nilradical]
  rfl⟩

/-- **Normalization of an irreducible scheme of finite type over a field**: there are a normal
scheme `X'`, a finite morphism `f : X' ⟶ X` and an open immersion `t : W ⟶ X'` of a nonempty open
`W` of the reduction `X_red` with `t ≫ f` the inclusion `W ⟶ X_red ⟶ X`. -/
theorem Scheme.exists_isNormalScheme_isFinite_of_irreducibleSpace {k : Type u} [Field k]
    (X : Scheme.{u}) (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] [IrreducibleSpace X] :
    ∃ (X' : Scheme.{u}) (f : X' ⟶ X) (_ : IsFinite f) (W : X.nilradical.subscheme.Opens)
      (_ : Nonempty W) (t : W.toScheme ⟶ X') (_ : IsOpenImmersion t),
      IsNormalScheme X' ∧ t ≫ f = W.ι ≫ X.nilradical.subschemeι := by
  have : IrreducibleSpace X.nilradical.subscheme :=
    (IsUniversalHomeomorphism.homeomorph X.nilradical.subschemeι).symm.surjective.irreducibleSpace
      (IsUniversalHomeomorphism.homeomorph X.nilradical.subschemeι).symm.continuous
  have : IsIntegral X.nilradical.subscheme :=
    isIntegral_of_irreducibleSpace_of_isReduced X.nilradical.subscheme
  obtain ⟨V, hV, hVst⟩ := Scheme.exists_nonempty_forall_isIntegrallyClosed_stalk
    X.nilradical.subscheme (X.nilradical.subschemeι ≫ q)
  have : Nonempty V := hV.to_subtype
  have : IsLocallyNoetherian X.nilradical.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (X.nilradical.subschemeι ≫ q)
  have hV' : ∀ v : V.toScheme, IsIntegrallyClosed (V.toScheme.presheaf.stalk v) := fun v ↦
    have := hVst v.1 v.2
    IsIntegrallyClosed.of_equiv (V.stalkIso v).commRingCatIsoToRingEquiv.symm
  have : Nonempty ((TopologicalSpace.Opens.toTopCat X.nilradical.subscheme.toPresheafedSpace).obj
      V) := hV.to_subtype
  have : IrreducibleSpace V.toScheme :=
    V.isOpenEmbedding.irreducibleSpace
  obtain ⟨-, -, hto, hfin, hint, hst, -⟩ := Scheme.normalization_comp_of_finite_etale
    (X.nilradical.subschemeι ≫ q) V.ι hV' (𝟙 V.toScheme)
  refine ⟨(𝟙 V.toScheme ≫ V.ι).normalization,
    (𝟙 V.toScheme ≫ V.ι).fromNormalization ≫ X.nilradical.subschemeι, inferInstance, V,
    inferInstance, (𝟙 V.toScheme ≫ V.ι).toNormalization, hto,
    ⟨hint, fun y ↦ ⟨inferInstance, hst y⟩⟩, ?_⟩
  rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, Category.id_comp]

end AlgebraicGeometry
