/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.KInjective

/-!
# A lifting criterion for K-injectivity

We show that a cochain complex `L` in an abelian category which has the right lifting
property with respect to all monomorphic quasi-isomorphisms is K-injective.

## Main results

* `CochainComplex.isKInjective_of_forall_exists_lift`: if every morphism `A ⟶ L` extends
  along every monomorphic quasi-isomorphism `A ⟶ B`, then `L` is K-injective.
* `CochainComplex.isKInjective_of_rlp`: if `p : L ⟶ Z` has the right lifting property with
  respect to the monomorphic quasi-isomorphisms and `Z` is a zero object, then `L` is
  K-injective. This is the form in which the small object argument produces K-injective
  complexes.

The proof of the first statement applies the lifting property to the inclusion
`CochainComplex.mappingCone.inr (𝟙 K) : K ⟶ mappingCone (𝟙 K)`, which is a monomorphism,
and a quasi-isomorphism as soon as `K` is acyclic, since the mapping cone of an identity
is contractible. The resulting lift produces the required null-homotopy.
-/

@[expose] public section

namespace CochainComplex

open CategoryTheory Category Limits HomComplex

variable {C : Type*} [Category* C] [Abelian C]

namespace mappingCone

variable {F G K : CochainComplex C ℤ}

instance (φ : F ⟶ G) : Mono (mappingCone.inr φ) :=
  HomologicalComplex.mono_of_mono_f _
    (fun n ↦ mono_of_mono_fac (mappingCone.inr_f_snd_v φ n))

/-- The mapping cone of an identity is contractible. -/
noncomputable def homotopyIdZeroOfId : Homotopy (𝟙 (mappingCone (𝟙 K))) 0 :=
  mappingCone.liftHomotopy _ _ _ (mappingCone.snd _) 0 (by simp) (by simp)

lemma acyclic_of_id (K : CochainComplex C ℤ) : (mappingCone (𝟙 K)).Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero,
    ← HomologicalComplex.homologyMap_id, homotopyIdZeroOfId.homologyMap_eq,
    HomologicalComplex.homologyMap_zero]

lemma quasiIso_inr_id (hK : K.Acyclic) : QuasiIso (mappingCone.inr (𝟙 K)) where
  quasiIsoAt n := by
    rw [quasiIsoAt_iff_exactAt _ _ (hK n)]
    exact acyclic_of_id K n

end mappingCone

/-- A cochain complex which has the right lifting property with respect to all monomorphic
quasi-isomorphisms is K-injective. -/
theorem isKInjective_of_forall_exists_lift (L : CochainComplex C ℤ)
    (hL : ∀ {A B : CochainComplex C ℤ} (i : A ⟶ B), Mono i → QuasiIso i →
      ∀ (f : A ⟶ L), ∃ g : B ⟶ L, i ≫ g = f) :
    L.IsKInjective where
  nonempty_homotopy_zero {K} f hK := by
    obtain ⟨g, hg⟩ := hL (mappingCone.inr (𝟙 K)) inferInstance
      (mappingCone.quasiIso_inr_id hK) f
    refine ⟨(Cochain.equivHomotopy f 0).symm
      ⟨(mappingCone.inl (𝟙 K)).comp (Cochain.ofHom g) (add_zero (-1)), ?_⟩⟩
    rw [δ_comp_zero_cochain _ _ _ (by omega), δ_ofHom, Cochain.comp_zero,
      mappingCone.δ_inl, ← Cochain.ofHom_comp, assoc, hg]
    simp

/-- A cochain complex `L` which admits a morphism `p : L ⟶ Z` to a zero object which has the
right lifting property with respect to the monomorphic quasi-isomorphisms is K-injective. -/
theorem isKInjective_of_rlp {L Z : CochainComplex C ℤ} (p : L ⟶ Z) (hZ : IsZero Z)
    (hp : MorphismProperty.rlp (MorphismProperty.monomorphisms (CochainComplex C ℤ) ⊓
      HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) p) :
    L.IsKInjective := by
  refine isKInjective_of_forall_exists_lift L (fun {A B} i hi hi' f ↦ ?_)
  have := hp i ⟨hi, hi'⟩
  have sq : CommSq f i p (0 : B ⟶ Z) := ⟨hZ.eq_of_tgt _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

end CochainComplex
