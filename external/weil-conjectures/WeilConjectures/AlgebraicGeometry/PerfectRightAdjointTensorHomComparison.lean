/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import WeilConjectures.CategoryTheory.MonoidalProjectionConjugate

/-! # The counit calculation for tensor-Hom duality and a right adjoint

Source: Stacks Project, Duality for Schemes, Tag 0A9T.
(blueprint: lem-sc-perfect-right-adjoint-tensor-hom-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe u w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

private theorem conjugate_homEquiv
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    (A : C) (B : D) (t : L₁.obj A ⟶ B) :
    a₁.homEquiv A B t ≫ (conjugateEquiv a₁ a₂ α).app B =
      a₂.homEquiv A B (α.app A ≫ t) := by
  simp only [Adjunction.homEquiv_unit]
  rw [Category.assoc, (conjugateEquiv a₁ a₂ α).naturality,
    ← Category.assoc, unit_conjugateEquiv, Category.assoc, ← Functor.map_comp]

private theorem projection_duality
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (R : D ⥤ C) [F.Monoidal] (a : F ⊣ R)
    (K L : C) [ExactPairing K L] (E B : D)
    (pfK : R.obj (F.obj K ⊗ B) ≅ K ⊗ R.obj B)
    (hpK : pfK.inv = a.homEquiv _ _
      ((Functor.Monoidal.μIso F K (R.obj B)).inv ≫ F.obj K ◁ a.counit.app B))
    (pfL : R.obj (F.obj L ⊗ E) ≅ L ⊗ R.obj E)
    (hpL : pfL.inv = a.homEquiv _ _
      ((Functor.Monoidal.μIso F L (R.obj E)).inv ≫ F.obj L ◁ a.counit.app E))
    (q : E ⟶ F.obj K ⊗ B) :
    let p := ExactPairing.map F K L
    tensorLeftHomEquiv (R.obj E) K L (R.obj B)
      (pfL.inv ≫ R.map ((@tensorLeftHomEquiv _ _ _ E (F.obj K) (F.obj L) B p).symm q)) =
        R.map q ≫ pfK.hom := by
  let := ExactPairing.map F K L
  let t := (tensorLeftHomEquiv E (F.obj K) (F.obj L) B).symm q
  let b₁ := (tensorLeftAdjunction K L).comp a
  let b₂ := a.comp (tensorLeftAdjunction (F.obj K) (F.obj L))
  -- Transport a Hom equivalence along the tensorator and its canonical mate.
  have h := conjugate_homEquiv b₁ b₂ (Functor.Monoidal.commTensorLeft F L).hom
    (R.obj E) B
    ((Functor.Monoidal.μIso F L (R.obj E)).inv ≫ F.obj L ◁ a.counit.app E ≫ t)
  rw [monoidal_projection_conjugate F R a K L B, ← hpK] at h
  simp only [b₁, b₂, Adjunction.comp_homEquiv,
    tensorLeftAdjunction, Adjunction.mkOfHomEquiv_homEquiv,
    Functor.Monoidal.commTensorLeft_hom_app] at h
  change tensorLeftHomEquiv (R.obj E) K L (R.obj B)
      (a.homEquiv _ _ ((Functor.Monoidal.μIso F L (R.obj E)).inv ≫
        F.obj L ◁ a.counit.app E ≫ t)) ≫ pfK.inv =
    a.homEquiv _ _
      (tensorLeftHomEquiv (F.obj (R.obj E)) (F.obj K) (F.obj L) B
        (Functor.LaxMonoidal.μ F L (R.obj E) ≫
          (Functor.Monoidal.μIso F L (R.obj E)).inv ≫
          F.obj L ◁ a.counit.app E ≫ t)) at h
  rw [← Category.assoc, a.homEquiv_naturality_right, ← hpL] at h
  simp only [Category.assoc, ← Functor.Monoidal.μIso_hom, Iso.hom_inv_id_assoc] at h
  have hn := tensorLeftHomEquiv_symm_naturality (Y' := F.obj L) (a.counit.app E) q
  change (tensorLeftHomEquiv (F.obj (R.obj E)) (F.obj K) (F.obj L) B).symm
      (a.counit.app E ≫ q) = F.obj L ◁ a.counit.app E ≫ t at hn
  have hn' : tensorLeftHomEquiv (F.obj (R.obj E)) (F.obj K) (F.obj L) B
      (F.obj L ◁ a.counit.app E ≫ t) = a.counit.app E ≫ q := by
    rw [← hn]
    exact Equiv.apply_symm_apply _ _
  rw [hn'] at h
  have hc : a.homEquiv (R.obj E) (F.obj K ⊗ B) (a.counit.app E ≫ q) =
      R.map q := by
    rw [a.homEquiv_naturality_right, Adjunction.homEquiv_unit]
    simp
  rw [hc] at h
  -- The calculation gives the comparison after composing with the inverse projection.
  apply (cancel_mono pfK.inv).1
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h

/-- The tensor-Hom chain of Tag 0A9T is postcomposition with the canonical mate.
Source: Stacks Project, Duality for Schemes, Tag 0A9T.
(blueprint: lem-sc-perfect-right-adjoint-tensor-hom-comparison).
Proof: transpose both sides under `adj`. Naturality of its Hom equivalence turns
postcomposition with the mate into application of the restricted direct image to q,
followed by the counit defining that mate. Expand the two tensor-Hom equivalences:
the first inserts evaluation of the pulled-back dual and the second inserts
coevaluation of the original dual. Replace the inverses of pfK and pfD by their
specified pullback-adjoint formulas. Naturality of the pullback and right-adjoint
counits moves q and evaluation through those formulas. The tensorator's naturality
identifies evaluation of the mapped pairing with pullback of evaluation. Its
associativity and unit laws rearrange the resulting evaluation-coevaluation pair;
the triangle identity cancels it. The remaining composite is the restricted direct
image of q followed by pfK, the tensor of the right-adjoint counit at the unit, and
the right unitor. This is precisely the transpose of the right-hand side.
Full-subcategory morphisms have the same composition as the ambient morphisms,
so the same calculation applies to the displayed `homMk` morphisms. -/
theorem perfect_rightAdjoint_tensor_hom_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (hRf : ∀ E : schemeDerivedQCohCategory X,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
    (hTensor : ∀ (K : schemeDerivedQCohCategory Y) (E : schemeDerivedQCohCategory X),
      schemeDerivedQCohProperty X (((derivedPullback f).obj K.obj) ⊗ E.obj))
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) hRf ⊣ c)
    (K D : schemeDerivedQCohCategory Y) [ExactPairing K.obj D.obj]
    (E : schemeDerivedQCohCategory X)
    (pfK : (schemeDerivedDirectImage f).obj
        (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
      K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)
    (hpK : pfK.inv = (a.homEquiv _ _)
      ((Functor.Monoidal.μIso (derivedPullback f) K.obj
        ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
        (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj))
    (pfD : (schemeDerivedDirectImage f).obj
        (((derivedPullback f).obj D.obj) ⊗ E.obj) ≅
      D.obj ⊗ (schemeDerivedDirectImage f).obj E.obj)
    (hpD : pfD.inv = (a.homEquiv _ _)
      ((Functor.Monoidal.μIso (derivedPullback f) D.obj
        ((schemeDerivedDirectImage f).obj E.obj)).inv ≫
        (derivedPullback f).obj D.obj ◁ a.counit.app E.obj))
    (q : E ⟶ ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
      hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩) :
    let p := ExactPairing.map (derivedPullback f) K.obj D.obj
    (adj.homEquiv E K)
      (ObjectProperty.homMk
        (tensorLeftHomEquiv ((schemeDerivedDirectImage f).obj E.obj) K.obj D.obj
          (𝟙_ (schemeDerivedCategory Y))
          (pfD.inv ≫ ((adj.homEquiv
            ⟨((derivedPullback f).obj D.obj) ⊗ E.obj, hTensor D E⟩ ⟨𝟙_ _, hO⟩).symm
            (ObjectProperty.homMk
              ((@tensorLeftHomEquiv _ _ _ E.obj ((derivedPullback f).obj K.obj)
                ((derivedPullback f).obj D.obj) (c.obj ⟨𝟙_ _, hO⟩).obj p).symm
                q.hom))).hom) ≫ (ρ_ K.obj).hom)) =
      q ≫ (adj.homEquiv
        ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
          hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
        (ObjectProperty.homMk (pfK.hom ≫
          K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom)) := by
  let := ExactPairing.map (derivedPullback f) K.obj D.obj
  let O : schemeDerivedQCohCategory Y := ⟨𝟙_ _, hO⟩
  let T : schemeDerivedQCohCategory X :=
    ⟨((derivedPullback f).obj D.obj) ⊗ E.obj, hTensor D E⟩
  let t : T ⟶ c.obj O := ObjectProperty.homMk
    ((tensorLeftHomEquiv E.obj ((derivedPullback f).obj K.obj)
      ((derivedPullback f).obj D.obj) (c.obj O).obj).symm q.hom)
  let r := (adj.homEquiv T O).symm t
  have hr : r.hom = (schemeDerivedDirectImage f).map t.hom ≫
      (adj.counit.app O).hom := by
    dsimp only [r]
    rw [Adjunction.homEquiv_counit]
    rfl
  have ht := projection_duality (derivedPullback f) (schemeDerivedDirectImage f)
    a K.obj D.obj E.obj (c.obj O).obj pfK hpK pfD hpD q.hom
  change tensorLeftHomEquiv ((schemeDerivedDirectImage f).obj E.obj) K.obj D.obj
      ((schemeDerivedDirectImage f).obj (c.obj O).obj)
      (pfD.inv ≫ (schemeDerivedDirectImage f).map t.hom) =
    (schemeDerivedDirectImage f).map q.hom ≫ pfK.hom at ht
  apply (adj.homEquiv E K).symm.injective
  rw [Equiv.symm_apply_apply, adj.homEquiv_naturality_left_symm,
    Equiv.symm_apply_apply]
  apply ObjectProperty.hom_ext
  change tensorLeftHomEquiv ((schemeDerivedDirectImage f).obj E.obj) K.obj D.obj
      (𝟙_ (schemeDerivedCategory Y)) (pfD.inv ≫ r.hom) ≫ (ρ_ K.obj).hom =
    (schemeDerivedDirectImage f).map q.hom ≫ pfK.hom ≫
      K.obj ◁ (adj.counit.app O).hom ≫ (ρ_ K.obj).hom
  rw [hr, ← Category.assoc pfD.inv,
    tensorLeftHomEquiv_naturality, ht]
  simp only [Category.assoc]

end AlgebraicGeometry
