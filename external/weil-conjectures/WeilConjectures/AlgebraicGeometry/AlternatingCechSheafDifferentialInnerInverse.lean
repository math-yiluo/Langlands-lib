/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafConstruction
import WeilConjectures.AlgebraicGeometry.AlternatingCechPresheafPositiveInsertion

/-! # Inner inverses of local alternating face differentials

Source: Stacks Project, Tag 02FU (cohomology-lemma-covering-resolution),
with increasing tuples as in Tag 01FM.
(blueprint: lem-pc-s3-alternating-cech-sheaf-differential-inner-inverse).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Sheafification and local restriction transport the presheaf insertion identity.
The cap units become isomorphisms locally; their naturality moves each
face differential across the inverses. Additivity then transports cancellation. -/
private theorem alternatingCechSheaf_restrict_natural_insertion
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r)
    (p : ℕ) :
    let F := Scheme.Modules.restrictFunctor (U i).ι
    let D := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (alternatingCechSheafComplex U G)
    ∃ (s : D.X (p + 1) ⟶ D.X p) (t : D.X (p + 1 + 1) ⟶ D.X (p + 1)),
      s ≫ D.d p (p + 1) + D.d (p + 1) (p + 1 + 1) ≫ t = 𝟙 (D.X (p + 1)) := by
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let : L.Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).left_adjoint_additive
  let F := Scheme.Modules.restrictFunctor (U i).ι
  let : F.Additive := ⟨by intro A B f g; ext V; rfl⟩
  let T := L ⋙ F
  let : T.Additive := inferInstanceAs (L ⋙ F).Additive
  let K := cechCapPresheafFunctor (U i)
  let ν := cechCapPresheafUnit (U i)
  let P₀ := alternatingCechSheafPresheafTerms U G p
  let P₁ := alternatingCechSheafPresheafTerms U G (p + 1)
  let P₂ := alternatingCechSheafPresheafTerms U G (p + 1 + 1)
  let d₀ := alternatingCechSheafPresheafD U G p
  let d₁ := alternatingCechSheafPresheafD U G (p + 1)
  obtain ⟨s, t, hst⟩ := alternatingCechSheafPresheaf_positive_insertion U G i p
  change ν.app P₁ = s ≫ K.map d₀ + d₁ ≫ t at hst
  have h₀ : IsIso (T.map (ν.app P₀)) := cechCapPresheafUnit_local_isIso (U i) P₀
  have h₁ : IsIso (T.map (ν.app P₁)) := cechCapPresheafUnit_local_isIso (U i) P₁
  dsimp only
  simp only [alternatingCechSheafComplex, Functor.mapHomologicalComplex_obj_d,
    alternatingCechSheafPresheafComplex, CochainComplex.of_d]
  change ∃ (s' : T.obj P₁ ⟶ T.obj P₀) (t' : T.obj P₂ ⟶ T.obj P₁),
    s' ≫ T.map d₀ + T.map d₁ ≫ t' = 𝟙 _
  refine ⟨T.map s ≫ inv (T.map (ν.app P₀)),
    T.map t ≫ inv (T.map (ν.app P₁)), ?_⟩
  apply (cancel_mono (T.map (ν.app P₁))).mp
  have hn := congrArg T.map (ν.naturality d₀)
  change T.map (d₀ ≫ ν.app P₁) = T.map (ν.app P₀ ≫ K.map d₀) at hn
  simp only [Functor.map_comp] at hn
  simp only [Preadditive.add_comp, Category.assoc, Category.id_comp]
  rw [hn, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]
  simpa only [Functor.map_add, Functor.map_comp] using (congrArg T.map hst).symm


/-- Each local face differential has an inner inverse, independently of the others.
Source: Stacks Project, Tag 02FU (cohomology-lemma-covering-resolution),
adapted to the increasing-tuple convention of Tag 01FM.
(blueprint: lem-pc-s3-alternating-cech-sheaf-differential-inner-inverse).

Proof: For a nonnegative degree k, on each test open V contained in U i,
define s from degree k+1 to k by signed insertion of i: the t-coordinate
is zero when t contains i, and otherwise is (-1)^b times the coordinate
indexed by t with i inserted in its increasing position b. The two
intersection opens inside V coincide. These formulas are linear and commute
with restriction, giving a morphism of restricted module presheaves.
Apply this formula to d(x). Its differential is d(x): on an inserted tuple
this follows from d(d(x))=0 and the face deleting i; on a tuple containing i
only the face omitting i contributes, with sign squared one. Consequently
d s d=d. This calculation only concerns boundaries, and does not assert
an identity on arbitrary cochains or compare adjacent choices of s.
The intersection presheaves V ↦ G(V intersect W) are already sheaves,
being direct images of restrictions to W. Their finite products are
sheaves, so each term's sheafification unit is an isomorphism. Restrict
these units to U i; naturality identifies their differential with the
restricted sheafified differential. Lift the insertion map through the
fully faithful forgetful functor and conjugate by these units. This
preserves d s d=d. Transport through extendXIso in the three
occurrences of d. For k<0 the differential is zero, since its source is
an extension-by-zero term, and s=0 works. Empty opens and zero terms cause
no exception; r=0 admits no index i. -/
theorem alternatingCechSheaf_restrict_differential_inner_inverse
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r)
    (k : ℤ) :
    let F := Scheme.Modules.restrictFunctor (U i).ι
    let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat)
    ∃ s : C.X (k + 1) ⟶ C.X k,
      C.d k (k + 1) ≫ s ≫ C.d k (k + 1) = C.d k (k + 1) := by
  let F := Scheme.Modules.restrictFunctor (U i).ι
  let K := alternatingCechSheafComplex U G
  let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (K.extend ComplexShape.embeddingUpNat)
  change ∃ s : C.X (k + 1) ⟶ C.X k, _
  by_cases hk : 0 ≤ k
  · obtain ⟨s, t, hst⟩ := alternatingCechSheaf_restrict_natural_insertion U G i k.toNat
    let D := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
    change s ≫ D.d k.toNat (k.toNat + 1) +
      D.d (k.toNat + 1) (k.toNat + 1 + 1) ≫ t = 𝟙 (D.X (k.toNat + 1)) at hst
    have hs : D.d k.toNat (k.toNat + 1) ≫ s ≫ D.d k.toNat (k.toNat + 1) =
        D.d k.toNat (k.toNat + 1) := by
      have h := congrArg (fun f ↦ D.d k.toNat (k.toNat + 1) ≫ f) hst
      simpa only [Preadditive.comp_add, ← Category.assoc, D.d_comp_d,
        Limits.zero_comp, add_zero, Category.comp_id] using h
    let e₀ := K.extendXIso ComplexShape.embeddingUpNat
      (i := k.toNat) (i' := k) (by change (k.toNat : ℤ) = k; omega)
    let e₁ := K.extendXIso ComplexShape.embeddingUpNat
      (i := k.toNat + 1) (i' := k + 1) (by change ((k.toNat + 1 : ℕ) : ℤ) = k + 1; omega)
    have hd : C.d k (k + 1) = F.map e₀.hom ≫ D.d k.toNat (k.toNat + 1) ≫
        F.map e₁.inv := by
      change F.map ((K.extend _).d k (k + 1)) = _
      rw [K.extend_d_eq ComplexShape.embeddingUpNat
        (i := k.toNat) (j := k.toNat + 1)
        (by change (k.toNat : ℤ) = k; omega)
        (by change ((k.toNat + 1 : ℕ) : ℤ) = k + 1; omega)]
      simp only [Functor.map_comp]
      rfl
    refine ⟨F.map e₁.hom ≫ s ≫ F.map e₀.inv, ?_⟩
    rw [hd]
    simp only [Category.assoc]
    rw [← F.map_comp_assoc e₁.inv, Iso.inv_hom_id, F.map_id, Category.id_comp]
    rw [← F.map_comp_assoc e₀.inv, Iso.inv_hom_id, F.map_id, Category.id_comp]
    simpa only [Category.assoc] using
      congrArg (fun f ↦ F.map e₀.hom ≫ f ≫ F.map e₁.inv) hs
  · have hz : Limits.IsZero (C.X k) := by
      apply F.map_isZero
      apply K.isZero_extend_X
      intro n hn
      change (n : ℤ) = k at hn
      omega
    refine ⟨0, ?_⟩
    exact hz.eq_of_src _ _

end AlgebraicGeometry
