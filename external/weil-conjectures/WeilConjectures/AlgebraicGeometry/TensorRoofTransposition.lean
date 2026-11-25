/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorAugmentation
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.AlgebraicGeometry.TensorModelRestrictionAdjunction

/-! # Transposing a supplied augmented complex after open restriction

Source: Stacks Project, Tags 08DJ, 08DL and 08EH.
(blueprint: lem-sc-tensor-roof-transposition).
-/

@[expose] public section

set_option autoImplicit false

universe uX wD

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem unit_transposition_comp {C D : Type*} [Category C] [Category D]
    (R : C ⥤ D) {B BT A E : C} (d : B ⟶ BT) (c : BT ≅ A)
    (f : R.obj A ⟶ R.obj E) (g : R.obj BT ⟶ R.obj E)
    (k : R.obj B ⟶ R.obj E)
    (hf : f = (R.mapIso c).inv ≫ g) (hg : R.map d ≫ g = k) :
    R.map (d ≫ c.hom) ≫ f = k := by
  rw [hf, Functor.map_comp]
  change (R.map d ≫ (R.mapIso c).hom) ≫ (R.mapIso c).inv ≫ g = k
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hg

private theorem homCongr_refl_apply {C : Type*} [Category C]
    {B A E : C} (c : B ≅ A) (f : B ⟶ E) :
    Iso.homCongr c (Iso.refl E) f = c.inv ≫ f := by
  simp [Iso.homCongr]

private theorem isIso_of_two_precomp_tests {C : Type*} [Category C]
    {B B' : C} (d : B ⟶ B')
    (hs : Function.Surjective (fun g : B' ⟶ B ↦ d ≫ g))
    (hi : Function.Injective (fun g : B' ⟶ B' ↦ d ≫ g)) : IsIso d := by
  obtain ⟨g, hg⟩ := hs (𝟙 B)
  have hg' : g ≫ d = 𝟙 B' := hi (by simp [← Category.assoc, hg])
  exact ⟨⟨g, hg, hg'⟩⟩

private theorem precomp_bijective_of_equivs {C : Type*} [Category C]
    {I I' B B' H Z : C} (a : I ⟶ I') [IsIso a] (d : B ⟶ B')
    (r : (I ⟶ H) ≃ (B ⟶ Z)) (r' : (I' ⟶ H) ≃ (B' ⟶ Z))
    (hn : ∀ s, r (a ≫ s) = d ≫ r' s) :
    Function.Bijective (fun g : B' ⟶ Z ↦ d ≫ g) := by
  constructor
  · intro f g hfg
    apply r'.symm.injective
    apply (cancel_epi a).1
    apply r.injective
    simpa only [hn, Equiv.apply_symm_apply] using hfg
  · intro f
    refine ⟨r' (inv a ≫ r.symm f), ?_⟩
    change d ≫ r' (inv a ≫ r.symm f) = f
    rw [← hn]
    simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The total tensor and restriction instances require extra elaboration heartbeats.
set_option synthInstance.maxSize 512 in
/-- Tensor-Hom transposition converts a supplied section representative into a map
from the total tensor model. The augmentation and its representative are inputs;
no affine hypothesis, quasi-coherence, or existence of a perfect roof is asserted.

Source: Stacks Project, cohomology.tex, Tags 08DJ and 08DL; perfect.tex, Tag 08EH,
construction of the two maps and the restriction identity.
(blueprint: lem-sc-tensor-roof-transposition).

Proof:
1. The unit-tensor-Hom adjunction on U and the canonical restriction comparison
   for RHom identify Hom(R(Q(O_X[0])),R(RHom(A,E))) with Hom(R(A),R(E)).
   Use the tensor-unit comparison for restriction and the right unitor. This is
   the equivalence e, fixed by the canonical adjunction, rather than an arbitrary
   isomorphism between the objects supplied by restriction of RHom.
2. For a supplied K-flat J, transpose ξ:J→RHom(A,E) under the canonical derived
   tensor-Hom adjunction. The K-flat comparison identifies A tensor^L Q(J) with
   Q(Tot(P tensor J)), using eA on the first factor. Transport the transpose
   through this comparison to obtain γ.
3. Restriction is exact and preserves K-flat complexes and total tensors. The
   augmentation on the restricted total tensor identifies with id_R(A) tensor
   R(Q(u)), followed by the right unitor. Hence its image is invertible when
   R(Q(u)) is invertible; the chain right unitor and eA are also invertible.
4. The representative tensor-Hom adjunction commutes with restriction, since its
   evaluation maps on tensor summands are the same sheaf maps after restriction.
   Apply its naturality in J to R(Q(u))≫s=R(ξ). The unit adjunction and right-unitor
   identity give R(β)≫e(s)=R(γ), with β exactly the chain formula below.
   The zero complex and empty open satisfy the same identities. -/
theorem tensor_roof_transposition
    (X : Scheme.{uX}) (U : X.Opens)
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))]
    (A E : schemeDerivedCategory X)
    (P : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
    (eA : DerivedCategory.Q.obj P ≅ A) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := (SheafOfModules.tensorClosed X.sheaf).1.some
    let T := HomologicalComplex.tensorUnit
      (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)
    let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    let H := (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf).obj (op A, E)
    ∃ e : (R.obj (DerivedCategory.Q.obj T) ⟶ R.obj H) ≃ (R.obj A ⟶ R.obj E),
      ∀ (J : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ)
        (_ : CochainComplex.IsKFlatTensor (R := X.sheaf) J) (u : J ⟶ T),
        IsIso (R.map (DerivedCategory.Q.map u)) →
        ∀ (ξ : DerivedCategory.Q.obj J ⟶ H)
          (s : R.obj (DerivedCategory.Q.obj T) ⟶ R.obj H),
          R.map (DerivedCategory.Q.map u) ≫ s = R.map ξ →
          let B := DerivedCategory.Q.obj (CochainComplex.mapBifunctor P J (curriedTensor _))
          let β : B ⟶ A := DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor _)
              (ComplexShape.up ℤ)) ≫
            DerivedCategory.Q.map (HomologicalComplex.rightUnitor P).hom ≫ eA.hom
          ∃ γ : B ⟶ E, IsIso (R.map β) ∧ R.map β ≫ e s = R.map γ := by
  classical
  let := SheafOfModules.monoidalCategory X.sheaf
  let := (SheafOfModules.tensorClosed X.sheaf).1.some
  let T := HomologicalComplex.tensorUnit
    (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)
  let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
    Equivalence.functor
      (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
      (Modules.overEquiv U)).mapDerivedCategory
  let B := fun J ↦ DerivedCategory.Q.obj
    (CochainComplex.mapBifunctor P J (curriedTensor _))
  have hh := exists_tensorModel_restriction_adjunction.{uX, wD} X U A P hP eA
  obtain ⟨t, r, hr, hn⟩ := hh
  let c : B T ≅ A :=
    DerivedCategory.Q.mapIso (HomologicalComplex.rightUnitor P) ≪≫ eA
  let e := (r T E).trans (Iso.homCongr (R.mapIso c) (Iso.refl (R.obj E)))
  refine ⟨e, ?_⟩
  intro J _hJ u hu ξ s hs
  let d : B J ⟶ B T := DerivedCategory.Q.map
    (HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor _) (ComplexShape.up ℤ))
  have := hu
  -- Naturality conjugates precomposition by the invertible augmentation.
  have hb (F : schemeDerivedCategory X) :
      Function.Bijective (fun g : R.obj (B T) ⟶ R.obj F ↦ R.map d ≫ g) :=
    precomp_bijective_of_equivs (R.map (DerivedCategory.Q.map u)) (R.map d)
      (r J F) (r T F) (hn J T F u)
  -- The two tests construct a two-sided inverse; no conservativity is assumed.
  have : IsIso (R.map d) := isIso_of_two_precomp_tests (R.map d)
    (hb (B J)).surjective (hb (B T)).injective
  refine ⟨t J E ξ, ?_, ?_⟩
  · change IsIso (R.map (d ≫ c.hom))
    rw [Functor.map_comp]
    infer_instance
  · change R.map (d ≫ c.hom) ≫ e s = R.map (t J E ξ)
    have he : e s = (R.mapIso c).inv ≫ r T E s := by
      change Iso.homCongr (R.mapIso c) (Iso.refl (R.obj E)) (r T E s) = _
      exact homCongr_refl_apply (R.mapIso c) (r T E s)
    apply unit_transposition_comp R d c (e s) (r T E s) (R.map (t J E ξ)) he
    exact (hn J T E u s).symm.trans ((congrArg (r J E) hs).trans (hr J E ξ))

end AlgebraicGeometry.Scheme
