/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientIsoConstructible

/-!
# Constructible finite-Tor complexes under a condensed coefficient isomorphism

Source: blueprint main-20261015, sk-lem-brown-hypotheses-generation.proof.md,
coefficient identifications in Compactness
(blueprint: lem-sfb-condensed-coefficient-iso-constructible).
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

section FinitePresentation

open CategoryTheory.MonoidalCategory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    {R : C} {S : D} [MonObj R] [MonObj S]
    [PreservesFiniteColimits (tensorLeft R)] [PreservesFiniteColimits (tensorLeft S)]

private theorem fp_map (F : Mod C R ⥤ Mod D S) [F.Additive]
    [PreservesFiniteColimits F]
    (e : ∀ n : ℕ, F.obj (Mod.finiteFree R n) ≅ Mod.finiteFree S n)
    {M : Mod C R} (hM : Mod.IsFinitelyPresented R M) :
    Mod.IsFinitelyPresented S (F.obj M) := by
  obtain ⟨n, m, g, ⟨eg⟩⟩ := hM
  refine ⟨n, m, (e m).inv ≫ F.map g ≫ (e n).hom, ⟨?_⟩⟩
  exact F.mapIso eg ≪≫ PreservesCokernel.iso F g ≪≫
    cokernel.mapIso _ _ (e m) (e n) (by simp)

end FinitePresentation

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar

private theorem fp_comap
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ']
    (φ : Λ' ⟶ Λ) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ}
    (hM : Mod.IsFinitelyPresented Λ M) :
    Mod.IsFinitelyPresented Λ' ((Mod.comap φ).obj M) := by
  apply fp_map (Mod.comap φ) _ hM
  intro n
  exact (Mod.comap φ).mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫
    biproduct.mapIso (fun _ ↦ (Mod.comapUnitIso φ).symm)

section Constructible

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ']

private theorem localModel_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨h⟩⟩ := hU i
  exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (U.f i)).mapIso e.symm ≪≫ h⟩⟩

private theorem stratified_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsFiniteConstantStratified Λ X M) :
    IsFiniteConstantStratified Λ X N := by
  obtain ⟨S, hS⟩ := hM
  exact ⟨S, fun a ↦ localModel_iso
    ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩

private theorem constructible_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  classical
  unfold IsConstantModelConstructible at hM ⊢
  split at hM
  · rw [ite_eq_left ‹_›]
    exact stratified_iso e hM
  · rw [ite_eq_right ‹_›]
    exact fun U hU ↦ stratified_iso
      ((CondensedRing.upperStar Λ U.ι).mapIso e) (hM U hU)

private theorem localModel_comap (φ : Λ' ⟶ Λ) [IsMonHom φ] [IsIso φ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ' X
      ((Mod.comap ((upperStarFromPoint X).map φ)).obj M) := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨h⟩⟩ := hU i
  refine ⟨(Mod.comap φ).obj P, fp_comap φ hP, ⟨?_⟩⟩
  exact ((CondensedRing.comapUpperStarIso (Λ := Λ') (Λ' := Λ) φ (U.f i)).app M).symm ≪≫
    (Mod.comap ((upperStarFromPoint (U.X i)).map φ)).mapIso h ≪≫
    (((upperStarFromPoint (U.X i)).mapModComapIso φ).app P).symm

private theorem stratified_comap (φ : Λ' ⟶ Λ) [IsMonHom φ] [IsIso φ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsFiniteConstantStratified Λ X M) :
    IsFiniteConstantStratified Λ' X
      ((Mod.comap ((upperStarFromPoint X).map φ)).obj M) := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  exact localModel_iso ((CondensedRing.comapUpperStarIso (Λ := Λ') (Λ' := Λ) φ
    (S.immersion a)).app M)
    (localModel_comap φ _ _ (hS a))

private theorem constructible_comap (φ : Λ' ⟶ Λ) [IsMonHom φ] [IsIso φ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ' X
      ((Mod.comap ((upperStarFromPoint X).map φ)).obj M) := by
  classical
  unfold IsConstantModelConstructible at hM ⊢
  split at hM
  · rw [ite_eq_left ‹_›]
    exact stratified_comap φ X M hM
  · rw [ite_eq_right ‹_›]
    intro U hU
    exact stratified_iso ((CondensedRing.comapUpperStarIso (Λ := Λ') (Λ' := Λ) φ U.ι).app M)
      (stratified_comap φ _ _ (hM U hU))

end Constructible

/-- Restricting scalars along the inverse of a condensed ring isomorphism preserves
bounded constructibility with finite constant models and finite Tor amplitude.

Source: blueprint main-20261015, sk-lem-brown-hypotheses-generation.proof.md,
coefficient identifications in Compactness
(blueprint: lem-sfb-condensed-coefficient-iso-constructible).

Proof: At the point and on each scheme, restriction along the inverse isomorphism
is an additive exact equivalence, inverse to restriction along the forward map.
It sends the regular module to the regular module using the ring isomorphism;
finite sums and cokernels then carry each finite matrix presentation to a finite
matrix presentation. For every scheme morphism, naturality of the pulled-back
coefficient map gives a commutative square of ring objects. The scalar-restriction
comparison for that square identifies restriction of each constant local model
with the pullback of the transported presentation on the point. Use the same
pro-etale cover and finite constructible stratification, or the same affine opens
in the affine-local convention. Thus constructible sheaves remain constructible.
Exactness identifies the cohomology of the termwise derived functor with the
transported cohomology, and reflects its vanishing, preserving boundedness.
Finally restriction along a ring isomorphism is a strong monoidal equivalence,
so it preserves flat objects. For the given Tor interval [a,b], use the flat-model
characterization of Tor amplitude: represent C by a complex of flat objects
concentrated in [a,b]. Exact scalar restriction takes that complex to a complex
of flat objects in the same interval, and its derived comparison identifies the
result with the transported C. The same characterization gives the required
finite Tor amplitude. The construction works
for the zero ring and the empty scheme, and uses no finite-type hypothesis. -/
theorem constantModelCtf_coefficientIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (X : Scheme.{u})
    (C : ConstantModelConstructibleFiniteTor Λ X) :
    (constantModelBoundedConstructible Λ' X ⊓ DerivedCategory.finiteTorAmplitude _)
      ((Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        ((upperStarFromPoint X).map (show Λ' ⟶ Λ from e.inv.hom))).mapDerivedCategory.obj
          C.obj) := by
  classical
  let φ := (upperStarFromPoint X).map e.inv.hom
  have _ : IsIso e.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  have _ : IsIso φ := inferInstanceAs (IsIso ((upperStarFromPoint X).map e.inv.hom))
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) φ
  have _ : F.IsEquivalence :=
    (inferInstance : (Mod.comapEquivalenceOfIsIso φ).functor.IsEquivalence)
  have _ : F.PreservesFlat := Functor.preservesFlat_of_isEquivalence F
  refine ⟨⟨F.bounded_mapDerivedCategory_obj C.property.1.1, ?_⟩, ?_⟩
  · intro n
    exact constructible_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app C.obj)
      (constructible_comap (Λ := Λ) (Λ' := Λ') e.inv.hom X _ (C.property.1.2 n))
  · obtain ⟨a, b, h⟩ := C.property.2
    exact ⟨a, b, DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj F h⟩

end AlgebraicGeometry.ProEtale
