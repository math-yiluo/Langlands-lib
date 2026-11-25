/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientPullback
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower

/-! # Completion of continuous integral coefficients -/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry Scheme
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionIdeal

/-- Constant functions as sections of the continuous coefficient sheaf. -/
noncomputable def continuousCoefficientConstants (X : Scheme.{u}) (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of T) ⟶
      (continuousCoefficientSheaf X T).obj where
  app U := CommRingCat.ofHom
    { toFun := fun a ↦ ContinuousMap.const U.unop.left a
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  naturality _ _ _ := by ext; rfl

/-- The canonical constant-sheaf comparison, extended from constant functions. -/
noncomputable def continuousCoefficientConstantComparison (X : Scheme.{u})
    (T : Type (u + 1)) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of T) ⟶
      continuousCoefficientSheaf X T :=
  ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv _ _).symm
    (continuousCoefficientConstants X T)

private theorem continuousCoefficientConstantComparison_unit (X : Scheme.{u})
    (T : Type (u + 1)) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of T)) ≫
      (continuousCoefficientConstantComparison X T).hom = continuousCoefficientConstants X T :=
  Equiv.apply_symm_apply
    ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv _ _) _

/-- For discrete coefficients constant sections identify sheafified constants with
continuous functions. Open fibres are pro-etale covers, including the empty cover. -/
theorem continuousCoefficientConstantComparison_isIso (X : Scheme.{u})
    (T : Type (u + 1)) [TopologicalSpace T] [DiscreteTopology T]
    [CommRing T] [IsTopologicalRing T] :
    IsIso (continuousCoefficientConstantComparison X T) := by
  classical
  have hinj : Presheaf.IsLocallyInjective (ProEt.topology X)
      (continuousCoefficientConstants X T) := by
    refine ⟨?_⟩
    intro U a b hab
    by_cases hU : Nonempty U.unop.left
    · obtain ⟨x⟩ := hU
      have hab' := congrArg (fun s : C(U.unop.left, T) ↦ s x) hab
      change a = b at hab'
      subst b
      simpa only [Presheaf.equalizerSieve_self_eq_top] using
        (ProEt.topology X).top_mem U.unop
    · have : IsEmpty U.unop.left := not_nonempty_iff.mp hU
      exact (ProEt.topology X).superset_covering bot_le (ProEt.bot_mem_topology U.unop)
  have hsurj : Presheaf.IsLocallySurjective (ProEt.topology X)
      (continuousCoefficientConstants X T) := by
    refine ⟨?_⟩
    intro U s
    change C(U.left, T) at s
    let O (x : U.left) : U.left.Opens :=
      ⟨s ⁻¹' {s x}, (isOpen_discrete _).preimage s.continuous⟩
    apply ProEt.mem_topology_of_openImmersion _ (fun x ↦ (O x).ι)
    · intro x
      exact ⟨x, ⟨⟨x, rfl⟩, rfl⟩⟩
    · intro x
      refine ⟨s x, ?_⟩
      apply ContinuousMap.ext
      intro y
      change s x = s y.val
      exact y.property.symm
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  constructor
  · change Presheaf.IsLocallyInjective _ (continuousCoefficientConstantComparison X T).hom
    rw [← Presheaf.comp_isLocallyInjective_iff _
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of T))),
      continuousCoefficientConstantComparison_unit]
    exact hinj
  · change Presheaf.IsLocallySurjective _ (continuousCoefficientConstantComparison X T).hom
    rw [← Presheaf.comp_isLocallySurjective_iff _
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of T))),
      continuousCoefficientConstantComparison_unit]
    exact hsurj

/-- Continuous functions with discrete coefficients, functorial in ring maps. -/
noncomputable def discreteContinuousCoefficientFunctor (X : Scheme.{u}) :
    CommRingCat.{u + 1} ⥤ Sheaf (ProEt.topology X) CommRingCat.{u + 1} where
  obj T := by
    let : TopologicalSpace T := ⊥
    let : DiscreteTopology T := ⟨rfl⟩
    exact continuousCoefficientSheaf X T
  map {T S} f := by
    let : TopologicalSpace T := ⊥
    let : DiscreteTopology T := ⟨rfl⟩
    let : TopologicalSpace S := ⊥
    let : DiscreteTopology S := ⟨rfl⟩
    exact continuousCoefficientMap f.hom (continuous_of_discreteTopology) X
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

theorem discreteConstantComparison_naturality (X : Scheme.{u})
    {T S : CommRingCat.{u + 1}} (f : T ⟶ S) :
    let : TopologicalSpace T := ⊥
    let : DiscreteTopology T := ⟨rfl⟩
    let : TopologicalSpace S := ⊥
    let : DiscreteTopology S := ⟨rfl⟩
    (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map f ≫
        continuousCoefficientConstantComparison X S =
      continuousCoefficientConstantComparison X T ≫
        (discreteContinuousCoefficientFunctor X).map f := by
  let adj := sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}
  unfold continuousCoefficientConstantComparison
  change (presheafToSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      ((Functor.const X.ProEtᵒᵖ).map f) ≫
      (adj.homEquiv _ _).symm _ = (adj.homEquiv _ _).symm _ ≫ _
  rw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm]
  congr 1

/-- The discrete continuous-function functor is canonically the constant sheaf functor. -/
noncomputable def discreteContinuousCoefficientIso (X : Scheme.{u}) :
    constantSheaf (ProEt.topology X) CommRingCat.{u + 1} ≅
      discreteContinuousCoefficientFunctor X :=
  NatIso.ofComponents (fun T ↦ by
    let : TopologicalSpace T := ⊥
    let : DiscreteTopology T := ⟨rfl⟩
    let := continuousCoefficientConstantComparison_isIso X T
    exact asIso (continuousCoefficientConstantComparison X T))
    (fun f ↦ discreteConstantComparison_naturality X f)

private theorem commRingForgetReflectsLimit {J : Type v} [Category J]
    (F : J ⥤ CommRingCat.{u}) (c : Limits.Cone F)
    (hc : Limits.IsLimit ((CategoryTheory.forget CommRingCat).mapCone c)) :
    Nonempty (Limits.IsLimit c) := by
  let ext (x y : c.pt) (h : ∀ j, c.π.app j x = c.π.app j y) : x = y := by
    apply (Limits.Types.isLimitEquivSections hc).injective
    exact Subtype.ext (funext h)
  let lift (s : Limits.Cone F) : s.pt ⟶ c.pt := CommRingCat.ofHom
    { toFun := hc.lift ((CategoryTheory.forget CommRingCat).mapCone s)
      map_one' := by
        apply ext
        intro j
        simpa using ConcreteCategory.congr_hom (hc.fac
          ((CategoryTheory.forget CommRingCat).mapCone s) j) (1 : s.pt)
      map_mul' := by
        intro x y
        apply ext
        intro j
        have hj (z : s.pt) : c.π.app j
            (hc.lift ((CategoryTheory.forget CommRingCat).mapCone s) z) = s.π.app j z :=
          ConcreteCategory.congr_hom (hc.fac
            ((CategoryTheory.forget CommRingCat).mapCone s) j) z
        simp only [map_mul]
        rw [hj, hj, hj, map_mul]
      map_zero' := by
        apply ext
        intro j
        simpa using ConcreteCategory.congr_hom (hc.fac
          ((CategoryTheory.forget CommRingCat).mapCone s) j) (0 : s.pt)
      map_add' := by
        intro x y
        apply ext
        intro j
        have hj (z : s.pt) : c.π.app j
            (hc.lift ((CategoryTheory.forget CommRingCat).mapCone s) z) = s.π.app j z :=
          ConcreteCategory.congr_hom (hc.fac
            ((CategoryTheory.forget CommRingCat).mapCone s) j) z
        simp only [map_add]
        rw [hj, hj, hj, map_add] }
  refine ⟨{ lift := lift, fac := ?_, uniq := ?_ }⟩
  · intro s j
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact ConcreteCategory.congr_hom (hc.fac ((CategoryTheory.forget CommRingCat).mapCone s) j) x
  · intro s m hm
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    apply ext
    intro j
    exact (congrArg (fun f : s.pt ⟶ _ ↦ f x) (hm j)).trans
      (ConcreteCategory.congr_hom (hc.fac ((CategoryTheory.forget CommRingCat).mapCone s) j) x).symm

end AlgebraicGeometry.Scheme
