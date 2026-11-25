/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.TorsorAssociatedModule
import WeilConjectures.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf
import WeilConjectures.ConstructibleSheaf.TorsorDiagonalEvaluationBijective

/-!
# Invariant sections descend along a finite etale torsor

Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
(blueprint: lem-weil-pbc-torsor-invariant-sections)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.GaloisCover

private noncomputable def constantToInvariant {V : Scheme.{u}} (ℓ : ℕ)
    {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) :
    (Functor.const V.Etaleᵒᵖ).obj
        (ModuleCat.of (ULift.{u + 1} (ZMod ℓ)) (ULift.{u + 1} (ZMod ℓ))) ⟶
      c.equivariantModulePresheaf ℓ
          (Rep.trivial (ZMod ℓ) P (ULift.{u + 1} (ZMod ℓ))) ⋙
        ModuleCat.restrictScalars
          (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ) where
  app W := ModuleCat.ofHom
    { toFun := fun a ↦ ⟨LocallyConstant.const _ a, by intro g x; rfl⟩
      map_add' := by intro a b; rfl
      map_smul' := by intro r a; rfl }
  naturality _ _ _ := by rfl

/-- Invariant locally constant coefficient functions on the torsor are precisely
sections of the constant coefficient sheaf downstairs, before sheafification.
Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
(blueprint: lem-weil-pbc-torsor-invariant-sections)

Proof: Over an etale object W, trivialize the pulled-back torsor on an etale
cover of W. An invariant function has the same value on all translates of a
local torsor section, so evaluation gives a locally constant function on each
member of this cover. A different section differs locally by a group element;
invariance makes the evaluations identical. They therefore glue uniquely on
W. Conversely pull back a locally constant function on W to the torsor; it is
invariant. Surjectivity of the torsor and its local trivializations show that
these operations are inverse. They commute with restriction and pointwise
module operations, including restriction of scalars. Locally constant functions
on W identify with sections of the constant coefficient sheaf: the constant
presheaf maps to them by constant functions; any locally constant function is
locally in its image on its open fibers, and equality of two such sections is
local. This gives the identification after sheafification of the constant
presheaf. On the empty object both section modules are zero. -/
theorem equivariantModulePresheaf_trivial {V : Scheme.{u}} (ℓ : ℕ)
    {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) :
    Nonempty (
      c.equivariantModulePresheaf ℓ
          (Rep.trivial (ZMod ℓ) P (ULift.{u + 1} (ZMod ℓ))) ⋙
        ModuleCat.restrictScalars.{u + 1}
          (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ) ≅
      ((constantSheaf V.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
          (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))).obj) := by
  have := c.etale
  have := c.surjective
  let Q := c.equivariantModulePresheaf ℓ
      (Rep.trivial (ZMod ℓ) P (ULift.{u + 1} (ZMod ℓ))) ⋙
    ModuleCat.restrictScalars
      (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ)
  let η := constantToInvariant ℓ c
  have hQ : Presheaf.IsSheaf V.smallEtaleTopology Q :=
    c.equivariantModulePresheaf_isSheaf ℓ P _
  have hηinj : Presheaf.IsLocallyInjective V.smallEtaleTopology η := by
    constructor
    intro W a b hab
    by_cases h : a = b
    · subst h
      exact V.smallEtaleTopology.superset_covering (fun _ _ _ ↦ rfl)
        (V.smallEtaleTopology.top_mem _)
    · have : IsEmpty (Opposite.unop W).left := ⟨fun w ↦ by
        obtain ⟨x, hx⟩ := Surjective.surj (f := Limits.pullback.fst (Opposite.unop W).hom c.π) w
        exact h (congrArg (fun s ↦ s.val x) hab)⟩
      apply V.smallEtaleTopology.superset_covering _
        ((Scheme.ofArrows_mem_smallEtaleTopology_iff (Z := PEmpty.elim) (W := Opposite.unop W)
          (fun i : PEmpty.{1} ↦ i.elim)).2
          (Set.eq_univ_of_forall fun x ↦ isEmptyElim x))
      rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨i⟩
      exact i.elim
  have hηsurj : Presheaf.IsLocallySurjective V.smallEtaleTopology η := by
    constructor
    intro W s
    let U (a : ULift.{u + 1} (ZMod ℓ)) : (c.sectionSpace W).Opens :=
      ⟨s.val ⁻¹' {a}, s.val.isLocallyConstant.isOpen_fiber a⟩
    let T' (a : ULift.{u + 1} (ZMod ℓ)) : c.P.Etale :=
      Scheme.Etale.mk ((U a).ι ≫ Limits.pullback.snd W.hom c.π)
    let T (a : ULift.{u + 1} (ZMod ℓ)) : V.Etale :=
      (MorphismProperty.Over.map ⊤ c.etale).obj (T' a)
    let ι (a : ULift.{u + 1} (ZMod ℓ)) : T a ⟶ W :=
      MorphismProperty.Over.homMk ((U a).ι ≫ Limits.pullback.fst W.hom c.π)
        (by simp [T, T', Category.assoc, Limits.pullback.condition])
    apply V.smallEtaleTopology.superset_covering _
      ((Scheme.ofArrows_mem_smallEtaleTopology_iff ι).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨a⟩
      refine ⟨a, ?_⟩
      apply (c.diagonalEvaluation_bijective ℓ _ (T' a)).1
      apply LocallyConstant.ext
      intro x
      let graph := c.diagonalSection (T' a)
      change a = s.val (c.sectionRestriction (ι a) (graph x))
      have hp : graph ≫ c.sectionRestriction (ι a) = (U a).ι := by
        apply Limits.pullback.hom_ext <;>
          simp only [Functor.id_obj, Functor.const_obj_obj, diagonalSection,
            MorphismProperty.Over.mk_hom, sectionRestriction,
            MorphismProperty.Over.homMk_hom, Over.homMk_left, Category.assoc,
            Limits.limit.lift_π, Limits.PullbackCone.mk_π_app,
            Limits.limit.lift_π_assoc, Limits.cospan_left, Category.comp_id,
            T', graph, ι]
        exact Category.id_comp _
      rw [← Scheme.Hom.comp_apply, hp]
      exact x.property.symm
    · apply Set.eq_univ_of_forall
      intro w
      obtain ⟨x, hx⟩ := Surjective.surj (f := Limits.pullback.fst W.hom c.π) w
      exact Set.mem_iUnion.2 ⟨s.val x, ⟨⟨x, rfl⟩, hx⟩⟩
  let F : Sheaf V.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) := ⟨Q, hQ⟩
  let φ : (constantSheaf V.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
        (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))) ⟶ F :=
    ⟨sheafifyLift V.smallEtaleTopology η hQ⟩
  have hfac : toSheafify V.smallEtaleTopology _ ≫ φ.hom = η :=
    toSheafify_sheafifyLift _ _ _
  have : Presheaf.IsLocallyInjective V.smallEtaleTopology φ.hom := by
    rw [← Presheaf.comp_isLocallyInjective_iff _ (toSheafify _ _), hfac]
    exact hηinj
  have : Presheaf.IsLocallySurjective V.smallEtaleTopology φ.hom := by
    rw [← Presheaf.comp_isLocallySurjective_iff _ (toSheafify _ _), hfac]
    exact hηsurj
  have : CategoryTheory.Limits.PreservesLimitsOfSize.{u, u + 1}
      (CategoryTheory.forget (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :=
    CategoryTheory.Limits.preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have : V.smallEtaleTopology.HasSheafCompose
      (CategoryTheory.forget (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) := inferInstance
  have : IsIso φ := (Sheaf.isLocallyBijective_iff_isIso φ).1 ⟨‹_›, ‹_›⟩
  exact ⟨((sheafToPresheaf _ _).mapIso (asIso φ)).symm⟩

end AlgebraicGeometry.Scheme.GaloisCover
