import Langlands.Sheaf.PointActionModules
import WeilConjectures.AlgebraicGeometry.EtaleSheafDiscreteContinuousRep

/-!
# Étale sheaves of modules on the spectrum of a field and discrete Galois representations

Let `K` be a field, `Ks` a separable closure of `K` and `Λ` a commutative ring, in one universe
`u`. The fibre at weil-conjectures's Galois point `AlgebraicGeometry.Scheme.galoisPoint K Ks`
(the geometric point `Spec Ks → Spec K`) with its action of `Gal(Ks/K)` by transport of
structure is an equivalence `Langlands.Geometry.FieldEtaleModuleSheaves.equivalence` from étale
sheaves of `Λ`-modules on `Spec K` to `Rep.DiscreteContinuousRep Λ Gal(Ks/K)`, the
`Λ`-representations with open stabilizers (Stacks Project, Theorem 59.56.3, Tag 03QT). Its
inverse is the sheaf of equivariant maps of `Langlands.Sheaf.PointActionModules`. The underlying
module of the representation attached to a sheaf is its stalk at `Spec Ks → Spec K`
(`forgetIso`), and `σ` sends the germ of a section at a lift `x` to its germ at `Spec σ ≫ x`
(`forgetIso_hom_app_ρ`).

The proof follows weil-conjectures's proof of the case `Λ = ℤ`
(`AlgebraicGeometry.Scheme.isGaloisPoint_galoisPoint`), with the same inputs on the points
`x_E : Spec Ks → Spec E` of the finite subextensions `E` of `Ks / K`: stalks have open
stabilizers, the counit is bijective on representations with open stabilizers, and the unit is
an isomorphism since the fibre at the Galois point reflects isomorphisms.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry
open Langlands.Sheaf.PointActionModules

namespace Langlands.Geometry.FieldEtaleModuleSheaves

variable (K Ks : Type u) [Field K] [Field Ks] [Algebra K Ks] [IsSepClosed Ks]
  [Algebra.IsSeparable K Ks] (Λ : Type u) [CommRing Λ]

/-- Forgetting the `Λ`-module structure preserves filtered colimits indexed by categories in the
universe of the modules, for a ring `Λ` in a smaller universe. -/
instance forget₂_preservesFilteredColimitsOfSize :
    PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) where
  preserves_filtered_colimits _ _ _ :=
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone
          (ModuleCat.FilteredColimits.colimitCoconeIsColimit.{u + 1, u} F)
          (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit.{u + 1, u}
            (F ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) }

/-- Forgetting the `Λ`-module structure to sets preserves filtered colimits indexed by
categories in the universe of the modules. -/
instance forget_preservesFilteredColimitsOfSize :
    PreservesFilteredColimitsOfSize.{u + 1, u + 1} (forget (ModuleCat.{u + 1} Λ)) :=
  Limits.comp_preservesFilteredColimits (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    (forget AddCommGrpCat.{u + 1})

/-- The stabilizer of a vector of a representation. -/
def vecStabilizer {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module Λ V]
    (ρ : Representation Λ G V) (v : V) : Subgroup G where
  carrier := {σ | ρ σ v = v}
  one_mem' := by simp
  mul_mem' {σ τ} hσ hτ := by
    simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at hσ hτ ⊢
    rw [hτ, hσ]
  inv_mem' {σ} hσ := by
    simp only [Set.mem_ofPred_eq] at hσ ⊢
    conv_lhs => rw [← hσ]
    exact ρ.inv_self_apply σ v

/-- The stalks at the Galois point of étale sheaves of `Λ`-modules on `Spec K` have open
stabilizers. -/
lemma isOpen_fixed (F : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (v : (sheafFiberRep (Scheme.galoisPoint K Ks) (Scheme.galoisPointAct K Ks) Λ).obj F) :
    IsOpen {σ : Gal(Ks/K) |
      ((sheafFiberRep (Scheme.galoisPoint K Ks) (Scheme.galoisPointAct K Ks) Λ).obj F).ρ σ v =
        v} := by
  obtain ⟨X, x, t, rfl⟩ := (Scheme.galoisPoint K Ks).toPresheafFiber_jointly_surjective
    (A := ModuleCat.{u + 1} Λ) (P := F.obj) v
  obtain ⟨E, _, g, rfl⟩ := Scheme.exists_galoisPoint_fiber_map_eq X x
  refine Subgroup.isOpen_mono (H₂ := vecStabilizer Λ _ _) (fun σ hσ ↦ ?_)
    E.fixingSubgroup_isOpen
  change fiberRepresentation _ _ Λ F.obj σ _ = _
  rw [fiberRepresentation_toPresheafFiber,
    Scheme.galoisPointAct_fiber_map_galoisPointFiberSpec g hσ]

omit [Algebra.IsSeparable K Ks] in
/-- The fibre at the Galois point reflects isomorphisms of étale sheaves of `Λ`-modules. -/
lemma isIso_of_isIso_sheafFiber_map
    {F F' : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : F ⟶ F')
    (hf : IsIso ((Scheme.galoisPoint K Ks).sheafFiber.map f)) : IsIso f := by
  have h := Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ
    (Spec (.of K)) (ι := PUnit.{u + 1}) (Ω := fun _ ↦ Ks)
    (fun _ ↦ Scheme.specAlgebraMap K Ks) (by
      refine Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 ⟨PUnit.unit, default, ?_⟩
      exact Subsingleton.elim _ _)
  refine ((h.jointlyReflectIsomorphisms (ModuleCat.{u + 1} Λ)).isIso_iff f).2 ?_
  rintro ⟨-, ⟨⟨⟩⟩⟩
  exact hf

/-- The counit is an isomorphism at every representation with open stabilizers. -/
lemma isIso_fromEquivariantSheaf (M : Rep.{u + 1} Λ Gal(Ks/K))
    (hM : ∀ m : M, IsOpen {σ : Gal(Ks/K) | M.ρ σ m = m}) :
    IsIso (fromEquivariantSheaf (Scheme.galoisPoint K Ks) (Scheme.galoisPointAct K Ks) Λ M) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro v hv
    obtain ⟨X, x, f, rfl⟩ := (Scheme.galoisPoint K Ks).toPresheafFiber_jointly_surjective
      (A := ModuleCat.{u + 1} Λ)
      (P := equivariantPresheaf (Scheme.galoisPoint K Ks) (Scheme.galoisPointAct K Ks) Λ M) v
    obtain ⟨E, _, g, rfl⟩ := Scheme.exists_galoisPoint_fiber_map_eq X x
    rw [← GrothendieckTopology.Point.toPresheafFiber_w_apply] at hv ⊢
    set f' := (equivariantPresheaf (Scheme.galoisPoint K Ks) (Scheme.galoisPointAct K Ks) Λ M).map
      g.op f
    have h₀ : f'.1 (Scheme.galoisPointFiberSpec K Ks E) = 0 := by
      rw [← hv]
      exact (fromEquivariantSheaf_hom_apply _ _ _ _ _ _ _).symm
    have hf' : f' = 0 := by
      refine Subtype.ext (funext fun y ↦ ?_)
      obtain ⟨σ, rfl⟩ := Scheme.exists_galoisPointAct_galoisPointFiberSpec_eq y
      rw [f'.2 σ, h₀, map_zero]
      rfl
    rw [hf', map_zero]
    rfl
  · intro m
    have hU : (vecStabilizer Λ M.ρ m : Set Gal(Ks/K)) ∈ nhds 1 :=
      (hM m).mem_nhds (one_mem (vecStabilizer Λ M.ρ m))
    obtain ⟨E, _, hEU⟩ := (krullTopology_mem_nhds_one_iff K Ks _).1 hU
    choose τ hτ using fun y ↦ Scheme.exists_galoisPointAct_galoisPointFiberSpec_eq (E := E) y
    have key (σ : Gal(Ks/K)) (y : (Scheme.galoisPoint K Ks).fiber.obj (Scheme.galoisEtaleSpec K Ks E))
        (hσ : (Scheme.galoisPointAct K Ks σ).asHom.app _ (Scheme.galoisPointFiberSpec K Ks E) = y) :
        M.ρ σ m = M.ρ (τ y) m := by
      have h : (τ y)⁻¹ * σ ∈ E.fixingSubgroup := by
        set t := τ y
        have ht : (Scheme.galoisPointAct K Ks t).asHom.app _ (Scheme.galoisPointFiberSpec K Ks E) =
          y := hτ y
        rw [← Scheme.galoisPointAct_galoisPointFiberSpec_eq_iff, act_mul_app, hσ, ← ht,
          ← act_mul_app, inv_mul_cancel, act_one_app]
      have h' : M.ρ ((τ y)⁻¹ * σ) m = m := hEU h
      rw [map_mul, Module.End.mul_apply] at h'
      conv_rhs => rw [← h']
      exact (M.ρ.self_inv_apply (τ y) _).symm
    let f : (equivariantPresheaf (Scheme.galoisPoint K Ks) (Scheme.galoisPointAct K Ks) Λ M).obj
        (op (Scheme.galoisEtaleSpec K Ks E)) :=
      ⟨fun y ↦ M.ρ (τ y) m, fun σ y ↦ by
        dsimp only
        rw [← key (σ * τ y) _ (by rw [act_mul_app, hτ y]), map_mul, Module.End.mul_apply]⟩
    refine ⟨(Scheme.galoisPoint K Ks).toPresheafFiber _ (Scheme.galoisPointFiberSpec K Ks E)
      (equivariantPresheaf (Scheme.galoisPoint K Ks) (Scheme.galoisPointAct K Ks) Λ M) f, ?_⟩
    rw [fromEquivariantSheaf_hom_apply]
    change M.ρ (τ _) m = m
    rw [← key 1 _ (act_one_app _ _ _ _), map_one, Module.End.one_apply]

/-- The unit is an isomorphism at every étale sheaf of `Λ`-modules on `Spec K`. -/
lemma isIso_toEquivariantSheaf
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (toEquivariantSheaf (Scheme.galoisPoint K Ks) (Scheme.galoisPointAct K Ks) Λ F) := by
  refine isIso_of_isIso_sheafFiber_map K Ks Λ _ ?_
  have := isIso_fromEquivariantSheaf K Ks Λ
    ((sheafFiberRep (Scheme.galoisPoint K Ks) (Scheme.galoisPointAct K Ks) Λ).obj F)
    (isOpen_fixed K Ks Λ F)
  have h₁ := sheafFiberRep_map_toEquivariantSheaf_comp_fromEquivariantSheaf
    (Scheme.galoisPoint K Ks) (Scheme.galoisPointAct K Ks) Λ F
  have h₂ : IsIso ((sheafFiberRep (Scheme.galoisPoint K Ks) (Scheme.galoisPointAct K Ks) Λ).map
      (toEquivariantSheaf (Scheme.galoisPoint K Ks) (Scheme.galoisPointAct K Ks) Λ F)) := by
    have : IsIso ((sheafFiberRep (Scheme.galoisPoint K Ks) (Scheme.galoisPointAct K Ks) Λ).map
        (toEquivariantSheaf (Scheme.galoisPoint K Ks) (Scheme.galoisPointAct K Ks) Λ F) ≫
          fromEquivariantSheaf (Scheme.galoisPoint K Ks) (Scheme.galoisPointAct K Ks) Λ
            ((sheafFiberRep (Scheme.galoisPoint K Ks) (Scheme.galoisPointAct K Ks) Λ).obj F)) := by
      rw [h₁]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (fromEquivariantSheaf (Scheme.galoisPoint K Ks) (Scheme.galoisPointAct K Ks) Λ _)
  rw [ConcreteCategory.isIso_iff_bijective] at h₂ ⊢
  exact h₂

/-- The fibre at the Galois point, as a functor from étale sheaves of `Λ`-modules on `Spec K` to
discrete continuous representations of `Gal(Ks/K)`. -/
def sheafFiberDiscreteRep : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
    Rep.DiscreteContinuousRep.{u, u, u + 1} Λ Gal(Ks/K) :=
  ObjectProperty.lift _ (sheafFiberRep (Scheme.galoisPoint K Ks) (Scheme.galoisPointAct K Ks) Λ)
    (isOpen_fixed K Ks Λ)

/-- **Étale sheaves of `Λ`-modules on `Spec K` are discrete continuous `Λ`-representations of
`Gal(Ks/K)`.** The functor is the fibre at the Galois point with its Galois action, the inverse
the sheaf of equivariant maps. -/
def equivalence : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ) ≌
    Rep.DiscreteContinuousRep.{u, u, u + 1} Λ Gal(Ks/K) :=
  CategoryTheory.Equivalence.mk (sheafFiberDiscreteRep K Ks Λ)
    (ObjectProperty.ι _ ⋙
      equivariantSheafFunctor (Scheme.galoisPoint K Ks) (Scheme.galoisPointAct K Ks) Λ)
    (NatIso.ofComponents (fun F ↦ @asIso _ _ _ _
        (toEquivariantSheaf (Scheme.galoisPoint K Ks) (Scheme.galoisPointAct K Ks) Λ F)
        (isIso_toEquivariantSheaf K Ks Λ F))
      fun g ↦ toEquivariantSheaf_naturality _ _ Λ g)
    (NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ (@asIso _ _ _ _
        (fromEquivariantSheaf (Scheme.galoisPoint K Ks) (Scheme.galoisPointAct K Ks) Λ M.obj)
        (isIso_fromEquivariantSheaf K Ks Λ M.obj M.property)))
      fun f ↦ ObjectProperty.hom_ext _ (fromEquivariantSheaf_naturality _ _ Λ f.hom))

lemma equivalence_functor_obj_obj
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((equivalence K Ks Λ).functor.obj F).obj =
      (sheafFiberRep (Scheme.galoisPoint K Ks) (Scheme.galoisPointAct K Ks) Λ).obj F :=
  rfl

/-- The underlying `Λ`-module of the representation attached to a sheaf is its stalk at the
geometric point `Spec Ks → Spec K`. -/
def forgetIso :
    (equivalence K Ks Λ).functor ⋙ ObjectProperty.ι _ ⋙
        forget₂ (Rep.{u + 1} Λ Gal(Ks/K)) (ModuleCat.{u + 1} Λ) ≅
      (Scheme.pointSmallEtale (Scheme.specAlgebraMap K Ks)).sheafFiber :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl) ≪≫
    (Scheme.pointSmallEtale (Scheme.specAlgebraMap K Ks)).uliftSheafFiberIso.{u + 1}
      (ModuleCat.{u + 1} Λ)

lemma forgetIso_hom_app_toPresheafFiber
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (X : (Spec (.of K)).Etale)
    (x : (Scheme.pointSmallEtale (Scheme.specAlgebraMap K Ks)).fiber.obj X)
    (z : F.obj.obj (op X)) :
    (forgetIso K Ks Λ).hom.app F
        ((Scheme.galoisPoint K Ks).toPresheafFiber X (ULift.up x) F.obj z) =
      (Scheme.pointSmallEtale (Scheme.specAlgebraMap K Ks)).toPresheafFiber X x F.obj z :=
  ConcreteCategory.congr_hom
    (GrothendieckTopology.Point.toPresheafFiber_uliftSheafFiberIso_hom_app
      (Scheme.pointSmallEtale (Scheme.specAlgebraMap K Ks)) (ModuleCat.{u + 1} Λ) F X x) z

lemma forgetIso_inv_app_toPresheafFiber
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (X : (Spec (.of K)).Etale)
    (x : (Scheme.pointSmallEtale (Scheme.specAlgebraMap K Ks)).fiber.obj X)
    (z : F.obj.obj (op X)) :
    (forgetIso K Ks Λ).inv.app F
        ((Scheme.pointSmallEtale (Scheme.specAlgebraMap K Ks)).toPresheafFiber X x F.obj z) =
      (Scheme.galoisPoint K Ks).toPresheafFiber X (ULift.up x) F.obj z := by
  rw [← forgetIso_hom_app_toPresheafFiber K Ks Λ F X x z]
  exact Iso.hom_inv_id_apply ((forgetIso K Ks Λ).app F) _

/-- Under `forgetIso`, `σ ∈ Gal(Ks/K)` sends the germ of a section at a lift `x` of
`Spec Ks → Spec K` to its germ at the lift `Spec σ ≫ x`. -/
lemma forgetIso_hom_app_ρ (F : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (σ : Gal(Ks/K)) (X : (Spec (.of K)).Etale)
    (x x' : (Scheme.pointSmallEtale (Scheme.specAlgebraMap K Ks)).fiber.obj X)
    (hx : x'.left = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.left)
    (z : F.obj.obj (op X)) :
    (forgetIso K Ks Λ).hom.app F (((equivalence K Ks Λ).functor.obj F).obj.ρ σ
        ((forgetIso K Ks Λ).inv.app F
          ((Scheme.pointSmallEtale (Scheme.specAlgebraMap K Ks)).toPresheafFiber X x F.obj z))) =
      (Scheme.pointSmallEtale (Scheme.specAlgebraMap K Ks)).toPresheafFiber X x' F.obj z := by
  rw [forgetIso_inv_app_toPresheafFiber]
  have h : (Scheme.galoisPointAct K Ks σ).asHom.app X (ULift.up x) = ULift.up x' :=
    ULift.ext (Over.OverMorphism.ext hx.symm)
  have h2 := fiberRepresentation_toPresheafFiber (Scheme.galoisPoint K Ks)
    (Scheme.galoisPointAct K Ks) Λ F.obj σ X (ULift.up x) z
  rw [h] at h2
  exact (congrArg (fun v ↦ (forgetIso K Ks Λ).hom.app F v) h2).trans
    (forgetIso_hom_app_toPresheafFiber K Ks Λ F X x' z)

end Langlands.Geometry.FieldEtaleModuleSheaves
