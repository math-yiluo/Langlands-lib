/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.Algebra.OpenSubgroup
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.EtaleSheafDiscreteContinuousRep
import WeilConjectures.FieldTheory.OpenSubgroupFixedField
import WeilConjectures.Mathlib.FieldTheory.KrullTopology

/-!
# Restricted subgroup representations and the fixed-field comparison

Source: Stacks Project, Tags 04JQ, 03QT and 03SF; blueprint
`theorem-cohomology-curves--2`, proof paragraphs 1--2.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits ZeroObject Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false


variable (K Ks : Type u) [Field K] [Field Ks] [Algebra K Ks]
variable (H : OpenSubgroup (Gal(Ks/K)))

/-- Forget the action and the integer module structure. -/
abbrev primaryModuleForget :
    Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ H.toSubgroup ⥤ AddCommGrpCat.{u + 1} :=
  ObjectProperty.ι _ ⋙ Rep.RepToAction ℤ H.toSubgroup ⋙
    Action.forget (ModuleCat.{u + 1} ℤ) H.toSubgroup ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}

/-- Restrict the ambient representation to the open subgroup. -/
noncomputable def primaryRestrictedModule
    (R : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K))) :
    Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ H.toSubgroup := by
  letI : Module ℤ R.obj.V := AddCommGroup.toIntModule _
  let ρ : Representation ℤ H.toSubgroup R.obj.V :=
    { toFun := fun g ↦ (R.obj.ρ (g : Gal(Ks/K))).toAddMonoidHom.toIntLinearMap
      map_one' := by ext x; simp
      map_mul' := fun g h ↦ by
        ext x
        simp [Module.End.mul_apply] }
  exact ⟨Rep.of ρ, fun x ↦ (R.property x).preimage continuous_subtype_val⟩

/-- The actual representation on an invariant additive subgroup, viewed as a Z-submodule. -/
noncomputable def primarySubmodule
    (R : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)))
    (B : AddSubgroup R.obj.V)
    (hB : ∀ (g : H.toSubgroup) (x : R.obj.V), x ∈ B → R.obj.ρ (g : Gal(Ks/K)) x ∈ B) :
    Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ H.toSubgroup := by
  let W := (primaryRestrictedModule K Ks H R).obj.subrepresentation B.toIntSubmodule
    (fun g x hx ↦ hB g x hx)
  refine ⟨W, fun x ↦ ?_⟩
  convert ((primaryRestrictedModule K Ks H R).property x.val) using 1
  ext g
  exact Subtype.ext_iff

/-- The subgroup of B consisting of elements of A; its quotient is literally B/A. -/
abbrev primaryRelativeSubmodule
    (R : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)))
    (A B : AddSubgroup R.obj.V) : Submodule ℤ B.toIntSubmodule := by
  letI : Module ℤ R.obj.V := AddCommGroup.toIntModule _
  exact A.toIntSubmodule.comap B.toIntSubmodule.subtype

/-- The quotient representation with trivial action. It agrees with the induced action
when g*x-x lies in A, which is required by the exactness theorem below. -/
noncomputable def primaryTrivialQuotient
    (R : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)))
    (A B : AddSubgroup R.obj.V) : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ H.toSubgroup :=
  ⟨Rep.trivial ℤ H.toSubgroup (B.toIntSubmodule ⧸ primaryRelativeSubmodule K Ks R A B),
    fun _ ↦ by simp⟩

/-- The chosen geometric point of the fixed field, via its given embedding in Omega. -/
noncomputable abbrev primaryFixedFieldPoint (Ω : Type u) [Field Ω] [Algebra Ks Ω]
    [IsAlgClosed Ω] :=
  pointSmallEtale (Spec.map (CommRingCat.ofHom
    ((algebraMap Ks Ω).comp (algebraMap (IntermediateField.fixedField H.toSubgroup) Ks))))

/-- The category equivalence used to associate sheaves to specified H-modules. -/
abbrev PrimaryFixedFieldEquivalence :=
  Sheaf (Spec (.of (IntermediateField.fixedField H.toSubgroup))).smallEtaleTopology
    AddCommGrpCat.{u + 1} ≌ Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ H.toSubgroup

/-- The equivalence has the canonical underlying stalk and action on represented germs. -/
def PrimaryFixedFieldComparison (Ω : Type u) [Field Ω]
    [Algebra Ks Ω] [Algebra K Ω] [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (C : PrimaryFixedFieldEquivalence K Ks H) : Prop :=
  ∃ fiberIso : C.functor ⋙ primaryModuleForget K Ks H ≅
      (primaryFixedFieldPoint K Ks H Ω).sheafFiber (A := AddCommGrpCat.{u + 1}),
    ∀ (F : Sheaf
      (Spec (.of (IntermediateField.fixedField H.toSubgroup))).smallEtaleTopology
      AddCommGrpCat.{u + 1}) (g : H.toSubgroup) (τ : Ω ≃ₐ[K] Ω)
      (_hτ : (algebraMap Ks Ω).comp (g : Gal(Ks/K)).toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω))
      (X : (Spec (.of (IntermediateField.fixedField H.toSubgroup))).Etale)
      (x x' : (primaryFixedFieldPoint K Ks H Ω).fiber.obj X)
      (_hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
      (z : F.obj.obj (op X)),
    (fiberIso.hom.app F) ((C.functor.obj F).obj.ρ g
      ((fiberIso.inv.app F) ((primaryFixedFieldPoint K Ks H Ω).toPresheafFiber X x F.obj z))) =
    (primaryFixedFieldPoint K Ks H Ω).toPresheafFiber X x' F.obj z

/-- The associated sheaf of a specified discrete H-module, transported across e. -/
noncomputable def primaryAssociatedSheaf
    (Ω : Type u) [Field Ω] [Algebra Ks Ω] [Algebra K Ω] [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (C : PrimaryFixedFieldEquivalence K Ks H) (T : Scheme.{u})
    (e : Spec (.of (IntermediateField.fixedField H.toSubgroup)) ≅ T)
    (V : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ H.toSubgroup) :
    Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (Etale.upperStar AddCommGrpCat.{u + 1} e.inv).obj (C.inverse.obj V)

/-- The actual inclusion of the two restricted subrepresentations. -/
noncomputable def primarySubmoduleInclusion
    (R : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)))
    (A B : AddSubgroup R.obj.V) (hle : A ≤ B)
    (hA : ∀ (g : H.toSubgroup) (x : R.obj.V), x ∈ A →
      R.obj.ρ (g : Gal(Ks/K)) x ∈ A)
    (hB : ∀ (g : H.toSubgroup) (x : R.obj.V), x ∈ B →
      R.obj.ρ (g : Gal(Ks/K)) x ∈ B) :
    primarySubmodule K Ks H R A hA ⟶ primarySubmodule K Ks H R B hB :=
  ObjectProperty.homMk (Rep.ofHom
    ⟨Submodule.inclusion (AddSubgroup.toIntSubmodule.monotone hle), fun _ ↦ rfl⟩)

/-- The short complex formed from the specified inclusion and its categorical cokernel. -/
noncomputable def primarySheafSequence
    (Ω : Type u) [Field Ω] [Algebra Ks Ω] [Algebra K Ω] [IsScalarTower K Ks Ω]
    [IsAlgClosed Ω] (C : PrimaryFixedFieldEquivalence K Ks H) (T : Scheme.{u})
    (e : Spec (.of (IntermediateField.fixedField H.toSubgroup)) ≅ T)
    (R : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)))
    (A B : AddSubgroup R.obj.V) (hle : A ≤ B)
    (hA : ∀ (g : H.toSubgroup) (x : R.obj.V), x ∈ A →
      R.obj.ρ (g : Gal(Ks/K)) x ∈ A)
    (hB : ∀ (g : H.toSubgroup) (x : R.obj.V), x ∈ B →
      R.obj.ρ (g : Gal(Ks/K)) x ∈ B) :
    ShortComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) := by
  let f := (Etale.upperStar AddCommGrpCat.{u + 1} e.inv).map
    (C.inverse.map (primarySubmoduleInclusion K Ks H R A B hle hA hB))
  exact ShortComplex.mk f (cokernel.π f) (cokernel.condition f)

/-- A bottom subgroup gives a zero associated sheaf. -/
theorem primaryAssociatedSheaf_zero
    (Ω : Type u) [Field Ω] [Algebra Ks Ω] [Algebra K Ω] [IsScalarTower K Ks Ω]
    [IsAlgClosed Ω] (C : PrimaryFixedFieldEquivalence K Ks H) (T : Scheme.{u})
    (e : Spec (.of (IntermediateField.fixedField H.toSubgroup)) ≅ T)
    (R : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)))
    (B : AddSubgroup R.obj.V) (hzero : B = ⊥)
    (hB : ∀ (g : H.toSubgroup) (x : R.obj.V), x ∈ B →
      R.obj.ρ (g : Gal(Ks/K)) x ∈ B) :
    IsZero (primaryAssociatedSheaf K Ks H Ω C T e (primarySubmodule K Ks H R B hB)) := by
  have hV : IsZero (primarySubmodule K Ks H R B hB).obj := by
    apply (Rep.isZero_iff _).mpr
    change Subsingleton B.toIntSubmodule
    subst B
    rw [map_bot]
    infer_instance
  have hD := IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _)
    (primarySubmodule K Ks H R B hB) hV
  have hS := IsZero.of_full_of_faithful_of_isZero C.functor
    (C.inverse.obj (primarySubmodule K Ks H R B hB))
    (hD.of_iso (C.counitIso.app _))
  exact (Etale.upperStar AddCommGrpCat.{u + 1} e.inv).map_isZero hS

/-- A top subgroup is isomorphic to the actual restricted ambient representation. -/
theorem primarySubmoduleTopIso
    (R : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)))
    (B : AddSubgroup R.obj.V) (htop : B = ⊤)
    (hB : ∀ (g : H.toSubgroup) (x : R.obj.V), x ∈ B →
      R.obj.ρ (g : Gal(Ks/K)) x ∈ B) :
    Nonempty (primarySubmodule K Ks H R B hB ≅ primaryRestrictedModule K Ks H R) := by
  let f := (primaryRestrictedModule K Ks H R).obj.subtype B.toIntSubmodule
    (fun g x hx ↦ hB g x hx)
  have : Mono f := (Rep.mono_iff_injective f).mpr Subtype.val_injective
  have : Epi f := (Rep.epi_iff_surjective f).mpr (by
    intro x
    exact ⟨⟨x, by change x ∈ B; rw [htop]; trivial⟩, rfl⟩)
  have : IsIso f := isIso_of_mono_of_epi f
  exact ⟨ObjectProperty.isoMk _ (asIso f)⟩

private noncomputable def reindexDiscrete
    (A : Type) [Ring A]
    {G J : Type u} [Group G] [Group J] [TopologicalSpace G] [TopologicalSpace J]
    [IsTopologicalGroup G] [IsTopologicalGroup J]
    (e : G →* J) (he : Continuous e) :
    Rep.DiscreteContinuousRep.{0, u, u + 1} A J ⥤
      Rep.DiscreteContinuousRep.{0, u, u + 1} A G where
  obj R := ⟨Rep.of (R.obj.ρ.comp e), fun x ↦ (R.property x).preimage he⟩
  map f := ObjectProperty.homMk (Rep.ofHom
    ⟨f.hom.hom.toLinearMap, fun g ↦ f.hom.hom.2 (e g)⟩)
  map_id _ := rfl
  map_comp _ _ := rfl

private noncomputable def reindexDiscreteEquiv
    (A : Type) [Ring A]
    {G J : Type u} [Group G] [Group J] [TopologicalSpace G] [TopologicalSpace J]
    [IsTopologicalGroup G] [IsTopologicalGroup J]
    (e : G ≃* J) (he : Continuous e) (hi : Continuous e.symm) :
    Rep.DiscreteContinuousRep.{0, u, u + 1} A J ≌
      Rep.DiscreteContinuousRep.{0, u, u + 1} A G where
  functor := reindexDiscrete A e.toMonoidHom he
  inverse := reindexDiscrete A e.symm.toMonoidHom hi
  unitIso := NatIso.ofComponents (fun R ↦ ObjectProperty.isoMk _
    (Rep.mkIso { __ := LinearEquiv.refl A R.obj.V
                 isIntertwining' := fun g ↦ by ext x; simp [reindexDiscrete] }))
    (by intros; ext x; rfl)
  counitIso := NatIso.ofComponents (fun R ↦ ObjectProperty.isoMk _
    (Rep.mkIso { __ := LinearEquiv.refl A R.obj.V
                 isIntertwining' := fun g ↦ by ext x; simp [reindexDiscrete] }))
    (by intros; ext x; rfl)

/-- Source: Stacks Project, Tags 0BML, 03QT, 03QW and 04JQ.
(blueprint: lem-sc-primary-fixed-field-module-comparison)

Proof: The fixed-field correspondence identifies Gal(Ks/L) with H, where L=Ks^H;
openness gives a finite separable extension L/K. Ks is a separable closure of L.
The identification sends an L-automorphism to its underlying K-automorphism, and is a
homeomorphism for the Krull topologies: stabilizers of finite subsets of Ks are the
neighborhood basis on both sides. Apply the abelian sheaf/module equivalence over L
and change the acting group along this homeomorphism. Its natural stalk isomorphism
is unchanged. For g in H any extension tau to Omega fixes L, since every element of
L is fixed by g and embeds in Omega through Ks. Consequently the germ formula over L
is exactly the action formula in this structure. This constructs the comparison.
The stalk and germ action determine its functor on objects and morphisms up to natural
isomorphism; the inverse sheaves are therefore determined up to the isomorphisms used
here, rather than arbitrary witnesses of mere existence. No chain or original sheaf
is assumed or returned. -/
theorem nonempty_primaryFixedFieldComparison
    (K Ks : Type u) [Field K] [Field Ks] [Algebra K Ks]
    (H : OpenSubgroup (Gal(Ks/K))) [IsSepClosure K Ks]
    (Ω : Type u) [Field Ω] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] :
    ∃ C : PrimaryFixedFieldEquivalence K Ks H,
      PrimaryFixedFieldComparison K Ks H Ω C := by
  let L := IntermediateField.fixedField H.toSubgroup
  obtain ⟨hfinite, _, hfix, _⟩ :=
    (openSubgroup_fixedField_finite_separable.{u, u, u} K Ks).1 H.toSubgroup H.isOpen
  have : FiniteDimensional K L := hfinite
  have : IsScalarTower L Ks Ω := inferInstance
  have : IsSepClosure L Ks :=
    ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K L Ks⟩
  let e : H.toSubgroup ≃* Gal(Ks/L) :=
    (MulEquiv.subgroupCongr hfix.symm).trans L.fixingSubgroupEquiv
  have hc : Continuous L.fixingSubgroupEquiv ∧ Continuous L.fixingSubgroupEquiv.symm :=
    ⟨L.fixingSubgroupContinuousMulEquiv.continuous,
      L.fixingSubgroupContinuousMulEquiv.symm.continuous⟩
  have he : Continuous e := by
    exact hc.1.comp (continuous_subtype_val.subtype_mk _)
  have hi : Continuous e.symm := by
    exact (continuous_subtype_val.comp hc.2).subtype_mk _
  have : IsSepClosed Ks := IsSepClosure.sep_closed K
  have : Algebra.IsSeparable L Ks := Algebra.isSeparable_tower_top_of_isSeparable K L Ks
  let E := etaleSheafEquivDiscreteContinuousRep L Ks
  let i := etaleSheafEquivDiscreteContinuousRepForgetIso L Ks Ω
  let D := reindexDiscreteEquiv ℤ e he hi
  let C : PrimaryFixedFieldEquivalence K Ks H := E.trans D
  let i' : C.functor ⋙ primaryModuleForget K Ks H ≅
      (primaryFixedFieldPoint K Ks H Ω).sheafFiber (A := AddCommGrpCat.{u + 1}) := i
  refine ⟨C, i', ?_⟩
  intro F g τ hτ X x x' hx z
  have hg (a : L) : (g : Gal(Ks/K)) (a : Ks) = a := a.property g
  let τL : Ω ≃ₐ[L] Ω :=
    { τ.toRingEquiv with
      commutes' := fun a ↦ by
        have h := DFunLike.congr_fun hτ (a : Ks)
        change τ ((algebraMap Ks Ω) (a : Ks)) = (algebraMap Ks Ω) (a : Ks)
        change (algebraMap Ks Ω) ((g : Gal(Ks/K)) (a : Ks)) =
          τ ((algebraMap Ks Ω) (a : Ks)) at h
        rw [hg] at h
        exact h.symm }
  have hτL : (algebraMap Ks Ω).comp (e g).toRingHom =
      τL.toRingHom.comp (algebraMap Ks Ω) := by
    ext a
    exact DFunLike.congr_fun hτ a
  exact etaleSheafEquivDiscreteContinuousRepForgetIso_ρ L Ks Ω F (e g) τL hτL X x x' hx z

end AlgebraicGeometry.Scheme
