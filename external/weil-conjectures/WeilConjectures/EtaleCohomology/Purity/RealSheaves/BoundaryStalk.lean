/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.InertiaNeighbourhood
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.StalkTransport
public import WeilConjectures.ConstructibleSheaf.DenseOpenUnit
public import WeilConjectures.ConstructibleSheaf.LowerStarSpecialization
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryInertia

/-!
# Boundary stalks of direct images as inertia invariants

Let `j : U ⟶ C` be an open immersion into an integral scheme, `W` an affine open with Dedekind
ring of sections `R = Γ(C, W)` and `W ∩ U = D(ϖ)`, `Ω` a separable closure of the function field
`K = k(C)` and `Q` a maximal ideal of the integral closure `B` of `R` in `Ω` over a maximal
ideal `m` of `R` (the boundary point). The local ring `A = B_Q` is strictly henselian with
fraction field `Ω`; its closed geometric point `x̄ : Spec κ(A) ⟶ Spec A ⟶ C` is a geometric point
over the boundary point and `η : Spec Ω ⟶ Spec A` lies over the generic geometric point of `U`.
The inertia group `I = {σ ∈ Gal(Ω / K) | σ ≡ id mod Q}` acts on the geometric generic stalk `F_η`
of a sheaf `F` on `U`.

For `F` finite locally constant (blueprint `lemma-boundary-stalk--1`, at a finite
coefficient level), the specialization map
`(j_* F)_x̄ ⟶ F_η` (`AlgebraicGeometry.Etale.boundarySpecialization`) is injective with image the
inertia invariants `F_η^I`, and it intertwines the action of an element `σ` of the decomposition
group (the stabiliser of `Q`) on `F_η` with the action on `(j_* F)_x̄` of the automorphism of the
geometric point `x̄` induced by the residue automorphism of `σ`
(`AlgebraicGeometry.Etale.boundaryStalkMap_comp_boundarySpecialization`). In particular
`(j_* F)_x̄ ≅ F_η^I` (`AlgebraicGeometry.Etale.boundaryStalkLinearEquiv`).

* Injectivity is `AlgebraicGeometry.Etale.injective_specializationStalk`.
* The image consists of invariants since an inertia element induces an automorphism of `A` over
  `C` acting trivially on the residue field.
* Conversely, an invariant `m ∈ F_η` is a point over `η` of the finite étale `U`-scheme `P`
  representing `F`, fixed by inertia; it extends to an étale neighbourhood `V` of `x̄`
  together with a `U`-morphism `V ×_C U ⟶ P`
  (`AlgebraicGeometry.Scheme.FiniteEtale.exists_etale_lift_of_forall_inertia`), that is a section
  of `j_* F` over `V` specializing to `m`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme Scheme.FiniteEtale

namespace Etale

variable {C U : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j] [IsIntegral C]
  [Nonempty U] {W : C.Opens} [Fact (IsAffineOpen W)] [Nonempty W]
  {Ω : Type u} [Field Ω] [Algebra C.functionField Ω] [Algebra Γ(C, W) Ω]
  [IsScalarTower Γ(C, W) C.functionField Ω] [IsGalois C.functionField Ω] [IsSepClosed Ω]
  (Q : Ideal (integralClosure Γ(C, W) Ω)) [Q.IsMaximal] {Λ : Type (u + 1)} [Ring Λ]

/-- The geometric point `x̄ : Spec κ(B_Q) ⟶ Spec B_Q ⟶ C` over the boundary point. -/
noncomputable abbrev boundaryGeometricPoint :
    Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime Q))) ⟶ C :=
  closedGeometricPoint (Localization.AtPrime Q) ≫ specAtPrime Fact.out Q

omit [IsGalois C.functionField Ω] [IsSepClosed Ω] in
lemma specMap_comp_genericGeometricPoint (σ : Ω ≃ₐ[C.functionField] Ω) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ genericGeometricPoint (Ω := Ω) j =
      genericGeometricPoint j := by
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext a
  exact σ.commutes a

variable {j} in
/-- The action of `σ ∈ Gal(Ω / k(C))` on the geometric generic stalk `F_η`. -/
noncomputable def galoisStalkMap (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (σ : Ω ≃ₐ[C.functionField] Ω) :
    (pointSmallEtale (genericGeometricPoint (Ω := Ω) j)).sheafFiber.obj F ⟶
      (pointSmallEtale (genericGeometricPoint (Ω := Ω) j)).sheafFiber.obj F :=
  (pointSmallEtaleHom (genericGeometricPoint j) (σ : Ω →+* Ω)
    (specMap_comp_genericGeometricPoint j σ)).sheafFiber.app F

/-- Blueprint `lemma-boundary-stalk--1` (the comparison map): the specialization map
`(j_* F)_x̄ ⟶ F_η` from the stalk of the direct image at the geometric point over the boundary
point to the geometric generic stalk, sending the germ of a section of `F` over `V ×_C U`, for an
étale neighbourhood `V` of `x̄`, to its germ at the lift of `η` through `Spec B_Q ⟶ V`. -/
noncomputable def boundarySpecialization (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (pointSmallEtale (boundaryGeometricPoint Q)).sheafFiber.obj
        ((j)_*[ModuleCat.{u + 1} Λ].obj F) ⟶
      (pointSmallEtale (genericGeometricPoint (Ω := Ω) j)).sheafFiber.obj F :=
  specializationStalk j (specAtPrime Fact.out Q) (CommRingCat.ofHom (Ideal.atPrimeToField Q)) _
    (pointOfAlgebra_comp_eq_specAtPrime j Fact.out Q) F

/-- Blueprint `lemma-boundary-stalk--1` (injectivity): for `F` locally constant and `C`
locally noetherian with étale local rings that are domains (e.g. regular), the specialization
map of the boundary stalk is injective. -/
theorem injective_boundarySpecialization
    (hC : ∀ (V : C.Etale) (v : V.left), IsDomain (V.left.presheaf.stalk v))
    [IsLocallyNoetherian C] (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsLocallyConstantSheaf F] :
    Function.Injective (boundarySpecialization j Q F) :=
  injective_specializationStalk j _ _ _ _ hC F

section Decomposition

open scoped Pointwise

variable {σ : Ω ≃ₐ[C.functionField] Ω}
  (hσ : σ ∈ MulAction.stabilizer (Ω ≃ₐ[C.functionField] Ω) Q)

omit [IsGalois C.functionField Ω] [IsSepClosed Ω] in
lemma specMap_atPrimeMap_comp_specAtPrime :
    Spec.map (CommRingCat.ofHom (Ideal.atPrimeMap Q σ hσ)) ≫ specAtPrime Fact.out Q =
      specAtPrime Fact.out Q := by
  rw [specAtPrime, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext r
  exact Ideal.atPrimeMap_algebraMap_base Q σ hσ r

/-- The automorphism of the residue field `κ(B_Q)` induced by an element `σ` of the decomposition
group. -/
noncomputable abbrev residueAut : IsLocalRing.ResidueField (Localization.AtPrime Q) →+*
    IsLocalRing.ResidueField (Localization.AtPrime Q) :=
  IsLocalRing.ResidueField.map (Ideal.atPrimeMap Q σ hσ)

omit [Fact (IsAffineOpen W)] [IsGalois C.functionField Ω] [IsSepClosed Ω] in
lemma closedGeometricPoint_comp_specMap_atPrimeMap :
    closedGeometricPoint (Localization.AtPrime Q) ≫
        Spec.map (CommRingCat.ofHom (Ideal.atPrimeMap Q σ hσ)) =
      Spec.map (CommRingCat.ofHom (residueAut Q hσ)) ≫
        closedGeometricPoint (Localization.AtPrime Q) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

lemma specMap_residueAut_comp_boundaryGeometricPoint :
    Spec.map (CommRingCat.ofHom (residueAut Q hσ)) ≫ boundaryGeometricPoint Q =
      boundaryGeometricPoint Q :=
  comp_closedGeometricPoint_comp_eq _ _ (specMap_atPrimeMap_comp_specAtPrime Q hσ) _
    (closedGeometricPoint_comp_specMap_atPrimeMap Q hσ)

omit [Fact (IsAffineOpen W)] [IsGalois C.functionField Ω] [IsSepClosed Ω] in
lemma atPrimeToField_comp_eq :
    CommRingCat.ofHom (Ideal.atPrimeToField Q) ≫ CommRingCat.ofHom (σ : Ω →+* Ω) =
      CommRingCat.ofHom (Ideal.atPrimeMap Q σ hσ) ≫ CommRingCat.ofHom (Ideal.atPrimeToField Q) := by
  ext x
  exact (Ideal.atPrimeToField_atPrimeMap Q σ hσ x).symm

variable {j} in
/-- The action of an element `σ` of the decomposition group on the boundary stalk `(j_* F)_x̄`,
through the automorphism of the geometric point `x̄` given by the residue automorphism of `σ`. -/
noncomputable def boundaryStalkMap (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (pointSmallEtale (boundaryGeometricPoint Q)).sheafFiber.obj
        ((j)_*[ModuleCat.{u + 1} Λ].obj F) ⟶
      (pointSmallEtale (boundaryGeometricPoint Q)).sheafFiber.obj
        ((j)_*[ModuleCat.{u + 1} Λ].obj F) :=
  (pointSmallEtaleHom _ (residueAut Q hσ)
    (specMap_residueAut_comp_boundaryGeometricPoint Q hσ)).sheafFiber.app _

/-- Blueprint `lemma-boundary-stalk--1` (Frobenius equivariance): the specialization
map intertwines the action of an element `σ` of the decomposition group on `F_η` with the action
on `(j_* F)_x̄` of its residue automorphism. For a lift of the geometric Frobenius of `κ(x)` this is
the compatibility of the geometric Frobenius on the boundary stalk with the residue Frobenius
lift on the inertia invariants. -/
theorem boundaryStalkMap_comp_boundarySpecialization
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    boundaryStalkMap Q hσ F ≫ boundarySpecialization j Q F =
      boundarySpecialization j Q F ≫ galoisStalkMap F σ :=
  stalkHom_comp_specializationStalk j (specAtPrime Fact.out Q)
    (CommRingCat.ofHom (Ideal.atPrimeToField Q)) (genericGeometricPoint j)
    (pointOfAlgebra_comp_eq_specAtPrime j Fact.out Q) (Ideal.atPrimeMap Q σ hσ)
    (specMap_atPrimeMap_comp_specAtPrime Q hσ) (residueAut Q hσ)
    (closedGeometricPoint_comp_specMap_atPrimeMap Q hσ) σ (atPrimeToField_comp_eq Q hσ)
    (specMap_comp_genericGeometricPoint j σ) F

omit [Fact (IsAffineOpen W)] [IsGalois C.functionField Ω] [IsSepClosed Ω] in
lemma residueAut_apply_of_mem_inertia (hσ' : σ ∈ Q.inertia (Ω ≃ₐ[C.functionField] Ω))
    (x : IsLocalRing.ResidueField (Localization.AtPrime Q)) :
    residueAut Q (Ideal.inertia_le_stabilizer Q hσ') x = x := by
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  rw [IsLocalRing.ResidueField.map_residue]
  exact Ideal.residue_atPrimeMap_of_mem_inertia Q hσ' y

omit [IsOpenImmersion j] [Nonempty U] in
/-- Inertia acts trivially on the boundary stalk. -/
lemma boundaryStalkMap_eq_id_of_mem_inertia (hσ' : σ ∈ Q.inertia (Ω ≃ₐ[C.functionField] Ω))
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    boundaryStalkMap (j := j) Q (Ideal.inertia_le_stabilizer Q hσ') F = 𝟙 _ :=
  pointSmallEtaleHom_sheafFiber_app_eq_id _ _ (residueAut_apply_of_mem_inertia Q hσ') _ _

/-- Blueprint `lemma-boundary-stalk--1` (the image consists of invariants): the image of
the specialization map is fixed by the inertia group. -/
theorem galoisStalkMap_boundarySpecialization (hσ' : σ ∈ Q.inertia (Ω ≃ₐ[C.functionField] Ω))
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (x : ToType ((pointSmallEtale (boundaryGeometricPoint Q)).sheafFiber.obj
        ((j)_*[ModuleCat.{u + 1} Λ].obj F))) :
    galoisStalkMap F σ (boundarySpecialization j Q F x) = boundarySpecialization j Q F x := by
  have h := boundaryStalkMap_comp_boundarySpecialization j Q (Ideal.inertia_le_stabilizer Q hσ') F
  rw [boundaryStalkMap_eq_id_of_mem_inertia j Q hσ', Category.id_comp] at h
  exact (ConcreteCategory.congr_hom h x).symm

end Decomposition

section Surjective

variable [QuasiCompact j] [IsDedekindDomain Γ(C, W)] (ϖ : Γ(C, W)) (hϖ : ϖ ≠ 0)
  (hWU : j.opensRange ⊓ W = C.basicOpen ϖ) (m : Ideal Γ(C, W)) [m.IsMaximal]
  [PerfectField m.ResidueField] [Q.LiesOver m]

include hϖ hWU m in
/-- Blueprint `lemma-boundary-stalk--1` (the inertia invariants lie in the image): for `F`
finite locally constant, every inertia invariant of the geometric generic stalk `F_η` comes from
the boundary stalk `(j_* F)_x̄`. -/
theorem exists_boundarySpecialization_eq {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    [ConnectedSpace U]
    (hint : ∀ Y : U.FiniteEtale, PreGaloisCategory.IsConnected Y → IsIntegral Y.obj.left)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf F]
    (x : ToType ((pointSmallEtale (genericGeometricPoint (Ω := Ω) j)).sheafFiber.obj F))
    (hx : ∀ σ ∈ Q.inertia (Ω ≃ₐ[C.functionField] Ω), galoisStalkMap F σ x = x) :
    ∃ y, boundarySpecialization j Q F y = x := by
  have hF : IsFiniteLocallyConstantSheaf F := inferInstance
  let F' := hF.toFLC
  let P := (equivalenceFiniteLocallyConstant U).inverse.obj F'
  let i := (equivalenceFiniteLocallyConstant U).counitIso.app F'
  let η := genericGeometricPoint (Ω := Ω) j
  -- `x` as a germ, and the corresponding point `t` of `P` over `η`
  obtain ⟨V₀, v₀, z₀, hz₀⟩ := (pointSmallEtale η).toPresheafFiber_jointly_surjective
    (P := F'.obj.obj) (hF.stalkEquiv η x)
  have hx₀ : (pointSmallEtale η).toPresheafFiber V₀ v₀ F.obj z₀ = x := by
    apply (hF.stalkEquiv η).injective
    rw [IsFiniteLocallyConstantSheaf.stalkEquiv_toPresheafFiber]
    exact hz₀
  let f₀ := (i.inv.hom.hom.app (op V₀) z₀).down
  let t : (fiber η).obj P := (pointSmallEtale η).fiber.map f₀ v₀
  have hgerm (V : U.Etale) (v : (pointSmallEtale η).fiber.obj V)
      (z : ToType (F'.obj.obj.obj (op V))) :
      FiniteLocallyConstant.stalkEquiv η F'
        (hF.stalkEquiv η ((pointSmallEtale η).toPresheafFiber V v F.obj z)) =
        ULift.up ((pointSmallEtale η).fiber.map (i.inv.hom.hom.app (op V) z).down v) := by
    rw [IsFiniteLocallyConstantSheaf.stalkEquiv_toPresheafFiber,
      FiniteLocallyConstant.stalkEquiv_toPresheafFiber]
    rfl
  have ht : ∀ σ ∈ Q.inertia (Ω ≃ₐ[C.functionField] Ω),
      (galoisToAut (genericPointLift j) σ).asIso.hom.app P t = t := by
    intro σ hσ
    have h := hx σ hσ
    rw [← hx₀, galoisStalkMap] at h
    have h' := ConcreteCategory.congr_hom (toPresheafFiber_pointSmallEtaleHom_sheafFiber_app η
      (σ : Ω →+* Ω) (specMap_comp_genericGeometricPoint j σ) F V₀ v₀) z₀
    rw [ConcreteCategory.comp_apply] at h'
    replace h := h'.symm.trans h
    have h'' : (pointSmallEtale η).fiber.map f₀ ((pointSmallEtaleHom η (σ : Ω →+* Ω)
        (specMap_comp_genericGeometricPoint j σ)).hom.app V₀ v₀) =
          (pointSmallEtale η).fiber.map f₀ v₀ := by
      apply ULift.up_injective
      rw [← hgerm, ← hgerm]
      exact congrArg (fun y ↦ FiniteLocallyConstant.stalkEquiv η F' (hF.stalkEquiv η y)) h
    refine fiber_ext _ ?_
    rw [galoisToAut_hom_app_left]
    exact (Category.assoc _ _ _).symm.trans (congrArg Over.Hom.left h'')
  -- the étale neighbourhood and the section over its punctured part
  obtain ⟨V, ℓ, hℓ, g, hg, hgt⟩ :=
    exists_etale_lift_of_forall_inertia j Fact.out ϖ hϖ hWU m Q hint P t ht
  let gU : (MorphismProperty.Over.pullback @Etale ⊤ j).obj V ⟶ P.obj :=
    MorphismProperty.Over.homMk g hg
  let z : ToType (F'.obj.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ j).obj V))) :=
    i.hom.hom.hom.app _ (ULift.up gU)
  let v : (pointSmallEtale (boundaryGeometricPoint Q)).fiber.obj V :=
    Over.homMk (closedGeometricPoint _ ≫ ℓ) (by
      change (closedGeometricPoint _ ≫ ℓ) ≫ V.hom = _
      rw [Category.assoc, hℓ]
      rfl)
  refine ⟨(pointSmallEtale _).toPresheafFiber V v
    ((sheafToPresheaf _ _).obj ((j)_*[ModuleCat.{u + 1} Λ].obj F)) z, ?_⟩
  rw [boundarySpecialization, specializationStalk_toPresheafFiber, ← hx₀]
  apply (hF.stalkEquiv η).injective
  apply (FiniteLocallyConstant.stalkEquiv η F').injective
  rw [hgerm]
  refine (hgerm _ _ z).trans ?_
  congr 1
  -- the specialized point maps to `t`
  have hz : (i.inv.hom.hom.app _ z).down = gU := by
    change (i.inv.hom.hom.app _ (i.hom.hom.hom.app _ (ULift.up gU))).down = gU
    exact congrArg (fun φ : (toFiniteLocallyConstant U).obj P ⟶ (toFiniteLocallyConstant U).obj P ↦
      (φ.hom.hom.app (op ((MorphismProperty.Over.pullback
      @Etale ⊤ j).obj V)) (ULift.up gU)).down) i.hom_inv_id
  rw [hz]
  refine Over.OverMorphism.ext ?_
  change _ ≫ g = t.left
  rw [← hgt]
  congr 1
  refine pullback.hom_ext ?_ ?_
  · rw [specializationFiber_left_fst, pullback.lift_fst]
    congr 1
    exact henselianLift_eq _ _ _ _ _ hℓ rfl
  · rw [specializationFiber_left_snd, pullback.lift_snd]


section Invariants

variable {Λ : Type (u + 1)} [CommRing Λ] (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))

omit [IsSepClosed Ω] [Nonempty W] [Fact (IsAffineOpen W)] [IsOpenImmersion j] in
/-- The inertia invariants `F_η^I` of the geometric generic stalk. -/
def inertiaInvariants :
    Submodule Λ ((pointSmallEtale (genericGeometricPoint (Ω := Ω) j)).sheafFiber.obj F :
      ModuleCat.{u + 1} Λ) where
  carrier := {x | ∀ σ ∈ Q.inertia (Ω ≃ₐ[C.functionField] Ω), galoisStalkMap F σ x = x}
  add_mem' {a b} ha hb σ hσ := by rw [map_add, ha σ hσ, hb σ hσ]
  zero_mem' σ _ := map_zero _
  smul_mem' c x hx σ hσ := by rw [map_smul, hx σ hσ]

include hϖ hWU m in
/-- Blueprint `lemma-boundary-stalk--1`: the image of the specialization map is the
module of inertia invariants of the geometric generic stalk. -/
theorem range_boundarySpecialization [Finite Λ] [ConnectedSpace U]
    (hint : ∀ Y : U.FiniteEtale, PreGaloisCategory.IsConnected Y → IsIntegral Y.obj.left)
    [IsFiniteLocallyConstantSheaf F] :
    Set.range (boundarySpecialization j Q F) = inertiaInvariants j Q F := by
  ext x
  refine ⟨?_, fun hx ↦ exists_boundarySpecialization_eq j Q ϖ hϖ hWU m hint F x hx⟩
  rintro ⟨y, rfl⟩ σ hσ
  exact galoisStalkMap_boundarySpecialization j Q hσ F y

include hϖ hWU m in
/-- Blueprint `lemma-boundary-stalk--1` (finite coefficient level): for a finite locally
constant sheaf `F` of modules over a finite ring, the boundary stalk `(j_* F)_x̄` is isomorphic,
through the specialization map, to the inertia invariants `F_η^I` of the geometric generic
stalk. -/
noncomputable def boundaryStalkLinearEquiv [Finite Λ] [ConnectedSpace U]
    (hint : ∀ Y : U.FiniteEtale, PreGaloisCategory.IsConnected Y → IsIntegral Y.obj.left)
    (hC : ∀ (V : C.Etale) (v : V.left), IsDomain (V.left.presheaf.stalk v))
    [IsLocallyNoetherian C] [IsFiniteLocallyConstantSheaf F] :
    ((pointSmallEtale (boundaryGeometricPoint Q)).sheafFiber.obj
        ((j)_*[ModuleCat.{u + 1} Λ].obj F) : ModuleCat.{u + 1} Λ) ≃ₗ[Λ] inertiaInvariants j Q F :=
  LinearEquiv.ofBijective ((boundarySpecialization j Q F).hom.codRestrict (inertiaInvariants j Q F)
      fun y σ hσ ↦ galoisStalkMap_boundarySpecialization j Q hσ F y)
    ⟨fun y₁ y₂ h ↦ injective_boundarySpecialization j Q hC F (congrArg Subtype.val h),
      fun x ↦ by
        obtain ⟨y, hy⟩ := exists_boundarySpecialization_eq j Q ϖ hϖ hWU m hint F x.1 x.2
        exact ⟨y, Subtype.ext hy⟩⟩

lemma coe_boundaryStalkLinearEquiv_apply [Finite Λ] [ConnectedSpace U]
    (hint : ∀ Y : U.FiniteEtale, PreGaloisCategory.IsConnected Y → IsIntegral Y.obj.left)
    (hC : ∀ (V : C.Etale) (v : V.left), IsDomain (V.left.presheaf.stalk v))
    [IsLocallyNoetherian C] [IsFiniteLocallyConstantSheaf F]
    (y : ((pointSmallEtale (boundaryGeometricPoint Q)).sheafFiber.obj
        ((j)_*[ModuleCat.{u + 1} Λ].obj F) : ModuleCat.{u + 1} Λ)) :
    (boundaryStalkLinearEquiv j Q ϖ hϖ hWU m F hint hC y : _) =
      boundarySpecialization j Q F y :=
  rfl

end Invariants

end Surjective

section Transport

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [ConnectedSpace U]
  {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] {s : Spec (.of Ω') ⟶ U}
  (τ : FiniteEtale.fiber (genericGeometricPoint (Ω := Ω) j) ≅ FiniteEtale.fiber s)
  (G : Type u) [Group G] [∀ P, MulAction G ((FiniteEtale.fiber s).obj P)] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]
  [PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber s) G]

omit [IsGalois C.functionField Ω] in
/-- Transported along a path `τ` from the generic geometric point `η` to a base point `s`
(`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.transport`), the action of
`σ ∈ Gal(Ω / k(C))` on the stalk `F_η` becomes the action of its image in `π₁(U, s)` on the stalk
`F_s` (`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.galoisAct`). -/
theorem transport_galoisStalkMap (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsFiniteLocallyConstantSheaf F) (σ : Ω ≃ₐ[C.functionField] Ω)
    (x : ((pointSmallEtale (genericGeometricPoint (Ω := Ω) j)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj F) :
    hF.transport _ s τ (galoisStalkMap F σ x) =
      hF.galoisAct s G (galoisToFundamentalGroup (genericPointLift j) τ G σ)
        (hF.transport _ s τ x) := by
  let η := genericGeometricPoint (Ω := Ω) j
  let c := (equivalenceFiniteLocallyConstant U).counitIso.inv.app hF.toFLC
  obtain ⟨V, v, z, hz⟩ := (pointSmallEtale η).toPresheafFiber_jointly_surjective
    (P := hF.toFLC.obj.obj) (hF.stalkEquiv η x)
  have hx : (pointSmallEtale η).toPresheafFiber V v F.obj z = x := by
    apply (hF.stalkEquiv η).injective
    rw [IsFiniteLocallyConstantSheaf.stalkEquiv_toPresheafFiber]
    exact hz
  have hgerm (w : (pointSmallEtale η).fiber.obj V) :
      FiniteLocallyConstant.stalkEquiv η hF.toFLC
        (hF.stalkEquiv η ((pointSmallEtale η).toPresheafFiber V w F.obj z)) =
        ULift.up ((pointSmallEtale η).fiber.map (c.hom.hom.app (op V) z).down w) := by
    rw [IsFiniteLocallyConstantSheaf.stalkEquiv_toPresheafFiber,
      FiniteLocallyConstant.stalkEquiv_toPresheafFiber]
  have hσ : galoisStalkMap F σ x = (pointSmallEtale η).toPresheafFiber V
      ((pointSmallEtaleHom η (σ : Ω →+* Ω) (specMap_comp_genericGeometricPoint j σ)).hom.app V v)
        F.obj z := by
    rw [← hx]
    exact ConcreteCategory.congr_hom (toPresheafFiber_pointSmallEtaleHom_sheafFiber_app η
      (σ : Ω →+* Ω) (specMap_comp_genericGeometricPoint j σ) F V v) z
  apply (hF.stalkEquiv s).injective
  apply (FiniteLocallyConstant.stalkEquiv s hF.toFLC).injective
  have e₁ := hF.stalkEquiv_transport _ s τ (galoisStalkMap F σ x)
  have e₂ := hF.stalkEquiv_transport _ s τ x
  simp only [IsFiniteLocallyConstantSheaf.galoisAct, Equiv.apply_symm_apply,
    FiniteLocallyConstant.galoisSMul]
  erw [e₁, e₂]
  rw [FiniteLocallyConstant.stalkEquiv_transport, FiniteLocallyConstant.stalkEquiv_transport, hσ,
    hgerm, ← hx, hgerm]
  refine congrArg ULift.up ((congrArg (τ.hom.app _) ?_).trans
    (galoisToFundamentalGroup_smul (genericPointLift j) τ G σ _ _).symm)
  exact fiber_ext _ (Category.assoc _ _ _)

end Transport

end Etale

namespace WeilGroup.BoundaryChart

open Etale

open scoped Pointwise

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  [Smooth p] [IsIntegral C] {pU : U ⟶ Spec (.of K)} [IsCurve pU] [ConnectedSpace U]
  {j : U ⟶ C} [IsOpenImmersion j] [Nonempty U] {z : C} (c : BoundaryChart p j z)

local notation "Ω" => SeparableClosure (Scheme.functionField C)

instance : Fact (IsAffineOpen c.W) := ⟨c.isAffineOpen⟩

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
  (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf F]

-- instance search through `SeparableClosure` and its integral closures is slow
/-- Blueprint `lemma-boundary-stalk--1` (finite coefficient level): for a dense open
`j : U₀ ⟶ C₀` of a smooth curve over a finite field, a boundary point `z` with an affine chart
`c`, and a finite locally constant sheaf `F` of modules over a finite ring on `U₀`, the stalk of
the middle extension `j_* F` at the geometric point `x̄` over `z` given by the point `Q` of `c`
(the closed point of `Spec B_Q`) is the module of invariants under the inertia group
`I_Q ⊆ Gal(Ω / k(C))` of the geometric generic stalk `F_η`, through the specialization map. -/
noncomputable def boundaryStalkEquiv (hz : z ∉ Set.range j.base) :
    ((pointSmallEtale (boundaryGeometricPoint c.point)).sheafFiber.obj
        ((j)_*[ModuleCat.{u + 1} Λ].obj F) : ModuleCat.{u + 1} Λ) ≃ₗ[Λ]
      inertiaInvariants j c.point F :=
  have := c.isMaximal_ideal
  have : Finite (C.residueField z) := boundary_subset_finitePoints (p := p) j hz
  have := c.finite_quotient
  have := isDedekindDomain_of_isAffineOpen p c.isAffineOpen
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have := IsRegular.of_smooth p
  boundaryStalkLinearEquiv j c.point c.ϖ (c.ϖ_ne_zero hz) (c.opensRange_inf hz) c.ideal F
    (fun Y _ ↦
      have : ConnectedSpace Y.obj.left := connectedSpace_of_isConnected Y
      have : Etale Y.obj.hom := Y.obj.prop
      let q : Y.obj.left ⟶ Spec (.of K) := Y.obj.hom ≫ j ≫ p
      have : Smooth q := inferInstance
      have := LocallyOfFiniteType.isLocallyNoetherian q
      have := IsRegular.of_smooth q
      IsRegular.isIntegral _)
    (isDomain_stalk_left_of_isRegular)

lemma boundaryStalkEquiv_apply (hz : z ∉ Set.range j.base)
    (y : ((pointSmallEtale (boundaryGeometricPoint c.point)).sheafFiber.obj
        ((j)_*[ModuleCat.{u + 1} Λ].obj F) : ModuleCat.{u + 1} Λ)) :
    (c.boundaryStalkEquiv F hz y).1 = boundarySpecialization j c.point F y :=
  rfl

set_option synthInstance.maxHeartbeats 200000 in
-- instance search through `SeparableClosure` and its integral closures is slow
/-- Blueprint `lemma-boundary-stalk--1` (Frobenius equivariance): for `σ` in the
decomposition group of `Q`, the identification `(j_* F)_x̄ ≃ F_η^I` intertwines the action of `σ`
on `F_η^I` with the action on `(j_* F)_x̄` of the automorphism of the geometric point `x̄`
induced by the residue automorphism of `σ`. For `σ` a residue Frobenius lift, this is the
action of the geometric Frobenius of `κ(z)` on the boundary stalk. -/
theorem boundaryStalkEquiv_boundaryStalkMap (hz : z ∉ Set.range j.base) {σ : Gal(Ω/C.functionField)}
    (hσ : σ ∈ MulAction.stabilizer Gal(Ω/C.functionField) c.point)
    (y : ((pointSmallEtale (boundaryGeometricPoint c.point)).sheafFiber.obj
        ((j)_*[ModuleCat.{u + 1} Λ].obj F) : ModuleCat.{u + 1} Λ)) :
    (c.boundaryStalkEquiv F hz (boundaryStalkMap c.point hσ F y)).1 =
      galoisStalkMap F σ (c.boundaryStalkEquiv F hz y).1 :=
  ConcreteCategory.congr_hom (boundaryStalkMap_comp_boundarySpecialization j c.point hσ F) y

section Representation

variable (sU : Spec (.of (AlgebraicClosure K)) ⟶ U)
  (GU : Type u) [Group GU] [TopologicalSpace GU] [IsTopologicalGroup GU] [CompactSpace GU]
  [∀ P, MulAction GU ((FiniteEtale.fiber sU).obj P)]
  [PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber sU) GU]

omit [Finite K] in
lemma map_inertiaInvariants_transport :
    (inertiaInvariants j c.point F).map (IsFiniteLocallyConstantSheaf.transportLinearEquiv
      _ sU (genericPath j sU) ‹IsFiniteLocallyConstantSheaf F›).toLinearMap =
      Representation.invariants ((IsFiniteLocallyConstantSheaf.galoisRep sU GU
        ‹IsFiniteLocallyConstantSheaf F›).comp (inertiaGroup sU GU c c.point).subtype) := by
  let T := IsFiniteLocallyConstantSheaf.transportLinearEquiv
    _ sU (genericPath j sU) ‹IsFiniteLocallyConstantSheaf F›
  have hT (σ : Gal(Ω/C.functionField)) (x) : T (galoisStalkMap F σ x) =
      IsFiniteLocallyConstantSheaf.galoisAct sU GU (genericGaloisMap j sU GU σ)
        ‹IsFiniteLocallyConstantSheaf F› (T x) :=
    transport_galoisStalkMap j (genericPath j sU) GU F ‹IsFiniteLocallyConstantSheaf F› σ x
  ext y
  simp only [Submodule.mem_map, LinearEquiv.coe_coe, Representation.mem_invariants]
  constructor
  · rintro ⟨x, hx, rfl⟩ ⟨_, σ, hσ, rfl⟩
    exact (hT σ x).symm.trans (congrArg T (hx σ hσ))
  · intro hy
    refine ⟨T.symm y, fun σ hσ ↦ T.injective ?_, T.apply_symm_apply y⟩
    rw [hT, T.apply_symm_apply]
    exact hy ⟨_, σ, hσ, rfl⟩

/-- Blueprint `lemma-boundary-stalk--1` (finite coefficient level, representation form):
the boundary stalk `(j_* F)_x̄` is isomorphic to the invariants, in the stalk `F_{s_U}` with its
action of `π₁(U₀, s_U)` (`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.galoisRep`), of
the image of the inertia group at the point `Q` of the chart. -/
noncomputable def boundaryStalkEquivInvariants (hz : z ∉ Set.range j.base) :
    ((pointSmallEtale (boundaryGeometricPoint c.point)).sheafFiber.obj
        ((j)_*[ModuleCat.{u + 1} Λ].obj F) : ModuleCat.{u + 1} Λ) ≃ₗ[Λ]
      Representation.invariants ((IsFiniteLocallyConstantSheaf.galoisRep sU GU
        ‹IsFiniteLocallyConstantSheaf F›).comp (inertiaGroup sU GU c c.point).subtype) :=
  (c.boundaryStalkEquiv F hz).trans (LinearEquiv.ofSubmodules _ _ _
    (c.map_inertiaInvariants_transport F sU GU))

set_option synthInstance.maxHeartbeats 200000 in
-- instance search through `SeparableClosure` and its integral closures is slow
/-- Blueprint `lemma-boundary-stalk--1` (Frobenius equivariance, representation form):
for `σ` in the decomposition group of `Q`, the identification of the boundary stalk with the
inertia invariants in `F_{s_U}` intertwines the action of the residue automorphism of `σ` on
`(j_* F)_x̄` with the action of the image of `σ` in `π₁(U₀, s_U)`. -/
theorem boundaryStalkEquivInvariants_boundaryStalkMap (hz : z ∉ Set.range j.base)
    {σ : Gal(Ω/C.functionField)}
    (hσ : σ ∈ MulAction.stabilizer Gal(Ω/C.functionField) c.point)
    (y : ((pointSmallEtale (boundaryGeometricPoint c.point)).sheafFiber.obj
        ((j)_*[ModuleCat.{u + 1} Λ].obj F) : ModuleCat.{u + 1} Λ)) :
    (c.boundaryStalkEquivInvariants F sU GU hz (boundaryStalkMap c.point hσ F y)).1 =
      IsFiniteLocallyConstantSheaf.galoisAct sU GU (genericGaloisMap j sU GU σ)
        ‹IsFiniteLocallyConstantSheaf F› (c.boundaryStalkEquivInvariants F sU GU hz y).1 := by
  change IsFiniteLocallyConstantSheaf.transport _ sU (genericPath j sU)
      ‹IsFiniteLocallyConstantSheaf F›
      (c.boundaryStalkEquiv F hz (boundaryStalkMap c.point hσ F y)).1 = _
  rw [c.boundaryStalkEquiv_boundaryStalkMap F hz hσ y]
  exact transport_galoisStalkMap j (genericPath j sU) GU F ‹IsFiniteLocallyConstantSheaf F› σ _

end Representation

end WeilGroup.BoundaryChart

end AlgebraicGeometry
