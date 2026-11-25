/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed

/-!
# Comparison of `derivedInternalHom` with the internal hom of the derived category

Let `R` be a sheaf of commutative rings on a small site. The derived internal Hom
`derivedInternalHom J R` is induced by `(L, M) ↦ Q (homComplex L (I M))`, where `I` is the
functorial K-injective resolution. On the other hand, when the derived category `D(R)` carries
the derived tensor product (that is, when K-flat complexes form a left derivability structure),
`DerivedCategory.internalHomQhObj P` is the right derived functor of the internal hom
`HomotopyCategory.internalHom P` of the homotopy category, and it is right adjoint to
`Qh.obj P ⊗ᴸ -` (`DerivedCategory.tensorHomAdjunctionQhObj`).

## Main definitions

- `CategoryTheory.derivedInternalHomIsoInternalHomQhObj L`: for a complex `L`, the natural
  isomorphism `R𝓗om(Q L, -) ≅ internalHomQhObj L` of functors `D(R) ⥤ D(R)`. On `Q M` it is
  induced by the comparison `homComplex L (I M) ≅ internalHomObj L (I M)`
  (`CategoryTheory.homComplexIsoInternalHomObj`) together with the fact that both functors are
  computed on the K-injective complex `I M`.

Source: Stacks Project, sites-cohomology.tex, Sections 08J7 and 0A8X
(blueprint: def-pur-derived-internal-hom).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonoidalClosed

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}

set_option hygiene false in
local notation "𝒜" =>
  SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

noncomputable local instance : MonoidalCategory 𝒜 := SheafOfModules.monoidalCategory R

noncomputable local instance : SymmetricCategory 𝒜 := SheafOfModules.symmetricCategory R

noncomputable local instance : MonoidalClosed 𝒜 := SheafOfModules.monoidalClosed.{u} (R := R)

local instance : MonoidalPreadditive 𝒜 := (SheafOfModules.tensorClosed R).1.some

local instance : HasColimitsOfSize.{0, 0} 𝒜 := hasColimitsOfSizeShrink.{0, 0, u, u} 𝒜

local instance (X₁ X₂ : GradedObject ℤ 𝒜) : X₁.HasTensor X₂ := inferInstance

local instance (X₁ X₂ X₃ X₄ : GradedObject ℤ 𝒜) : GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ :=
  inferInstance

local instance (X₁ X₂ X₃ : GradedObject ℤ 𝒜) : GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ :=
  inferInstance

local instance (X₁ X₂ X₃ : GradedObject ℤ 𝒜) : GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ :=
  inferInstance

local instance : IsGrothendieckAbelian.{u} 𝒜 := SheafOfModules.isGrothendieckAbelian _

local instance : Abelian.HasKInjectiveResolutions 𝒜 :=
  Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian

set_option synthInstance.maxSize 512 in
noncomputable local instance : MonoidalCategory (HomotopyCategory 𝒜 (.up ℤ)) := inferInstance

variable [HasDerivedCategory.{u} 𝒜] (L : CochainComplex 𝒜 ℤ)

set_option maxHeartbeats 800000 in
-- Matching the identities of `(CochainComplex 𝒜 ℤ)ᵒᵖ` in the naturality square needs
-- unification up to the universe presentation `max u u u` of `homComplexFunctor`.
/-- `R𝓗om(Q L, -) ∘ Q ≅ Q ∘ 𝓗om^•(L, -) ∘ I`, where `I` is the functorial K-injective
resolution used to define `derivedInternalHom`. -/
noncomputable def derivedInternalHomCompQIso :
    DerivedCategory.Q ⋙
        (Functor.curry.obj (derivedInternalHom J R)).obj (op (DerivedCategory.Q.obj L)) ≅
      CochainComplex.kInjectiveResolutionFunctor.{u} 𝒜 ⋙
        (homComplexFunctor.{u, u, u, u} (C := C) (J := J) (R := R)).obj (op L) ⋙
          DerivedCategory.Q :=
  let e := Localization.fac _ (derivedInternalHom_inverts J R _
      (CochainComplex.toKInjectiveResolution.{u} 𝒜)
      (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} 𝒜 M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} 𝒜 M⟩))
      ((DerivedCategory.Q).op.prod DerivedCategory.Q)
  NatIso.ofComponents (fun M ↦ e.app (op L, M)) fun {M M'} g ↦ by
    have h := e.hom.naturality ((𝟙 (op L), g) : (op L, M) ⟶ (op L, M'))
    simp only [Functor.comp_map, Functor.prod_map, Functor.op_map, Functor.id_map,
      Functor.uncurry_obj_map, Functor.curry_obj_obj_map, unop_id, Functor.map_id, op_id,
      Iso.app_hom] at h ⊢
    rw [show (homComplexFunctor.{u, u, u, u} (C := C) (J := J) (R := R)).map (𝟙 (op L)) = 𝟙 _
      from Functor.map_id _ _, NatTrans.id_app] at h
    refine h.trans ?_
    congr 2

variable [(HomotopyCategory.quasiIso 𝒜
  (ComplexShape.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure]

/-- `internalHomQhObj L ∘ Q ≅ Q ∘ 𝓗om^•(L, -) ∘ I`: the right derived functor
`internalHomQhObj L` is computed on the K-injective complexes `I M`, where it is given by the
internal hom complex, and `homComplexIsoInternalHomObj` compares the latter with `homComplex`. -/
noncomputable def internalHomQhObjCompQIso :
    DerivedCategory.Q ⋙
        DerivedCategory.internalHomQhObj ((HomotopyCategory.quotient _ (.up ℤ)).obj L) ≅
      CochainComplex.kInjectiveResolutionFunctor.{u} 𝒜 ⋙
        (homComplexFunctor.{u, u, u, u} (C := C) (J := J) (R := R)).obj (op L) ⋙
          DerivedCategory.Q := by
  let P := (HomotopyCategory.quotient 𝒜 (.up ℤ)).obj L
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} 𝒜
  let η := CochainComplex.toKInjectiveResolution.{u} 𝒜
  let G := DerivedCategory.internalHomQhObj P
  have : IsIso (Functor.whiskerRight η DerivedCategory.Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} 𝒜 M).2
  have : IsIso (Functor.whiskerLeft (I ⋙ HomotopyCategory.quotient _ _)
      (DerivedCategory.internalHomQhObjUnit P)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    have := CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} 𝒜 M
    dsimp
    infer_instance
  exact Functor.isoWhiskerRight (asIso (Functor.whiskerRight η DerivedCategory.Q)) G ≪≫
    Functor.isoWhiskerLeft I
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso 𝒜).symm G) ≪≫
    (asIso (Functor.whiskerLeft (I ⋙ HomotopyCategory.quotient _ _)
      (DerivedCategory.internalHomQhObjUnit P))).symm ≪≫
    Functor.isoWhiskerLeft I
      (Functor.isoWhiskerRight (HomotopyCategory.quotientCompInternalHomIso P)
        DerivedCategory.Qh) ≪≫
    Functor.isoWhiskerLeft (I ⋙ CochainComplex.internalHom L)
      (DerivedCategory.quotientCompQhIso 𝒜) ≪≫
    Functor.isoWhiskerLeft I (Functor.isoWhiskerRight (homComplexFunctorObjIsoInternalHom L).symm
      DerivedCategory.Q)

/-- **Comparison of the two derived internal Homs.** For a complex `L` of sheaves of
`R`-modules, the functor `R𝓗om(Q L, -) : D(R) ⥤ D(R)` of `derivedInternalHom` is isomorphic to
the internal hom `DerivedCategory.internalHomQhObj L` out of `Qh L` for the derived tensor
product. Both are computed on K-injective complexes, by `homComplex` and `internalHomObj`
respectively, which are identified by `homComplexIsoInternalHomObj`. -/
noncomputable def derivedInternalHomIsoInternalHomQhObj :
    (Functor.curry.obj (derivedInternalHom J R)).obj (op (DerivedCategory.Q.obj L)) ≅
      DerivedCategory.internalHomQhObj ((HomotopyCategory.quotient _ (.up ℤ)).obj L) :=
  (Localization.whiskeringLeftFunctor' DerivedCategory.Q
    (HomologicalComplex.quasiIso 𝒜 (ComplexShape.up ℤ)) _).preimageIso
      (derivedInternalHomCompQIso L ≪≫ (internalHomQhObjCompQIso L).symm)

end CategoryTheory
