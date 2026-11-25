/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale
public import WeilConjectures.CategoryTheory.Sites.ConstantForget
public import WeilConjectures.ConstructibleSheaf.KernelCokernel

/-!
# Finite local constancy of sheaves of modules can be tested on sets

Let `Λ` be a finite ring and `F` a sheaf of `Λ`-modules on the small étale site of a scheme `Y`.
If the underlying sheaf of sets of `F` is finite locally constant, then so is `F`
(`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_forget`): on a member `V` of a cover
trivialising the underlying sheaf of sets, that sheaf is the constant sheaf at a set `X`, finite
because it is a stalk; then `F|_V` is constant locally on `V`
(`CategoryTheory.Sheaf.exists_mem_forall_isConstant_over_of_forget`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

omit [Finite Λ] in
/-- A sheaf of modules is finite if its underlying sheaf of sets is: the stalks
of the latter are the underlying sets of the stalks of the former. -/
theorem IsFiniteSheaf.of_forget (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsFiniteSheaf ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj F)) :
    IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    have : PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    have h := hF.isFinitelyGenerated_sheafFiber Ω s
    rw [ConcreteCategory.isFinitelyGenerated_iff_finite] at h
    rw [ModuleCat.isFinitelyGenerated_iff]
    have : Finite (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) :=
      @Finite.of_equiv _ _ h (((pointSmallEtale s).sheafFiberCompIso
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app F).toEquiv
    exact Module.Finite.of_finite

/-- **A sheaf of modules over a finite ring is finite locally constant as soon as its underlying
sheaf of sets is.** -/
theorem IsFiniteLocallyConstantSheaf.of_forget
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsFiniteLocallyConstantSheafOfTypes
      ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj F)) :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F := by
  have hfin := IsFiniteSheaf.of_forget F hF.2
  obtain ⟨𝒰₀, h𝒰₀⟩ := hF.1
  let 𝒰 := 𝒰₀.nonemptyMembers
  have key : ∀ i : 𝒰.I₀, ∃ 𝒱 : Cover.{u} etalePrecoverage (𝒰.X i), ∀ j,
      (F.over (Etale.mk (𝒱.f j ≫ 𝒰.f i))).IsConstant
        (Y.smallEtaleTopology.over (Etale.mk (𝒱.f j ≫ 𝒰.f i))) := by
    intro i
    let V := 𝒰₀.etalePrecoverageToEtale i.1
    have : Nonempty V.left := i.2
    let G := (Etale.overSheafEquiv V (ModuleCat.{u + 1} Λ)).functor.obj (F.over V)
    have eG : G ≅ (Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).obj F :=
      overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} Λ) V F
    have : ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj G).IsConstant
        V.left.smallEtaleTopology :=
      have := h𝒰₀ i.1
      (Sheaf.isConstant_sheafCongr_functor_iff (Etale.overEquiv V) (A := Type (u + 1))
        Over.mkIdTerminal (((sheafCompose _ (CategoryTheory.forget _)).obj F).over V)).mpr this
    obtain ⟨X, ⟨eX⟩⟩ :=
      Sheaf.mem_essImage_of_isConstant _
        ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj G)
    -- the value `X` is finite, being a stalk of `G`
    have : Finite X := by
      have : PreservesFilteredColimitsOfSize.{u, u}
          (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
        preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
      have := IsFiniteSheaf.upperStar (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) V.hom F
      have := IsFiniteSheaf.of_iso (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) eG.symm
      let y : V.left := Classical.arbitrary _
      let s : Spec (.of (SeparableClosure (V.left.residueField y))) ⟶ V.left :=
        (SpecToEquivOfField (SeparableClosure (V.left.residueField y)) _).2
          ⟨y, CommRingCat.ofHom (algebraMap (V.left.residueField y) _)⟩
      have hs := IsFiniteSheaf.isFinitelyGenerated_sheafFiber
        (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
        (F := G) _ s
      rw [ModuleCat.isFinitelyGenerated_iff] at hs
      have hG : Finite (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G) :=
        Module.finite_of_finite Λ
      have : Finite ((pointSmallEtale s).sheafFiber.obj
          ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj G)) :=
        @Finite.of_equiv _ _ hG (((pointSmallEtale s).sheafFiberCompIso
          (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app G).symm.toEquiv
      exact Finite.of_equiv _ ((pointSmallEtale s).sheafFiber.mapIso eX.symm ≪≫
        (pointSmallEtale s).sheafFiberConstantSheafIso X).toEquiv
    obtain ⟨S, hS, hmem⟩ :=
      Sheaf.exists_mem_forall_isConstant_over_of_forget eX.symm (Etale.mk (𝟙 V.left))
    refine ⟨Cover.ofSieve S hS, fun y ↦ ?_⟩
    set V' := Cover.ofSieveObj S hS y
    set a := Cover.ofSieveHom S hS y
    have hc := hmem a (Cover.ofSieveHom_mem S hS y)
    rw [isConstant_over_iff_upperStar] at hc
    rw [isConstant_over_iff_upperStar]
    change ((Etale.upperStar (ModuleCat.{u + 1} Λ) (a.left ≫ V.hom)).obj F).IsConstant
      V'.left.smallEtaleTopology
    refine Sheaf.isConstant_congr _ (?_ : (Etale.upperStar _ V'.hom).obj G ≅ _)
    exact eqToIso (congrArg (fun m ↦ (Etale.upperStar (ModuleCat.{u + 1} Λ) m).obj G)
        (Cover.ofSieveHom_left S hS y).symm) ≪≫
      (Etale.upperStar (ModuleCat.{u + 1} Λ) a.left).mapIso eG ≪≫
      ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) a.left V.hom).app F).symm
  choose 𝒱 h𝒱 using key
  exact { toIsLocallyConstantSheaf := ⟨⟨⟨𝒰.bind 𝒱, fun ⟨i, j⟩ ↦ h𝒱 i j⟩⟩⟩
          toIsFiniteSheaf := hfin }

end AlgebraicGeometry.Scheme
