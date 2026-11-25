/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.ConstructibleSheaf.Biproduct
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# Kernels and cokernels of morphisms between finite locally constant sheaves

Let `Λ` be a ring and let `φ : F ⟶ G` be a morphism of finite locally constant sheaves of
`Λ`-modules on the small étale site of `X`. On a common trivialising cover `φ` is a morphism
`M_U ⟶ N_U` between constant sheaves with finitely generated values (the value of a constant
sheaf on a nonempty scheme is a stalk,
`AlgebraicGeometry.Scheme.moduleFinite_of_isFiniteSheaf_constantSheaf`),
which is, on a further étale cover, induced by a linear map `f : M ⟶ N`
(`CategoryTheory.exists_mem_forall_exists_constantSheafOverHom_comp_map_eq`); the kernel and
cokernel of `φ` restrict to the constant sheaves at `ker f` and `coker f` there. Hence
kernels and cokernels of morphisms between finite locally constant sheaves are locally
constant; their stalks are kernels and cokernels of maps between finitely generated modules,
hence finitely generated, for kernels when `Λ` is noetherian
(`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.kernel`,
`IsFiniteLocallyConstantSheaf.cokernel`). Pulling back to the strata of a common refinement of
stratifications, kernels, cokernels and direct sums of constructible sheaves of modules are
constructible (`IsConstructibleSheaf.kernel`, `IsConstructibleSheaf.cokernel`,
`IsConstructibleSheaf.biprod`).

For a finite ring `Λ`, an extension of finite locally constant sheaves is finite locally
constant (`IsFiniteLocallyConstantSheaf.of_shortExact`): étale locally the outer terms are
constant, a presentation of the quotient lifts to the extension, and the extension is the
constant sheaf at the pushout of the presentation, by the five lemma.
(blueprint: `lemma:constructible-hom-constant-locally`, `lemma:constructible-flc-serre`)

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

noncomputable section

namespace CategoryTheory.ShortComplex.ShortExact

/-- **Pushout of a short exact sequence.** For a short exact sequence
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` in an abelian category and `α : S.X₁ ⟶ M`, the sequence
`0 ⟶ M ⟶ M ⊔_{S.X₁} S.X₂ ⟶ S.X₃ ⟶ 0` is short exact. -/
lemma pushout_shortExact {C : Type*} [Category* C] [Abelian C] {S : ShortComplex C}
    (hS : S.ShortExact) {M : C} (α : S.X₁ ⟶ M) :
    (ShortComplex.mk (pushout.inl α S.f) (pushout.desc 0 S.g (by rw [comp_zero, S.zero]))
      (by rw [pushout.inl_desc])).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  refine { exact := ?_, mono_f := inferInstance, epi_g := ?_ }
  · refine ShortComplex.exact_of_g_is_cokernel _ (CokernelCofork.IsColimit.ofπ _ _
      (fun h hh ↦ hS.exact.desc (pushout.inr _ _ ≫ h)
        (by rw [← pushout.condition_assoc, hh, comp_zero]))
      (fun h hh ↦ ?_) (fun h hh m hm ↦ ?_))
    · apply pushout.hom_ext
      · rw [pushout.inl_desc_assoc, zero_comp]
        exact hh.symm
      · rw [pushout.inr_desc_assoc, hS.exact.g_desc]
    · rw [← cancel_epi S.g, ShortComplex.Exact.g_desc, ← hm, pushout.inr_desc_assoc]
  · exact epi_of_epi_fac (pushout.inr_desc _ _ _)

end CategoryTheory.ShortComplex.ShortExact

namespace AlgebraicGeometry.Scheme

section Cover

variable {Y : Scheme.{u}}

/-- A covering sieve of `Etale.mk (𝟙 Y)` in the small étale site of `Y` gives an étale cover
of `Y`, indexed by the points of `Y`: for every point one chooses a member of the sieve whose
image contains it. -/
def Cover.ofSieve (S : Sieve (Etale.mk (𝟙 Y))) (hS : S ∈ Y.smallEtaleTopology _) :
    Cover.{u} etalePrecoverage Y where
  I₀ := Y
  X y := ((mem_smallEtaleTopology_iff S).mp hS y).choose.left
  f y := ((mem_smallEtaleTopology_iff S).mp hS y).choose_spec.choose.left
  mem₀ := by
    refine (presieve₀_mem_precoverage_iff _).mpr ⟨fun y ↦ ?_, fun y ↦ inferInstance⟩
    exact ⟨y, ((mem_smallEtaleTopology_iff S).mp hS y).choose_spec.choose_spec.2⟩

variable (S : Sieve (Etale.mk (𝟙 Y))) (hS : S ∈ Y.smallEtaleTopology _)

/-- The member of the sieve chosen for the point `y`, as an object of the small étale site. -/
def Cover.ofSieveObj (y : Y) : Y.Etale :=
  ((mem_smallEtaleTopology_iff S).mp hS y).choose

/-- The member of the sieve chosen for the point `y`. -/
def Cover.ofSieveHom (y : Y) : Cover.ofSieveObj S hS y ⟶ Etale.mk (𝟙 Y) :=
  ((mem_smallEtaleTopology_iff S).mp hS y).choose_spec.choose

lemma Cover.ofSieveHom_mem (y : Y) : S (Cover.ofSieveHom S hS y) :=
  ((mem_smallEtaleTopology_iff S).mp hS y).choose_spec.choose_spec.1

lemma Cover.ofSieve_f (y : Y) : (Cover.ofSieve S hS).f y = (Cover.ofSieveHom S hS y).left :=
  rfl

lemma Cover.ofSieve_X (y : Y) : (Cover.ofSieve S hS).X y = (Cover.ofSieveObj S hS y).left :=
  rfl

lemma Cover.ofSieveHom_left (y : Y) :
    (Cover.ofSieveHom S hS y).left = (Cover.ofSieveObj S hS y).hom :=
  (Category.comp_id _).symm.trans (MorphismProperty.Over.w (Cover.ofSieveHom S hS y))

/-- The members of the cover are nonempty. -/
lemma Cover.nonempty_ofSieveObj (y : Y) : Nonempty (Cover.ofSieveObj S hS y).left :=
  let h := ((mem_smallEtaleTopology_iff S).mp hS y).choose_spec.choose_spec.2
  ⟨h.choose⟩

/-- The empty sieve does not cover a nonempty scheme. -/
lemma bot_not_mem_smallEtaleTopology (U : Y.Etale) [Nonempty U.left] :
    (⊥ : Sieve U) ∉ Y.smallEtaleTopology U := by
  intro h
  obtain ⟨V, g, hg, -⟩ := (mem_smallEtaleTopology_iff _).mp h (Classical.arbitrary _)
  exact hg

end Cover

section Finite

variable {Y : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ]

/-- **The value of a finite constant sheaf on a nonempty scheme is finitely generated**: it is
the stalk at any geometric point. -/
lemma moduleFinite_of_isFiniteSheaf_constantSheaf [Nonempty Y] (M : ModuleCat.{u + 1} Λ)
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)] :
    Module.Finite Λ M := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let y : Y := Classical.arbitrary _
  let s : Spec (.of (SeparableClosure (Y.residueField y))) ⟶ Y :=
    (SpecToEquivOfField (SeparableClosure (Y.residueField y)) _).2
      ⟨y, CommRingCat.ofHom (algebraMap (Y.residueField y) _)⟩
  exact (ModuleCat.isFinitelyGenerated_iff M).1
    ((IsFiniteSheaf.isFinitelyGenerated_sheafFiber
      (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
      (F := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) _ s).of_iso
      ((pointSmallEtale s).sheafFiberConstantSheafIso M))

end Finite

section Constant

variable {X : Scheme.{u}} {A : Type*} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]

/-- Two locally constant sheaves are trivialised by a common étale cover. -/
lemma IsLocallyConstantSheaf.exists_cover₂ (F G : Sheaf X.smallEtaleTopology A)
    [IsLocallyConstantSheaf F] [IsLocallyConstantSheaf G] :
    ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i,
      ((Etale.upperStar A (𝒰.f i)).obj F).IsConstant (𝒰.X i).smallEtaleTopology ∧
      ((Etale.upperStar A (𝒰.f i)).obj G).IsConstant (𝒰.X i).smallEtaleTopology := by
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
  obtain ⟨⟨𝒱, h𝒱⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := G)
  refine ⟨𝒰.bind fun i ↦ 𝒱.pullback₂ (𝒰.f i), fun ⟨i, j⟩ ↦ ?_⟩
  set f := pullback.snd (𝒱.f j) (𝒰.f i) ≫ 𝒰.f i
  change ((Etale.upperStar A f).obj F).IsConstant (pullback (𝒱.f j) (𝒰.f i)).smallEtaleTopology ∧
    ((Etale.upperStar A f).obj G).IsConstant (pullback (𝒱.f j) (𝒰.f i)).smallEtaleTopology
  constructor
  · have h₁ : ((Etale.upperStar A (𝒰.f i)).obj F).IsConstant (𝒰.X i).smallEtaleTopology :=
      (isConstant_over_iff_upperStar A (𝒰.etalePrecoverageToEtale i) F).mp (h𝒰 i)
    have h₂ : ((Etale.upperStar A (𝒰.f i) ⋙ Etale.upperStar A (pullback.snd (𝒱.f j) (𝒰.f i))).obj
        F).IsConstant (pullback (𝒱.f j) (𝒰.f i)).smallEtaleTopology :=
      Sheaf.IsConstant.upperStar A (pullback.snd (𝒱.f j) (𝒰.f i))
        ((Etale.upperStar A (𝒰.f i)).obj F)
    exact Sheaf.isConstant_congr _
      ((Etale.upperStarComp A (pullback.snd (𝒱.f j) (𝒰.f i)) (𝒰.f i)).app F).symm
  · have h₁ : ((Etale.upperStar A (𝒱.f j)).obj G).IsConstant (𝒱.X j).smallEtaleTopology :=
      (isConstant_over_iff_upperStar A (𝒱.etalePrecoverageToEtale j) G).mp (h𝒱 j)
    have h₂ : ((Etale.upperStar A (𝒱.f j) ⋙ Etale.upperStar A (pullback.fst (𝒱.f j) (𝒰.f i))).obj
        G).IsConstant (pullback (𝒱.f j) (𝒰.f i)).smallEtaleTopology :=
      Sheaf.IsConstant.upperStar A (pullback.fst (𝒱.f j) (𝒰.f i))
        ((Etale.upperStar A (𝒱.f j)).obj G)
    exact Sheaf.isConstant_congr _
      (((Etale.upperStarComp A (pullback.fst (𝒱.f j) (𝒰.f i)) (𝒱.f j)).app G).symm ≪≫
        eqToIso (congrArg (fun m ↦ (Etale.upperStar A m).obj G) pullback.condition))

/-- The nonempty members of an étale cover form an étale cover. -/
def Cover.nonemptyMembers (𝒰 : Cover.{u} etalePrecoverage X) : Cover.{u} etalePrecoverage X where
  I₀ := { i : 𝒰.I₀ // Nonempty (𝒰.X i) }
  X i := 𝒰.X i.1
  f i := 𝒰.f i.1
  mem₀ := by
    refine (presieve₀_mem_precoverage_iff _).mpr ⟨fun x ↦ ?_, fun i ↦ 𝒰.map_prop i.1⟩
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    exact ⟨⟨i, ⟨y⟩⟩, y, hy⟩

instance (𝒰 : Cover.{u} etalePrecoverage X) (i : 𝒰.nonemptyMembers.I₀) :
    Nonempty (𝒰.nonemptyMembers.X i) :=
  i.2

end Constant

section Kernel

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ]
  {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G)

/-- **The kernel and cokernel of a morphism between finite locally constant sheaves of modules
are locally constant**: on a common trivialising cover `φ` is a morphism of constant sheaves
with finitely generated values, which is étale-locally induced by a linear map `f`, so that the
kernel and cokernel are étale-locally the constant sheaves at `ker f` and `coker f`.
(blueprint: `lemma:constructible-hom-constant-locally`, `lemma:constructible-flc-serre`) -/
theorem IsLocallyConstantSheaf.kernel_and_cokernel
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F] [IsLocallyConstantSheaf G] :
    IsLocallyConstantSheaf (kernel φ) ∧ IsLocallyConstantSheaf (cokernel φ) := by
  obtain ⟨𝒰₀, h𝒰₀⟩ := IsLocallyConstantSheaf.exists_cover₂ F G
  let 𝒰 := 𝒰₀.nonemptyMembers
  have key : ∀ i : 𝒰.I₀, ∃ 𝒱 : Cover.{u} etalePrecoverage (𝒰.X i), ∀ j,
      ((kernel φ).over (Etale.mk (𝒱.f j ≫ 𝒰.f i))).IsConstant
        (X.smallEtaleTopology.over (Etale.mk (𝒱.f j ≫ 𝒰.f i))) ∧
      ((cokernel φ).over (Etale.mk (𝒱.f j ≫ 𝒰.f i))).IsConstant
        (X.smallEtaleTopology.over (Etale.mk (𝒱.f j ≫ 𝒰.f i))) := by
    intro i
    set Y := 𝒰.X i
    set g := 𝒰.f i
    have hF : ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj F).IsConstant Y.smallEtaleTopology :=
      (h𝒰₀ i.1).1
    have hG : ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj G).IsConstant Y.smallEtaleTopology :=
      (h𝒰₀ i.1).2
    obtain ⟨M, ⟨eF⟩⟩ := ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj F).mem_essImage_of_isConstant
    obtain ⟨N, ⟨eG⟩⟩ := ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj G).mem_essImage_of_isConstant
    let ψ : (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M ⟶
        (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N :=
      eF.hom ≫ (Etale.upperStar (ModuleCat.{u + 1} Λ) g).map φ ≫ eG.inv
    have hfin : IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
      have := IsFiniteSheaf.upperStar (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) g F
      IsFiniteSheaf.of_iso (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) eF.symm
    have : Module.Finite Λ M := moduleFinite_of_isFiniteSheaf_constantSheaf (Y := Y) M
    obtain ⟨S, hS, hmem⟩ := exists_mem_forall_exists_constantSheafOverHom_comp_map_eq
      Y.smallEtaleTopology (T := Etale.mk (𝟙 Y)) M N ψ
    refine ⟨Cover.ofSieve S hS, fun y ↦ ?_⟩
    set V := Cover.ofSieveObj S hS y
    set a := Cover.ofSieveHom S hS y
    have := Cover.nonempty_ofSieveObj S hS y
    obtain ⟨f, hf⟩ := hmem a (Cover.ofSieveHom_mem S hS y) (bot_not_mem_smallEtaleTopology V)
    have hk := Sheaf.isConstant_kernel_over Y.smallEtaleTopology _ V f ψ hf
    have hc := Sheaf.isConstant_cokernel_over Y.smallEtaleTopology _ V f ψ hf
    rw [isConstant_over_iff_upperStar] at hk hc
    have hw : (Etale.upperStar (ModuleCat.{u + 1} Λ) g).map φ ≫ eG.symm.hom = eF.symm.hom ≫ ψ := by
      simp [ψ]
    constructor
    · rw [isConstant_over_iff_upperStar]
      change ((Etale.upperStar (ModuleCat.{u + 1} Λ) (a.left ≫ g)).obj (kernel φ)).IsConstant
        V.left.smallEtaleTopology
      refine Sheaf.isConstant_congr _ (?_ : (Etale.upperStar _ V.hom).obj (kernel ψ) ≅ _)
      refine eqToIso (congrArg (fun m ↦ (Etale.upperStar (ModuleCat.{u + 1} Λ) m).obj (kernel ψ))
        (Cover.ofSieveHom_left S hS y).symm) ≪≫
        (Etale.upperStar (ModuleCat.{u + 1} Λ) a.left).mapIso
          ((kernel.mapIso _ ψ eF.symm eG.symm hw).symm ≪≫
            (PreservesKernel.iso (Etale.upperStar (ModuleCat.{u + 1} Λ) g) φ).symm) ≪≫
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) a.left g).app (kernel φ)).symm
    · rw [isConstant_over_iff_upperStar]
      change ((Etale.upperStar (ModuleCat.{u + 1} Λ) (a.left ≫ g)).obj (cokernel φ)).IsConstant
        V.left.smallEtaleTopology
      refine Sheaf.isConstant_congr _ (?_ : (Etale.upperStar _ V.hom).obj (cokernel ψ) ≅ _)
      refine eqToIso (congrArg (fun m ↦ (Etale.upperStar (ModuleCat.{u + 1} Λ) m).obj (cokernel ψ))
        (Cover.ofSieveHom_left S hS y).symm) ≪≫
        (Etale.upperStar (ModuleCat.{u + 1} Λ) a.left).mapIso
          ((cokernel.mapIso _ ψ eF.symm eG.symm hw).symm ≪≫
            (PreservesCokernel.iso (Etale.upperStar (ModuleCat.{u + 1} Λ) g) φ).symm) ≪≫
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) a.left g).app (cokernel φ)).symm
  choose 𝒱 h𝒱 using key
  exact ⟨⟨⟨⟨𝒰.bind 𝒱, fun ⟨i, j⟩ ↦ (h𝒱 i j).1⟩⟩⟩, ⟨⟨⟨𝒰.bind 𝒱, fun ⟨i, j⟩ ↦ (h𝒱 i j).2⟩⟩⟩⟩

end Kernel

section FiniteStalks

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ]
  {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G)

/-- Filtered colimits of size `u` are exact in `ModuleCat.{u + 1} Λ`. -/
instance : AB5OfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
  AB5OfSize_shrink.{u, u, u + 1, u + 1} _

/-- Limits of size `u` exist in `ModuleCat.{u + 1} Λ`; stated explicitly, since the universe
constraint of the general instance does not unify. -/
instance : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
  hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _

/-- The stalk functors at geometric points, with values in `ModuleCat.{u + 1} Λ`, preserve
finite colimits. -/
instance {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    PreservesFiniteColimits ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)) :=
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have : PreservesColimitsOfSize.{0, 0}
      ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)) :=
    ((pointSmallEtale s).skyscraperSheafAdjunction
      (A := ModuleCat.{u + 1} Λ)).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- Over a noetherian ring, the kernel of a morphism out of a finite sheaf is finite: its stalks
are kernels of maps out of finitely generated modules, submodules of noetherian modules. -/
theorem IsFiniteSheaf.kernel [IsNoetherianRing Λ]
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F] :
    IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (kernel φ) where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    have := (ModuleCat.isFinitelyGenerated_iff _).1
      (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
        (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F := F) Ω s)
    let e := PreservesKernel.iso (pointSmallEtale s).sheafFiber φ
    have hι : Function.Injective (kernel.ι ((pointSmallEtale s).sheafFiber.map φ)) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    exact ((ModuleCat.isFinitelyGenerated_iff _).2
      (Module.Finite.of_injective (kernel.ι ((pointSmallEtale s).sheafFiber.map φ)).hom hι)).of_iso
      e.symm

/-- The cokernel of a morphism into a finite sheaf is finite: its stalks are cokernels of maps
into finitely generated modules. -/
theorem IsFiniteSheaf.cokernel
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) G] :
    IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (cokernel φ) where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    let e := PreservesCokernel.iso ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)) φ
    have := (ModuleCat.isFinitelyGenerated_iff ((pointSmallEtale s).sheafFiber.obj G)).1
      (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
        (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F := G) Ω s)
    have hπ : Function.Surjective (cokernel.π ((pointSmallEtale s).sheafFiber.map φ)) :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
    exact ((ModuleCat.isFinitelyGenerated_iff
      (Limits.cokernel ((pointSmallEtale s).sheafFiber.map φ))).2
      (Module.Finite.of_surjective (cokernel.π ((pointSmallEtale s).sheafFiber.map φ)).hom
        hπ)).of_iso e.symm

/-- **The kernel of a morphism between finite locally constant sheaves of modules over a
noetherian ring is finite locally constant.** (blueprint: `lemma:constructible-flc-serre`) -/
theorem IsFiniteLocallyConstantSheaf.kernel [IsNoetherianRing Λ]
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F]
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) G] :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (kernel φ) where
  toIsLocallyConstantSheaf := (IsLocallyConstantSheaf.kernel_and_cokernel φ).1
  toIsFiniteSheaf := IsFiniteSheaf.kernel φ

/-- **The cokernel of a morphism between finite locally constant sheaves of modules is finite
locally constant.** (blueprint: `lemma:constructible-flc-serre`) -/
theorem IsFiniteLocallyConstantSheaf.cokernel
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F]
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) G] :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (cokernel φ) where
  toIsLocallyConstantSheaf := (IsLocallyConstantSheaf.kernel_and_cokernel φ).2
  toIsFiniteSheaf := IsFiniteSheaf.cokernel φ

/-- **The homology of a short complex of finite locally constant sheaves of modules over a
noetherian ring is finite locally constant**: it is the cokernel of a morphism into the cycles,
the kernel of the second morphism. -/
theorem IsFiniteLocallyConstantSheaf.homology [IsNoetherianRing Λ]
    (S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₂]
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.homology := by
  have := IsFiniteLocallyConstantSheaf.kernel S.g
  have : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.cycles :=
    IsFiniteLocallyConstantSheaf.of_iso (F := Limits.kernel S.g)
      ((S.cyclesIsKernel.conePointUniqueUpToIso (kernelIsKernel S.g)).symm)
  have := IsFiniteLocallyConstantSheaf.cokernel S.toCycles
  exact IsFiniteLocallyConstantSheaf.of_iso (F := Limits.cokernel S.toCycles)
    ((cokernelIsCokernel S.toCycles).coconePointUniqueUpToIso S.homologyIsCokernel)

end FiniteStalks

section Extension

variable {X Y : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ]

/-- **An extension of constant sheaves with a lifted presentation is constant.** Let
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of sheaves of modules on `Y_ét` with
`S.X₁ ≅ M_Y` and `S.X₃ ≅ N_Y`, let `p : Λᵇ ⟶ N` be surjective with kernel `K`, and let `V` be an
étale `Y`-scheme over which the images of the basis vectors under `p` lift to sections `y i` of
`S.X₂`, and such that the induced map `K_V ⟶ S.X₁|_V` is the constant map at a linear map
`α : K ⟶ M`. Then `S.X₂|_V` is the constant sheaf at the pushout `L` of `α` and `K ⟶ Λᵇ`: the
constant sequence `0 ⟶ M_V ⟶ L_V ⟶ N_V ⟶ 0` maps to the restriction of `S`, by isomorphisms on
the outer terms, so the middle map is an isomorphism by the five lemma. -/
lemma isConstant_over_of_shortExact_of_lift
    {S : ShortComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    {M N : ModuleCat.{u + 1} Λ}
    (e₁ : (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M ≅ S.X₁)
    (e₃ : (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N ≅ S.X₃)
    {b : ℕ} (p : (Fin b → Λ) →ₗ[Λ] N) (hp : Function.Surjective p) (V : Y.Etale)
    (y : Fin b → S.X₂.obj.obj (op V))
    (hy : ∀ i, S.g.hom.app (op V) (y i) = e₃.hom.hom.app (op V)
      ((toSheafify Y.smallEtaleTopology ((Functor.const _).obj N)).app (op V)
        (p (Pi.single i 1))))
    (α : LinearMap.ker p →ₗ[Λ] M)
    (hα : ∀ k : LinearMap.ker p, S.f.hom.app (op V) (e₁.hom.hom.app (op V)
      ((toSheafify Y.smallEtaleTopology ((Functor.const _).obj M)).app (op V) (α k))) =
        ∑ i, (k : Fin b → Λ) i • y i) :
    (S.X₂.over V).IsConstant (Y.smallEtaleTopology.over V) := by
  let J := Y.smallEtaleTopology
  let A := ModuleCat.{u + 1} Λ
  let c' := constantSheaf (J.over V) A
  let O := J.overPullback A V
  let adj := constantSheafAdj (J.over V) A Over.mkIdTerminal
  let Sm := p.shortComplexKer
  have hSm : Sm.ShortExact := LinearMap.shortExact_shortComplexKer hp
  have hSc := hSm.map_of_exact c'
  let α' : (Sm.map c').X₁ ⟶ c'.obj M := c'.map (ModuleCat.ofHom α)
  have hP := hSc.pushout_shortExact α'
  have hO := hS.map_of_exact O
  let τ₁ : c'.obj M ⟶ O.obj S.X₁ := constantSheafOverHom J A V M ≫ O.map e₁.hom
  let τ₃ : c'.obj N ⟶ O.obj S.X₃ := constantSheafOverHom J A V N ≫ O.map e₃.hom
  let φ : c'.obj (ModuleCat.of Λ (Fin b → Λ)) ⟶ O.obj S.X₂ :=
    (adj.homEquiv _ _).symm (ModuleCat.ofHom (Fintype.linearCombination Λ y))
  have hcond : α' ≫ τ₁ ≫ O.map S.f = (Sm.map c').f ≫ φ := by
    apply (adj.homEquiv _ _).injective
    change adj.homEquiv _ _ (c'.map (ModuleCat.ofHom α) ≫ (constantSheafOverHom J A V M ≫
      O.map e₁.hom) ≫ O.map S.f) = adj.homEquiv _ _ (c'.map Sm.f ≫ φ)
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left, Category.assoc,
      adj.homEquiv_naturality_right]
    erw [constantSheafAdj_homEquiv_constantSheafOverHom]
    simp only [φ]
    erw [Equiv.apply_symm_apply]
    ext k
    exact (hα k).trans (by
      change _ = Fintype.linearCombination Λ y (k : Fin b → Λ)
      rw [Fintype.linearCombination_apply])
  have hg : φ ≫ O.map S.g = (Sm.map c').g ≫ τ₃ := by
    apply (adj.homEquiv _ _).injective
    change adj.homEquiv _ _ (φ ≫ O.map S.g) = adj.homEquiv _ _ (c'.map Sm.g ≫
      constantSheafOverHom J A V N ≫ O.map e₃.hom)
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
      adj.homEquiv_naturality_right,
      show adj.homEquiv _ _ (constantSheafOverHom J A V N) = _ from
        constantSheafAdj_homEquiv_constantSheafOverHom J A V N,
      show adj.homEquiv _ _ φ = ModuleCat.ofHom (Fintype.linearCombination Λ y) from
        Equiv.apply_symm_apply _ _]
    ext i
    change S.g.hom.app (op V) (Fintype.linearCombination Λ y (Pi.single i 1)) =
      e₃.hom.hom.app (op V) ((toSheafify Y.smallEtaleTopology ((Functor.const _).obj N)).app
        (op V) (p (Pi.single i 1)))
    rw [Fintype.linearCombination_apply_single, one_smul]
    exact hy i
  let τ₂ : pushout α' (Sm.map c').f ⟶ O.obj S.X₂ := pushout.desc (τ₁ ≫ O.map S.f) φ hcond
  have key := fun (ψ : _ ⟶ S.map O) (h₁ : IsIso ψ.τ₁) (h₃ : IsIso ψ.τ₃) ↦
    ShortComplex.isIso₂_of_shortExact_of_isIso₁₃' ψ hP hO h₁ h₃
  have : IsIso τ₂ := key ⟨τ₁, τ₂, τ₃, by dsimp only [τ₂]; exact (pushout.inl_desc _ _ _).symm, by
    dsimp only [τ₂]
    apply pushout.hom_ext
    · erw [pushout.inl_desc_assoc, pushout.inl_desc_assoc]
      change (τ₁ ≫ O.map S.f) ≫ O.map S.g = 0 ≫ τ₃
      rw [zero_comp, Category.assoc, ← O.map_comp, S.zero, O.map_zero, comp_zero]
    · erw [pushout.inr_desc_assoc, pushout.inr_desc_assoc]
      exact hg⟩ (by change IsIso τ₁; infer_instance) (by change IsIso τ₃; infer_instance)
  exact Sheaf.isConstant_of_iso _ ((asIso τ₂).symm.trans
    (PreservesPushout.iso c' (ModuleCat.ofHom α) Sm.f))

/-- **An extension of finite constant sheaves is locally constant.** For a finite ring `Λ` and a
short exact sequence `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` of sheaves of modules on `Y_ét` with
`S.X₁ ≅ M_Y` and `S.X₃ ≅ N_Y`, `N` finitely generated, every object `T` of the small étale site
has a covering sieve over whose non-degenerate members `V` the restriction of `S.X₂` is
constant. Choose a surjection `p : Λᵇ ⟶ N` with kernel `K`; the images of the basis vectors
lift to sections of `S.X₂` locally (`S.X₂ ⟶ S.X₃` being locally surjective), the finitely many
resulting sections of `S.X₁ ≅ M_Y` indexed by the finite set `K` are locally constant, and then
`isConstant_over_of_shortExact_of_lift` applies. -/
lemma exists_isConstant_over_of_shortExact [Finite Λ]
    {S : ShortComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    {M N : ModuleCat.{u + 1} Λ} [Module.Finite Λ N]
    (e₁ : (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M ≅ S.X₁)
    (e₃ : (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N ≅ S.X₃)
    (T : Y.Etale) :
    ∃ R ∈ Y.smallEtaleTopology T, ∀ ⦃V : Y.Etale⦄ (g : V ⟶ T), R g →
      (⊥ : Sieve V) ∉ Y.smallEtaleTopology V →
        (S.X₂.over V).IsConstant (Y.smallEtaleTopology.over V) := by
  obtain ⟨b, p, hp⟩ := Module.Finite.exists_fin' Λ N
  let J := Y.smallEtaleTopology
  let A := ModuleCat.{u + 1} Λ
  let x (i : Fin b) : S.X₃.obj.obj (op T) := e₃.hom.hom.app (op T)
    ((toSheafify J ((Functor.const _).obj N)).app (op T) (p (Pi.single i 1)))
  have : Sheaf.IsLocallySurjective S.g :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := S.g)).2 hS.epi_g
  have hR₁ : (⨅ i, Presheaf.imageSieve S.g.hom (x i)) ∈ J T :=
    J.iInf_mem _ fun i ↦ Presheaf.imageSieve_mem J S.g.hom (x i)
  -- sections of the short exact sequence
  have hsec (U : Y.Etale) :
      (S.map (sheafToPresheaf J A ⋙ (CategoryTheory.evaluation Y.Etaleᵒᵖ A).obj (op U))).Exact :=
    hS.exact.map_of_mono_of_preservesKernel _ hS.mono_f inferInstance
  have hinj (U : Y.Etale) : Function.Injective (S.f.hom.app (op U)) :=
    have := hS.mono_f
    have : Mono S.f.hom := inferInstance
    (ModuleCat.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 this (op U))
  -- naturality of the constant sections
  have hconst {Q : ModuleCat.{u + 1} Λ} {U U' : Y.Etale} (f : U' ⟶ U) (q : Q) :
      (sheafify J ((Functor.const _).obj Q)).map f.op
        ((toSheafify J ((Functor.const _).obj Q)).app (op U) q) =
      (toSheafify J ((Functor.const _).obj Q)).app (op U') q := by
    have := (toSheafify J ((Functor.const Y.Etaleᵒᵖ).obj Q)).naturality f.op
    exact (ConcreteCategory.congr_hom this q).symm
  have step : ∀ ⦃U : Y.Etale⦄ (g : U ⟶ T), (⨅ i, Presheaf.imageSieve S.g.hom (x i)) g →
      ∃ R₂ ∈ J U, ∀ ⦃V : Y.Etale⦄ (f : V ⟶ U), R₂ f → (⊥ : Sieve V) ∉ J V →
        (S.X₂.over V).IsConstant (J.over V) := by
    intro U g hg
    have hy (i : Fin b) := ((iInf_le _ i : (⨅ i, Presheaf.imageSieve S.g.hom (x i)) ≤ _) _ hg)
    choose y hy using hy
    have nat {F G : Y.Etaleᵒᵖ ⥤ A} (η : F ⟶ G) {U₁ U₂ : Y.Etale} (f : U₂ ⟶ U₁)
        (a : ToType (F.obj (op U₁))) :
        η.app (op U₂) (F.map f.op a) = G.map f.op (η.app (op U₁) a) :=
      ConcreteCategory.congr_hom (η.naturality f.op) a
    have hyU (i : Fin b) : S.g.hom.app (op U) (y i) = e₃.hom.hom.app (op U)
        ((toSheafify J ((Functor.const _).obj N)).app (op U) (p (Pi.single i 1))) := by
      rw [hy i]
      exact (nat e₃.hom.hom g _).symm.trans (congrArg (e₃.hom.hom.app (op U)) (hconst g _))
    have hsum (k : LinearMap.ker p) :
        ∑ i, (k : Fin b → Λ) i • (Pi.single i 1 : Fin b → Λ) = k := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    have hw (k : LinearMap.ker p) : ∃ w : ToType (S.X₁.obj.obj (op U)),
        S.f.hom.app (op U) w = ∑ i, (k : Fin b → Λ) i • y i := by
      refine (ShortComplex.moduleCat_exact_iff _).1 (hsec U) _ ?_
      change S.g.hom.app (op U) (∑ i, (k : Fin b → Λ) i • y i) = 0
      let L : (Fin b → Λ) →ₗ[Λ] ToType (S.X₃.obj.obj (op U)) := (e₃.hom.hom.app (op U)).hom ∘ₗ
        ((toSheafify J ((Functor.const _).obj N)).app (op U)).hom ∘ₗ p
      have hL (v : Fin b → Λ) : e₃.hom.hom.app (op U)
          ((toSheafify J ((Functor.const _).obj N)).app (op U) (p v)) = L v := rfl
      calc S.g.hom.app (op U) (∑ i, (k : Fin b → Λ) i • y i)
          = ∑ i, (k : Fin b → Λ) i • L (Pi.single i 1) := by
            simp only [map_sum, map_smul]
            exact Finset.sum_congr rfl fun i _ ↦ congrArg ((k : Fin b → Λ) i • ·) (hyU i)
        _ = L (∑ i, (k : Fin b → Λ) i • Pi.single i 1) := by simp only [map_sum, map_smul]
        _ = 0 := by
            rw [hsum]
            change e₃.hom.hom.app (op U) ((toSheafify J ((Functor.const _).obj N)).app (op U)
              (p k)) = 0
            rw [LinearMap.mem_ker.1 k.2, map_zero]
            exact map_zero (e₃.hom.hom.app (op U)).hom
    choose w hw using hw
    obtain ⟨R₂, hR₂, hm⟩ := J.exists_mem_forall_exists_toSheafify_const_app_eq M
      (fun k : LinearMap.ker p ↦ e₁.inv.hom.app (op U) (w k))
    refine ⟨R₂, hR₂, fun V f hf hV ↦ ?_⟩
    choose m hm using hm f hf
    let y' (i : Fin b) : ToType (S.X₂.obj.obj (op V)) := S.X₂.obj.map f.op (y i)
    have hy' (i : Fin b) : S.g.hom.app (op V) (y' i) = e₃.hom.hom.app (op V)
        ((toSheafify J ((Functor.const _).obj N)).app (op V) (p (Pi.single i 1))) := by
      change S.g.hom.app (op V) (S.X₂.obj.map f.op (y i)) = _
      rw [nat S.g.hom f, hyU]
      exact (nat e₃.hom.hom f _).symm.trans (congrArg (e₃.hom.hom.app (op V)) (hconst f _))
    let θ : M →ₗ[Λ] ToType (S.X₂.obj.obj (op V)) := (S.f.hom.app (op V)).hom ∘ₗ
      (e₁.hom.hom.app (op V)).hom ∘ₗ ((toSheafify J ((Functor.const _).obj M)).app (op V)).hom
    have hθ : Function.Injective θ := by
      have he : Function.Injective (e₁.hom.hom.app (op V)) :=
        ((sheafToPresheaf J A ⋙ (CategoryTheory.evaluation Y.Etaleᵒᵖ A).obj (op V)).mapIso
          e₁).toLinearEquiv.injective
      exact (hinj V).comp (he.comp (J.toSheafify_const_app_injective M hV))
    have hinv (a : ToType (S.X₁.obj.obj (op U))) :
        e₁.hom.hom.app (op U) (e₁.inv.hom.app (op U) a) = a :=
      ((sheafToPresheaf J A ⋙ (CategoryTheory.evaluation Y.Etaleᵒᵖ A).obj (op U)).mapIso
          e₁).toLinearEquiv.apply_symm_apply a
    have key (k : LinearMap.ker p) : θ (m k) = ∑ i, (k : Fin b → Λ) i • y' i := by
      calc θ (m k) = S.f.hom.app (op V) (S.X₁.obj.map f.op (w k)) := by
              exact congrArg (S.f.hom.app (op V)) ((congrArg (e₁.hom.hom.app (op V)) (hm k)).trans
                ((nat e₁.hom.hom f _).trans (congrArg _ (hinv _))))
        _ = ∑ i, (k : Fin b → Λ) i • y' i := by
              rw [nat S.f.hom f, hw k, map_sum]
              simp only [map_smul, y']
    let α : LinearMap.ker p →ₗ[Λ] M :=
      { toFun := m
        map_add' := fun k k' ↦ hθ (by
          rw [map_add, key, key, key]
          simp [add_smul, Finset.sum_add_distrib])
        map_smul' := fun c k ↦ hθ (by
          rw [map_smul, key, key]
          simp [Finset.smul_sum, smul_smul]) }
    exact isConstant_over_of_shortExact_of_lift hS e₁ e₃ p hp V y' hy' α key
  choose R₂ hR₂ hP using step
  exact ⟨Sieve.bind _ R₂, J.bind_covering hR₁ hR₂, by
    rintro V _ ⟨U, f, g, hg, hf, rfl⟩ hV
    exact hP g hg f hf hV⟩


/-- Blueprint `lemma-constructible-flc-serre`: Kernels, cokernels and extensions of finite
locally constant sheaves.

**The extension clause.** For a finite ring `Λ`, the middle term of a short exact sequence of
sheaves of `Λ`-modules whose outer terms are finite locally constant is finite locally constant.
On an étale cover trivialising the outer terms, `S.X₁ ≅ M_U` and `S.X₃ ≅ N_U` with `M`, `N`
finite; choosing a presentation `0 ⟶ K ⟶ Λᵇ ⟶ N ⟶ 0`, the generators of `N` lift to sections
of `S.X₂` étale locally and the induced map `K_U ⟶ M_U` is étale locally constant, at a linear
map `α`; there `S.X₂` is the constant sheaf at the pushout of `α` and `K ⟶ Λᵇ`, by the five
lemma (`AlgebraicGeometry.Scheme.exists_isConstant_over_of_shortExact`). The stalks of `S.X₂`
are extensions of finitely generated modules, hence finitely generated.

Implementation note: the blueprint argues that the extension is étale locally split, the sheaf
of splittings being a torsor under `Hom_Λ(N, M)`. This fails: over `Λ = ℤ/4`, the constant
extension `0 ⟶ ℤ/2 ⟶ ℤ/4 ⟶ ℤ/2 ⟶ 0` does not split on any nonempty étale scheme. The proof
above shows instead that the extension is étale locally the constant sheaf at an extension of
modules. -/
theorem IsFiniteLocallyConstantSheaf.of_shortExact [Finite Λ]
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₂ where
  toIsLocallyConstantSheaf := by
    obtain ⟨𝒰₀, h𝒰₀⟩ := IsLocallyConstantSheaf.exists_cover₂ S.X₁ S.X₃
    let 𝒰 := 𝒰₀.nonemptyMembers
    have key : ∀ i : 𝒰.I₀, ∃ 𝒱 : Cover.{u} etalePrecoverage (𝒰.X i), ∀ j,
        (S.X₂.over (Etale.mk (𝒱.f j ≫ 𝒰.f i))).IsConstant
          (X.smallEtaleTopology.over (Etale.mk (𝒱.f j ≫ 𝒰.f i))) := by
      intro i
      set Y := 𝒰.X i
      set g := 𝒰.f i
      have hF : ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj S.X₁).IsConstant
          Y.smallEtaleTopology := (h𝒰₀ i.1).1
      have hG : ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj S.X₃).IsConstant
          Y.smallEtaleTopology := (h𝒰₀ i.1).2
      obtain ⟨M, ⟨eM⟩⟩ :=
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj S.X₁).mem_essImage_of_isConstant
      obtain ⟨N, ⟨eN⟩⟩ :=
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj S.X₃).mem_essImage_of_isConstant
      have hfin : IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
          (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N) :=
        have := IsFiniteSheaf.upperStar (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
          (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) g S.X₃
        IsFiniteSheaf.of_iso (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
          (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) eN.symm
      have : Module.Finite Λ N := moduleFinite_of_isFiniteSheaf_constantSheaf (Y := Y) N
      obtain ⟨R, hR, hP⟩ := exists_isConstant_over_of_shortExact
        (hS.map_of_exact (Etale.upperStar (ModuleCat.{u + 1} Λ) g)) eM eN (Etale.mk (𝟙 Y))
      refine ⟨Cover.ofSieve R hR, fun y ↦ ?_⟩
      set V := Cover.ofSieveObj R hR y
      set a := Cover.ofSieveHom R hR y
      have := Cover.nonempty_ofSieveObj R hR y
      have hk : ((Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj S.X₂)).IsConstant
            V.left.smallEtaleTopology := by
        have := hP a (Cover.ofSieveHom_mem R hR y) (bot_not_mem_smallEtaleTopology V)
        rwa [isConstant_over_iff_upperStar] at this
      rw [isConstant_over_iff_upperStar]
      change ((Etale.upperStar (ModuleCat.{u + 1} Λ) (a.left ≫ g)).obj S.X₂).IsConstant
        V.left.smallEtaleTopology
      refine Sheaf.isConstant_congr _ (?_ : (Etale.upperStar _ V.hom).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj S.X₂) ≅ _)
      exact eqToIso (congrArg (fun m ↦ (Etale.upperStar (ModuleCat.{u + 1} Λ) m).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj S.X₂))
          (Cover.ofSieveHom_left R hR y).symm) ≪≫
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) a.left g).app S.X₂).symm
    choose 𝒱 h𝒱 using key
    exact ⟨⟨⟨𝒰.bind 𝒱, fun ⟨i, j⟩ ↦ h𝒱 i j⟩⟩⟩
  toIsFiniteSheaf := ⟨fun Ω _ _ s ↦ by
    have hs := hS.map_of_exact ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ))
    have : Module.Finite Λ (S.map (pointSmallEtale s).sheafFiber).X₁ :=
      (ModuleCat.isFinitelyGenerated_iff _).1
        (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
          (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
          (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F := S.X₁) Ω s)
    have : Module.Finite Λ (S.map (pointSmallEtale s).sheafFiber).X₃ :=
      (ModuleCat.isFinitelyGenerated_iff _).1
        (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
          (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
          (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F := S.X₃) Ω s)
    exact (ModuleCat.isFinitelyGenerated_iff _).2
      (Module.Finite.of_exact
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hs.exact)
        hs.moduleCat_surjective_g)⟩


end Extension

section Constructible

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ]
  {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G)

/-- **The kernel of a morphism between constructible sheaves of modules over a noetherian ring
is constructible**: on the common refinement of witnessing stratifications, the pullback of the
kernel to a stratum is the kernel of a morphism between finite locally constant sheaves.
(blueprint: `thm:constructible-serre`) -/
theorem IsConstructibleSheaf.kernel [IsNoetherianRing Λ]
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F]
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) G] :
    IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (kernel φ) := by
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := F)
  obtain ⟨T, hT⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := G)
  refine ⟨S.inter T, fun k ↦ ?_⟩
  have hF := (S.inter_refines_left T).isFiniteLocallyConstantSheaf_upperStar F hS k
  have hG := (S.inter_refines_right T).isFiniteLocallyConstantSheaf_upperStar G hT k
  have := IsFiniteLocallyConstantSheaf.kernel
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) ((S.inter T).immersion k)).map φ)
  exact IsFiniteLocallyConstantSheaf.of_iso (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
    (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (PreservesKernel.iso (Etale.upperStar (ModuleCat.{u + 1} Λ) ((S.inter T).immersion k)) φ).symm

/-- **The cokernel of a morphism between constructible sheaves of modules is constructible.**
(blueprint: `thm:constructible-serre`) -/
theorem IsConstructibleSheaf.cokernel
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F]
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) G] :
    IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (cokernel φ) := by
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := F)
  obtain ⟨T, hT⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := G)
  refine ⟨S.inter T, fun k ↦ ?_⟩
  have hF := (S.inter_refines_left T).isFiniteLocallyConstantSheaf_upperStar F hS k
  have hG := (S.inter_refines_right T).isFiniteLocallyConstantSheaf_upperStar G hT k
  have := IsFiniteLocallyConstantSheaf.cokernel
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) ((S.inter T).immersion k)).map φ)
  exact IsFiniteLocallyConstantSheaf.of_iso (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
    (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (PreservesCokernel.iso (Etale.upperStar (ModuleCat.{u + 1} Λ) ((S.inter T).immersion k)) φ).symm

/-- **A retract of a constructible sheaf of modules over a noetherian ring is constructible**:
it is the kernel of the complementary idempotent. -/
theorem IsConstructibleSheaf.of_retract [IsNoetherianRing Λ] {S : Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)} (e : Retract S F)
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F] :
    IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S := by
  have h : e.i ≫ (𝟙 F - e.r ≫ e.i) = 0 := by simp
  have := IsConstructibleSheaf.kernel (𝟙 F - e.r ≫ e.i)
  refine IsConstructibleSheaf.of_iso (F' := S)
    ⟨Limits.kernel.ι _ ≫ e.r, Limits.kernel.lift _ e.i h, (cancel_mono (Limits.kernel.ι _)).1 ?_,
      by simp⟩
  have := Limits.kernel.condition (𝟙 F - e.r ≫ e.i)
  rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at this
  simpa using this.symm

variable (F G) in
/-- **The direct sum of two constructible sheaves of modules is constructible**: on the common
refinement of witnessing stratifications, the pullback of `F ⊞ G` to a stratum is the direct sum
of two finite locally constant sheaves. (blueprint: `lemma:constructible-flc-biproduct`) -/
theorem IsConstructibleSheaf.biprod
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F]
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) G] :
    IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F ⊞ G) := by
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := F)
  obtain ⟨T, hT⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := G)
  refine ⟨S.inter T, fun k ↦ ?_⟩
  have hF := (S.inter_refines_left T).isFiniteLocallyConstantSheaf_upperStar F hS k
  have hG := (S.inter_refines_right T).isFiniteLocallyConstantSheaf_upperStar G hT k
  have := IsFiniteLocallyConstantSheaf.biprod (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
    (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) ((S.inter T).immersion k)).obj F)
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) ((S.inter T).immersion k)).obj G)
  exact IsFiniteLocallyConstantSheaf.of_iso (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
    (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      ((S.inter T).immersion k)).leftAdjointBiprodIso F G).symm

/-- **The middle term of a short exact sequence of sheaves of modules over a finite ring whose
outer terms are constructible is constructible**: on the common refinement of witnessing
stratifications, the pullback of the sequence to a stratum is a short exact sequence of finite
locally constant sheaves. (blueprint: `thm:constructible-serre`) -/
theorem IsConstructibleSheaf.of_shortExact [Finite Λ]
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₂ := by
  obtain ⟨T₁, hT₁⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := S.X₁)
  obtain ⟨T₃, hT₃⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := S.X₃)
  refine ⟨T₁.inter T₃, fun k ↦ ?_⟩
  have h₁ := (T₁.inter_refines_left T₃).isFiniteLocallyConstantSheaf_upperStar S.X₁ hT₁ k
  have h₃ := (T₁.inter_refines_right T₃).isFiniteLocallyConstantSheaf_upperStar S.X₃ hT₃ k
  let F := Etale.upperStar (ModuleCat.{u + 1} Λ) ((T₁.inter T₃).immersion k)
  have : PreservesFiniteLimits F := inferInstance
  have : PreservesFiniteColimits F := inferInstance
  have hS' : (S.map F).ShortExact := hS.map_of_exact F
  have : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (S.map F).X₁ := h₁
  have : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (S.map F).X₃ := h₃
  exact IsFiniteLocallyConstantSheaf.of_shortExact hS'

end Constructible

end AlgebraicGeometry.Scheme

end
