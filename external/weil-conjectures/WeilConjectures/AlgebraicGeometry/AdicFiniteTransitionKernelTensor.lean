/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
import WeilConjectures.AlgebraicGeometry.ConstantCoefficientLocalModelsComparison
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImage
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat

/-! # The ordinary kernel of consecutive flat coefficient reductions

Source: Stacks Project, proetale.tex, Tag 09C2, proof of (1), and
sites-cohomology.tex, Tags 06YS and 06YY.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.ConstantCompletion
open Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme

@[instance_reducible, no_expose]
private def adicKernelSectionModule {C : Type w} [SmallCategory C]
    {T : GrothendieckTopology C} (R : Sheaf T CommRingCat.{w})
    (M : Mod R) (U : Cᵒᵖ) : Module (R.obj.obj U) (M.val.obj U) :=
  (M.val.obj U).isModule

attribute [local instance 10000] adicKernelSectionModule

/-- The actual quotient regarded as an A-module.
Source: Stacks Project, Tag 09C2
(auxiliary; not a blueprint node). -/
private def adicFiniteUnderlyingCoeffModule (A : Type w) [CommRing A] (J : Ideal A) (n : ℕ) :
    ModuleCat.{w} A :=
  (ModuleCat.restrictScalars (adicFiniteQuotient J n)).obj
    (ModuleCat.of (adicFiniteCoeff J n) (adicFiniteCoeff J n))

/-- The quotient factor, retaining the original scalar action.
Source: Stacks Project, Tag 09C2
(auxiliary; not a blueprint node). -/
private def adicFiniteUnderlyingCoeffMap (A : Type w) [CommRing A] (J : Ideal A) (n : ℕ) :
    adicFiniteUnderlyingCoeffModule A J (n + 1) ⟶ adicFiniteUnderlyingCoeffModule A J n :=
  ModuleCat.ofHom
    { toFun := adicFiniteFactor J (Nat.le_succ n)
      map_add' := map_add _
      map_smul' := fun a b ↦ by
        change adicFiniteFactor J (Nat.le_succ n)
          (adicFiniteQuotient J (n + 1) a * b) =
            adicFiniteQuotient J n a * adicFiniteFactor J (Nat.le_succ n) b
        rw [map_mul]
        rfl }

section Comparison
variable {C : Type w} [SmallCategory C] (T : GrothendieckTopology C)
  (A : Type w) [CommRing A] (J : Ideal A)

private abbrev coeffSheaf (n : ℕ) :=
  (res (quotient T A J n)).obj (SheafOfModules.unit (siteModuleRings (finite T A J n)))

private def coeffPresheafMap (n : ℕ) :
    (SheafOfModules.strictPerfectConstantPresheaf (C := C) A).obj
        (adicFiniteUnderlyingCoeffModule A J n) ⟶
      (PresheafOfModules.restrictScalars (SheafOfModules.constantCoefficientUnit T A)).obj
        (coeffSheaf T A J n).val := by
  let α := SheafOfModules.constantCoefficientUnit T A
  let β := SheafOfModules.constantCoefficientUnit T (adicFiniteCoeff J n)
  let φ := quotient T A J n
  let P := (SheafOfModules.strictPerfectConstantPresheaf (C := C) A).obj
    (adicFiniteUnderlyingCoeffModule A J n)
  refine ⟨?_, ?_⟩
  · intro U
    refine ModuleCat.ofHom (X := P.obj U)
      (Y := ((PresheafOfModules.restrictScalars α).obj (coeffSheaf T A J n).val).obj U) ?_
    refine { toFun := β.app U, map_add' := map_add _, map_smul' := ?_ }
    intro a b
    have hs : β.app U (adicFiniteQuotient J n a) = (φ.hom.app U).hom (α.app U a) :=
      ConcreteCategory.congr_hom
        (NatTrans.congr_app (toSheafify_naturality T
          ((Functor.const Cᵒᵖ).map (CommRingCat.ofHom (adicFiniteQuotient J n)))) U) a
    exact ((β.app U).hom.map_mul (adicFiniteQuotient J n a) b).trans
      (congrArg (fun x : (SheafOfModules.constantCoefficientRing T
        (adicFiniteCoeff J n)).obj.obj U ↦ x * β.app U b) hs)
  · intro U V f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    exact ConcreteCategory.congr_hom (β.naturality f) b

private def coeffHom (n : ℕ) :
    (SheafOfModules.constantCoefficientModule T A).obj
        (adicFiniteUnderlyingCoeffModule A J n) ⟶ coeffSheaf T A J n :=
  (PresheafOfModules.sheafificationHomEquiv
    (SheafOfModules.constantCoefficientUnit T A)).symm (coeffPresheafMap T A J n)

private theorem coeffHom_isIso (n : ℕ) : IsIso (coeffHom T A J n) := by
  let α := SheafOfModules.constantCoefficientUnit T A
  let β := SheafOfModules.constantCoefficientUnit T (adicFiniteCoeff J n)
  let P := (SheafOfModules.strictPerfectConstantPresheaf (C := C) A).obj
    (adicFiniteUnderlyingCoeffModule A J n)
  let g := (PresheafOfModules.toPresheaf _).map (coeffPresheafMap T A J n)
  have : Presheaf.IsLocallyInjective T g := by
    constructor
    intro U x y h
    exact Presheaf.equalizerSieve_mem T β x y h
  have : Presheaf.IsLocallySurjective T g := by
    constructor
    intro U x
    exact Presheaf.imageSieve_mem T β x
  have hfac : toSheafify T P.presheaf ≫
      ((SheafOfModules.toSheaf _).map (coeffHom T A J n)).hom = g := by
    exact congrArg ((PresheafOfModules.toPresheaf _).map)
      ((PresheafOfModules.sheafificationHomEquiv α (P := P)
        (F := coeffSheaf T A J n)).apply_symm_apply (coeffPresheafMap T A J n))
  have : Presheaf.IsLocallySurjective T (toSheafify T P.presheaf) :=
    (T.W_toSheafify P.presheaf).isLocallySurjective
  have : Presheaf.IsLocallyInjective T
      ((SheafOfModules.toSheaf _).map (coeffHom T A J n)).hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac T g hfac
  have : Presheaf.IsLocallySurjective T
      ((SheafOfModules.toSheaf _).map (coeffHom T A J n)).hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac T hfac
  have : IsIso ((SheafOfModules.toSheaf _).map (coeffHom T A J n)) :=
    (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨inferInstance, inferInstance⟩
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)

private def coeffStep (n : ℕ) : coeffSheaf T A J (n + 1) ⟶ coeffSheaf T A J n where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := (coeffSheaf T A J (n + 1)).val.obj U)
        (Y := (coeffSheaf T A J n).val.obj U)
        { toFun := (transition T A J n).hom.app U
          map_add' := map_add _
          map_smul' := fun a b ↦ by
            have hq : quotient T A J (n + 1) ≫ transition T A J n =
                quotient T A J n := by
              simpa only [Functor.const_obj_map, Functor.const_obj_obj,
                Category.id_comp, finiteSystem, Functor.ofOpSequence_map_homOfLE_succ] using
                (quotient_step T A J n).symm
            have h := ConcreteCategory.congr_hom
              (NatTrans.congr_app
                (congrArg (fun (k : constant T A ⟶ finite T A J n) ↦ k.hom) hq) U) a
            let τ := (transition T A J n).hom.app U
            exact (τ.hom.map_mul ((quotient T A J (n + 1)).hom.app U a) b).trans
              (congrArg (fun x : (finite T A J n).obj.obj U ↦ x * τ b) h) }
      naturality := fun {U V} f ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro b
        exact ConcreteCategory.congr_hom ((transition T A J n).hom.naturality f) b }

private theorem coeffHom_step (n : ℕ) :
    (SheafOfModules.constantCoefficientModule T A).map
        (adicFiniteUnderlyingCoeffMap A J n) ≫ coeffHom T A J n =
      coeffHom T A J (n + 1) ≫ coeffStep T A J n := by
  let α := SheafOfModules.constantCoefficientUnit T A
  apply (PresheafOfModules.sheafificationHomEquiv α).injective
  change (PresheafOfModules.sheafificationAdjunction α).homEquiv _ _
      ((PresheafOfModules.sheafification α).map
        ((SheafOfModules.strictPerfectConstantPresheaf (C := C) A).map
          (adicFiniteUnderlyingCoeffMap A J n)) ≫ coeffHom T A J n) =
    (PresheafOfModules.sheafificationAdjunction α).homEquiv _ _
      (coeffHom T A J (n + 1) ≫ coeffStep T A J n)
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [α, PresheafOfModules.sheafificationAdjunction_homEquiv_apply,
    coeffHom, Equiv.apply_symm_apply]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_naturality T
      ((Functor.const Cᵒᵖ).map
        (CommRingCat.ofHom (adicFiniteFactor J (Nat.le_succ n))))) U) b

private def coeffIso (n : ℕ) :
    (SheafOfModules.constantCoefficientModule T A).obj
        (adicFiniteUnderlyingCoeffModule A J n) ≅ coeffSheaf T A J n := by
  have := coeffHom_isIso T A J n
  exact asIso (coeffHom T A J n)

end Comparison

private theorem adicKernel_pure_whisker
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    (R : Sheaf T CommRingCat.{w}) {L L' : Mod R} (f : L ⟶ L')
    (M : Mod R) (U : Cᵒᵖ) (s : L.val.obj U) (m : M.val.obj U) :
    let _ := SheafOfModules.monoidalCategory R
    (f ▷ M).val.app U (SheafOfModules.RingedTensor.pure R L M U s m) =
      SheafOfModules.RingedTensor.pure R L' M U (f.val.app U s) m := by
  let := SheafOfModules.monoidalCategory R
  simpa only [tensorHom_id, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply] using SheafOfModules.RingedTensor.pure_map R f (𝟙 M) U s m

/-- Tensoring with a constant algebraic quotient is ordinary scalar reduction, naturally
in the module and compatibly with the specified quotient factor.

Source: Stacks Project, Modules on Sites, Tag 03EK; Cohomology on Sites, Tag 06YY.
(auxiliary; not a blueprint node).

Proof: constant-module sheafification commutes with restriction of scalars, by its
adjunction and the scalar square for the constant-ring sheafification units. Its
value on the regular module is the coefficient-ring unit. Compose these comparisons
with the extension-tensor comparison. The resulting natural comparison sends a local
pure tensor s tensor m to s tensor m in scalar extension. Naturality of the constant
module sheafification unit shows that the algebraic quotient factor acts on its first
factor as the coefficient-ring transition. The tensor-unit naturality formula then
shows that the displayed composite sends s tensor m to bar(s) tensor m. This is the
unique formula defining reductionStep, proving the equality. This argument uses no
flatness, exactness, kernel or complex, and includes the zero ring and both extreme ideals. -/
private theorem adicFiniteReduction_tensor_presentation
    {C : Type w} [SmallCategory C] (T : GrothendieckTopology C)
    (A : Type w) [CommRing A] (J : Ideal A) :
    let _ := SheafOfModules.monoidalCategory (constant T A)
    let G := SheafOfModules.constantCoefficientModule T A
    ∃ e : ∀ n : ℕ,
      MonoidalCategory.tensorLeft (G.obj (adicFiniteUnderlyingCoeffModule A J n)) ≅
        reduction T A J false n,
      ∀ (n : ℕ) (M : Mod (constant T A)),
        (G.map (adicFiniteUnderlyingCoeffMap A J n) ▷ M) ≫ (e n).hom.app M =
          (e (n + 1)).hom.app M ≫ (reductionStep T A J false n).app M  := by
  let := SheafOfModules.monoidalCategory (constant T A)
  let G := SheafOfModules.constantCoefficientModule T A
  let e (n : ℕ) : tensorLeft (G.obj (adicFiniteUnderlyingCoeffModule A J n)) ≅
      reduction T A J false n :=
    (curriedTensor (Mod (constant T A))).mapIso (coeffIso T A J n) ≪≫
      extensionTensorIso (quotient T A J n)
  refine ⟨e, ?_⟩
  intro n M
  apply SheafOfModules.RingedTensor.pure_hom_ext (constant T A)
    (G.obj (adicFiniteUnderlyingCoeffModule A J (n + 1))) M
  intro U s m
  dsimp only [e, Iso.trans_hom, NatTrans.comp_app]
  change (extensionTensorComponent (quotient T A J n) M).hom.val.app U
      (((coeffHom T A J n ▷ M).val.app U)
        (((G.map (adicFiniteUnderlyingCoeffMap A J n) ▷ M).val.app U)
          (SheafOfModules.RingedTensor.pure (constant T A) _ M U s m))) =
    ((reductionStep T A J false n).app M).val.app U
      ((extensionTensorComponent (quotient T A J (n + 1)) M).hom.val.app U
        (((coeffHom T A J (n + 1) ▷ M).val.app U)
          (SheafOfModules.RingedTensor.pure (constant T A) _ M U s m)))
  erw [adicKernel_pure_whisker, adicKernel_pure_whisker, adicKernel_pure_whisker]
  rw [extensionTensorComponent_pure, extensionTensorComponent_pure]
  have ht := (reductionStep_existsUnique T A J false n).exists.choose_spec M U
    ((coeffHom T A J (n + 1)).val.app U s) m
  dsimp only [finiteMap, reductionStep] at ht
  have h := congrArg (fun k ↦ k.val.app U s) (coeffHom_step T A J n)
  exact (congrArg (fun (x : (finite T A J n).obj.obj U) ↦
    tensorSection (quotient T A J n) M U x m) h).trans ht.symm

/-- Multiplication by the residue ideal kills the concrete transition kernel.
Source: Stacks Project, Tag 09C2, coefficient sequence in the proof of (1).
(auxiliary; not a blueprint node).
Proof: lift the kernel element to J^(n+1). Its product with a member of J lies
in J^(n+2), hence is zero in the larger quotient. -/
theorem adicFiniteCoefficientKernel_annihilated
    (A : Type w) [CommRing A] (J : Ideal A) (n : ℕ) :
    let L := RingHom.ker (adicFiniteFactor J (Nat.le_succ n))
    let _ : Module A L := Module.compHom L (adicFiniteQuotient J (n + 1))
    Module.IsTorsionBySet A L (J ^ 1 : Ideal A) := by
  dsimp only
  intro x a
  apply Subtype.ext
  change Ideal.Quotient.mk (J ^ (n + 1 + 1)) (a : A) * (x : A ⧸ J ^ (n + 1 + 1)) = 0
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (x : A ⧸ J ^ (n + 1 + 1))
  have hb' : b ∈ J ^ (n + 1) := Ideal.Quotient.eq_zero_iff_mem.mp (by
    change adicFiniteFactor J (Nat.le_succ n) (Ideal.Quotient.mk _ b) = 0
    rw [hb]
    exact x.property)
  rw [← hb, ← map_mul]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  simpa only [← pow_add, Nat.add_comm 1 (n + 1)] using Ideal.mul_mem_mul a.property hb'

/-- The actual successive ideal quotient, with its action of A/J obtained by quotient lift.
Source: Stacks Project, Tag 09C2, coefficient sequence in the proof of (1).
(auxiliary; not a blueprint node). -/
def adicFiniteCoefficientKernelModule
    (A : Type w) [CommRing A] (J : Ideal A) (n : ℕ) : ModuleCat.{w} (adicFiniteCoeff J 0) :=
  let L := RingHom.ker (adicFiniteFactor J (Nat.le_succ n))
  letI : Module A L := Module.compHom L (adicFiniteQuotient J (n + 1))
  letI : Module (adicFiniteCoeff J 0) L :=
    (adicFiniteCoefficientKernel_annihilated A J n).module
  ModuleCat.of (adicFiniteCoeff J 0) L

/-- Constant-module sheafification of the concrete successive ideal quotient.
Source: Stacks Project, Tag 09C2, coefficient sequence in the proof of (1).
(auxiliary; not a blueprint node). -/
def adicFiniteCoefficientKernelSheaf {C : Type w} [SmallCategory C]
    (T : GrothendieckTopology C) (A : Type w) [CommRing A] (J : Ideal A) (n : ℕ) :
    Mod (constant T (adicFiniteCoeff J 0)) :=
  (SheafOfModules.constantCoefficientModule T (adicFiniteCoeff J 0)).obj
    (adicFiniteCoefficientKernelModule A J n)

private theorem adicFiniteConstant_limits
    {C : Type w} [SmallCategory C] (T : GrothendieckTopology C)
    (A : Type w) [CommRing A] :
    PreservesFiniteLimits (SheafOfModules.constantCoefficientModule T A) := by
  have : PreservesFiniteLimits (SheafOfModules.strictPerfectConstantPresheaf (C := C) A) := by
    constructor
    intro D _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun _ ↦ hc)⟩
  dsimp only [SheafOfModules.constantCoefficientModule]
  infer_instance

private def adicFiniteConstantRestrictionIso
    {C : Type w} [SmallCategory C] (T : GrothendieckTopology C)
    {A B : Type w} [CommRing A] [CommRing B] (f : A →+* B) (M : ModuleCat.{w} B) :
    (SheafOfModules.constantCoefficientModule T A).obj
        ((ModuleCat.restrictScalars f).obj M) ≅
      (res ((constantSheaf T CommRingCat.{w}).map (CommRingCat.ofHom f))).obj
        ((SheafOfModules.constantCoefficientModule T B).obj M) := by
  let ηA := SheafOfModules.constantCoefficientUnit T A
  let ηB := SheafOfModules.constantCoefficientUnit T B
  let f₀ := (Functor.const Cᵒᵖ).map (RingCat.ofHom f)
  let φ := (sheafCompose T (forget₂ CommRingCat.{w} RingCat.{w})).map
    ((constantSheaf T CommRingCat.{w}).map (CommRingCat.ofHom f))
  have hsq : f₀ ≫ ηB = ηA ≫ φ.hom := by
    exact congrArg (fun η ↦ Functor.whiskerRight η (forget₂ CommRingCat.{w} RingCat.{w}))
      (toSheafify_naturality T ((Functor.const Cᵒᵖ).map (CommRingCat.ofHom f)))
  let P := (SheafOfModules.strictPerfectConstantPresheaf (C := C) B).obj M
  have := SheafOfModules.restrictSheafificationComparison_isIso T ηA ηB f₀ φ hsq P
  exact asIso (SheafOfModules.restrictSheafificationComparison T ηA ηB f₀ φ hsq P)

private def adicFiniteComplexKernel
    {V : Type*} [Category V] [Preadditive V]
    {X Y Z : CochainComplex V ℤ} (i : X ⟶ Y) (g : Y ⟶ Z) (h : i ≫ g = 0)
    (hq : ∀ q, IsLimit (KernelFork.ofι (i.f q)
      (show i.f q ≫ g.f q = 0 from congrArg (fun k ↦ k.f q) h))) :
    IsLimit (KernelFork.ofι i h) := by
  let liftAt {W : CochainComplex V ℤ} (k : W ⟶ Y) (hk : k ≫ g = 0)
      (q : ℤ) : W.X q ⟶ X.X q :=
    (hq q).lift (KernelFork.ofι (k.f q)
      (show k.f q ≫ g.f q = 0 from congrArg (fun a ↦ a.f q) hk))
  have facAt {W : CochainComplex V ℤ} (k : W ⟶ Y) (hk : k ≫ g = 0) (q : ℤ) :
      liftAt k hk q ≫ i.f q = k.f q :=
    (hq q).fac _ WalkingParallelPair.zero
  let lift {W : CochainComplex V ℤ} (k : W ⟶ Y) (hk : k ≫ g = 0) : W ⟶ X :=
    { f := liftAt k hk
      comm' := by
        intro p q _
        apply Fork.IsLimit.hom_ext (hq q)
        change (liftAt k hk p ≫ X.d p q) ≫ i.f q =
          (W.d p q ≫ liftAt k hk q) ≫ i.f q
        calc
          _ = (liftAt k hk p ≫ i.f p) ≫ Y.d p q := by
            rw [Category.assoc, ← i.comm p q, ← Category.assoc]
          _ = k.f p ≫ Y.d p q := by rw [facAt k hk p]
          _ = W.d p q ≫ k.f q := k.comm p q
          _ = _ := by rw [Category.assoc, facAt k hk q] }
  refine KernelFork.IsLimit.ofι i h (fun k hk ↦ lift k hk) ?_ ?_
  · intro W k hk
    apply HomologicalComplex.hom_ext
    intro q
    exact facAt k hk q
  · intro W k hk m hm
    apply HomologicalComplex.hom_ext
    intro q
    apply Fork.IsLimit.hom_ext (hq q)
    change m.f q ≫ i.f q = liftAt k hk q ≫ i.f q
    rw [facAt k hk q]
    exact congrArg (fun a ↦ a.f q) hm

/-- Flat tensor commutes with the concrete consecutive-reduction kernel.
This statement uses only ordinary module sheaves and complexes.

Source: Stacks Project, Tag 09C2, coefficient sequence in the proof of (1), and
Modules on Sites, Tags 03CY, 03EK and 03ER.
(auxiliary; not a blueprint node).

Proof: let L be the kernel of A/J^(n+2) -> A/J^(n+1), with its concrete
A/J action given above. The algebraic sequence
0 -> L -> A/J^(n+2) -> A/J^(n+1) -> 0 is exact. The first arrow is inclusion,
and the second is the quotient factor; its surjectivity follows by lifting a
representative in A. Constant-module sheafification is exact and commutes with
restriction of scalars. Thus its first term identifies with restriction of the
explicit coefficient kernel sheaf. Tensor this sheaf sequence with each flat
term of K. The extension-tensor comparison identifies the other two terms with
the ordinary reductions; on a local pure tensor the second arrow sends s tensor x
to bar(s) tensor x, exactly the defining formula of reductionStep. The kernel
universal property identifies the first tensor term with the kernel of this map.
Every comparison is natural in the terms of K, so commutes with differentials;
the degreewise kernel property is the kernel property in complexes. The argument
uses termwise flatness only, and works for zero and unit ideals, zero rings,
empty sites and every complex degree. -/
theorem adicFiniteTransitionKernel_tensor
    {C : Type w} [SmallCategory C] (T : GrothendieckTopology C)
    (A : Type w) [CommRing A] (J : Ideal A)
    (K : Cx (constant T A)) (hflat : ∀ q : ℤ, SheafOfModules.IsFlat (K.X q))
    (n : ℕ) :
    let _ := SheafOfModules.monoidalCategory (constant T A)
    Nonempty ((kernel ((reductionComplex T A J false K).asFunctor.map
        (homOfLE (Nat.le_succ n)).op)) ≅
      ((MonoidalCategory.tensorLeft ((res (quotient T A J 0)).obj
        (adicFiniteCoefficientKernelSheaf T A J n))).mapHomologicalComplex
        (.up ℤ)).obj K) := by
  let := SheafOfModules.monoidalCategory (constant T A)
  let G := SheafOfModules.constantCoefficientModule T A
  have : PreservesFiniteLimits G := adicFiniteConstant_limits T A
  let L := RingHom.ker (adicFiniteFactor J (Nat.le_succ n))
  let : Module A L := Module.compHom L (adicFiniteQuotient J (n + 1))
  let B := adicFiniteUnderlyingCoeffModule A J (n + 1)
  let D := adicFiniteUnderlyingCoeffModule A J n
  let f : ModuleCat.of A L ⟶ B := ModuleCat.ofHom
    { toFun := Subtype.val
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let g := adicFiniteUnderlyingCoeffMap A J n
  have hz : f ≫ g = 0 := by
    ext x
    exact x.property
  let S := ShortComplex.mk f g hz
  have hs : S.ShortExact := by
    apply ModuleCat.shortComplex_shortExact
    · intro x
      change adicFiniteFactor J (Nat.le_succ n) x = 0 ↔ ∃ y : L, (y : adicFiniteCoeff J (n + 1)) = x
      exact ⟨fun h ↦ ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.property⟩
    · exact Subtype.val_injective
    · intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  have hc := KernelFork.mapIsLimit _ hs.fIsKernel G
  let LG := G.obj (ModuleCat.of A L)
  let BG := G.obj B
  let DG := G.obj D
  let fi : MonoidalCategory.tensorLeft LG ⟶ MonoidalCategory.tensorLeft BG :=
    (curriedTensor (Mod (constant T A))).map (G.map f)
  let gi : MonoidalCategory.tensorLeft BG ⟶ MonoidalCategory.tensorLeft DG :=
    (curriedTensor (Mod (constant T A))).map (G.map g)
  let X := ((MonoidalCategory.tensorLeft LG).mapHomologicalComplex (.up ℤ)).obj K
  let Y := ((MonoidalCategory.tensorLeft BG).mapHomologicalComplex (.up ℤ)).obj K
  let Z := ((MonoidalCategory.tensorLeft DG).mapHomologicalComplex (.up ℤ)).obj K
  let ii : X ⟶ Y := (fi.mapHomologicalComplex (.up ℤ)).app K
  let gg : Y ⟶ Z := (gi.mapHomologicalComplex (.up ℤ)).app K
  have hzero : ii ≫ gg = 0 := by
    apply HomologicalComplex.hom_ext
    intro q
    change (tensorRight (K.X q)).map (G.map f) ≫
      (tensorRight (K.X q)).map (G.map g) = 0
    rw [← Functor.map_comp, ← G.map_comp, hz, G.map_zero, Functor.map_zero]
  have hker : IsLimit (KernelFork.ofι ii hzero) := by
    apply adicFiniteComplexKernel ii gg hzero
    intro q
    have : PreservesFiniteLimits (tensorRight (K.X q)) := (hflat q).1
    exact KernelFork.mapIsLimit _ hc (tensorRight (K.X q))
  obtain ⟨e, he⟩ := adicFiniteReduction_tensor_presentation T A J
  let target := (reductionComplex T A J false K).asFunctor.map
    (homOfLE (Nat.le_succ n)).op
  have reductionAdd (m : ℕ) : (reduction T A J false m).Additive := by
    dsimp only [reduction, res]
    infer_instance
  let eb := (NatIso.mapHomologicalComplex (e (n + 1)) (.up ℤ)).app K
  let ed := (NatIso.mapHomologicalComplex (e n) (.up ℤ)).app K
  have hmap : eb.hom ≫ target = gg ≫ ed.hom := by
    apply HomologicalComplex.hom_ext
    intro q
    change (e (n + 1)).hom.app (K.X q) ≫
        ((Functor.ofOpSequence (reductionStep T A J false)).map
          (homOfLE (Nat.le_succ n)).op).app (K.X q) =
      (G.map g ▷ K.X q) ≫ (e n).hom.app (K.X q)
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact (he n (K.X q)).symm
  let jj : X ⟶ _ := ii ≫ eb.hom
  have hj : jj ≫ target = 0 := by
    dsimp only [jj]
    rw [Category.assoc, hmap, ← Category.assoc, hzero, zero_comp]
  have hk : IsLimit (KernelFork.ofι jj hj) :=
    IsKernel.ofIso gg hker (KernelFork.ofι jj hj) eb ed (Iso.refl _) hmap (by simp [jj])
  let eL : ModuleCat.of A L ≅
      (ModuleCat.restrictScalars (adicFiniteQuotient J 0)).obj
        (adicFiniteCoefficientKernelModule A J n) := by
    refine ModuleCat.isoMk (Iso.refl _) ?_
    intro a
    ext x
    rfl
  let er : LG ≅ (res (quotient T A J 0)).obj
      (adicFiniteCoefficientKernelSheaf T A J n) :=
    G.mapIso eL ≪≫ adicFiniteConstantRestrictionIso T
      (adicFiniteQuotient J 0) (adicFiniteCoefficientKernelModule A J n)
  let et : MonoidalCategory.tensorLeft LG ≅
      MonoidalCategory.tensorLeft ((res (quotient T A J 0)).obj
        (adicFiniteCoefficientKernelSheaf T A J n)) :=
    (curriedTensor (Mod (constant T A))).mapIso er
  exact ⟨(kernelIsKernel target).conePointUniqueUpToIso hk ≪≫
    (NatIso.mapHomologicalComplex et (.up ℤ)).app K⟩

end AlgebraicGeometry.Scheme
