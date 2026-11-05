import Langlands.Algebra.RenardEndomorphismLocalization
import Langlands.Algebra.RenardLocalModuleCategory

/-! # Local polynomial modules and invertible endomorphisms -/

set_option autoImplicit false

universe u v

open CategoryTheory Polynomial Langlands.Algebra

noncomputable section

namespace Langlands.Renard.EndomorphismLocalization

variable (R : Type u) [CommRing R]

/-- Invertibility of the specified endomorphism, as a property of actual pairs. -/
def invertibleEndomorphismProperty : ObjectProperty (PolynomialEndomorphism.EndomorphismCat.{u, v} R) :=
  fun A => IsUnit (PolynomialEndomorphism.endomorphism R A)

/-- The full subcategory retaining every linear intertwiner between invertible pairs. -/
abbrev InvertibleEndomorphismCat :=
  (invertibleEndomorphismProperty.{u, v} R).FullSubcategory

/-- Inclusion into the published category of modules with an endomorphism. -/
abbrev invertibleEndomorphismInclusion :
    InvertibleEndomorphismCat.{u, v} R ⥤ PolynomialEndomorphism.EndomorphismCat.{u, v} R :=
  (invertibleEndomorphismProperty.{u, v} R).ι

/-- The inclusion is fully faithful, with no restriction on intertwiners. -/
abbrev invertibleEndomorphismInclusionFullyFaithful :
    (invertibleEndomorphismInclusion.{u, v} R).FullyFaithful :=
  (invertibleEndomorphismProperty.{u, v} R).fullyFaithfulι

/-- Powers of `X` act invertibly exactly when the original `X` action is invertible. -/
theorem isSLocal_iff_isUnit_fromPolynomial (M : ModuleCat.{v} R[X]) :
    ModuleLocalization.IsSLocal (powersX R) M ↔
      IsUnit (PolynomialEndomorphism.endomorphism R ((PolynomialEndomorphism.fromPolynomial R).obj M)) := by
  rw [ModuleLocalization.isSLocal_iff_bijective, Module.End.isUnit_iff]
  constructor
  · intro h
    exact h ⟨X, Submonoid.mem_powers X⟩
  · intro h s
    change Function.Bijective (fun m : M => (X : R[X]) • m) at h
    obtain ⟨n, hn⟩ := s.property
    change Function.Bijective (fun m : M => (s : R[X]) • m)
    rw [← hn]
    clear hn
    induction n with
    | zero =>
      constructor
      · intro x y hxy
        simpa only [pow_zero, one_smul] using hxy
      · intro y
        exact ⟨y, by simp only [pow_zero, one_smul]⟩
    | succ n ih =>
      simpa only [pow_succ', mul_smul, Function.comp_def] using h.comp ih

/-- The evaluation module is local exactly when its defining endomorphism is a unit. -/
theorem evalModule_isSLocal_iff {V : Type v} [AddCommGroup V] [Module R V]
    (a : Module.End R V) :
    ModuleLocalization.IsSLocal (powersX R) (EvalModule a) ↔ IsUnit a := by
  constructor
  · intro h
    have hX := (ModuleLocalization.isSLocal_iff_bijective (powersX R) (EvalModule a)).mp h
      ⟨X, Submonoid.mem_powers X⟩
    rw [Module.End.isUnit_iff]
    have hfun : (fun x : V => a x) =
        (Module.AEval'.of a).symm ∘
          (fun m : EvalModule a => (X : R[X]) • m) ∘ Module.AEval'.of a := by
      funext x
      simp only [Function.comp_apply, Module.AEval'.X_smul_of,
        LinearEquiv.symm_apply_apply]
    change Function.Bijective (fun x : V => a x)
    rw [hfun]
    exact (Module.AEval'.of a).symm.bijective.comp
      (hX.comp (Module.AEval'.of a).bijective)
  · exact evalModule_isSLocal a

/-- The exact selection law on the inverse functor's actual polynomial module. -/
theorem toPolynomial_isSLocal_iff (A : PolynomialEndomorphism.EndomorphismCat.{u, v} R) :
    ModuleLocalization.IsSLocal (powersX R) ((PolynomialEndomorphism.toPolynomial R).obj A) ↔
      IsUnit (PolynomialEndomorphism.endomorphism R A) :=
  evalModule_isSLocal_iff R (PolynomialEndomorphism.endomorphism R A)

/-- Restriction of the actual polynomial-module functor to local modules. -/
def localFromPolynomial :
    ModuleLocalization.LocalModuleCat.{u, v} (powersX R) ⥤ InvertibleEndomorphismCat.{u, v} R :=
  (invertibleEndomorphismProperty R).lift
    (ModuleLocalization.localModuleInclusion (powersX R) ⋙ PolynomialEndomorphism.fromPolynomial R)
    (fun M => (isSLocal_iff_isUnit_fromPolynomial R M.obj).mp M.property)

/-- Restriction of the actual evaluation functor to invertible pairs. -/
def localToPolynomial :
    InvertibleEndomorphismCat.{u, v} R ⥤ ModuleLocalization.LocalModuleCat.{u, v} (powersX R) :=
  (ModuleLocalization.localModuleProperty (powersX R)).lift
    (invertibleEndomorphismInclusion R ⋙ PolynomialEndomorphism.toPolynomial R)
    (fun A => (toPolynomial_isSLocal_iff R A.obj).mpr A.property)

/-- The forward inclusion square commutes on the actual functors. -/
theorem localFromPolynomial_comp_inclusion :
    localFromPolynomial.{u, v} R ⋙ invertibleEndomorphismInclusion R =
      ModuleLocalization.localModuleInclusion (powersX R) ⋙ PolynomialEndomorphism.fromPolynomial R :=
  rfl

/-- The inverse inclusion square commutes on the actual functors. -/
theorem localToPolynomial_comp_inclusion :
    localToPolynomial.{u, v} R ⋙ ModuleLocalization.localModuleInclusion (powersX R) =
      invertibleEndomorphismInclusion R ⋙ PolynomialEndomorphism.toPolynomial R :=
  rfl

/-- The forward morphism is exactly the existing ambient functor's map. -/
@[simp] theorem localFromPolynomial_map_hom
    {M N : ModuleLocalization.LocalModuleCat.{u, v} (powersX R)} (f : M ⟶ N) :
    ((localFromPolynomial R).map f).hom = (PolynomialEndomorphism.fromPolynomial R).map f.hom :=
  rfl

/-- On vectors the forward functor retains the original polynomial-linear map. -/
@[simp] theorem localFromPolynomial_map_apply
    {M N : ModuleLocalization.LocalModuleCat.{u, v} (powersX R)} (f : M ⟶ N) (x : M.obj) :
    ((localFromPolynomial R).map f).hom.f x = f.hom x :=
  rfl

/-- The inverse morphism is exactly the existing evaluation functor's map. -/
@[simp] theorem localToPolynomial_map_hom
    {A B : InvertibleEndomorphismCat.{u, v} R} (f : A ⟶ B) :
    ((localToPolynomial R).map f).hom = (PolynomialEndomorphism.toPolynomial R).map f.hom :=
  rfl

/-- The inverse functor evaluates the original intertwiner on the original vector. -/
@[simp] theorem localToPolynomial_map_of
    {A B : InvertibleEndomorphismCat.{u, v} R} (f : A ⟶ B) (x : A.obj.a) :
    ((localToPolynomial R).map f).hom
        (Module.AEval'.of (PolynomialEndomorphism.endomorphism R A.obj) x) =
      Module.AEval'.of (PolynomialEndomorphism.endomorphism R B.obj) (f.hom.f x) :=
  rfl

/-- The natural unit is the ambient polynomial equivalence's actual unit. -/
def localUnitIso :
    𝟭 (ModuleLocalization.LocalModuleCat.{u, v} (powersX R)) ≅
      localFromPolynomial R ⋙ localToPolynomial R :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _ ((PolynomialEndomorphism.equivalence R).unitIso.app M.obj))
    (fun f => ObjectProperty.hom_ext _
      ((PolynomialEndomorphism.equivalence R).unitIso.hom.naturality f.hom))

/-- The natural counit is the ambient polynomial equivalence's actual counit. -/
def localCounitIso :
    localToPolynomial R ⋙ localFromPolynomial R ≅
      𝟭 (InvertibleEndomorphismCat.{u, v} R) :=
  NatIso.ofComponents
    (fun A => ObjectProperty.isoMk _ ((PolynomialEndomorphism.equivalence R).counitIso.app A.obj))
    (fun f => ObjectProperty.hom_ext _
      ((PolynomialEndomorphism.equivalence R).counitIso.hom.naturality f.hom))

/-- Inclusion identifies the restricted unit component with the existing unit. -/
@[simp] theorem localUnitIso_app_inclusion
    (M : ModuleLocalization.LocalModuleCat.{u, v} (powersX R)) :
    (ModuleLocalization.localModuleInclusion (powersX R)).mapIso ((localUnitIso R).app M) =
      (PolynomialEndomorphism.equivalence R).unitIso.app M.obj :=
  rfl

/-- Inclusion identifies the restricted counit component with the existing counit. -/
@[simp] theorem localCounitIso_app_inclusion
    (A : InvertibleEndomorphismCat.{u, v} R) :
    (invertibleEndomorphismInclusion R).mapIso ((localCounitIso R).app A) =
      (PolynomialEndomorphism.equivalence R).counitIso.app A.obj :=
  rfl

/-- The published polynomial equivalence restricted to the two actual full subcategories. -/
def localEquivalence :
    ModuleLocalization.LocalModuleCat.{u, v} (powersX R) ≌ InvertibleEndomorphismCat.{u, v} R where
  functor := localFromPolynomial R
  inverse := localToPolynomial R
  unitIso := localUnitIso R
  counitIso := localCounitIso R
  functor_unitIso_comp M :=
    ObjectProperty.hom_ext _ ((PolynomialEndomorphism.equivalence R).functor_unit_comp M.obj)

/-- The source's exact arbitrary-field specialization, with arbitrary carrier universe. -/
abbrev fieldLocalEquivalence (k : Type u) [Field k] :
    ModuleLocalization.LocalModuleCat.{u, v} (powersX k) ≌ InvertibleEndomorphismCat.{u, v} k :=
  localEquivalence k

end Langlands.Renard.EndomorphismLocalization
