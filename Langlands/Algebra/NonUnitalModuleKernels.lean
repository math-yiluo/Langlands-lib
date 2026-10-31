import Langlands.Algebra.NonUnitalModuleAdditive
import Langlands.Algebra.IntegerNonUnitalSubmodule
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Concrete kernels and cokernels of original nonunital modules

The kernel is the original stable additive subgroup of vectors sent to zero.
The cokernel uses the published integer-compatible quotient by the stable range.
The universal maps retain the original actions and construct categorical limits
and colimits directly. This is internal derived content motivated by Renard's
module conventions and Appendix A.VI.1–2, rather than an abelianness assumption.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra

universe uA uM uN uP

namespace NonUnitalModuleHom

variable {A : Type uA} [NonUnitalRing A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  {N : Type uN} [AddCommGroup N] [NonUnitalModule A N]
  {P : Type uP} [AddCommGroup P] [NonUnitalModule A P]

/-- The existing integer-compatible kernel, regarded as an original stable subgroup. -/
def kernelSubmodule (f : NonUnitalModuleHom A M N) : NonUnitalSubmodule A M :=
  NonUnitalSubmodule.ofIntCompatible f.toIntLinearIntertwiner.ker

@[simp] theorem mem_kernelSubmodule (f : NonUnitalModuleHom A M N) (m : M) :
    m ∈ f.kernelSubmodule ↔ f m = 0 := Iff.rfl

/-- The existing integer-compatible range, regarded as an original stable subgroup. -/
def rangeSubmodule (f : NonUnitalModuleHom A M N) : NonUnitalSubmodule A N :=
  NonUnitalSubmodule.ofIntCompatible f.toIntLinearIntertwiner.range

@[simp] theorem mem_rangeSubmodule (f : NonUnitalModuleHom A M N) (n : N) :
    n ∈ f.rangeSubmodule ↔ ∃ m, f m = n := Iff.rfl

/-- The carrier of the published quotient by the integer-compatible range. -/
abbrev cokernelCarrier (f : NonUnitalModuleHom A M N) : Type uN :=
  N ⧸ f.toIntLinearIntertwiner.range.toSubmodule

/-- The published quotient action, with no unit law on the original action. -/
abbrev cokernelNonUnitalModule (f : NonUnitalModuleHom A M N) :
    NonUnitalModule A f.cokernelCarrier :=
  f.toIntLinearIntertwiner.range.quotientNonUnitalModule

/-- The published quotient projection, retaining the original action on `N`. -/
def cokernelProjection (f : NonUnitalModuleHom A M N) :
    letI := f.cokernelNonUnitalModule
    NonUnitalModuleHom A N f.cokernelCarrier :=
  f.toIntLinearIntertwiner.range.mkQNonUnitalModuleHom

@[simp] theorem cokernelProjection_apply (f : NonUnitalModuleHom A M N) (n : N) :
    (letI := f.cokernelNonUnitalModule
     f.cokernelProjection n) = Submodule.Quotient.mk n := rfl

/-- The quotient carries the given original action on cosets. -/
theorem cokernel_smul_mk (f : NonUnitalModuleHom A M N) (a : A) (n : N) :
    (letI := f.cokernelNonUnitalModule
     a • (Submodule.Quotient.mk n : f.cokernelCarrier)) =
      Submodule.Quotient.mk (a • n) := rfl

/-- A coset vanishes precisely when its representative belongs to the original stable range. -/
@[simp] theorem cokernelProjection_eq_zero_iff (f : NonUnitalModuleHom A M N) (n : N) :
    (letI := f.cokernelNonUnitalModule
     f.cokernelProjection n = 0) ↔ n ∈ f.rangeSubmodule :=
  Submodule.Quotient.mk_eq_zero f.toIntLinearIntertwiner.range.toSubmodule

/-- The actual lift `p ↦ ⟨g p, _⟩` into the inherited original kernel action. -/
def kernelLift (f : NonUnitalModuleHom A M N) (g : NonUnitalModuleHom A P M)
    (h : f.comp g = 0) : NonUnitalModuleHom A P f.kernelSubmodule where
  toFun p := ⟨g p, congrArg (fun k : NonUnitalModuleHom A P N => k p) h⟩
  map_zero' := Subtype.ext g.map_zero
  map_add' p q := Subtype.ext (g.map_add p q)
  map_smul' a p := Subtype.ext (g.map_smul a p)

@[simp] theorem kernelLift_apply_coe (f : NonUnitalModuleHom A M N)
    (g : NonUnitalModuleHom A P M) (h : f.comp g = 0) (p : P) :
    (f.kernelLift g h p : M) = g p := rfl

/-- An annihilating original intertwiner kills the existing stable range. -/
theorem range_le_ker_of_comp_eq_zero (f : NonUnitalModuleHom A M N)
    (g : NonUnitalModuleHom A N P) (h : g.comp f = 0) :
    f.toIntLinearIntertwiner.range ≤ g.toIntLinearIntertwiner.ker := by
  rintro n ⟨m, rfl⟩
  exact congrArg (fun k : NonUnitalModuleHom A M P => k m) h

/-- Descent is exactly the published integer-compatible `liftQ`, followed by forgetting
integer linearity; its target is the given original action on `P`. -/
def cokernelDesc (f : NonUnitalModuleHom A M N) (g : NonUnitalModuleHom A N P)
    (h : g.comp f = 0) :
    letI := f.cokernelNonUnitalModule
    NonUnitalModuleHom A f.cokernelCarrier P :=
  (g.toIntLinearIntertwiner.liftQ f.toIntLinearIntertwiner.range
    (f.range_le_ker_of_comp_eq_zero g h)).toNonUnitalModuleHom

@[simp] theorem cokernelDesc_apply_mk (f : NonUnitalModuleHom A M N)
    (g : NonUnitalModuleHom A N P) (h : g.comp f = 0) (n : N) :
    (letI := f.cokernelNonUnitalModule
     f.cokernelDesc g h (Submodule.Quotient.mk n)) = g n := rfl

end NonUnitalModuleHom

namespace NonUnitalModuleCat

variable {A : Type uA} [NonUnitalRing A]
  {M N P : NonUnitalModuleCat.{uA, uM} A}

/-- The concrete kernel, with its existing inherited original action. -/
def concreteKernel (f : M ⟶ N) : NonUnitalModuleCat.{uA, uM} A :=
  of A f.kernelSubmodule

/-- Its carrier is the actual subtype of vectors sent to zero. -/
theorem concreteKernel_carrier (f : M ⟶ N) :
    (concreteKernel f : Type uM) =
      {m : M // NonUnitalModuleHom.toAddMonoidHom f m = 0} := rfl

/-- The actual subtype inclusion. -/
def concreteKernelι (f : M ⟶ N) : concreteKernel f ⟶ M :=
  f.kernelSubmodule.subtype

@[simp] theorem concreteKernelι_apply (f : M ⟶ N) (m : concreteKernel f) :
    NonUnitalModuleHom.toAddMonoidHom (concreteKernelι f) m =
      (m : f.kernelSubmodule).val := rfl

@[simp] theorem concreteKernel_smul_coe (f : M ⟶ N) (a : A) (m : concreteKernel f) :
    ((concreteKernel f).isModule.smul a m : f.kernelSubmodule).val =
      a • (m : f.kernelSubmodule).val := rfl

@[simp] theorem concreteKernelι_comp (f : M ⟶ N) : concreteKernelι f ≫ f = 0 := by
  apply NonUnitalModuleHom.ext
  intro m
  exact m.property

/-- The concrete factorization into the kernel. -/
def concreteKernelLift (f : M ⟶ N) (g : P ⟶ M) (h : g ≫ f = 0) :
    P ⟶ concreteKernel f := f.kernelLift g h

@[simp] theorem concreteKernelLift_apply_coe (f : M ⟶ N) (g : P ⟶ M)
    (h : g ≫ f = 0) (p : P) :
    (NonUnitalModuleHom.toAddMonoidHom (concreteKernelLift f g h) p :
      f.kernelSubmodule).val = NonUnitalModuleHom.toAddMonoidHom g p := rfl

@[simp] theorem concreteKernelLift_ι (f : M ⟶ N) (g : P ⟶ M) (h : g ≫ f = 0) :
    concreteKernelLift f g h ≫ concreteKernelι f = g := by
  apply NonUnitalModuleHom.ext
  intro p
  rfl

/-- The subtype lift is the unique factorization through the inclusion. -/
theorem concreteKernelLift_unique (f : M ⟶ N) (g : P ⟶ M) (h : g ≫ f = 0)
    (l : P ⟶ concreteKernel f) (hl : l ≫ concreteKernelι f = g) :
    l = concreteKernelLift f g h := by
  apply NonUnitalModuleHom.ext
  intro p
  apply Subtype.ext
  exact congrArg (fun k : P ⟶ M => NonUnitalModuleHom.toAddMonoidHom k p) hl

/-- The actual kernel fork on the concrete inclusion. -/
def concreteKernelFork (f : M ⟶ N) : KernelFork f :=
  KernelFork.ofι (concreteKernelι f) (concreteKernelι_comp f)

/-- The universal property constructed from the actual subtype lift. -/
def concreteKernelIsLimit (f : M ⟶ N) : IsLimit (concreteKernelFork f) :=
  KernelFork.IsLimit.ofι (concreteKernelι f) (concreteKernelι_comp f)
    (fun g h => concreteKernelLift f g h)
    (fun g h => concreteKernelLift_ι f g h)
    (fun g h l hl => concreteKernelLift_unique f g h l hl)

/-- The constructed limiting lift is the concrete lift. -/
@[simp] theorem concreteKernelIsLimit_lift (f : M ⟶ N) (s : KernelFork f) :
    (concreteKernelIsLimit f).lift s = concreteKernelLift f s.ι s.condition := rfl

/-- The quotient by the existing stable integer-compatible range, with its published action. -/
def concreteCokernel (f : M ⟶ N) : NonUnitalModuleCat.{uA, uM} A :=
  letI := f.cokernelNonUnitalModule
  of A f.cokernelCarrier

/-- Its carrier is the existing quotient, in the original carrier universe. -/
theorem concreteCokernel_carrier (f : M ⟶ N) :
    (concreteCokernel f : Type uM) = (N ⧸ f.toIntLinearIntertwiner.range.toSubmodule) := rfl

/-- The actual published quotient projection. -/
def concreteCokernelπ (f : M ⟶ N) : N ⟶ concreteCokernel f := f.cokernelProjection

@[simp] theorem concreteCokernelπ_apply (f : M ⟶ N) (n : N) :
    NonUnitalModuleHom.toAddMonoidHom (concreteCokernelπ f) n =
      Submodule.Quotient.mk n := rfl

@[simp] theorem concreteCokernel_smul_mk (f : M ⟶ N) (a : A) (n : N) :
    (concreteCokernel f).isModule.smul a (Submodule.Quotient.mk n) =
      Submodule.Quotient.mk (a • n) := rfl

@[simp] theorem concreteCokernelπ_eq_zero_iff (f : M ⟶ N) (n : N) :
    NonUnitalModuleHom.toAddMonoidHom (concreteCokernelπ f) n = 0 ↔ n ∈ f.rangeSubmodule :=
  f.cokernelProjection_eq_zero_iff n

@[simp] theorem comp_concreteCokernelπ (f : M ⟶ N) : f ≫ concreteCokernelπ f = 0 := by
  apply NonUnitalModuleHom.ext
  intro m
  exact (concreteCokernelπ_eq_zero_iff f (NonUnitalModuleHom.toAddMonoidHom f m)).2 ⟨m, rfl⟩

/-- The concrete descent uses the published integer-compatible `liftQ`. -/
def concreteCokernelDesc (f : M ⟶ N) (g : N ⟶ P) (h : f ≫ g = 0) :
    concreteCokernel f ⟶ P := f.cokernelDesc g h

@[simp] theorem concreteCokernelDesc_apply_mk (f : M ⟶ N) (g : N ⟶ P)
    (h : f ≫ g = 0) (n : N) :
    NonUnitalModuleHom.toAddMonoidHom (concreteCokernelDesc f g h) (Submodule.Quotient.mk n) =
      NonUnitalModuleHom.toAddMonoidHom g n := rfl

@[simp] theorem concreteCokernelπ_desc (f : M ⟶ N) (g : N ⟶ P) (h : f ≫ g = 0) :
    concreteCokernelπ f ≫ concreteCokernelDesc f g h = g := by
  apply NonUnitalModuleHom.ext
  intro n
  rfl

/-- Every coset has a representative, so the quotient descent is unique. -/
theorem concreteCokernelDesc_unique (f : M ⟶ N) (g : N ⟶ P) (h : f ≫ g = 0)
    (l : concreteCokernel f ⟶ P) (hl : concreteCokernelπ f ≫ l = g) :
    l = concreteCokernelDesc f g h := by
  apply NonUnitalModuleHom.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H n => exact congrArg (fun k : N ⟶ P => NonUnitalModuleHom.toAddMonoidHom k n) hl

/-- The actual cokernel cofork on the concrete projection. -/
def concreteCokernelCofork (f : M ⟶ N) : CokernelCofork f :=
  CokernelCofork.ofπ (concreteCokernelπ f) (comp_concreteCokernelπ f)

/-- The universal property constructed from the actual quotient descent. -/
def concreteCokernelIsColimit (f : M ⟶ N) : IsColimit (concreteCokernelCofork f) :=
  CokernelCofork.IsColimit.ofπ (concreteCokernelπ f) (comp_concreteCokernelπ f)
    (fun g h => concreteCokernelDesc f g h)
    (fun g h => concreteCokernelπ_desc f g h)
    (fun g h l hl => concreteCokernelDesc_unique f g h l hl)

/-- The constructed colimiting descent is the concrete descent. -/
@[simp] theorem concreteCokernelIsColimit_desc (f : M ⟶ N) (s : CokernelCofork f) :
    (concreteCokernelIsColimit f).desc s = concreteCokernelDesc f s.π s.condition := rfl

/-- All original intertwiners have kernels, supplied by the concrete universal properties. -/
instance hasKernels : HasKernels (NonUnitalModuleCat.{uA, uM} A) :=
  ⟨fun f => HasLimit.mk ⟨_, concreteKernelIsLimit f⟩⟩

/-- All original intertwiners have cokernels, supplied by the concrete universal properties. -/
instance hasCokernels : HasCokernels (NonUnitalModuleCat.{uA, uM} A) :=
  ⟨fun f => HasColimit.mk ⟨_, concreteCokernelIsColimit f⟩⟩

/-- Mathlib's chosen kernel is canonically isomorphic to the concrete original kernel. -/
noncomputable def kernelIsoConcrete (f : M ⟶ N) : kernel f ≅ concreteKernel f :=
  limit.isoLimitCone ⟨_, concreteKernelIsLimit f⟩

@[simp] theorem kernelIsoConcrete_inv_ι (f : M ⟶ N) :
    (kernelIsoConcrete f).inv ≫ kernel.ι f = concreteKernelι f :=
  limit.isoLimitCone_inv_π _ _

@[simp] theorem kernelIsoConcrete_hom_ι (f : M ⟶ N) :
    (kernelIsoConcrete f).hom ≫ concreteKernelι f = kernel.ι f :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) WalkingParallelPair.zero

/-- Mathlib's chosen cokernel is canonically isomorphic to the concrete original quotient. -/
noncomputable def cokernelIsoConcrete (f : M ⟶ N) : cokernel f ≅ concreteCokernel f :=
  colimit.isoColimitCocone ⟨_, concreteCokernelIsColimit f⟩

@[simp] theorem π_cokernelIsoConcrete_hom (f : M ⟶ N) :
    cokernel.π f ≫ (cokernelIsoConcrete f).hom = concreteCokernelπ f :=
  colimit.isoColimitCocone_ι_hom _ _

@[simp] theorem π_cokernelIsoConcrete_inv (f : M ⟶ N) :
    concreteCokernelπ f ≫ (cokernelIsoConcrete f).inv = cokernel.π f :=
  colimit.isoColimitCocone_ι_inv ⟨_, concreteCokernelIsColimit f⟩ WalkingParallelPair.one

end NonUnitalModuleCat

end Langlands.Algebra
