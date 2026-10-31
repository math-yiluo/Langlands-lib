import Langlands.Algebra.NonUnitalModuleKernels
import Langlands.Algebra.NonUnitalModuleSubobject
import Langlands.Algebra.NonUnitalModuleAmbientAbelianProof
import Mathlib.CategoryTheory.Abelian.Opposite

/-!
# Concrete coimages of original nonunital-module morphisms

The actual quotient by the original stable kernel, its original quotient maps,
its cokernel universal property and its opposite-category image universal
property. Internal derived specialization of Renard A.VI.2, properties 4–5.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra.NonUnitalModuleCat

universe uA uM

variable {A : Type uA} [NonUnitalRing A]
  {M N P : NonUnitalModuleCat.{uA, uM} A}

/-- The quotient by the original stable kernel, with its published quotient action. -/
def concreteCoimage (f : M ⟶ N) : NonUnitalModuleCat.{uA, uM} A :=
  letI := f.kernelSubmodule.toIntCompatible.quotientNonUnitalModule
  of A (M ⧸ f.kernelSubmodule.toIntCompatible.toSubmodule)

/-- The carrier is the actual kernel quotient, in the original carrier universe. -/
theorem concreteCoimage_carrier (f : M ⟶ N) :
    (concreteCoimage f : Type uM) =
      (M ⧸ f.kernelSubmodule.toIntCompatible.toSubmodule) := rfl

/-- The original quotient projection, using the published quotient mechanism. -/
def concreteCoimageπ (f : M ⟶ N) : M ⟶ concreteCoimage f :=
  f.kernelSubmodule.toIntCompatible.mkQNonUnitalModuleHom

@[simp] theorem concreteCoimageπ_apply (f : M ⟶ N) (m : M) :
    NonUnitalModuleHom.toAddMonoidHom (concreteCoimageπ f) m =
      Submodule.Quotient.mk m := rfl

@[simp] theorem concreteCoimage_smul_mk (f : M ⟶ N) (a : A) (m : M) :
    (concreteCoimage f).isModule.smul a (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (a • m) := rfl

/-- Vanishing of a coset identifies exactly the original stable kernel. -/
@[simp] theorem concreteCoimageπ_eq_zero_iff (f : M ⟶ N) (m : M) :
    NonUnitalModuleHom.toAddMonoidHom (concreteCoimageπ f) m = 0 ↔
      m ∈ f.kernelSubmodule :=
  Submodule.Quotient.mk_eq_zero f.kernelSubmodule.toIntCompatible.toSubmodule

/-- Equivalently, a coset vanishes exactly when the original map vanishes. -/
theorem concreteCoimageπ_eq_zero_iff_map_eq_zero (f : M ⟶ N) (m : M) :
    NonUnitalModuleHom.toAddMonoidHom (concreteCoimageπ f) m = 0 ↔
      NonUnitalModuleHom.toAddMonoidHom f m = 0 :=
  concreteCoimageπ_eq_zero_iff f m

/-- The actual descended original morphism, obtained by the published `liftQ`. -/
def factorThruConcreteCoimage (f : M ⟶ N) : concreteCoimage f ⟶ N :=
  (f.toIntLinearIntertwiner.liftQ f.kernelSubmodule.toIntCompatible le_rfl).toNonUnitalModuleHom

@[simp] theorem factorThruConcreteCoimage_apply_mk (f : M ⟶ N) (m : M) :
    NonUnitalModuleHom.toAddMonoidHom (factorThruConcreteCoimage f)
      (Submodule.Quotient.mk m) = NonUnitalModuleHom.toAddMonoidHom f m := rfl

@[simp] theorem concreteCoimage_fac (f : M ⟶ N) :
    concreteCoimageπ f ≫ factorThruConcreteCoimage f = f := by
  apply NonUnitalModuleHom.ext
  intro m
  rfl

/-- Every coset has an original representative. -/
theorem concreteCoimageπ_surjective (f : M ⟶ N) :
    Function.Surjective (NonUnitalModuleHom.toAddMonoidHom (concreteCoimageπ f)) :=
  Submodule.Quotient.mk_surjective _

/-- The original quotient projection is categorically epic. -/
instance concreteCoimageπ_epi (f : M ⟶ N) : Epi (concreteCoimageπ f) where
  left_cancellation g h w := by
    apply NonUnitalModuleHom.ext
    intro q
    obtain ⟨m, rfl⟩ := concreteCoimageπ_surjective f q
    exact congrArg (fun k : M ⟶ _ => NonUnitalModuleHom.toAddMonoidHom k m) w

/-- Equality of descended values means the representatives differ by the stable kernel. -/
theorem factorThruConcreteCoimage_injective (f : M ⟶ N) :
    Function.Injective (NonUnitalModuleHom.toAddMonoidHom (factorThruConcreteCoimage f)) := by
  intro q r
  induction q using Submodule.Quotient.induction_on with
  | H m =>
    induction r using Submodule.Quotient.induction_on with
    | H n =>
      intro h
      apply (Submodule.Quotient.eq _).mpr
      change NonUnitalModuleHom.toAddMonoidHom f (m - n) = 0
      rw [map_sub, sub_eq_zero]
      exact h

/-- The descended original map is categorically monic. -/
instance factorThruConcreteCoimage_mono (f : M ⟶ N) : Mono (factorThruConcreteCoimage f) :=
  (mono_iff_injective _).2 (factorThruConcreteCoimage_injective f)

@[simp] theorem concreteKernelι_comp_concreteCoimageπ (f : M ⟶ N) :
    concreteKernelι f ≫ concreteCoimageπ f = 0 := by
  apply NonUnitalModuleHom.ext
  intro m
  exact (concreteCoimageπ_eq_zero_iff f m.val).2 m.property

/-- An original map annihilating the concrete kernel kills its stable subgroup. -/
theorem kernel_le_ker_of_concreteKernelι_comp_eq_zero (f : M ⟶ N) (g : M ⟶ P)
    (h : concreteKernelι f ≫ g = 0) :
    f.kernelSubmodule.toIntCompatible ≤ g.toIntLinearIntertwiner.ker := by
  intro m hm
  exact congrArg
    (fun k : concreteKernel f ⟶ P => NonUnitalModuleHom.toAddMonoidHom k ⟨m, hm⟩) h

/-- Original descent from the kernel quotient, with its original target action. -/
def concreteCoimageDesc (f : M ⟶ N) (g : M ⟶ P)
    (h : concreteKernelι f ≫ g = 0) : concreteCoimage f ⟶ P :=
  (g.toIntLinearIntertwiner.liftQ f.kernelSubmodule.toIntCompatible
    (kernel_le_ker_of_concreteKernelι_comp_eq_zero f g h)).toNonUnitalModuleHom

@[simp] theorem concreteCoimageDesc_apply_mk (f : M ⟶ N) (g : M ⟶ P)
    (h : concreteKernelι f ≫ g = 0) (m : M) :
    NonUnitalModuleHom.toAddMonoidHom (concreteCoimageDesc f g h)
      (Submodule.Quotient.mk m) = NonUnitalModuleHom.toAddMonoidHom g m := rfl

@[simp] theorem concreteCoimageπ_desc (f : M ⟶ N) (g : M ⟶ P)
    (h : concreteKernelι f ≫ g = 0) :
    concreteCoimageπ f ≫ concreteCoimageDesc f g h = g := by
  apply NonUnitalModuleHom.ext
  intro m
  rfl

/-- A descent is unique because every coset has an original representative. -/
theorem concreteCoimageDesc_unique (f : M ⟶ N) (g : M ⟶ P)
    (h : concreteKernelι f ≫ g = 0) (l : concreteCoimage f ⟶ P)
    (hl : concreteCoimageπ f ≫ l = g) : l = concreteCoimageDesc f g h := by
  apply (cancel_epi (concreteCoimageπ f)).1
  rw [hl, concreteCoimageπ_desc]

/-- The concrete kernel's actual cokernel cofork on the quotient projection. -/
def concreteCoimageCofork (f : M ⟶ N) : CokernelCofork (concreteKernelι f) :=
  CokernelCofork.ofπ (concreteCoimageπ f) (concreteKernelι_comp_concreteCoimageπ f)

/-- The explicit quotient descents construct the cokernel universal property. -/
def concreteCoimageIsColimit (f : M ⟶ N) : IsColimit (concreteCoimageCofork f) :=
  CokernelCofork.IsColimit.ofπ (concreteCoimageπ f) (concreteKernelι_comp_concreteCoimageπ f)
    (fun g h => concreteCoimageDesc f g h)
    (fun g h => concreteCoimageπ_desc f g h)
    (fun g h l hl => concreteCoimageDesc_unique f g h l hl)

@[simp] theorem concreteCoimageIsColimit_desc (f : M ⟶ N)
    (s : CokernelCofork (concreteKernelι f)) :
    (concreteCoimageIsColimit f).desc s = concreteCoimageDesc f s.π s.condition := rfl

/-- For this particular map, quotient descent is the constructed second factor. -/
@[simp] theorem concreteCoimageDesc_self (f : M ⟶ N) :
    concreteCoimageDesc f f (concreteKernelι_comp f) = factorThruConcreteCoimage f := rfl

/-- The selected cokernel of the concrete kernel is the actual quotient. -/
noncomputable def cokernelConcreteKernelIsoCoimage (f : M ⟶ N) :
    cokernel (concreteKernelι f) ≅ concreteCoimage f :=
  colimit.isoColimitCocone ⟨_, concreteCoimageIsColimit f⟩

@[simp] theorem π_cokernelConcreteKernelIsoCoimage_hom (f : M ⟶ N) :
    cokernel.π (concreteKernelι f) ≫ (cokernelConcreteKernelIsoCoimage f).hom =
      concreteCoimageπ f :=
  colimit.isoColimitCocone_ι_hom _ _

@[simp] theorem π_cokernelConcreteKernelIsoCoimage_inv (f : M ⟶ N) :
    concreteCoimageπ f ≫ (cokernelConcreteKernelIsoCoimage f).inv =
      cokernel.π (concreteKernelι f) :=
  colimit.isoColimitCocone_ι_inv ⟨_, concreteCoimageIsColimit f⟩ WalkingParallelPair.one

@[simp] theorem cokernelConcreteKernelIsoCoimage_hom_factor (f : M ⟶ N) :
    (cokernelConcreteKernelIsoCoimage f).hom ≫ factorThruConcreteCoimage f =
      cokernel.desc (concreteKernelι f) f (concreteKernelι_comp f) := by
  apply (cancel_epi (cokernel.π (concreteKernelι f))).1
  rw [← Category.assoc, π_cokernelConcreteKernelIsoCoimage_hom,
    concreteCoimage_fac, cokernel.π_desc]

@[simp] theorem cokernelConcreteKernelIsoCoimage_inv_factor (f : M ⟶ N) :
    (cokernelConcreteKernelIsoCoimage f).inv ≫
      cokernel.desc (concreteKernelι f) f (concreteKernelι_comp f) =
        factorThruConcreteCoimage f := by
  apply (cancel_epi (concreteCoimageπ f)).1
  rw [← Category.assoc, π_cokernelConcreteKernelIsoCoimage_inv,
    cokernel.π_desc, concreteCoimage_fac]

/-- Compare Mathlib's `cokernel (kernel.ι f)` with the actual stable-kernel quotient. -/
noncomputable def coimageIsoConcrete (f : M ⟶ N) :
    Abelian.coimage f ≅ concreteCoimage f :=
  cokernel.mapIso (kernel.ι f) (concreteKernelι f) (kernelIsoConcrete f) (Iso.refl M)
    (by simp) ≪≫ cokernelConcreteKernelIsoCoimage f

@[simp] theorem π_coimageIsoConcrete_hom (f : M ⟶ N) :
    Abelian.coimage.π f ≫ (coimageIsoConcrete f).hom = concreteCoimageπ f := by
  simp [coimageIsoConcrete, cokernel.mapIso]

@[simp] theorem π_coimageIsoConcrete_inv (f : M ⟶ N) :
    concreteCoimageπ f ≫ (coimageIsoConcrete f).inv = Abelian.coimage.π f := by
  rw [← π_coimageIsoConcrete_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

@[simp] theorem coimageIsoConcrete_hom_factor (f : M ⟶ N) :
    (coimageIsoConcrete f).hom ≫ factorThruConcreteCoimage f =
      Abelian.factorThruCoimage f := by
  apply (cancel_epi (Abelian.coimage.π f)).1
  rw [← Category.assoc, π_coimageIsoConcrete_hom, concreteCoimage_fac, Abelian.coimage.fac]

@[simp] theorem coimageIsoConcrete_inv_factor (f : M ⟶ N) :
    (coimageIsoConcrete f).inv ≫ Abelian.factorThruCoimage f =
      factorThruConcreteCoimage f := by
  apply (cancel_epi (concreteCoimageπ f)).1
  rw [← Category.assoc, π_coimageIsoConcrete_inv, Abelian.coimage.fac, concreteCoimage_fac]

/-- The constructed epi-mono factorization becomes a mono factorization in the opposite. -/
def concreteCoimageOpMonoFactorisation (f : M ⟶ N) : MonoFactorisation f.op where
  I := Opposite.op (concreteCoimage f)
  m := (concreteCoimageπ f).op
  e := (factorThruConcreteCoimage f).op
  fac := by rw [← op_comp, concreteCoimage_fac]

@[simp] theorem concreteCoimageOpMonoFactorisation_I (f : M ⟶ N) :
    (concreteCoimageOpMonoFactorisation f).I = Opposite.op (concreteCoimage f) := rfl

@[simp] theorem concreteCoimageOpMonoFactorisation_m (f : M ⟶ N) :
    (concreteCoimageOpMonoFactorisation f).m = (concreteCoimageπ f).op := rfl

@[simp] theorem concreteCoimageOpMonoFactorisation_e (f : M ⟶ N) :
    (concreteCoimageOpMonoFactorisation f).e = (factorThruConcreteCoimage f).op := rfl

/-- The actual categorical coimage property, as Mathlib's image property in the opposite.
Opposite abelianness makes the opposite of the constructed monomorphism strongly epic. -/
noncomputable def concreteCoimageOpIsImage (f : M ⟶ N) :
    IsImage (concreteCoimageOpMonoFactorisation f) :=
  (show StrongEpiMonoFactorisation f.op from
    { toMonoFactorisation := concreteCoimageOpMonoFactorisation f
      e_strong_epi := strongEpi_of_epi (factorThruConcreteCoimage f).op }).toMonoIsImage

end Langlands.Algebra.NonUnitalModuleCat
