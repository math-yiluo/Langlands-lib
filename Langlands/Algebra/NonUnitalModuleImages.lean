import Langlands.Algebra.NonUnitalModuleKernels
import Langlands.Algebra.NonUnitalModuleSubobject
import Langlands.Algebra.NonUnitalModuleAmbientAbelianProof

/-!
# Concrete images of original nonunital modules

The image is the published original stable range, with its inherited action.
The actual surjective factor map and subtype inclusion give Mathlib's image
universal property. The comparisons retain both maps of the factorization.
This is internal derived content motivated by Renard A.VI.2, properties 4–5.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra.NonUnitalModuleCat

universe uA uM

variable {A : Type uA} [NonUnitalRing A]
  {M N : NonUnitalModuleCat.{uA, uM} A}

/-- The existing original stable range, bundled with its inherited action. -/
def concreteImage (f : M ⟶ N) : NonUnitalModuleCat.{uA, uM} A :=
  of A f.rangeSubmodule

/-- The carrier is precisely the subtype of vectors with an original preimage. -/
theorem concreteImage_carrier (f : M ⟶ N) :
    (concreteImage f : Type uM) =
      {n : N // ∃ m : M, NonUnitalModuleHom.toAddMonoidHom f m = n} := rfl

/-- The actual subtype inclusion into the original target. -/
def concreteImageι (f : M ⟶ N) : concreteImage f ⟶ N :=
  f.rangeSubmodule.subtype

@[simp] theorem concreteImageι_apply (f : M ⟶ N) (n : concreteImage f) :
    NonUnitalModuleHom.toAddMonoidHom (concreteImageι f) n =
      (n : f.rangeSubmodule).val := rfl

@[simp] theorem concreteImage_smul_coe (f : M ⟶ N) (a : A) (n : concreteImage f) :
    ((concreteImage f).isModule.smul a n : f.rangeSubmodule).val =
      a • (n : f.rangeSubmodule).val := rfl

/-- The actual original map with codomain restricted to its stable range. -/
def factorThruConcreteImage (f : M ⟶ N) : M ⟶ concreteImage f where
  toFun m := ⟨NonUnitalModuleHom.toAddMonoidHom f m, ⟨m, rfl⟩⟩
  map_zero' := Subtype.ext f.map_zero
  map_add' m n := Subtype.ext (f.map_add m n)
  map_smul' a m := Subtype.ext (f.map_smul a m)

@[simp] theorem factorThruConcreteImage_apply (f : M ⟶ N) (m : M) :
    NonUnitalModuleHom.toAddMonoidHom (factorThruConcreteImage f) m =
      (⟨NonUnitalModuleHom.toAddMonoidHom f m, ⟨m, rfl⟩⟩ : f.rangeSubmodule) := rfl

@[simp] theorem factorThruConcreteImage_apply_coe (f : M ⟶ N) (m : M) :
    (NonUnitalModuleHom.toAddMonoidHom (factorThruConcreteImage f) m :
      f.rangeSubmodule).val = NonUnitalModuleHom.toAddMonoidHom f m := rfl

@[reassoc (attr := simp)]
theorem factorThruConcreteImage_ι (f : M ⟶ N) :
    factorThruConcreteImage f ≫ concreteImageι f = f := by
  apply NonUnitalModuleHom.ext
  intro m
  rfl

/-- Every vector in the concrete range has an original preimage. -/
theorem factorThruConcreteImage_surjective (f : M ⟶ N) :
    Function.Surjective
      (NonUnitalModuleHom.toAddMonoidHom (factorThruConcreteImage f)) := by
  rintro ⟨n, m, hm⟩
  exact ⟨m, Subtype.ext hm⟩

instance mono_concreteImageι (f : M ⟶ N) : Mono (concreteImageι f) :=
  mono_subtype f.rangeSubmodule

/-- Epimorphism follows directly by evaluating on original preimages. -/
instance epi_factorThruConcreteImage (f : M ⟶ N) : Epi (factorThruConcreteImage f) := by
  constructor
  intro P g h w
  apply NonUnitalModuleHom.ext
  intro n
  obtain ⟨m, rfl⟩ := factorThruConcreteImage_surjective f n
  exact congrArg (fun k : M ⟶ P => NonUnitalModuleHom.toAddMonoidHom k m) w

/-- The mono factorization uses exactly the concrete inclusion and factor map. -/
def concreteImageMonoFactorisation (f : M ⟶ N) : MonoFactorisation f where
  I := concreteImage f
  m := concreteImageι f
  e := factorThruConcreteImage f
  fac := factorThruConcreteImage_ι f

/-- Ambient abelianness makes the proved epimorphism a strong epimorphism. -/
noncomputable def concreteImageStrongEpiMonoFactorisation (f : M ⟶ N) :
    StrongEpiMonoFactorisation f where
  toMonoFactorisation := concreteImageMonoFactorisation f
  e_strong_epi := by
    change StrongEpi (factorThruConcreteImage f)
    exact strongEpi_of_epi _

/-- The constructed concrete factorization has Mathlib's image universal property. -/
noncomputable def concreteImageIsImage (f : M ⟶ N) :
    IsImage (concreteImageMonoFactorisation f) :=
  (concreteImageStrongEpiMonoFactorisation f).toMonoIsImage

/-- The universal lift commutes with the actual inclusion. -/
@[reassoc (attr := simp)]
theorem concreteImageIsImage_lift_ι (f : M ⟶ N) (F : MonoFactorisation f) :
    (concreteImageIsImage f).lift F ≫ F.m = concreteImageι f :=
  (concreteImageIsImage f).lift_fac F

/-- The same universal lift also retains the source factor map. -/
@[reassoc (attr := simp)]
theorem factorThruConcreteImage_isImage_lift (f : M ⟶ N) (F : MonoFactorisation f) :
    factorThruConcreteImage f ≫ (concreteImageIsImage f).lift F = F.e :=
  (concreteImageIsImage f).fac_lift F

/-- A lift commuting with the inclusion is unique because the other inclusion is monic. -/
theorem concreteImageIsImage_lift_unique (f : M ⟶ N) (F : MonoFactorisation f)
    (l : concreteImage f ⟶ F.I) (hl : l ≫ F.m = concreteImageι f) :
    l = (concreteImageIsImage f).lift F :=
  (cancel_mono F.m).1 (hl.trans ((concreteImageIsImage f).lift_fac F).symm)

/-- Mathlib's selected image is canonically isomorphic to the original stable range. -/
noncomputable def imageIsoConcrete (f : M ⟶ N) : Limits.image f ≅ concreteImage f :=
  IsImage.isoExt (Image.isImage f) (concreteImageIsImage f)

@[reassoc (attr := simp)]
theorem imageIsoConcrete_hom_ι (f : M ⟶ N) :
    (imageIsoConcrete f).hom ≫ concreteImageι f = Limits.image.ι f :=
  IsImage.isoExt_hom_m (Image.isImage f) (concreteImageIsImage f)

@[reassoc (attr := simp)]
theorem imageIsoConcrete_inv_ι (f : M ⟶ N) :
    (imageIsoConcrete f).inv ≫ Limits.image.ι f = concreteImageι f :=
  IsImage.isoExt_inv_m (Image.isImage f) (concreteImageIsImage f)

@[reassoc (attr := simp)]
theorem factorThruImage_imageIsoConcrete_hom (f : M ⟶ N) :
    Limits.factorThruImage f ≫ (imageIsoConcrete f).hom = factorThruConcreteImage f :=
  IsImage.e_isoExt_hom (Image.isImage f) (concreteImageIsImage f)

@[reassoc (attr := simp)]
theorem factorThruConcreteImage_imageIsoConcrete_inv (f : M ⟶ N) :
    factorThruConcreteImage f ≫ (imageIsoConcrete f).inv = Limits.factorThruImage f :=
  IsImage.e_isoExt_inv (Image.isImage f) (concreteImageIsImage f)

/-- The concrete kernel-of-cokernel membership test is exactly the published zero-coset test. -/
@[simp] theorem mem_kernelSubmodule_concreteCokernelπ (f : M ⟶ N) (n : N) :
    n ∈ (concreteCokernelπ f).kernelSubmodule ↔ n ∈ f.rangeSubmodule :=
  concreteCokernelπ_eq_zero_iff f n

/-- The concrete image and the concrete kernel of the concrete cokernel have the same vectors. -/
def concreteImageIsoKernelCokernel (f : M ⟶ N) :
    concreteImage f ≅ concreteKernel (concreteCokernelπ f) where
  hom :=
    { toFun := fun n => ⟨n.val, (concreteCokernelπ_eq_zero_iff f n.val).2 n.property⟩
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  inv :=
    { toFun := fun n => ⟨n.val, (concreteCokernelπ_eq_zero_iff f n.val).1 n.property⟩
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  hom_inv_id := by
    apply NonUnitalModuleHom.ext
    intro n
    rfl
  inv_hom_id := by
    apply NonUnitalModuleHom.ext
    intro n
    rfl

@[simp] theorem concreteImageIsoKernelCokernel_hom_apply_coe
    (f : M ⟶ N) (n : concreteImage f) :
    (NonUnitalModuleHom.toAddMonoidHom (concreteImageIsoKernelCokernel f).hom n :
      (concreteCokernelπ f).kernelSubmodule).val = (n : f.rangeSubmodule).val := rfl

@[simp] theorem concreteImageIsoKernelCokernel_inv_apply_coe
    (f : M ⟶ N) (n : concreteKernel (concreteCokernelπ f)) :
    (NonUnitalModuleHom.toAddMonoidHom (concreteImageIsoKernelCokernel f).inv n :
      f.rangeSubmodule).val = (n : (concreteCokernelπ f).kernelSubmodule).val := rfl

@[reassoc (attr := simp)]
theorem concreteImageIsoKernelCokernel_hom_ι (f : M ⟶ N) :
    (concreteImageIsoKernelCokernel f).hom ≫ concreteKernelι (concreteCokernelπ f) =
      concreteImageι f := by
  apply NonUnitalModuleHom.ext
  intro n
  rfl

@[reassoc (attr := simp)]
theorem concreteImageIsoKernelCokernel_inv_ι (f : M ⟶ N) :
    (concreteImageIsoKernelCokernel f).inv ≫ concreteImageι f =
      concreteKernelι (concreteCokernelπ f) := by
  apply NonUnitalModuleHom.ext
  intro n
  rfl

/-- Mathlib's selected abelian image, `kernel (cokernel.π f)`, is the same concrete image. -/
noncomputable def abelianImageIsoConcrete (f : M ⟶ N) :
    Abelian.image f ≅ concreteImage f :=
  (Abelian.imageIsoImage f).trans (imageIsoConcrete f)

@[reassoc (attr := simp)]
theorem abelianImageIsoConcrete_hom_ι (f : M ⟶ N) :
    (abelianImageIsoConcrete f).hom ≫ concreteImageι f = kernel.ι (cokernel.π f) := by
  dsimp only [abelianImageIsoConcrete, Iso.trans_hom]
  rw [Category.assoc, imageIsoConcrete_hom_ι, Abelian.imageIsoImage_hom_comp_image_ι]

@[reassoc (attr := simp)]
theorem abelianImageIsoConcrete_inv_ι (f : M ⟶ N) :
    (abelianImageIsoConcrete f).inv ≫ kernel.ι (cokernel.π f) = concreteImageι f := by
  apply (cancel_epi (abelianImageIsoConcrete f).hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
    abelianImageIsoConcrete_hom_ι]

@[reassoc (attr := simp)]
theorem abelianFactorThruImage_abelianImageIsoConcrete_hom (f : M ⟶ N) :
    Abelian.factorThruImage f ≫ (abelianImageIsoConcrete f).hom =
      factorThruConcreteImage f := by
  apply (cancel_mono (concreteImageι f)).1
  rw [Category.assoc, abelianImageIsoConcrete_hom_ι,
    Abelian.image.fac, factorThruConcreteImage_ι]

@[reassoc (attr := simp)]
theorem factorThruConcreteImage_abelianImageIsoConcrete_inv (f : M ⟶ N) :
    factorThruConcreteImage f ≫ (abelianImageIsoConcrete f).inv =
      Abelian.factorThruImage f := by
  apply (cancel_mono (kernel.ι (cokernel.π f))).1
  rw [Category.assoc, abelianImageIsoConcrete_inv_ι,
    factorThruConcreteImage_ι, Abelian.image.fac]

/-! Complete unapplied construction interfaces and both unequal universe specializations. -/

noncomputable section InterfaceChecks

example : (A : Type uA) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{uA, uM} A} → (f : M ⟶ N) →
      NonUnitalModuleCat.{uA, uM} A :=
  @concreteImage.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{uA, uM} A} → (f : M ⟶ N) →
      concreteImage f ⟶ N :=
  @concreteImageι.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{uA, uM} A} → (f : M ⟶ N) →
      M ⟶ concreteImage f :=
  @factorThruConcreteImage.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{uA, uM} A} → (f : M ⟶ N) →
      Mono (concreteImageι f) :=
  @mono_concreteImageι.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{uA, uM} A} → (f : M ⟶ N) →
      Epi (factorThruConcreteImage f) :=
  @epi_factorThruConcreteImage.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{uA, uM} A} → (f : M ⟶ N) →
      MonoFactorisation f :=
  @concreteImageMonoFactorisation.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{uA, uM} A} → (f : M ⟶ N) →
      StrongEpiMonoFactorisation f :=
  @concreteImageStrongEpiMonoFactorisation.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{uA, uM} A} → (f : M ⟶ N) →
      IsImage (concreteImageMonoFactorisation f) :=
  @concreteImageIsImage.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{uA, uM} A} → (f : M ⟶ N) →
      Limits.image f ≅ concreteImage f :=
  @imageIsoConcrete.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{uA, uM} A} → (f : M ⟶ N) →
      concreteImage f ≅ concreteKernel (concreteCokernelπ f) :=
  @concreteImageIsoKernelCokernel.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{uA, uM} A} → (f : M ⟶ N) →
      Abelian.image f ≅ concreteImage f :=
  @abelianImageIsoConcrete.{uA, uM}

example : (A : Type) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{0, 1} A} → (f : M ⟶ N) →
      NonUnitalModuleCat.{0, 1} A :=
  @concreteImage.{0, 1}

example : (A : Type) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{0, 1} A} → (f : M ⟶ N) →
      concreteImage f ⟶ N :=
  @concreteImageι.{0, 1}

example : (A : Type) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{0, 1} A} → (f : M ⟶ N) →
      M ⟶ concreteImage f :=
  @factorThruConcreteImage.{0, 1}

example : (A : Type) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{0, 1} A} → (f : M ⟶ N) →
      Mono (concreteImageι f) :=
  @mono_concreteImageι.{0, 1}

example : (A : Type) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{0, 1} A} → (f : M ⟶ N) →
      Epi (factorThruConcreteImage f) :=
  @epi_factorThruConcreteImage.{0, 1}

example : (A : Type) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{0, 1} A} → (f : M ⟶ N) →
      MonoFactorisation f :=
  @concreteImageMonoFactorisation.{0, 1}

example : (A : Type) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{0, 1} A} → (f : M ⟶ N) →
      StrongEpiMonoFactorisation f :=
  @concreteImageStrongEpiMonoFactorisation.{0, 1}

example : (A : Type) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{0, 1} A} → (f : M ⟶ N) →
      IsImage (concreteImageMonoFactorisation f) :=
  @concreteImageIsImage.{0, 1}

example : (A : Type) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{0, 1} A} → (f : M ⟶ N) →
      Limits.image f ≅ concreteImage f :=
  @imageIsoConcrete.{0, 1}

example : (A : Type) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{0, 1} A} → (f : M ⟶ N) →
      concreteImage f ≅ concreteKernel (concreteCokernelπ f) :=
  @concreteImageIsoKernelCokernel.{0, 1}

example : (A : Type) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{0, 1} A} → (f : M ⟶ N) →
      Abelian.image f ≅ concreteImage f :=
  @abelianImageIsoConcrete.{0, 1}

example : (A : Type 1) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{1, 0} A} → (f : M ⟶ N) →
      NonUnitalModuleCat.{1, 0} A :=
  @concreteImage.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{1, 0} A} → (f : M ⟶ N) →
      concreteImage f ⟶ N :=
  @concreteImageι.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{1, 0} A} → (f : M ⟶ N) →
      M ⟶ concreteImage f :=
  @factorThruConcreteImage.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{1, 0} A} → (f : M ⟶ N) →
      Mono (concreteImageι f) :=
  @mono_concreteImageι.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{1, 0} A} → (f : M ⟶ N) →
      Epi (factorThruConcreteImage f) :=
  @epi_factorThruConcreteImage.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{1, 0} A} → (f : M ⟶ N) →
      MonoFactorisation f :=
  @concreteImageMonoFactorisation.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{1, 0} A} → (f : M ⟶ N) →
      StrongEpiMonoFactorisation f :=
  @concreteImageStrongEpiMonoFactorisation.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{1, 0} A} → (f : M ⟶ N) →
      IsImage (concreteImageMonoFactorisation f) :=
  @concreteImageIsImage.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{1, 0} A} → (f : M ⟶ N) →
      Limits.image f ≅ concreteImage f :=
  @imageIsoConcrete.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{1, 0} A} → (f : M ⟶ N) →
      concreteImage f ≅ concreteKernel (concreteCokernelπ f) :=
  @concreteImageIsoKernelCokernel.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{1, 0} A} → (f : M ⟶ N) →
      Abelian.image f ≅ concreteImage f :=
  @abelianImageIsoConcrete.{1, 0}

end InterfaceChecks

end Langlands.Algebra.NonUnitalModuleCat
