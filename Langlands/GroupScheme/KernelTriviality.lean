import Langlands.AbelianScheme.GroupScheme
import Langlands.AbelianScheme.KernelBaseChange

/-! # Monomorphisms and trivial scheme-theoretic kernels -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S B : Scheme.{u}} {G H : GroupScheme S}

/-- The structure map of the full kernel of a monomorphism is an isomorphism. -/
theorem kernel_hom_isIso_of_mono (f : G ⟶ H) [Mono f.hom.hom] :
    IsIso (kernel f).X.hom := by
  have : Mono f.hom.hom.left := inferInstance
  have : Mono (kernel f).X.hom := (kernel_isPullback_scheme f).mono_snd_of_mono
  have : IsSplitEpi (kernel f).X.hom :=
    ⟨⟨η[(kernel f).X].left, η[(kernel f).X].w⟩⟩
  exact isIso_of_mono_of_isSplitEpi _

/-- A group-scheme homomorphism whose full kernel is the unit group is a monomorphism. -/
theorem mono_of_kernel_hom_isIso (f : G ⟶ H) [IsIso (kernel f).X.hom] :
    Mono f.hom.hom := by
  constructor
  intro T a b hab
  have hsub : Subsingleton (T ⟶ (kernel f).X) := by
    constructor
    intro x y
    apply Over.OverMorphism.ext
    exact (cancel_mono (kernel f).X.hom).mp (x.w.trans y.w.symm)
  have hinj : Function.Injective ((yonedaGrp.map f).app (.op T)).hom := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro x hx
    let z : ((yonedaGrp.map f).app (.op T)).hom.ker := ⟨x, hx⟩
    have hz : z = 1 := by
      apply (kernelPointsEquiv f T).symm.injective
      exact hsub.elim _ _
    exact congrArg Subtype.val hz
  exact hinj hab

/-- A homomorphism is a monomorphism exactly when its full kernel is the unit group. -/
theorem mono_iff_kernel_hom_isIso (f : G ⟶ H) :
    Mono f.hom.hom ↔ IsIso (kernel f).X.hom := by
  constructor
  · intro hf
    let := hf
    exact kernel_hom_isIso_of_mono f
  · intro hf
    let := hf
    exact mono_of_kernel_hom_isIso f

/-- The canonical isomorphism from the full kernel of a monomorphism to the base. -/
def kernelBaseIsoOfMono (f : G ⟶ H) [Mono f.hom.hom] : (kernel f).X.left ≅ S := by
  let := kernel_hom_isIso_of_mono f
  exact asIso (kernel f).X.hom

@[simp]
theorem kernelBaseIsoOfMono_hom (f : G ⟶ H) [Mono f.hom.hom] :
    (kernelBaseIsoOfMono f).hom = (kernel f).X.hom := rfl

/-- The structure map of the base-changed kernel is an isomorphism exactly when
its original homomorphism becomes monomorphic after that base change. -/
theorem baseChange_kernel_hom_isIso_iff (b : B ⟶ S) (f : G ⟶ H) :
    IsIso ((baseChange b).obj (kernel f)).X.hom ↔
      Mono ((baseChange b).map f).hom.hom := by
  let e := kernelBaseChangeIso b f
  constructor
  · intro hf
    let := hf
    apply (mono_iff_kernel_hom_isIso _).mpr
    rw [← Over.w e.inv.hom.hom]
    infer_instance
  · intro hf
    let := hf
    have := kernel_hom_isIso_of_mono ((baseChange b).map f)
    rw [← Over.w e.hom.hom.hom]
    infer_instance

end Langlands.GroupScheme
