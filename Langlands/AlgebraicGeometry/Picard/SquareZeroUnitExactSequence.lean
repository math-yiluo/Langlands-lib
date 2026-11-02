import Langlands.AlgebraicGeometry.Picard.SquareZeroUnitSheaves
import Langlands.AlgebraicGeometry.Picard.NilpotentUnitReduction
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Topology.Sheaves.Abelian

/-! # The actual unit-sheaf sequence of a square-zero closed immersion -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.SquareZeroUnitExactSequence

open SquareZeroUnitKernels NilpotentUnitReduction

section Sheaves

variable {X : TopCat.{u}} {F G : X.Presheaf CommRingCat.{u}}
  (η : F ⟶ G) (hF : TopCat.Presheaf.IsSheaf F) (hG : TopCat.Presheaf.IsSheaf G)
  (h : ∀ U, SquareZeroKernel (η.app U).hom)

/-- Inclusion of the actual units mapped to one into the full unit sheaf. -/
def unitKernelι : unitKernelSheaf η hF hG h ⟶ unitsSheaf F hF :=
  ⟨{ app U := AddCommGrpCat.ofHom (UnitKernel (η.app U).hom).subtype.toAdditive
     naturality U V k := by
       apply AddCommGrpCat.ext
       intro a
       rfl }⟩

lemma unitKernelι_comp :
    unitKernelι η hF hG h ≫ unitsSheafMap η hF hG = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro a
  exact congrArg Additive.ofMul a.toMul.property

/-- A morphism annihilated by reduction factors through the actual unit kernel. -/
def unitKernelLift {A : X.Sheaf AddCommGrpCat.{u}} (k : A ⟶ unitsSheaf F hF)
    (hk : k ≫ unitsSheafMap η hF hG = 0) :
    A ⟶ unitKernelSheaf η hF hG h :=
  ⟨{ app U := AddCommGrpCat.ofHom
       (((show A.obj.obj U →+ Additive ((F.obj U)ˣ) from
         (k.hom.app U).hom).toMultiplicativeLeft.codRestrict
         (UnitKernel (η.app U).hom) (fun a ↦ by
           exact congrArg Additive.toMul
             (congrArg (fun q ↦ (q.hom.app U) a.toAdd) hk))).toAdditiveRight)
     naturality U V j := by
       apply AddCommGrpCat.ext
       intro a
       apply Additive.toMul.injective
       apply Subtype.ext
       exact congrArg Additive.toMul
         (ConcreteCategory.congr_hom (k.hom.naturality j) a) }⟩

lemma unitKernelLift_ι {A : X.Sheaf AddCommGrpCat.{u}} (k : A ⟶ unitsSheaf F hF)
    (hk : k ≫ unitsSheafMap η hF hG = 0) :
    unitKernelLift η hF hG h k hk ≫ unitKernelι η hF hG h = k := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro a
  rfl

/-- The actual sectionwise subgroup is also the categorical sheaf kernel. -/
def unitKernelι_isKernel :
    IsLimit (KernelFork.ofι (unitKernelι η hF hG h) (unitKernelι_comp η hF hG h)) :=
  KernelFork.IsLimit.ofι _ _ (fun k hk ↦ unitKernelLift η hF hG h k hk)
    (fun k hk ↦ unitKernelLift_ι η hF hG h k hk) (by
      intro A k hk m hm
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply AddCommGrpCat.ext
      intro a
      apply Additive.toMul.injective
      apply Subtype.ext
      exact congrArg Additive.toMul (congrArg (fun q ↦ (q.hom.app U) a) hm))

/-- The map from the actual additive kernel to units is sectionwise `a ↦ 1+a`. -/
def oneAdd : additiveKernelSheaf η hF hG ⟶ unitsSheaf F hF :=
  (kernelSheafIso η hF hG h).hom ≫ unitKernelι η hF hG h

@[simp]
lemma oneAdd_app_val (U : (Opens X)ᵒᵖ) (a : RingHom.ker (η.app U).hom) :
    (show (F.obj U)ˣ from ((oneAdd η hF hG h).hom.app U a).toMul).val =
      1 + (a : F.obj U) := rfl

lemma oneAdd_comp : oneAdd η hF hG h ≫ unitsSheafMap η hF hG = 0 := by
  rw [oneAdd, Category.assoc, unitKernelι_comp, comp_zero]

/-- The `1+a` map is the categorical kernel of actual unit reduction. -/
def oneAdd_isKernel :
    IsLimit (KernelFork.ofι (oneAdd η hF hG h) (oneAdd_comp η hF hG h)) :=
  IsKernel.isoKernel (unitsSheafMap η hF hG) (oneAdd η hF hG h)
    (unitKernelι_isKernel η hF hG h) (kernelSheafIso η hF hG h) rfl

end Sheaves

section Schemes

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]

/-- The actual square-zero ideal embeds into units by `a ↦ 1+a`. -/
def schemeOneAdd (hi : i.ker ^ 2 = ⊥) :
    schemeAdditiveKernelSheaf i ⟶ unitsSheaf X.presheaf X.sheaf.property :=
  oneAdd i.c X.sheaf.property
    (TopCat.Sheaf.pushforward_sheaf_of_sheaf i.base Y.sheaf.property)
    (fun U ↦ squareZeroKernel_app i hi U.unop)

@[simp]
lemma schemeOneAdd_app_val (hi : i.ker ^ 2 = ⊥) (U : X.Opens)
    (a : RingHom.ker (i.app U).hom) :
    (show (X.presheaf.obj (op U))ˣ from
      ((schemeOneAdd i hi).hom.app (op U) a).toMul).val =
      1 + (a : X.presheaf.obj (op U)) := rfl

/-- The actual ideal kernel and the two actual structure-unit sheaves. -/
def schemeUnitSequence (hi : i.ker ^ 2 = ⊥) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) where
  f := schemeOneAdd i hi
  g := unitsReduction i
  zero := oneAdd_comp i.c X.sheaf.property
    (TopCat.Sheaf.pushforward_sheaf_of_sheaf i.base Y.sheaf.property)
    (fun U ↦ squareZeroKernel_app i hi U.unop)

/-- The first arrow is the actual categorical kernel of the second. -/
def schemeUnitSequence_isKernel (hi : i.ker ^ 2 = ⊥) :
    IsLimit (KernelFork.ofι (schemeUnitSequence i hi).f (schemeUnitSequence i hi).zero) :=
  oneAdd_isKernel i.c X.sheaf.property
    (TopCat.Sheaf.pushforward_sheaf_of_sheaf i.base Y.sheaf.property)
    (fun U ↦ squareZeroKernel_app i hi U.unop)

/-- The units of any square-zero closed immersion form a short exact sheaf sequence. -/
lemma schemeUnitSequence_shortExact (hi : i.ker ^ 2 = ⊥) :
    (schemeUnitSequence i hi).ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · exact (schemeUnitSequence i hi).exact_of_f_is_kernel (schemeUnitSequence_isKernel i hi)
  · exact mono_of_isLimit_fork (schemeUnitSequence_isKernel i hi)
  · exact unitsReduction_epi i ⟨2, hi⟩

end Schemes

end Langlands.AlgebraicGeometry.Picard.SquareZeroUnitExactSequence
