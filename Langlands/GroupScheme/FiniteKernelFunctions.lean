import Langlands.AlgebraicGeometry.NoetherianIdealSheafFiniteSupport
import Langlands.GroupScheme.FieldSeparatedProof
import Langlands.AbelianScheme.Kernel
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop

/-! # Finite global functions detecting the full scheme kernel -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem ofIdealTop_iSup {X : Scheme.{u}} {Index : Type v}
    (I : Index → Ideal Γ(X, ⊤)) :
    Scheme.IdealSheafData.ofIdealTop (⨆ i, I i) =
      ⨆ i, Scheme.IdealSheafData.ofIdealTop (I i) := by
  ext U
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_iSup,
    Scheme.IdealSheafData.ideal_iSup, iSup_apply]

private theorem ofIdealTop_sup {X : Scheme.{u}} (I J : Ideal Γ(X, ⊤)) :
    Scheme.IdealSheafData.ofIdealTop (I ⊔ J) =
      Scheme.IdealSheafData.ofIdealTop I ⊔ Scheme.IdealSheafData.ofIdealTop J := by
  ext U
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_sup,
    Scheme.IdealSheafData.ideal_sup, Pi.sup_apply]

variable {k : Type u} [Field k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}

/-- Finitely many augmentation functions whose pullbacks generate the exact
ideal sheaf of the full kernel. -/
structure FiniteKernelDetector (q : G ⟶ Q) where
  functions : Finset Γ(Q.X.left, ⊤)
  vanishes : ∀ a ∈ functions, η[Q.X].left.appTop a = 0
  ideal_eq : (kernelι q).hom.hom.left.ker = Scheme.IdealSheafData.ofIdealTop
    ((Ideal.span (functions : Set Γ(Q.X.left, ⊤))).map q.hom.hom.left.appTop.hom)

private theorem kernelIdeal_eq [IsAffine Q.X.left] (q : G ⟶ Q) :
    (kernelι q).hom.hom.left.ker = Scheme.IdealSheafData.ofIdealTop
      ((RingHom.ker η[Q.X].left.appTop.hom).map q.hom.hom.left.appTop.hom) := by
  have : IsSeparated Q.X.hom := fieldSeparated k Q
  have hpb := kernel_isPullback_scheme q
  rw [← hpb.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    Scheme.ker_of_isAffine, Scheme.IdealSheafData.comap_ofIdealTopFLT]

/-- Choose finite augmentation functions detecting a homomorphism's full kernel
when its source is Noetherian and its target affine. -/
def finiteKernelDetector [IsNoetherian G.X.left] [IsAffine Q.X.left]
    (q : G ⟶ Q) : FiniteKernelDetector q := by
  classical
  let I := RingHom.ker η[Q.X].left.appTop.hom
  let F : I → G.X.left.IdealSheafData := fun a => Scheme.IdealSheafData.ofIdealTop
    ((Ideal.span ({a.val} : Set Γ(Q.X.left, ⊤))).map q.hom.hom.left.appTop.hom)
  have hI : (⨆ a : I, Ideal.span ({a.val} : Set Γ(Q.X.left, ⊤))) = I := by
    rw [← Ideal.span_range_eq_iSup, Subtype.range_coe, Ideal.span_eq]
  have hall : (⨆ a : I, F a) = (kernelι q).hom.hom.left.ker := by
    dsimp only [F]
    rw [← ofIdealTop_iSup, ← Ideal.map_iSup, hI]
    exact (kernelIdeal_eq q).symm
  let t := Langlands.AlgebraicGeometry.NoetherianIdealSheaf.finiteSupSupport F
  have ht := Langlands.AlgebraicGeometry.NoetherianIdealSheaf.finiteSupSupport_spec F
  have hgen (t : Finset I) :
      Scheme.IdealSheafData.ofIdealTop
        ((Ideal.span ((t.image Subtype.val : Finset Γ(Q.X.left, ⊤)) : Set Γ(Q.X.left, ⊤))).map
          q.hom.hom.left.appTop.hom) = t.sup F := by
    induction t using Finset.induction with
    | empty =>
      ext U
      simp [Scheme.IdealSheafData.ofIdealTop_ideal]
    | @insert a t ha ih =>
      simp only [Finset.image_insert, Finset.coe_insert, Ideal.span_insert, Ideal.map_sup,
        ofIdealTop_sup, Finset.sup_insert, ih]
      rfl
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
    exact b.property
  · exact hall.symm.trans (ht.trans (hgen t).symm)

end Langlands.GroupScheme
