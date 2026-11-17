import Langlands.GroupScheme.FppfExtensionClosedImmersionStatement
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent

/-! # Descent proof of closedness for homomorphisms of extensions -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.FppfExtension

open MorphismProperty

instance closedImmersion_fpqcDescent :
    DescendsAlong @IsClosedImmersion (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [IsClosedImmersion.eq_proper_inf_monomorphisms, ← diagonal_isomorphisms]
  infer_instance

variable {S : Scheme.{u}} {G Q G' Q' : GroupScheme S}

/-- The kernel-valued difference of two points with equal quotient image. -/
def delta (q : G ⟶ Q) {T : Over S} (x y : T ⟶ G.X)
    (h : x ≫ q.hom.hom = y ≫ q.hom.hom) : T ⟶ (kernel q).X :=
  pullback.lift x y h ≫ KernelPair.difference q

@[reassoc (attr := simp)]
theorem delta_ι (q : G ⟶ Q) {T : Over S} (x y : T ⟶ G.X)
    (h : x ≫ q.hom.hom = y ≫ q.hom.hom) :
    delta q x y h ≫ (kernelι q).hom.hom = x⁻¹ * y := by
  simp only [delta, Category.assoc, KernelPair.difference_ι,
    MonObj.comp_mul, GrpObj.comp_inv, pullback.lift_fst, pullback.lift_snd]

variable (q : G ⟶ Q) (q' : G' ⟶ Q') (f : G ⟶ G') (c : Q ⟶ Q')
  (hf : f.hom.hom ≫ q'.hom.hom = q.hom.hom ≫ c.hom.hom)

/-- Factor the middle homomorphism through the pullback of the target extension. -/
def factor : G.X ⟶ pullback q'.hom.hom c.hom.hom :=
  pullback.lift f.hom.hom q.hom.hom hf

@[reassoc (attr := simp)]
theorem factor_fst :
    factor q q' f c hf ≫ pullback.fst _ _ = f.hom.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem factor_snd :
    factor q q' f c hf ≫ pullback.snd _ _ = q.hom.hom :=
  pullback.lift_snd _ _ _

/-- Act by the target kernel after applying the middle homomorphism. -/
def coverAction : G.X ⊗ (kernel q').X ⟶ G'.X :=
  (fst _ _ ≫ f.hom.hom) * (snd _ _ ≫ (kernelι q').hom.hom)

include hf in
theorem coverAction_comp :
    coverAction q' f ≫ q'.hom.hom =
      (fst _ _ ≫ q.hom.hom) ≫ c.hom.hom := by
  rw [coverAction, MonObj.mul_comp, Category.assoc, hf, Category.assoc,
    (kernel_isPullback q').w]
  change _ * (snd _ _ ≫ (1 : (kernel q').X ⟶ Q'.X)) = _
  rw [MonObj.comp_one, mul_one, Category.assoc]

/-- The source quotient cover, translated by the target kernel. -/
def cover : G.X ⊗ (kernel q').X ⟶ pullback q'.hom.hom c.hom.hom :=
  pullback.lift (coverAction q' f) (fst _ _ ≫ q.hom.hom)
    (coverAction_comp q q' f c hf)

@[reassoc (attr := simp)]
theorem cover_fst :
    cover q q' f c hf ≫ pullback.fst _ _ = coverAction q' f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem cover_snd :
    cover q q' f c hf ≫ pullback.snd _ _ = fst _ _ ≫ q.hom.hom :=
  pullback.lift_snd _ _ _

/-- The translated cover is a base change of the source quotient. -/
theorem cover_isPullback :
    IsPullback (fst G.X (kernel q').X) (cover q q' f c hf)
      q.hom.hom (pullback.snd q'.hom.hom c.hom.hom) := by
  refine IsPullback.mk' (cover_snd q q' f c hf).symm ?_ ?_
  · intro T x y hx hy
    apply CartesianMonoidalCategory.hom_ext
    · exact hx
    · apply (cancel_mono (kernelι q').hom.hom).mp
      have h := congrArg (fun z => z ≫ pullback.fst q'.hom.hom c.hom.hom) hy
      simp only [Category.assoc, cover_fst, coverAction, MonObj.comp_mul] at h
      simp only [← Category.assoc] at h
      rw [hx] at h
      exact mul_left_cancel h
  · intro T g p h
    have hd : (g ≫ f.hom.hom) ≫ q'.hom.hom =
        (p ≫ pullback.fst q'.hom.hom c.hom.hom) ≫ q'.hom.hom := by
      calc
        (g ≫ f.hom.hom) ≫ q'.hom.hom =
            (g ≫ q.hom.hom) ≫ c.hom.hom := by simp only [Category.assoc, hf]
        _ = (p ≫ pullback.snd _ _) ≫ c.hom.hom := by rw [h]
        _ = (p ≫ pullback.fst _ _) ≫ q'.hom.hom := by
          simp only [Category.assoc, pullback.condition]
    let d := delta q' (g ≫ f.hom.hom)
      (p ≫ pullback.fst q'.hom.hom c.hom.hom) hd
    refine ⟨lift g d, lift_fst _ _, ?_⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, cover_fst, coverAction, MonObj.comp_mul,
        lift_fst_assoc, lift_snd_assoc]
      rw [delta_ι]
      exact mul_inv_cancel_left _ _
    · simp only [Category.assoc, cover_snd, lift_fst_assoc]
      exact h

variable (a : kernel q ⟶ kernel q')
  (ha : a.hom.hom ≫ (kernelι q').hom.hom = (kernelι q).hom.hom ≫ f.hom.hom)

include ha in
theorem action_naturality :
    (𝟙 G.X ⊗ₘ a.hom.hom) ≫ coverAction q' f =
      KernelPair.action q ≫ f.hom.hom := by
  simp only [coverAction, KernelPair.action, MonObj.comp_mul,
    tensorHom_fst_assoc, tensorHom_snd_assoc, Category.id_comp,
    Category.assoc, ha, MonObj.mul_comp]

include ha in
/-- Pulling the factorization back to the cover gives the product of the
identity and the kernel homomorphism. -/
theorem factor_isPullback :
    IsPullback (𝟙 G.X ⊗ₘ a.hom.hom) (KernelPair.action q)
      (cover q q' f c hf) (factor q q' f c hf) := by
  refine IsPullback.mk' ?_ ?_ ?_
  · apply pullback.hom_ext
    · simp only [Category.assoc, cover_fst, factor_fst]
      exact action_naturality q q' f a ha
    · simp only [Category.assoc, cover_snd, factor_snd,
        tensorHom_fst_assoc, Category.id_comp]
      exact (KernelPair.action_comp q).symm
  · intro T x y hx hy
    apply (KernelPair.isPullback q).hom_ext
    · have h := congrArg (fun z => z ≫ fst G.X (kernel q').X) hx
      simpa only [Category.assoc, tensorHom_fst, Category.comp_id] using h
    · exact hy
  · intro T z b h
    have hq : (z ≫ fst G.X (kernel q').X) ≫ q.hom.hom = b ≫ q.hom.hom := by
      have h' := congrArg (fun w => w ≫ pullback.snd q'.hom.hom c.hom.hom) h
      simpa only [Category.assoc, cover_snd, factor_snd] using h'
    let d := delta q (z ≫ fst G.X (kernel q').X) b hq
    have hd : d ≫ a.hom.hom = z ≫ snd G.X (kernel q').X := by
      apply (cancel_mono (kernelι q').hom.hom).mp
      rw [Category.assoc, ha, ← Category.assoc, delta_ι,
        MonObj.mul_comp, GrpObj.inv_comp]
      have h' := congrArg (fun w => w ≫ pullback.fst q'.hom.hom c.hom.hom) h
      simp only [Category.assoc, cover_fst, factor_fst, coverAction,
        MonObj.comp_mul] at h'
      simp only [← Category.assoc] at h'
      rw [← h', inv_mul_cancel_left]
    refine ⟨lift (z ≫ fst _ _) d, ?_, ?_⟩
    · apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, tensorHom_fst, Category.comp_id, lift_fst]
      · simpa only [Category.assoc, tensorHom_snd, lift_snd_assoc] using hd
    · simp only [KernelPair.action, MonObj.comp_mul, lift_fst, lift_snd_assoc]
      rw [delta_ι]
      exact mul_inv_cancel_left _ _

/-- Multiplying the kernel map by the identity is its base change. -/
theorem kernelProduct_isPullback :
    IsPullback (𝟙 G.X ⊗ₘ a.hom.hom) (snd G.X (kernel q).X)
      (snd G.X (kernel q').X) a.hom.hom := by
  refine IsPullback.mk' (tensorHom_snd _ _) ?_ ?_
  · intro T x y hx hy
    apply CartesianMonoidalCategory.hom_ext
    · have h := congrArg (fun z => z ≫ fst G.X (kernel q').X) hx
      simpa only [Category.assoc, tensorHom_fst, Category.comp_id] using h
    · exact hy
  · intro T z k h
    refine ⟨lift (z ≫ fst _ _) k, ?_, lift_snd _ _⟩
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, Category.comp_id, lift_fst]
    · simp only [Category.assoc, tensorHom_snd, lift_snd_assoc]
      exact h.symm

end Langlands.GroupScheme.FppfExtension

namespace Langlands.GroupScheme

open FppfExtension

/-- Closedness of the kernel and quotient maps implies closedness of the
homomorphism of extensions, by fppf descent. -/
theorem fppfExtensionClosedImmersion : FppfExtensionClosedImmersionStatement.{u} := by
  intro S G Q G' Q' q q' f c a hf ha hflat hsurj hlfp hcloseda hclosedc
  have hf' : f.hom.hom ≫ q'.hom.hom = q.hom.hom ≫ c.hom.hom :=
    congrArg (fun h => h.hom.hom) hf
  have ha' : a.hom.hom ≫ (kernelι q').hom.hom =
      (kernelι q).hom.hom ≫ f.hom.hom :=
    congrArg (fun h => h.hom.hom) ha
  have hcover := (cover_isPullback q q' f c hf').map (Over.forget S)
  simp only [Over.forget_map] at hcover
  have : Flat (cover q q' f c hf').left :=
    MorphismProperty.of_isPullback (P := @Flat) hcover hflat
  have : Surjective (cover q q' f c hf').left :=
    MorphismProperty.of_isPullback (P := @Surjective) hcover hsurj
  have : LocallyOfFinitePresentation (cover q q' f c hf').left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hcover hlfp
  have hprod := (kernelProduct_isPullback q q' a).map (Over.forget S)
  simp only [Over.forget_map] at hprod
  have : IsClosedImmersion (𝟙 G.X ⊗ₘ a.hom.hom).left :=
    MorphismProperty.of_isPullback hprod.flip hcloseda
  have hcart := (factor_isPullback q q' f c hf' a ha').map (Over.forget S)
  simp only [Over.forget_map] at hcart
  have : IsClosedImmersion (factor q q' f c hf').left :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := @IsClosedImmersion)
      (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
      hcart
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have hbase := (IsPullback.of_hasPullback q'.hom.hom c.hom.hom).map (Over.forget S)
  simp only [Over.forget_map] at hbase
  have : IsClosedImmersion (pullback.fst q'.hom.hom c.hom.hom).left :=
    MorphismProperty.of_isPullback hbase.flip hclosedc
  have hfactor : (factor q q' f c hf').left ≫
      (pullback.fst q'.hom.hom c.hom.hom).left = f.hom.hom.left :=
    congrArg Over.Hom.left (factor_fst q q' f c hf')
  rw [← hfactor]
  infer_instance

end Langlands.GroupScheme
