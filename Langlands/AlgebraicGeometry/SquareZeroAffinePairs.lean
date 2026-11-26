import Langlands.AlgebraicGeometry.AffineSchemePushoutProof
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-! # Affine pushouts for comparing lifts across a square-zero ideal -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Ring

namespace Langlands.AlgebraicGeometry.SquareZeroAffinePairs

/-- The contravariant map on spectra of unbundled commutative rings. -/
abbrev specMap {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :=
  Spec.map (CommRingCat.ofHom f)

@[reassoc]
theorem specMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    specMap (g.comp f) = specMap g ≫ specMap f :=
  Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

private theorem isPullback_of_elements {A B C D : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (i : A →+* B) (j : A →+* C) (f : B →+* D) (g : C →+* D)
    (hw : ∀ a, f (i a) = g (j a))
    (hinj : ∀ a a', i a = i a' → j a = j a' → a = a')
    (hsurj : ∀ b c, f b = g c → ∃ a, i a = b ∧ j a = c) :
    IsPullback (CommRingCat.ofHom i) (CommRingCat.ofHom j)
      (CommRingCat.ofHom f) (CommRingCat.ofHom g) := by
  have hw' : CommRingCat.ofHom i ≫ CommRingCat.ofHom f =
      CommRingCat.ofHom j ≫ CommRingCat.ofHom g := CommRingCat.hom_ext (RingHom.ext hw)
  let : ReflectsLimit (cospan (CommRingCat.ofHom f) (CommRingCat.ofHom g)) (forget CommRingCat) :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  apply IsPullback.of_map (forget CommRingCat) hw'
  rw [Types.isPullback_iff]
  refine ⟨by rw [← Functor.map_comp, ← Functor.map_comp, hw'], ?_, ?_⟩
  · rintro a a' ⟨h₁, h₂⟩
    exact hinj a a' h₁ h₂
  · intro b c h
    exact hsurj b c h

/-- The canonical right action associated to a module over a commutative ring. -/
scoped instance (priority := 100) oppositeModule (C M : Type u) [CommRing C]
    [AddCommGroup M] [Module C M] : Module Cᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id C).fromOpposite fun _ _ ↦ mul_comm _ _)

scoped instance (priority := 100) centralModule (C M : Type u) [CommRing C]
    [AddCommGroup M] [Module C M] : IsCentralScalar C M where
  op_smul_eq_smul _ _ := rfl

open scoped SquareZeroAffinePairs

section Split

variable {C D : Type u} [CommRing C] [CommRing D]
  {M N : Type u} [AddCommGroup M] [Module C M] [Module Cᵐᵒᵖ M] [IsCentralScalar C M]
  [AddCommGroup N] [Module D N] [Module Dᵐᵒᵖ N] [IsCentralScalar D N]

abbrev projection : (TrivSqZeroExt C M) →+* C := (TrivSqZeroExt.fstHom C C M).toRingHom

abbrev inclusion : C →+* (TrivSqZeroExt C M) := TrivSqZeroExt.inlHom C M

/-- A map between split extensions from a base map and a semilinear coefficient map. -/
def splitMap (f : C →+* D) (g : M →ₛₗ[f] N) :
    (TrivSqZeroExt C M) →+* (TrivSqZeroExt D N) where
  toFun z := ⟨f z.fst, g z.snd⟩
  map_one' := TrivSqZeroExt.ext (map_one f) (map_zero g)
  map_zero' := TrivSqZeroExt.ext (map_zero f) (map_zero g)
  map_add' z w := TrivSqZeroExt.ext (map_add f _ _) (map_add g _ _)
  map_mul' z w := TrivSqZeroExt.ext (map_mul f _ _) (by
    change g (z.fst • w.snd + MulOpposite.op w.fst • z.snd) =
      f z.fst • g w.snd + MulOpposite.op (f w.fst) • g z.snd
    simp only [op_smul_eq_smul, map_add, map_smulₛₗ])

@[simp] theorem splitMap_fst (f : C →+* D) (g : M →ₛₗ[f] N) (z : TrivSqZeroExt C M) :
    (splitMap f g z).fst = f z.fst := rfl

@[simp] theorem splitMap_snd (f : C →+* D) (g : M →ₛₗ[f] N) (z : TrivSqZeroExt C M) :
    (splitMap f g z).snd = g z.snd := rfl

variable (C M)

abbrev first : (TrivSqZeroExt C (M × M)) →+* (TrivSqZeroExt C M) :=
  splitMap (RingHom.id C) (LinearMap.fst C M M)

abbrev second : (TrivSqZeroExt C (M × M)) →+* (TrivSqZeroExt C M) :=
  splitMap (RingHom.id C) (LinearMap.snd C M M)

abbrev total : (TrivSqZeroExt C (M × M)) →+* (TrivSqZeroExt C M) :=
  splitMap (RingHom.id C) (LinearMap.fst C M M + LinearMap.snd C M M)

/-- Two split perturbations with a common reduction form a pushout of affine tests. -/
theorem pushout_split : IsPushout (specMap (projection (C := C) (M := M)))
    (specMap (projection (C := C) (M := M))) (specMap (first C M)) (specMap (second C M)) := by
  apply affineSchemePushout _ _ _ _ _ _ _ _ (fun c ↦ ⟨TrivSqZeroExt.inl c, rfl⟩)
  apply isPullback_of_elements
  · intro z; rfl
  · intro z w h₁ h₂
    have hf := congrArg (fun x : TrivSqZeroExt C M ↦ x.fst) h₁
    have hs₁ := congrArg (fun x : TrivSqZeroExt C M ↦ x.snd) h₁
    have hs₂ := congrArg (fun x : TrivSqZeroExt C M ↦ x.snd) h₂
    exact TrivSqZeroExt.ext (by simpa using hf)
      (Prod.ext (by simpa using hs₁) (by simpa using hs₂))
  · intro z w h
    refine ⟨⟨z.fst, (z.snd, w.snd)⟩, TrivSqZeroExt.ext rfl rfl, TrivSqZeroExt.ext ?_ rfl⟩
    change z.fst = w.fst
    exact h

end Split

section Pairs

variable {C : Type u} [CommRing C] (J : Ideal C)

/-- The second evaluation on the ring of pairs congruent modulo `J`. -/
def evaluation (hJ : J ^ 2 = ⊥) : (TrivSqZeroExt C J) →+* C :=
  (TrivSqZeroExt.lift (AlgHom.id C C) J.subtype (by
    intro x y
    exact Ideal.mem_bot.mp (hJ ▸ (pow_two J).symm ▸ Ideal.mul_mem_mul x.property y.property))
    (by intro _ _; rfl) (by intro _ _; rw [op_smul_eq_smul]; exact mul_comm _ _)).toRingHom

@[simp] theorem evaluation_apply (hJ : J ^ 2 = ⊥) (z : TrivSqZeroExt C J) :
    evaluation J hJ z = z.fst + z.snd.val := rfl

/-- The ring of pairs is the pullback of the two reductions modulo the square-zero ideal. -/
theorem pushout_pairs (hJ : J ^ 2 = ⊥) :
    IsPushout (specMap (Ideal.Quotient.mk J)) (specMap (Ideal.Quotient.mk J))
      (specMap (projection (C := C) (M := J))) (specMap (evaluation J hJ)) := by
  apply affineSchemePushout _ _ _ _ _ _ _ _ Ideal.Quotient.mk_surjective
  apply isPullback_of_elements
  · intro z
    simp [evaluation_apply, Ideal.Quotient.eq_zero_iff_mem.mpr z.snd.property]
  · intro z w h₁ h₂
    apply TrivSqZeroExt.ext h₁
    apply Subtype.ext
    change z.fst = w.fst at h₁
    change z.fst + z.snd.val = w.fst + w.snd.val at h₂
    rw [h₁] at h₂
    exact add_left_cancel h₂
  · intro a b h
    have hb : b - a ∈ J := Ideal.Quotient.eq.1 h.symm
    refine ⟨⟨a, ⟨b - a, hb⟩⟩, rfl, ?_⟩
    change a + (b - a) = b
    abel

private theorem smul_eq_zero (hJ : J ^ 2 = ⊥) (x y : J) : (x : C) • y = 0 := by
  apply Subtype.ext
  exact Ideal.mem_bot.mp (hJ ▸ (pow_two J).symm ▸ Ideal.mul_mem_mul x.property y.property)

/-- The second pair in `(a, a + x, a + x + y)` has base coordinate `a + x`. -/
def shiftedSecond (hJ : J ^ 2 = ⊥) :
    (TrivSqZeroExt C (J × J)) →+* (TrivSqZeroExt C J) where
  toFun z := ⟨z.fst + z.snd.1.val, z.snd.2⟩
  map_one' := TrivSqZeroExt.ext (add_zero 1) rfl
  map_zero' := TrivSqZeroExt.ext (add_zero 0) rfl
  map_add' z w := TrivSqZeroExt.ext
    (map_add ((evaluation J hJ).comp (first C J)) z w) rfl
  map_mul' z w := TrivSqZeroExt.ext
    (map_mul ((evaluation J hJ).comp (first C J)) z w) (by
      change z.fst • w.snd.2 + MulOpposite.op w.fst • z.snd.2 =
        (z.fst + z.snd.1.val) • w.snd.2 + MulOpposite.op (w.fst + w.snd.1.val) • z.snd.2
      simp only [op_smul_eq_smul, add_smul, smul_eq_zero J hJ, add_zero])

@[simp] theorem shiftedSecond_fst (hJ : J ^ 2 = ⊥) (z : TrivSqZeroExt C (J × J)) :
    (shiftedSecond J hJ z).fst = z.fst + z.snd.1.val := rfl

@[simp] theorem shiftedSecond_snd (hJ : J ^ 2 = ⊥) (z : TrivSqZeroExt C (J × J)) :
    (shiftedSecond J hJ z).snd = z.snd.2 := rfl

/-- The ring of triples is the pullback of the successive pair rings at their middle term. -/
theorem pushout_triple (hJ : J ^ 2 = ⊥) :
    IsPushout (specMap (evaluation J hJ)) (specMap (projection (C := C) (M := J)))
      (specMap (first C J)) (specMap (shiftedSecond J hJ)) := by
  apply affineSchemePushout _ _ _ _ _ _ _ _ (fun c ↦ ⟨TrivSqZeroExt.inl c, add_zero c⟩)
  apply isPullback_of_elements
  · intro z; rfl
  · intro z w h₁ h₂
    have hf := congrArg (fun a : TrivSqZeroExt C J ↦ a.fst) h₁
    have hs₁ := congrArg (fun a : TrivSqZeroExt C J ↦ a.snd) h₁
    have hs₂ := congrArg (fun a : TrivSqZeroExt C J ↦ a.snd) h₂
    exact TrivSqZeroExt.ext (by simpa using hf)
      (Prod.ext (by simpa using hs₁) (by simpa using hs₂))
  · intro z w h
    exact ⟨⟨z.fst, (z.snd, w.snd)⟩, TrivSqZeroExt.ext rfl rfl, TrivSqZeroExt.ext h rfl⟩

@[simp] theorem projection_comp_total :
    projection.comp (total C J) = projection.comp (first C J) := RingHom.ext fun _ ↦ rfl

@[simp] theorem evaluation_comp_total (hJ : J ^ 2 = ⊥) :
    (evaluation J hJ).comp (total C J) = (evaluation J hJ).comp (shiftedSecond J hJ) := by
  ext z
  change z.fst + (z.snd.1.val + z.snd.2.val) = z.fst + z.snd.1.val + z.snd.2.val
  exact (add_assoc _ _ _).symm

variable {D : Type u} [CommRing D] [Module D J] [Module Dᵐᵒᵖ J] [IsCentralScalar D J]
  (f : C →+* D)
  (hsmul : ∀ (c : C) (x : J), f c • x = c • x)

/-- Reducing the base coordinate keeps the infinitesimal coefficient. -/
def splitReduction : (TrivSqZeroExt C J) →+* (TrivSqZeroExt D J) :=
  splitMap f
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun c x ↦ (hsmul c x).symm }

@[simp] theorem splitReduction_fst (x : TrivSqZeroExt C J) :
    (splitReduction J f hsmul x).fst = f x.fst := rfl

@[simp] theorem splitReduction_snd (x : TrivSqZeroExt C J) :
    (splitReduction J f hsmul x).snd = x.snd := rfl

/-- The ring of pairs also glues the original test to the split reduced test. -/
theorem pushout_splitReduction (hf : Function.Surjective f) :
    IsPushout (specMap f) (specMap (projection (C := D) (M := J)))
      (specMap (projection (C := C) (M := J))) (specMap (splitReduction J f hsmul)) := by
  apply affineSchemePushout _ _ _ _ _ _ _ _ hf
  apply isPullback_of_elements
  · intro z; rfl
  · intro z w h₁ h₂
    have hs := congrArg (fun x : TrivSqZeroExt D J ↦ x.snd) h₂
    exact TrivSqZeroExt.ext h₁ hs
  · intro c z h
    exact ⟨⟨c, z.snd⟩, rfl, TrivSqZeroExt.ext h rfl⟩

/-- Reducing the base coordinate of a triple retains both increments. -/
def splitReductionTriple : (TrivSqZeroExt C (J × J)) →+* (TrivSqZeroExt D (J × J)) :=
  splitMap f
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun c x ↦ Prod.ext (hsmul c x.1).symm (hsmul c x.2).symm }

@[simp] theorem splitReduction_comp_first :
    (splitReduction J f hsmul).comp (first C J) =
      (first D J).comp (splitReductionTriple J f hsmul) := RingHom.ext fun _ ↦ rfl

@[simp] theorem splitReduction_comp_total :
    (splitReduction J f hsmul).comp (total C J) =
      (total D J).comp (splitReductionTriple J f hsmul) := RingHom.ext fun _ ↦ rfl

@[simp] theorem splitReduction_comp_shiftedSecond (hJ : J ^ 2 = ⊥)
    (hkill : ∀ x : J, f x = 0) :
    (splitReduction J f hsmul).comp (shiftedSecond J hJ) =
      (second D J).comp (splitReductionTriple J f hsmul) := by
  ext z
  · change f (z.fst + z.snd.1.val) = f z.fst
    rw [map_add, hkill, add_zero]
  · rfl

end Pairs

end Langlands.AlgebraicGeometry.SquareZeroAffinePairs
