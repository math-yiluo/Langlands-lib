import Langlands.GroupScheme.KernelPair
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Kernel domination from a parametrization over a quotient -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.KernelDomination

section Categorical

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {X Y Z W : C}

private theorem mapLeft_isPullback (p : X ⟶ Y) (q : Y ⟶ Z) (r : W ⟶ Z) :
    IsPullback (pullback.fst (p ≫ q) r)
      (pullback.map (p ≫ q) r q r p (𝟙 W) (𝟙 Z) (by simp) (by simp))
      p (pullback.fst q r) := by
  apply IsPullback.of_bot (t := IsPullback.of_hasPullback q r)
  · simpa only [pullback.lift_snd, Category.comp_id] using
      (IsPullback.of_hasPullback (p ≫ q) r)
  · simp

private theorem mapRight_isPullback (p : X ⟶ Y) (q : Y ⟶ Z) (r : W ⟶ Z) :
    IsPullback (pullback.snd r (p ≫ q))
      (pullback.map r (p ≫ q) r q (𝟙 W) p (𝟙 Z) (by simp) (by simp))
      p (pullback.snd r q) := by
  apply IsPullback.of_bot (t := (IsPullback.of_hasPullback r q).flip)
  · simpa only [pullback.lift_fst, Category.comp_id] using
      (IsPullback.of_hasPullback r (p ≫ q)).flip
  · simp

/-- Apply the same morphism to both entries of a pair with equal quotient. -/
def pairMap (a : X ⟶ Z) (q : Y ⟶ Z) (p : X ⟶ Y) (h : p ≫ q = a) :
    pullback a a ⟶ pullback q q :=
  pullback.map a a q q p p (𝟙 Z) (by simp [h]) (by simp [h])

@[reassoc (attr := simp)]
theorem pairMap_fst (a : X ⟶ Z) (q : Y ⟶ Z) (p : X ⟶ Y) (h : p ≫ q = a) :
    pairMap a q p h ≫ pullback.fst q q = pullback.fst a a ≫ p :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pairMap_snd (a : X ⟶ Z) (q : Y ⟶ Z) (p : X ⟶ Y) (h : p ≫ q = a) :
    pairMap a q p h ≫ pullback.snd q q = pullback.snd a a ≫ p :=
  pullback.lift_snd _ _ _

end Categorical

section Schemes

variable {S : Scheme.{u}} {X Y Z : Over S}

/-- Quasi-compactness of a morphism passes to the induced map on fiber pairs. -/
theorem pairMap_quasiCompact
    (a : X ⟶ Z) (q : Y ⟶ Z) (p : X ⟶ Y) (h : p ≫ q = a)
    [QuasiCompact p.left] : QuasiCompact (pairMap a q p h).left := by
  subst a
  let m₁ := pullback.map (p ≫ q) (p ≫ q) q (p ≫ q)
    p (𝟙 X) (𝟙 Z) (by simp) (by simp)
  let m₂ := pullback.map q (p ≫ q) q q
    (𝟙 Y) p (𝟙 Z) (by simp) (by simp)
  have hb₁ : IsPullback (pullback.fst (p ≫ q) (p ≫ q)).left
      m₁.left p.left (pullback.fst q (p ≫ q)).left :=
    (mapLeft_isPullback p q (p ≫ q)).map (Over.forget S)
  have hb₂ : IsPullback (pullback.snd q (p ≫ q)).left
      m₂.left p.left (pullback.snd q q).left :=
    (mapRight_isPullback p q q).map (Over.forget S)
  have : QuasiCompact m₁.left :=
    MorphismProperty.of_isPullback hb₁ inferInstance
  have : QuasiCompact m₂.left :=
    MorphismProperty.of_isPullback hb₂ inferInstance
  have he : m₁ ≫ m₂ = pairMap (p ≫ q) q p rfl := by
    apply pullback.hom_ext <;> simp [m₁, m₂]
  rw [← he]
  change QuasiCompact (m₁.left ≫ m₂.left)
  infer_instance

/-- Flatness of the two quotient maps makes the map on pairs schematically dominant. -/
theorem pairMap_isSchemeTheoreticallyDominant
    (a : X ⟶ Z) (q : Y ⟶ Z) (p : X ⟶ Y) (h : p ≫ q = a)
    [IsSchemeTheoreticallyDominant p.left] [QuasiCompact p.left]
    [Flat a.left] [Flat q.left] :
    IsSchemeTheoreticallyDominant (pairMap a q p h).left := by
  subst a
  let m₁ := pullback.map (p ≫ q) (p ≫ q) q (p ≫ q)
    p (𝟙 X) (𝟙 Z) (by simp) (by simp)
  let m₂ := pullback.map q (p ≫ q) q q
    (𝟙 Y) p (𝟙 Z) (by simp) (by simp)
  have hbf : IsPullback (pullback.fst q (p ≫ q)).left
      (pullback.snd q (p ≫ q)).left q.left (p ≫ q).left :=
    (IsPullback.of_hasPullback q (p ≫ q)).map (Over.forget S)
  have hbs : IsPullback (pullback.fst q q).left
      (pullback.snd q q).left q.left q.left :=
    (IsPullback.of_hasPullback q q).map (Over.forget S)
  have hf : Flat (pullback.fst q (p ≫ q)).left :=
    MorphismProperty.of_isPullback hbf.flip inferInstance
  have hs : Flat (pullback.snd q q).left :=
    MorphismProperty.of_isPullback hbs inferInstance
  have hb₁ : IsPullback (pullback.fst (p ≫ q) (p ≫ q)).left
      m₁.left p.left (pullback.fst q (p ≫ q)).left :=
    (mapLeft_isPullback p q (p ≫ q)).map (Over.forget S)
  have hb₂ : IsPullback (pullback.snd q (p ≫ q)).left
      m₂.left p.left (pullback.snd q q).left :=
    (mapRight_isPullback p q q).map (Over.forget S)
  have h₁ : IsSchemeTheoreticallyDominant m₁.left :=
    IsSchemeTheoreticallyDominant.of_isPullback hb₁
  have h₂ : IsSchemeTheoreticallyDominant m₂.left :=
    IsSchemeTheoreticallyDominant.of_isPullback hb₂
  have he : m₁ ≫ m₂ = pairMap (p ≫ q) q p rfl := by
    apply pullback.hom_ext <;> simp [m₁, m₂]
  rw [← he]
  change IsSchemeTheoreticallyDominant (m₁.left ≫ m₂.left)
  infer_instance

end Schemes

section Groups

variable {S : Scheme.{u}} {D H Q : GroupScheme S}

/-- A section of the kernel-pair difference, obtained from `(1,k)`. -/
def differenceSection (q : H ⟶ Q) :
    (kernel q).X ⟶ pullback q.hom.hom q.hom.hom :=
  lift (1 : (kernel q).X ⟶ H.X) (𝟙 (kernel q).X) ≫ KernelPair.hom q

@[reassoc (attr := simp)]
theorem differenceSection_comp (q : H ⟶ Q) :
    differenceSection q ≫ KernelPair.difference q = 𝟙 (kernel q).X := by
  have he := congrArg (fun f => f ≫ snd H.X (kernel q).X)
    (KernelPair.hom_inv_id q)
  rw [Category.assoc, KernelPair.inv_snd, Category.id_comp] at he
  rw [differenceSection, Category.assoc, he, lift_snd]

/-- The difference is schematically dominant because it has a section. -/
theorem difference_isSchemeTheoreticallyDominant (q : H ⟶ Q) :
    IsSchemeTheoreticallyDominant (KernelPair.difference q).left := by
  rw [isSchemeTheoreticallyDominant_iff, ← le_bot_iff]
  calc
    (KernelPair.difference q).left.ker ≤
        ((differenceSection q).left ≫ (KernelPair.difference q).left).ker :=
      Scheme.Hom.le_ker_comp _ _
    _ = ⊥ := by
      rw [show (differenceSection q).left ≫ (KernelPair.difference q).left = 𝟙 _ from
        congrArg (fun f => f.left) (differenceSection_comp q)]
      simp

/-- The kernel-pair difference is quasi-compact when the source group is
quasi-compact over the base. -/
theorem difference_quasiCompact (q : H ⟶ Q) [QuasiCompact H.X.hom] :
    QuasiCompact (KernelPair.difference q).left := by
  have : IsIso (KernelPair.inv q) :=
    (inferInstance : IsIso (KernelPair.iso q).inv)
  have : QuasiCompact (snd H.X (kernel q).X).left := by
    change QuasiCompact (pullback.snd H.X.hom (kernel q).X.hom)
    infer_instance
  rw [← KernelPair.inv_snd]
  change QuasiCompact ((KernelPair.inv q).left ≫ (snd H.X (kernel q).X).left)
  infer_instance

/-- The kernel-valued difference of a parametrization at `d` and `d k`. -/
def parametrization (φ : D ⟶ Q) (q : H ⟶ Q) (p : D.X ⟶ H.X)
    (h : p ≫ q.hom.hom = φ.hom.hom) : D.X ⊗ (kernel φ).X ⟶ (kernel q).X :=
  KernelPair.hom φ ≫ pairMap φ.hom.hom q.hom.hom p h ≫ KernelPair.difference q

@[reassoc (attr := simp)]
theorem parametrization_ι (φ : D ⟶ Q) (q : H ⟶ Q) (p : D.X ⟶ H.X)
    (h : p ≫ q.hom.hom = φ.hom.hom) :
    parametrization φ q p h ≫ (kernelι q).hom.hom =
      (fst D.X (kernel φ).X ≫ p)⁻¹ * (KernelPair.action φ ≫ p) := by
  simp only [parametrization, Category.assoc, KernelPair.difference_ι,
    MonObj.comp_mul, GrpObj.comp_inv, pairMap_fst, pairMap_snd,
    KernelPair.hom_fst_assoc, KernelPair.hom_snd_assoc]

/-- The difference parametrization preserves the identity even if `p` does not. -/
theorem parametrization_one (φ : D ⟶ Q) (q : H ⟶ Q) (p : D.X ⟶ H.X)
    (h : p ≫ q.hom.hom = φ.hom.hom) :
    lift (1 : 𝟙_ (Over S) ⟶ D.X) (1 : 𝟙_ (Over S) ⟶ (kernel φ).X) ≫
      parametrization φ q p h = 1 := by
  let e := lift (1 : 𝟙_ (Over S) ⟶ D.X) (1 : 𝟙_ (Over S) ⟶ (kernel φ).X)
  have ha : e ≫ KernelPair.action φ = 1 := by
    simp only [e, KernelPair.action, MonObj.comp_mul, lift_fst, lift_snd_assoc,
      MonObj.one_comp, one_mul]
  apply (cancel_mono (kernelι q).hom.hom).mp
  simp only [Category.assoc, parametrization_ι, MonObj.comp_mul, GrpObj.comp_inv,
    lift_fst_assoc, MonObj.one_comp]
  change (1 ≫ p)⁻¹ * (e ≫ KernelPair.action φ ≫ p) = 1
  rw [← Category.assoc, ha, inv_mul_cancel]

/-- A quasi-compact schematically dominant parametrization over flat quotient maps
induces a schematically dominant parametrization of the full represented kernel. -/
theorem parametrization_isSchemeTheoreticallyDominant
    (φ : D ⟶ Q) (q : H ⟶ Q) (p : D.X ⟶ H.X)
    (h : p ≫ q.hom.hom = φ.hom.hom)
    [IsSchemeTheoreticallyDominant p.left] [QuasiCompact p.left]
    [Flat φ.hom.hom.left] [Flat q.hom.hom.left] :
    IsSchemeTheoreticallyDominant (parametrization φ q p h).left := by
  have : IsSchemeTheoreticallyDominant (pairMap φ.hom.hom q.hom.hom p h).left :=
    pairMap_isSchemeTheoreticallyDominant _ _ _ h
  have : IsSchemeTheoreticallyDominant (KernelPair.difference q).left :=
    difference_isSchemeTheoreticallyDominant q
  have : IsIso (KernelPair.hom φ) :=
    (inferInstance : IsIso (KernelPair.iso φ).hom)
  change IsSchemeTheoreticallyDominant
    ((KernelPair.hom φ).left ≫
      (pairMap φ.hom.hom q.hom.hom p h).left ≫ (KernelPair.difference q).left)
  infer_instance

/-- Quasi-compactness of the full kernel parametrization. -/
theorem parametrization_quasiCompact
    (φ : D ⟶ Q) (q : H ⟶ Q) (p : D.X ⟶ H.X)
    (h : p ≫ q.hom.hom = φ.hom.hom)
    [QuasiCompact p.left] [QuasiCompact H.X.hom] :
    QuasiCompact (parametrization φ q p h).left := by
  have : QuasiCompact (pairMap φ.hom.hom q.hom.hom p h).left :=
    pairMap_quasiCompact _ _ _ h
  have : QuasiCompact (KernelPair.difference q).left := difference_quasiCompact q
  have : IsIso (KernelPair.hom φ) :=
    (inferInstance : IsIso (KernelPair.iso φ).hom)
  change QuasiCompact
    ((KernelPair.hom φ).left ≫
      (pairMap φ.hom.hom q.hom.hom p h).left ≫ (KernelPair.difference q).left)
  infer_instance

/-- Topological dominance of the full kernel parametrization. -/
theorem parametrization_isDominant
    (φ : D ⟶ Q) (q : H ⟶ Q) (p : D.X ⟶ H.X)
    (h : p ≫ q.hom.hom = φ.hom.hom)
    [IsSchemeTheoreticallyDominant p.left] [QuasiCompact p.left]
    [Flat φ.hom.hom.left] [Flat q.hom.hom.left] [QuasiCompact H.X.hom] :
    IsDominant (parametrization φ q p h).left := by
  have := parametrization_isSchemeTheoreticallyDominant φ q p h
  have := parametrization_quasiCompact φ q p h
  infer_instance

end Groups

end Langlands.GroupScheme.KernelDomination
