import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent

/-! # Normalizer transport through an fppf change of acting group -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TorusCoverTransport

variable {B : Scheme.{u}} {C G : GroupScheme B} {S T : CommGroupScheme B}
  {i : S.toGrp ⟶ C} {j : T.toGrp ⟶ G}
  [Mono j.hom.hom.left]
  (q : C ⟶ G) (t : S ⟶ T)
  [Flat (CommGroupScheme.groupHom t).hom.hom.left]
  [Surjective (CommGroupScheme.groupHom t).hom.hom.left]
  [LocallyOfFinitePresentation (CommGroupScheme.groupHom t).hom.hom.left]
  (h : i ≫ q = CommGroupScheme.groupHom t ≫ j)

include h

private theorem conjugate_range_le {n : Over.mk (𝟙 B) ⟶ C.X}
    {σ : S ≅ S} (hn : IsNormalizingPoint i n σ) :
    SubgroupFunctor.range (j ≫ (G.innerIso (n ≫ q.hom.hom)).hom) ≤
      SubgroupFunctor.range j := by
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  have hsquare :
      CommGroupScheme.groupHom t ≫ j ≫ (G.innerIso (n ≫ q.hom.hom)).hom =
        CommGroupScheme.groupHom σ.hom ≫ CommGroupScheme.groupHom t ≫ j := by
    calc
      _ = i ≫ q ≫ (G.innerIso (n ≫ q.hom.hom)).hom := by
        rw [← Category.assoc, h.symm, Category.assoc]
      _ = i ≫ (C.innerIso n).hom ≫ q := by rw [innerIso_hom_comp]
      _ = CommGroupScheme.groupHom σ.hom ≫ i ≫ q := by
        rw [← Category.assoc, hn, Category.assoc]
      _ = _ := by rw [← h.symm]
  rintro U x ⟨y, rfl⟩
  let V : Over B :=
    Over.mk (pullback.fst y.left (CommGroupScheme.groupHom t).hom.hom.left ≫ U.hom)
  let a : V ⟶ U :=
    Over.homMk (pullback.fst y.left (CommGroupScheme.groupHom t).hom.hom.left) rfl
  let z : V ⟶ S.toGrp.X :=
    Over.homMk (pullback.snd y.left (CommGroupScheme.groupHom t).hom.hom.left) (by
      rw [← Over.w (CommGroupScheme.groupHom t).hom.hom, ← Category.assoc,
        ← pullback.condition, Category.assoc, Over.w y]
      rfl)
  have haz : a ≫ y = z ≫ (CommGroupScheme.groupHom t).hom.hom :=
    Over.OverMorphism.ext pullback.condition
  have : Flat a.left := by change Flat (pullback.fst _ _); infer_instance
  have : Surjective a.left := by change Surjective (pullback.fst _ _); infer_instance
  have : LocallyOfFinitePresentation a.left := by
    change LocallyOfFinitePresentation (pullback.fst _ _)
    infer_instance
  apply SubgroupFunctor.mem_range_of_comp_mem_range j a
  refine SubgroupFunctor.mem_range.mpr
    ⟨z ≫ (CommGroupScheme.groupHom σ.hom).hom.hom ≫
      (CommGroupScheme.groupHom t).hom.hom, ?_⟩
  change (z ≫ (CommGroupScheme.groupHom σ.hom).hom.hom ≫
      (CommGroupScheme.groupHom t).hom.hom) ≫ j.hom.hom =
    a ≫ (y ≫ (j ≫ (G.innerIso (n ≫ q.hom.hom)).hom).hom.hom)
  have hs := congrArg (fun f : S.toGrp ⟶ G => f.hom.hom) hsquare
  simp only [Grp.comp_hom_hom] at hs ⊢
  rw [← Category.assoc a y, haz]
  simpa only [Category.assoc] using congrArg (fun f => z ≫ f) hs.symm

private def normalizerEnd (n : normalizerPoints i) : T.toGrp ⟶ T.toGrp :=
  letI : Mono j.hom.hom := Over.mono_of_mono_left _
  (show (SubgroupFunctor.range j).IsRepresentedBy j from ⟨inferInstance, rfl⟩).factorHom
    (j ≫ (G.innerIso (n.val ≫ q.hom.hom)).hom)
    (conjugate_range_le q t h (isNormalizingPoint_normalizingAut i n))

private theorem normalizerEnd_comp (n : normalizerPoints i) :
    normalizerEnd q t h n ≫ j = j ≫ (G.innerIso (n.val ≫ q.hom.hom)).hom := by
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  exact SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

private theorem normalizerEnd_inv (n : normalizerPoints i) :
    normalizerEnd q t h n ≫ normalizerEnd q t h n⁻¹ = 𝟙 T.toGrp := by
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  apply (show (SubgroupFunctor.range j).IsRepresentedBy j from
    ⟨inferInstance, rfl⟩).hom_ext
  rw [Category.assoc, normalizerEnd_comp q t h, ← Category.assoc,
    normalizerEnd_comp q t h, Category.assoc, Category.id_comp]
  change j ≫ (G.innerIso (n.val ≫ q.hom.hom)).hom ≫
    (G.innerIso (n.val⁻¹ ≫ q.hom.hom)).hom = j
  rw [GrpObj.inv_comp, innerIso_inv_hom, Iso.hom_inv_id, Category.comp_id]

/-- Conjugation by the actual image of a source normalizer point restricts
to an automorphism of the actual target acting group. -/
def normalizerAut (n : normalizerPoints i) : T ≅ T where
  hom := Additive.ofMul (normalizerEnd q t h n)
  inv := Additive.ofMul (normalizerEnd q t h n⁻¹)
  hom_inv_id := congrArg Additive.ofMul (normalizerEnd_inv q t h n)
  inv_hom_id := by
    have hi := normalizerEnd_inv q t h n⁻¹
    rw [inv_inv] at hi
    exact congrArg Additive.ofMul hi

/-- The constructed torus automorphism is the restriction of actual conjugation. -/
theorem isNormalizingPoint_normalizerAut (n : normalizerPoints i) :
    IsNormalizingPoint j (n.val ≫ q.hom.hom) (normalizerAut q t h n) :=
  (normalizerEnd_comp q t h n).symm

/-- The ambient homomorphism restricts to a homomorphism of actual normalizer point groups. -/
def normalizerPointsMap : normalizerPoints i →* normalizerPoints j where
  toFun n := ⟨n.val ≫ q.hom.hom, ⟨normalizerAut q t h n, isNormalizingPoint_normalizerAut q t h n⟩⟩
  map_one' := Subtype.ext (MonObj.one_comp _)
  map_mul' n m := Subtype.ext (MonObj.mul_comp n.val m.val _)

@[simp] theorem normalizerPointsMap_apply (n : normalizerPoints i) :
    (normalizerPointsMap q t h n : Over.mk (𝟙 B) ⟶ G.X) =
      n.val ≫ q.hom.hom := rfl

/-- The actual source and image normalizer automorphisms commute with the actual torus map. -/
theorem normalizingAut_comp (n : normalizerPoints i) :
    (normalizingAut i n).hom ≫ t =
      t ≫ (normalizingAut j (normalizerPointsMap q t h n)).hom := by
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  have ht := isNormalizingPoint_normalizingAut j (normalizerPointsMap q t h n)
  change j ≫ (G.innerIso (n.val ≫ q.hom.hom)).hom =
    CommGroupScheme.groupHom (normalizingAut j (normalizerPointsMap q t h n)).hom ≫ j at ht
  have he :
      CommGroupScheme.groupHom ((normalizingAut i n).hom ≫ t) ≫ j =
        CommGroupScheme.groupHom (t ≫ (normalizingAut j (normalizerPointsMap q t h n)).hom) ≫ j := by
    calc
      _ = (CommGroupScheme.groupHom (normalizingAut i n).hom ≫ i) ≫ q := by
        change (CommGroupScheme.groupHom (normalizingAut i n).hom ≫
          CommGroupScheme.groupHom t) ≫ j = _
        rw [Category.assoc, h.symm, Category.assoc]
      _ = (i ≫ (C.innerIso n.val).hom) ≫ q := by
        rw [isNormalizingPoint_normalizingAut i n]
      _ = (CommGroupScheme.groupHom t ≫ j) ≫
          (G.innerIso (n.val ≫ q.hom.hom)).hom := by
        rw [Category.assoc, innerIso_hom_comp, ← Category.assoc, ← h.symm]
      _ = _ := by
        rw [Category.assoc, ht]
        rfl
  have hf := (show (SubgroupFunctor.range j).IsRepresentedBy j from
    ⟨inferInstance, rfl⟩).hom_ext he
  exact congrArg Additive.ofMul hf

end Langlands.GroupScheme.TorusCoverTransport
