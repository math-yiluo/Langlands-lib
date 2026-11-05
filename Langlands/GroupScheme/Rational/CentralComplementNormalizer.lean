import Langlands.GroupScheme.Rational.DerivedNormalizerMap
import Langlands.GroupScheme.Rational.DerivedCoverNormalizerLift
import Langlands.GroupScheme.Rational.DerivedRootTransport
import Langlands.GroupScheme.Rational.CentralTorusFixedness
import Langlands.GroupScheme.Rational.SplitTorusFppfImage
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent

/-! # Actual normalizer images with a central torus complement -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem conjugate_range_le_of_fppf_parameterization
    {B : Scheme.{u}} {P G : GroupScheme B} {S : CommGroupScheme B}
    (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]
    (p b : P ⟶ S.toGrp)
    [Flat p.hom.hom.left] [Surjective p.hom.hom.left]
    [LocallyOfFinitePresentation p.hom.hom.left]
    (g : Over.mk (𝟙 B) ⟶ G.X)
    (h : p ≫ i ≫ (G.innerIso g).hom = b ≫ i) :
    SubgroupFunctor.range (i ≫ (G.innerIso g).hom) ≤ SubgroupFunctor.range i := by
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  rintro U x ⟨y, rfl⟩
  let V : Over B := Over.mk (pullback.fst y.left p.hom.hom.left ≫ U.hom)
  let a : V ⟶ U := Over.homMk (pullback.fst y.left p.hom.hom.left) rfl
  let z : V ⟶ P.X := Over.homMk (pullback.snd y.left p.hom.hom.left) (by
    rw [← Over.w p.hom.hom, ← Category.assoc, ← pullback.condition, Category.assoc,
      Over.w y]
    rfl)
  have haz : a ≫ y = z ≫ p.hom.hom :=
    Over.OverMorphism.ext pullback.condition
  have : Flat a.left := by change Flat (pullback.fst _ _); infer_instance
  have : Surjective a.left := by change Surjective (pullback.fst _ _); infer_instance
  have : LocallyOfFinitePresentation a.left := by
    change LocallyOfFinitePresentation (pullback.fst _ _)
    infer_instance
  apply SubgroupFunctor.mem_range_of_comp_mem_range i a
  refine SubgroupFunctor.mem_range.mpr ⟨z ≫ b.hom.hom, ?_⟩
  change (z ≫ b.hom.hom) ≫ i.hom.hom =
    a ≫ (y ≫ (i ≫ (G.innerIso g).hom).hom.hom)
  have hs := congrArg (fun f : P ⟶ G => f.hom.hom) h
  simp only [Grp.comp_hom_hom] at hs ⊢
  rw [← Category.assoc a y, haz]
  simpa only [Category.assoc] using congrArg (fun f => z ≫ f) hs.symm

namespace CentralComplementNormalizer

variable {k : Type u} [Field k]
    {T A S : CommGroupScheme (Spec (CommRingCat.of k))}
    {D G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]
    (q : D ⟶ G) (j : T.toGrp ⟶ D) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (e : T ⟶ S) (c : A ⟶ S)
    (h : j ≫ q = CommGroupScheme.groupHom e ≫ i)
    (hT : IsSplitTorus T.toGrp) (hA : IsSplitTorus A.toGrp)
    [hpflat : Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    [hpsurj : Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ i))

include h in
omit [IsAffineHom G.X.hom] in
private theorem conjugation_square (n : normalizerPoints j) :
    CommGroupScheme.groupHom e ≫ i ≫
        (G.innerIso (rationalPoints.map q n.val)).hom =
      CommGroupScheme.groupHom (normalizingAut j n).hom ≫
        CommGroupScheme.groupHom e ≫ i := by
  calc
    _ = j ≫ q ≫ (G.innerIso (rationalPoints.map q n.val)).hom := by
      rw [← Category.assoc, ← h, Category.assoc]
    _ = j ≫ (D.innerIso n.val).hom ≫ q := by
      rw [innerIso_hom_comp]
      rfl
    _ = CommGroupScheme.groupHom (normalizingAut j n).hom ≫ j ≫ q := by
      rw [← Category.assoc, isNormalizingPoint_normalizingAut j n, Category.assoc]
    _ = _ := by rw [h]

include h hc in
omit hpflat hpsurj [IsAffineHom G.X.hom] in
private theorem product_conjugation_square (n : normalizerPoints j) :
    RelativeRoot.centralComplementProduct e c ≫ i ≫
        (G.innerIso (rationalPoints.map q n.val)).hom =
      prodHom (CommGroupScheme.groupHom ((normalizingAut j n).hom ≫ e))
        (CommGroupScheme.groupHom c) (fun _ _ _ => Commute.all _ _) ≫ i := by
  have ht := conjugation_square q j i e h n
  have hz := hc.comp_innerIso_hom (rationalPoints.map q n.val)
  apply hom_ext_points
  intro U x
  simp only [Grp.comp_hom_hom, ← Category.assoc, RelativeRoot.centralComplementProduct,
    comp_prodHom, MonObj.mul_comp]
  simp only [Category.assoc, ← Grp.comp_hom_hom, ht, hz]
  rfl

include hi h hT hA hpflat hpsurj hc in
/-- The actual image of every source normalizer point normalizes the ambient
maximal split torus when the retained torus has an fppf central complement. -/
theorem mem_normalizerPoints (n : normalizerPoints j) :
    rationalPoints.map q n.val ∈ normalizerPoints i := by
  let P : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { toGrp := T.toGrp ⊗ A.toGrp
      comm := (inferInstance : IsCommMonObj (T.X ⊗ A.X)) }
  let p : P ⟶ S := Additive.ofMul (RelativeRoot.centralComplementProduct e c)
  have : Flat (CommGroupScheme.groupHom p).hom.hom.left := hpflat
  have : Surjective (CommGroupScheme.groupHom p).hom.hom.left := hpsurj
  have : LocallyOfFinitePresentation (CommGroupScheme.groupHom p).hom.hom.left :=
    locallyOfFinitePresentation_of_splitTori (hT.tensor hA) hi.1.1 p
  have : Mono i.hom.hom.left := hi.1.2.mono
  let b : P.toGrp ⟶ S.toGrp :=
    prodHom (CommGroupScheme.groupHom ((normalizingAut j n).hom ≫ e))
      (CommGroupScheme.groupHom c) (fun _ _ _ => Commute.all _ _)
  have hle := conjugate_range_le_of_fppf_parameterization i
    (CommGroupScheme.groupHom p) b (rationalPoints.map q n.val)
    (product_conjugation_square q j i e c h hc n)
  apply hi.mem_normalizerPoints_of_commute_conjugate (rationalPoints.map q n.val)
  intro U x y
  have hx : x ≫ (i ≫ (G.innerIso (rationalPoints.map q n.val)).hom).hom.hom ∈
      (SubgroupFunctor.range i).carrier U :=
    hle U (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hx
  rw [← hz]
  apply (commute_iff_eq _ _).mpr
  have hcomm := congrArg (fun v : U ⟶ S.X => v ≫ i.hom.hom) (Commute.all z y).eq
  simpa only [MonObj.mul_comp] using hcomm

/-- The original rational-point map restricted to the actual normalizer groups. -/
abbrev normalizerPointsMap :
    normalizerPoints j →* normalizerPoints i :=
  DerivedNormalizerMap.normalizerPointsHom e c j i q h hT hA hi hc

@[simp] theorem normalizerPointsMap_coe (n : normalizerPoints j) :
    (normalizerPointsMap q j i hi e c h hT hA hc n : rationalPoints G) =
      rationalPoints.map q n.val := rfl

/-- The actual source and image normalizer automorphisms commute with the
original retained torus map. -/
theorem normalizingAut_comp (n : normalizerPoints j) :
    (normalizingAut j n).hom ≫ e =
      e ≫ (normalizingAut i (normalizerPointsMap q j i hi e c h hT hA hc n)).hom := by
  have : Mono i.hom.hom.left := hi.1.2.mono
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have hn := isNormalizingPoint_normalizingAut i
    (normalizerPointsMap q j i hi e c h hT hA hc n)
  change i ≫ (G.innerIso (rationalPoints.map q n.val)).hom =
    CommGroupScheme.groupHom
      (normalizingAut i (normalizerPointsMap q j i hi e c h hT hA hc n)).hom ≫ i at hn
  have ht := conjugation_square q j i e h n
  have he :
      CommGroupScheme.groupHom ((normalizingAut j n).hom ≫ e) ≫ i =
        CommGroupScheme.groupHom
          (e ≫ (normalizingAut i (normalizerPointsMap q j i hi e c h hT hA hc n)).hom) ≫ i := by
    change CommGroupScheme.groupHom (normalizingAut j n).hom ≫
        CommGroupScheme.groupHom e ≫ i =
      CommGroupScheme.groupHom e ≫
        CommGroupScheme.groupHom
          (normalizingAut i (normalizerPointsMap q j i hi e c h hT hA hc n)).hom ≫ i
    rw [← ht, hn]
  apply Additive.toMul.injective
  apply Grp.hom_ext
  exact (cancel_mono i.hom.hom).mp
    (congrArg (fun f : T.toGrp ⟶ G => f.hom.hom) he)

end CentralComplementNormalizer

end Langlands.GroupScheme
