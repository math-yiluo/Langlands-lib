import Langlands.GroupScheme.Dynamic.NormalSubgroupContraction
import Langlands.GroupScheme.AutomorphicAction.SemidirectHomLift
import Langlands.GroupScheme.Lie.SurjectiveDifferentialProof
import Langlands.GroupScheme.Absolute.OppositeCellProof
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.AlgebraicGeometry.AffineChartPoints

/-! # Smooth surjectivity of multiplication by a normal subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace Lie

variable {R : CommRingCat.{u}} (A : Type u) [CommRing A] [Algebra R A]

/-- Reduction of the dual-number test is surjective on underlying spaces. -/
theorem dualNumberTestReduction_surjective :
    Function.Surjective
      (((algSpec R).map (CommAlgCat.ofHom (TrivSqZeroExt.fstHom R A A)).op).left) := by
  change Function.Surjective (Spec.map
    (CommRingCat.ofHom (TrivSqZeroExt.fstHom R A A).toRingHom))
  apply Langlands.AlgebraicGeometry.specMap_surjective
    (TrivSqZeroExt.fstHom R A A).toRingHom TrivSqZeroExt.fst_surjective
  intro z hz
  have hz0 : z.fst = 0 := hz
  refine ⟨2, ?_⟩
  apply TrivSqZeroExt.ext <;> simp [pow_two, hz0]

/-- A compatible reduced point lifts an entire dual-number point through an
open immersion; its reduction is the originally supplied point. -/
theorem exists_dualNumberLift_of_openImmersion
    {X Y : Over (Spec R)} (f : X ⟶ Y) [IsOpenImmersion f.left]
    (x : (algSpec R).obj (op (CommAlgCat.of R (DualNumber A))) ⟶ Y)
    (y : (algSpec R).obj (op (CommAlgCat.of R A)) ⟶ X)
    (h : (algSpec R).map (CommAlgCat.ofHom (TrivSqZeroExt.fstHom R A A)).op ≫ x =
      y ≫ f) :
    ∃ z : (algSpec R).obj (op (CommAlgCat.of R (DualNumber A))) ⟶ X,
      z ≫ f = x ∧
      (algSpec R).map (CommAlgCat.ofHom (TrivSqZeroExt.fstHom R A A)).op ≫ z = y := by
  have hr : Set.range x.left ⊆ Set.range f.left := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := dualNumberTestReduction_surjective A a
    refine ⟨y.left b, ?_⟩
    have he := congrArg (fun q => q.left b) h
    simpa only [Over.comp_left, Scheme.Hom.comp_apply, hb] using he.symm
  let z : (algSpec R).obj (op (CommAlgCat.of R (DualNumber A))) ⟶ X :=
    Over.homMk (IsOpenImmersion.lift f.left x.left hr) (by
      rw [← Over.w f, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w x])
  have hz : z ≫ f = x := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  refine ⟨z, hz, ?_⟩
  let : Mono f := Over.mono_of_mono_left f
  apply (cancel_mono f).mp
  rw [Category.assoc, hz, h]

end Lie

namespace AutomorphicAction

variable {R : CommRingCat.{u}} {G H P U V : GroupScheme (Spec R)}
    (a : AutomorphicAction P H) (d : H ⟶ G) (i : P ⟶ G)
    (hc : ∀ (T : Over (Spec R)) (p : T ⟶ P.X) (h : T ⟶ H.X),
      a.act p h ≫ d.hom.hom =
        (p ≫ i.hom.hom) * (h ≫ d.hom.hom) * (p ≫ i.hom.hom)⁻¹)
    (s : U ⟶ H) (t : V ⟶ P)

/-- An open multiplication chart with factors in the two subgroups lifts
every tangent vector to their actual semidirect product. -/
theorem exists_lieLift_of_openCell
    [IsOpenImmersion
      ((fst U.X V.X ≫ (s ≫ d).hom.hom) *
        (snd U.X V.X ≫ (t ≫ i).hom.hom)).left]
    (A : Type u) [CommRing A] [Algebra R A] (X : lieKernel G A) :
    ∃ Z : lieKernel a.semidirectProduct A,
      Lie.targetMap (a.semidirectHomLift d i hc) A Z = X := by
  let m : U.X ⊗ V.X ⟶ G.X :=
    (fst U.X V.X ≫ (s ≫ d).hom.hom) *
      (snd U.X V.X ≫ (t ≫ i).hom.hom)
  let y₀ : (algSpec R).obj (op (CommAlgCat.of R A)) ⟶ U.X ⊗ V.X :=
    lift 1 1
  have hred :
      (algSpec R).map (CommAlgCat.ofHom (TrivSqZeroExt.fstHom R A A)).op ≫ X.val =
        y₀ ≫ m := by
    calc
      _ = 1 := X.property
      _ = _ := by
        simp only [y₀, m, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
          MonObj.one_comp, one_mul]
  obtain ⟨y, hy, hyr⟩ :=
    Lie.exists_dualNumberLift_of_openImmersion A m X.val y₀ hred
  let u : Lie.AffinePoints U (DualNumber A) := y ≫ fst U.X V.X
  let v : Lie.AffinePoints V (DualNumber A) := y ≫ snd U.X V.X
  have hu : Lie.reduction U u = 1 := by
    change (algSpec R).map (CommAlgCat.ofHom (TrivSqZeroExt.fstHom R A A)).op ≫
      (y ≫ fst U.X V.X) = 1
    rw [← Category.assoc, hyr]
    exact lift_fst _ _
  have hv : Lie.reduction V v = 1 := by
    change (algSpec R).map (CommAlgCat.ofHom (TrivSqZeroExt.fstHom R A A)).op ≫
      (y ≫ snd U.X V.X) = 1
    rw [← Category.assoc, hyr]
    exact lift_snd _ _
  let z : Lie.AffinePoints a.semidirectProduct (DualNumber A) :=
    lift (u ≫ s.hom.hom) (v ≫ t.hom.hom)
  have hz : Lie.reduction a.semidirectProduct z = 1 := by
    apply (a.semidirectPointsEquiv _).injective
    rw [Lie.reduction, Lie.affineMap_apply]
    change a.semidirectPointsEquiv _ (_ ≫ lift _ _) = _
    rw [comp_lift, semidirectPointsEquiv_lift, map_one]
    apply SemidirectProduct.ext
    · change _ ≫ (u ≫ s.hom.hom) = 1
      rw [← Category.assoc]
      change Lie.reduction U u ≫ s.hom.hom = 1
      rw [hu, MonObj.one_comp]
    · change _ ≫ (v ≫ t.hom.hom) = 1
      rw [← Category.assoc]
      change Lie.reduction V v ≫ t.hom.hom = 1
      rw [hv, MonObj.one_comp]
  refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
  change z ≫ (a.semidirectHomLift d i hc).hom.hom = X.val
  rw [semidirectHomLift_points, semidirectPointsEquiv_lift]
  change ((u ≫ s.hom.hom) ≫ d.hom.hom) *
    ((v ≫ t.hom.hom) ≫ i.hom.hom) = X.val
  change (u ≫ (s ≫ d).hom.hom) * (v ≫ (t ≫ i).hom.hom) = X.val
  simpa only [m, MonObj.comp_mul, u, v, Category.assoc] using hy

/-- A chosen actual tangent lift furnished by an open multiplication chart. -/
def lieLiftOfOpenCell
    [IsOpenImmersion
      ((fst U.X V.X ≫ (s ≫ d).hom.hom) *
        (snd U.X V.X ≫ (t ≫ i).hom.hom)).left]
    (A : Type u) [CommRing A] [Algebra R A] (X : lieKernel G A) :
    lieKernel a.semidirectProduct A :=
  Classical.choose (a.exists_lieLift_of_openCell d i hc s t A X)

/-- The chosen tangent lift maps to the original actual tangent vector. -/
theorem lieLiftOfOpenCell_target
    [IsOpenImmersion
      ((fst U.X V.X ≫ (s ≫ d).hom.hom) *
        (snd U.X V.X ≫ (t ≫ i).hom.hom)).left]
    (A : Type u) [CommRing A] [Algebra R A] (X : lieKernel G A) :
    Lie.targetMap (a.semidirectHomLift d i hc) A
      (a.lieLiftOfOpenCell d i hc s t A X) = X :=
  Classical.choose_spec (a.exists_lieLift_of_openCell d i hc s t A X)

/-- An open multiplication chart whose factors lie in smooth affine subgroups
makes their semidirect multiplication a smooth surjection onto a connected
smooth affine group over a field. -/
theorem smoothSurjective_of_openCell
    {k : Type u} [Field k] {G H P U V : GroupScheme (Spec (CommRingCat.of k))}
    (a : AutomorphicAction P H) (d : H ⟶ G) (i : P ⟶ G)
    (hc : ∀ (T : Over (Spec (CommRingCat.of k))) (p : T ⟶ P.X) (h : T ⟶ H.X),
      a.act p h ≫ d.hom.hom =
        (p ≫ i.hom.hom) * (h ≫ d.hom.hom) * (p ≫ i.hom.hom)⁻¹)
    (s : U ⟶ H) (t : V ⟶ P)
    [Smooth H.X.hom] [Smooth P.X.hom] [Smooth G.X.hom]
    [IsAffineHom H.X.hom] [IsAffineHom P.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left]
    [IsOpenImmersion
      ((fst U.X V.X ≫ (s ≫ d).hom.hom) *
        (snd U.X V.X ≫ (t ≫ i).hom.hom)).left] :
    Smooth (a.semidirectHomLift d i hc).hom.hom.left ∧
      Surjective (a.semidirectHomLift d i hc).hom.hom.left := by
  apply Lie.smoothSurjectiveOfSurjectiveDifferential k a.semidirectProduct G
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (a.semidirectHomLift d i hc)
  intro X
  refine ⟨Additive.ofMul (a.lieLiftOfOpenCell d i hc s t k X.toMul), ?_⟩
  apply Additive.toMul.injective
  exact a.lieLiftOfOpenCell_target d i hc s t k X.toMul

end AutomorphicAction

namespace Dynamic

variable {k : Type u} [Field k] {G H P : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    [Smooth P.X.hom] [IsAffineHom P.X.hom]
    (d : H ⟶ G) (i : P ⟶ G) [Mono i.hom.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hd : IsClosedSubgroup d) (hn : (SubgroupFunctor.range d).IsNormal)
    (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range d)
    (hP : parabolic χ ≤ SubgroupFunctor.range i)

include hd hn hχ hP in
/-- A closed normal smooth affine subgroup containing the cocharacter,
together with any smooth affine subgroup containing its dynamic parabolic,
multiplies smoothly and surjectively onto the connected ambient group. -/
theorem normal_subgroup_product_smooth_surjective :
    Smooth ((fst H.X P.X ≫ d.hom.hom) * (snd H.X P.X ≫ i.hom.hom)).left ∧
      Surjective ((fst H.X P.X ≫ d.hom.hom) * (snd H.X P.X ≫ i.hom.hom)).left := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsClosedImmersion d.hom.hom.left := hd
  let : Mono d.hom.hom := Over.mono_of_mono_left d.hom.hom
  let hn' : (SubgroupFunctor.range d).IsNormalizedBy (SubgroupFunctor.range i) :=
    fun T g x _ hx => hn T g x (Subgroup.mem_top _) hx
  let a := AutomorphicAction.ofNormalizedConjugation d i hn'
  let χopp := CommGroupScheme.groupHom
    (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  have hχopp : SubgroupFunctor.range χopp ≤ SubgroupFunctor.range d := by
    rintro T g ⟨z, rfl⟩
    apply hχ T
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨z ≫ (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1))).hom.hom, ?_⟩
    rfl
  let U := Affine.unipotentScheme χopp
  let V := Affine.parabolicScheme χ
  let s : U ⟶ H := normalUnipotentLift d χopp hd hn hχopp
    (Affine.isRepresentedBy_unipotentHom χopp)
  let t : V ⟶ P :=
    (Affine.isRepresentedBy_parabolicHom χ).lift
      (⟨inferInstance, rfl⟩ : (SubgroupFunctor.range i).IsRepresentedBy i)
      (fun T => Subgroup.inclusion (hP T)) (fun _ _ => rfl)
  have hs : s ≫ d = Affine.unipotentHom χopp :=
    normalUnipotentLift_comp d χopp hd hn hχopp
      (Affine.isRepresentedBy_unipotentHom χopp)
  have ht : t ≫ i = Affine.parabolicHom χ :=
    (Affine.isRepresentedBy_parabolicHom χ).lift_comp_eq
      (⟨inferInstance, rfl⟩ : (SubgroupFunctor.range i).IsRepresentedBy i)
      (fun T => Subgroup.inclusion (hP T)) (fun _ _ => rfl) (fun _ _ => rfl)
  have hopen : IsOpenImmersion
      ((fst U.X V.X ≫ (s ≫ d).hom.hom) *
        (snd U.X V.X ≫ (t ≫ i).hom.hom)).left := by
    rw [hs, ht]
    exact oppositeCellStatement k G χ U V _ _
      (Affine.isRepresentedBy_unipotentHom χopp)
      (Affine.isRepresentedBy_parabolicHom χ)
  have h := a.smoothSurjective_of_openCell d i
    (fun T p h => SubgroupFunctor.lift_comp_normalizedConjugation_comp d i hn' p h)
    s t
  simpa only [AutomorphicAction.semidirectHomLift_hom] using h

end Dynamic

end Langlands.GroupScheme
