import Langlands.AbelianScheme.PolarizedFiniteLevel.FibreDetection
import Langlands.AbelianScheme.Tate.FiniteMonodromy
import Langlands.AbelianScheme.TorsionFiniteEtale
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Detection of actual torsion-scheme morphisms -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open GroupScheme.Tate

private theorem unramified_hom_ext {S : Scheme.{u}} {X Y : Over S}
    [FormallyUnramified Y.hom] [LocallyOfFiniteType Y.hom] {f k : X ⟶ Y}
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (s : Spec (CommRingCat.of K) ⟶ S) (x : Over.mk s ⟶ X), x ≫ f = x ≫ k) :
    f = k := by
  have hopen : IsOpenImmersion (equalizer.ι f k).left := by
    refine MorphismProperty.of_isPullback
      ((Limits.isPullback_equalizer_prod f k).map (Over.forget _)).flip ?_
    rw [← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _
      (Over.prodLeftIsoPullback Y Y).hom]
    convert! (inferInstance : IsOpenImmersion (pullback.diagonal Y.hom))
    ext1 <;> simp [← Over.comp_left]
  have hsurj : Surjective (equalizer.ι f k).left := by
    constructor
    intro x
    let K := AlgebraicClosure (X.left.residueField x)
    let t : Spec (CommRingCat.of K) ⟶ X.left :=
      Spec.map (CommRingCat.ofHom (algebraMap (X.left.residueField x) K)) ≫
        X.left.fromSpecResidueField x
    let s : Spec (CommRingCat.of K) ⟶ S := t ≫ X.hom
    let t' : Over.mk s ⟶ X := Over.homMk t rfl
    let l := equalizer.lift t' (h K s t')
    let z : Spec (CommRingCat.of K) := default
    refine ⟨l.left z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]
    exact Scheme.fromSpecResidueField_apply x _
  have : IsIso (equalizer.ι f k).left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨hopen, hsurj⟩
  apply Over.OverMorphism.ext
  rw [← cancel_epi (equalizer.ι f k).left]
  exact congrArg CommaMorphism.left (equalizer.condition f k)

variable {S : Scheme.{u}} {A B : AbelianScheme S} {g n : ℕ}

/-- Agreement on the ordered global sections determines the actual torsion map
when the order is positive and invertible on the base. -/
theorem FullLevel.torsionMap_ext (v : FullLevel A g n) {f k : A ⟶ B}
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (h : ∀ i, levelMap (Over.mk (𝟙 S)) (groupHom f) n (v.sections i) =
      levelMap (Over.mk (𝟙 S)) (groupHom k) n (v.sections i)) :
    kernelLevelMap (groupHom f) n = kernelLevelMap (groupHom k) n := by
  obtain ⟨hfin, het⟩ := torsionFiniteEtale S B n hn hunit
  have : IsFinite
      (GroupScheme.kernel (GroupScheme.multiplication B.toGrp (n : ℤ))).X.hom := hfin
  have : Etale
      (GroupScheme.kernel (GroupScheme.multiplication B.toGrp (n : ℤ))).X.hom := het
  apply unramified_hom_ext
  intro K _ _ s x
  apply Additive.ofMul.injective
  apply (kernelLevelEquiv B.toGrp (Over.mk s) n).injective
  have hf := kernelLevelEquiv_map (Over.mk s) (groupHom f) n (Additive.ofMul x)
  have hk := kernelLevelEquiv_map (Over.mk s) (groupHom k) n (Additive.ofMul x)
  simp only [toMul_ofMul] at hf hk
  rw [hf, hk]
  exact DFunLike.congr_fun (v.fibreLevelMap_ext h K s)
    (kernelLevelEquiv A.toGrp (Over.mk s) n (Additive.ofMul x))

variable {P : Prerequisites.{u}} {d : ℕ} {a b : Datum P S g d n}

/-- The actual isomorphism of torsion schemes induced by a polarized isomorphism. -/
def PolarizedIso.torsionIso (e : PolarizedIso a b) :
    (GroupScheme.torsion a.abelian.toGrp (n : ℤ)).X ≅
      (GroupScheme.torsion b.abelian.toGrp (n : ℤ)).X where
  hom := kernelLevelMap (groupHom e.abelianIso.hom) n
  inv := kernelLevelMap (groupHom e.abelianIso.inv) n
  hom_inv_id := by
    apply (cancel_mono (GroupScheme.kernelι
      (GroupScheme.multiplication a.abelian.toGrp (n : ℤ))).hom.hom).mp
    rw [Category.assoc, kernelLevelMap_ι, ← Category.assoc, kernelLevelMap_ι]
    have he := congrArg (fun f : a.abelian ⟶ a.abelian =>
      (GroupScheme.kernelι
        (GroupScheme.multiplication a.abelian.toGrp (n : ℤ))).hom.hom ≫
          (groupHom f).hom.hom) e.abelianIso.hom_inv_id
    change (GroupScheme.kernelι
        (GroupScheme.multiplication a.abelian.toGrp (n : ℤ))).hom.hom ≫
        ((groupHom e.abelianIso.hom).hom.hom ≫
          (groupHom e.abelianIso.inv).hom.hom) =
      (GroupScheme.kernelι
        (GroupScheme.multiplication a.abelian.toGrp (n : ℤ))).hom.hom ≫ 𝟙 _ at he
    simpa only [Category.assoc, Category.comp_id, Category.id_comp] using he
  inv_hom_id := by
    apply (cancel_mono (GroupScheme.kernelι
      (GroupScheme.multiplication b.abelian.toGrp (n : ℤ))).hom.hom).mp
    rw [Category.assoc, kernelLevelMap_ι, ← Category.assoc, kernelLevelMap_ι]
    have he := congrArg (fun f : b.abelian ⟶ b.abelian =>
      (GroupScheme.kernelι
        (GroupScheme.multiplication b.abelian.toGrp (n : ℤ))).hom.hom ≫
          (groupHom f).hom.hom) e.abelianIso.inv_hom_id
    change (GroupScheme.kernelι
        (GroupScheme.multiplication b.abelian.toGrp (n : ℤ))).hom.hom ≫
        ((groupHom e.abelianIso.inv).hom.hom ≫
          (groupHom e.abelianIso.hom).hom.hom) =
      (GroupScheme.kernelι
        (GroupScheme.multiplication b.abelian.toGrp (n : ℤ))).hom.hom ≫ 𝟙 _ at he
    simpa only [Category.assoc, Category.comp_id, Category.id_comp] using he

/-- Polarized isomorphisms preserving the ordered level induce the same actual
torsion-scheme isomorphism at positive invertible level. -/
theorem PolarizedIso.torsionIso_eq (e f : PolarizedIso a b)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) :
    e.torsionIso = f.torsionIso := by
  apply CategoryTheory.Iso.ext
  apply a.level.torsionMap_ext hn hunit
  intro i
  exact (e.level_eq i).trans (f.level_eq i).symm

@[simp] theorem PolarizedIso.torsionIso_refl (a : Datum P S g d n) :
    (PolarizedIso.refl a).torsionIso = CategoryTheory.Iso.refl _ := by
  apply CategoryTheory.Iso.ext
  apply (cancel_mono (GroupScheme.kernelι
    (GroupScheme.multiplication a.abelian.toGrp (n : ℤ))).hom.hom).mp
  rw [PolarizedIso.torsionIso, kernelLevelMap_ι]
  rfl

/-- A polarized automorphism preserving the ordered level is the identity on
the actual positive invertible torsion scheme. -/
theorem PolarizedIso.torsionIso_eq_refl (e : PolarizedIso a a)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) :
    e.torsionIso = CategoryTheory.Iso.refl _ := by
  rw [e.torsionIso_eq (PolarizedIso.refl a) hn hunit, PolarizedIso.torsionIso_refl]

end Langlands.AbelianScheme.PolarizedFiniteLevel
