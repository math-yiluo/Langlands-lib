import Langlands.GroupScheme.Reductive.RelativeRootDynamicCell
import Langlands.GroupScheme.Reductive.RelativeRootCommutatorFppf
import Langlands.GroupScheme.Reductive.RelativeCommutatorBaseChange
import Langlands.GroupScheme.Reductive.EtaleLocalSplitProof
import Langlands.GroupScheme.Reductive.RelativeDerivedReduction

/-! # Fppf-local perfectness of relative semisimple groups -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace Langlands.GroupScheme

open RelativeDerived

/-- The arbitrary-base target follows from the affine split case with its
actual fibrewise torus and root datum. -/
theorem relativeSemisimpleFppfPerfect_of_split
    (hsplit : ∀ (R : Type u) [CommRing R]
      (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
      (I : Type u) [Fintype I] (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
      (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
      IsReductive G → (∀ s, IsSemisimple (geometricFiber G s)) →
      IsClosedSubgroup i →
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
      IsFibrewiseRootDatumOf I G i P →
      ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ G.X), LocallyCommutator x) :
    RelativeSemisimpleFppfPerfectStatement.{u} := by
  classical
  intro S G hG hss T x
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have hcharts : ∀ s : S, ∃ (U : Scheme.{u}) (f : U ⟶ S),
      Etale f ∧ (∃ p : U, f p = s) ∧
      ∀ (Z : Over U) (y : Z ⟶ ((GroupScheme.baseChange f).obj G).X),
        LocallyCommutator y := by
    intro s
    obtain ⟨R, hR, f, hf, hs, I, hI, i, hi, hmax, J, P, hP, _⟩ :=
      etaleLocalSplitReductive S G hG s
    let : CommRing R := hR
    let : Fintype I := hI
    let H := (GroupScheme.baseChange f).obj G
    have hH : IsReductive H := hG.baseChange f
    let : IsAffineHom H.X.hom := hH.isAffineHom
    have hssH : ∀ p, IsSemisimple (geometricFiber H p) := by
      intro p
      exact (hG.isSemisimple_baseChange hss (geometricPoint _ p ≫ f)).of_iso
        (baseChangeCompIso f (geometricPoint _ p) G).symm
    exact ⟨_, f, hf, hs, hsplit R H I i J P hH hssH hi hmax hP⟩
  choose U f hf hs hperf using hcharts
  let 𝒱 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S :=
    Scheme.Cover.mkOfCovers S U f
      (fun s => by obtain ⟨p, hp⟩ := hs s; exact ⟨s, p, hp⟩) hf
  let 𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) T.left :=
    Scheme.Cover.changeProp (𝒱.pullback₁ T.hom) (fun j => by
      have := Scheme.Cover.map_prop (𝒱.pullback₁ T.hom) j
      exact ⟨inferInstance, inferInstance⟩)
  apply LocallyCommutator.of_cover 𝒰
  intro s
  let b := f s
  let V : Over (U s) := Over.mk (pullback.snd T.hom b)
  let W : Over S := Over.mk (pullback.fst T.hom b ≫ T.hom)
  let a : W ⟶ T := Over.homMk (pullback.fst T.hom b) rfl
  let r : (Over.map b).obj V ⟶ W := Over.homMk (𝟙 _) (by
    change (𝟙 _) ≫ (pullback.fst T.hom b ≫ T.hom) = pullback.snd T.hom b ≫ b
    simpa only [Category.id_comp] using (pullback.condition (f := T.hom) (g := b)))
  let q : W ⟶ (Over.map b).obj V := Over.homMk (𝟙 _) (by
    change (𝟙 _) ≫ (pullback.snd T.hom b ≫ b) = pullback.fst T.hom b ≫ T.hom
    simpa only [Category.id_comp] using (pullback.condition (f := T.hom) (g := b)).symm)
  let y := (baseChangePointsEquiv b G V).symm (r ≫ a ≫ x)
  have hy := (locallyCommutator_baseChange_iff b G V y).mp (hperf s V y)
  have hy' : LocallyCommutator (r ≫ a ≫ x) := by
    simpa only [y, MulEquiv.apply_symm_apply] using hy
  have he : q ≫ (r ≫ a ≫ x) = a ≫ x := by
    apply Over.OverMorphism.ext
    change (𝟙 _) ≫ ((𝟙 _) ≫ (pullback.fst T.hom b ≫ x.left)) =
      pullback.fst T.hom b ≫ x.left
    simp only [Category.id_comp]
  change LocallyCommutator (a ≫ x)
  simpa only [he] using hy'.restrict q

/-- Every point of a relative semisimple reductive group is fppf-locally
in the abstract commutator subgroup of its group of points. -/
theorem relativeSemisimpleFppfPerfect :
    RelativeSemisimpleFppfPerfectStatement.{u} := by
  classical
  apply relativeSemisimpleFppfPerfect_of_split
  intro R _ G _ I _ i J P hG hss hi hmax hP Z x
  apply RelativeRootDynamicCell.locallyCommutator_of_rootValues
    hG hss hi hmax hP
  intro a W p
  exact LocalRootGroup.locallyCommutator_root i
    (RelativeRootDynamicCell.isolatingExponent hP a).val hG hmax hP a
    (RelativeRootDynamicCell.isolatingExponent hP a).property.1
    (RelativeRootDynamicCell.isolatingExponent hP a).property.2 W p

end Langlands.GroupScheme
