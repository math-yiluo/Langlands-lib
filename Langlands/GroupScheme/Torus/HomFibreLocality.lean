import Langlands.GroupScheme.Torus.HomFamilyLocality
import Langlands.GroupScheme.Torus.CharacterProjection

/-! # Extending a prescribed split-torus fibre map to an open neighbourhood -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace HomFamily

variable {S : Scheme.{u}} {T D : GroupScheme S} {U : Over S}
  {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (eT : T ≅ splitTorus S I) (eD : D ≅ splitTorus S J)
  {F : ∀ V : Over S, (V ⟶ U) → (V ⟶ T.X) → (V ⟶ D.X)}
  (hF : IsHomFamily F)

include hF in
/-- A prescribed matrix on one residue fibre works on all tests over an open
neighbourhood of that point. -/
theorem exists_open_actsBy_of_actsAtPoint {m : Matrix J I ℤ} {x : U.left}
    (hx : ActsAtPoint eT eD F m x) :
    ∃ W : U.left.Opens, x ∈ W ∧
      ActsBy eT eD F m (TorusConjugation.overHom (U := U) W.ι) := by
  have hloc := isLocallyConstant_actsAtPoint eT eD hF m
  rw [IsLocallyConstant.iff_exists_open] at hloc
  obtain ⟨O, hO, hxO, hconst⟩ := hloc x
  let W : U.left.Opens := ⟨O, hO⟩
  refine ⟨W, hxO, actsBy_of_forall_actsAtPoint_on eT eD hF m
    (TorusConjugation.overHom (U := U) W.ι) ?_⟩
  intro y
  change ActsAtPoint eT eD F m y.val
  rw [hconst y.val y.property]
  exact hx

/-- The constant family defined by an actual group-scheme homomorphism. -/
def postcomposeFamily (f : T ⟶ D) :
    ∀ V : Over S, (V ⟶ Over.mk (𝟙 S)) → (V ⟶ T.X) → (V ⟶ D.X) :=
  fun _ _ x => x ≫ f.hom.hom

/-- Postcomposition is multiplicative and natural on every relative test. -/
theorem postcomposeFamily_isHomFamily (f : T ⟶ D) :
    IsHomFamily (postcomposeFamily f) where
  map_mul := fun _ _ _ _ => MonObj.mul_comp _ _ _
  naturality := fun _ _ _ => Category.assoc _ _ _

end HomFamily

namespace splitTorus

variable {S A : Scheme.{u}} {I J : Type u} [Fintype I] [Fintype J]

/-- Base change of an actual homomorphism, expressed in the canonical new
coordinate tori. -/
def coordinateBaseChangeGroupHom (p : A ⟶ S)
    (f : splitTorus S I ⟶ splitTorus S J) : splitTorus A I ⟶ splitTorus A J :=
  (baseChangeIso p I).inv ≫ (GroupScheme.baseChange p).map f ≫
    (baseChangeIso p J).hom

/-- The inverse canonical coordinate identification preserves coordinates. -/
theorem baseChangePointsEquiv_baseChangeIso_inv (p : A ⟶ S) (V : Over A)
    (x : V ⟶ (splitTorus A I).X) :
    baseChangePointsEquiv p I V (x ≫ (baseChangeIso p I).inv.hom.hom) =
      pointsEquiv I V x := by
  have h := pointsEquiv_baseChangeIso_hom p I V
    (x ≫ (baseChangeIso p I).inv.hom.hom)
  simpa only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id] using h.symm

/-- The normalized pullback of an actual map has its original all-test
coordinate formula. -/
theorem coordinateBaseChangeHom_points (p : A ⟶ S)
    (f : splitTorus S I ⟶ splitTorus S J) (V : Over A)
    (x : V ⟶ (splitTorus A I).X) :
    pointsEquiv J V (x ≫ (coordinateBaseChangeGroupHom p f).hom.hom) =
      pointsEquiv J ((Over.map p).obj V)
        ((pointsEquiv I ((Over.map p).obj V)).symm (pointsEquiv I V x) ≫
          f.hom.hom) := by
  simp only [coordinateBaseChangeGroupHom, Grp.comp_hom_hom, ← Category.assoc]
  rw [pointsEquiv_baseChangeIso_hom]
  change pointsEquiv J ((Over.map p).obj V)
    (GroupScheme.baseChangePointsEquiv p _ V
      ((x ≫ (baseChangeIso p I).inv.hom.hom) ≫
        ((GroupScheme.baseChange p).map f).hom.hom)) = _
  rw [GroupScheme.baseChangePointsEquiv_comp]
  congr 2
  apply (pointsEquiv I ((Over.map p).obj V)).injective
  rw [MulEquiv.apply_symm_apply]
  exact baseChangePointsEquiv_baseChangeIso_inv p V x

/-- A monomial description of the actual base-changed homomorphism is a
monomial formula on every original-base test factoring through that base. -/
theorem actsBy_postcomposeFamily_of_coordinateBaseChangeHom_eq
    (p : A ⟶ S) (f : splitTorus S I ⟶ splitTorus S J) (m : Matrix J I ℤ)
    (hf : coordinateBaseChangeGroupHom p f = characterProjection A m) :
    HomFamily.ActsBy (Iso.refl _) (Iso.refl _) (HomFamily.postcomposeFamily f) m
      (TorusConjugation.overHom (U := Over.mk (𝟙 S)) p) := by
  change J → I → ℤ at m
  intro V c x
  obtain ⟨Y, ⟨⟨⟩⟩, sV⟩ := V
  change Y ⟶ S at sV
  change (Over.mk sV ⟶ Over.mk p) at c
  have hc : c.left ≫ p = sV := c.w
  generalize hq : c.left = q at hc
  change Y ⟶ A at q
  change I → (Γ(Y, ⊤))ˣ at x
  simp only [HomFamily.famUnits, HomFamily.postcomposeFamily,
    Iso.refl_hom, Iso.refl_inv, Grp.id_hom_hom, Category.comp_id]
  clear hq c
  change (q ≫ p : Y ⟶ S) = sV at hc
  subst sV
  let Vp : Over A := Over.mk q
  let y := (GroupScheme.baseChangePointsEquiv p (splitTorus S I) Vp).symm
    ((pointsEquiv I ((Over.map p).obj Vp)).symm x)
  have hcomp : (GroupScheme.baseChange p).map f ≫ (baseChangeIso p J).hom =
      (baseChangeIso p I).hom ≫ characterProjection A m := by
    rw [← hf, coordinateBaseChangeGroupHom, Iso.hom_inv_id_assoc]
  have he := congrArg (fun g :
      (GroupScheme.baseChange p).obj (splitTorus S I) ⟶ splitTorus A J =>
    pointsEquiv J Vp (y ≫ g.hom.hom)) hcomp
  simp only [Grp.comp_hom_hom, ← Category.assoc] at he
  rw [pointsEquiv_baseChangeIso_hom] at he
  funext j
  have hej := congrFun he j
  rw [characterProjection_points, pointsEquiv_baseChangeIso_hom] at hej
  simp only [baseChangePointsEquiv, MulEquiv.trans_apply,
    GroupScheme.baseChangePointsEquiv_comp, y, MulEquiv.apply_symm_apply] at hej
  refine hej.trans ?_
  apply Finset.prod_congr rfl
  intro i _
  exact congrArg (fun a => a ^ m j i)
    (congrFun ((pointsEquiv I ((Over.map p).obj Vp)).apply_symm_apply x) i)

/-- An all-test monomial formula also identifies the actual normalized
base-changed homomorphism. -/
theorem coordinateBaseChangeHom_eq_of_actsBy_postcomposeFamily
    (p : A ⟶ S) (f : splitTorus S I ⟶ splitTorus S J) (m : Matrix J I ℤ)
    (h : HomFamily.ActsBy (Iso.refl _) (Iso.refl _)
      (HomFamily.postcomposeFamily f) m
      (TorusConjugation.overHom (U := Over.mk (𝟙 S)) p)) :
    coordinateBaseChangeGroupHom p f = characterProjection A m := by
  apply hom_ext_points
  intro V x
  apply (pointsEquiv J V).injective
  rw [coordinateBaseChangeHom_points]
  have hm := h ((Over.map p).obj V) (Over.homMk V.hom (by simp))
    (pointsEquiv I V x)
  simp only [HomFamily.famUnits, HomFamily.postcomposeFamily,
    Iso.refl_hom, Iso.refl_inv, Grp.id_hom_hom, Category.comp_id] at hm
  refine hm.trans ?_
  funext j
  exact (characterProjection_points A m V x j).symm

/-- A prescribed residue-fibre matrix identifies the actual homomorphism
on an open neighbourhood. -/
theorem exists_open_coordinateBaseChangeHom_eq_of_residue_eq
    [DecidableEq I] [DecidableEq J]
    (f : splitTorus S I ⟶ splitTorus S J) (m : Matrix J I ℤ) (s : S)
    (hf : coordinateBaseChangeGroupHom (S.fromSpecResidueField s) f =
      characterProjection _ m) :
    ∃ W : S.Opens, s ∈ W ∧
      coordinateBaseChangeGroupHom W.ι f = characterProjection W m := by
  have hs : HomFamily.ActsAtPoint (Iso.refl _) (Iso.refl _)
      (HomFamily.postcomposeFamily f) m s :=
    actsBy_postcomposeFamily_of_coordinateBaseChangeHom_eq
      (S.fromSpecResidueField s) f m hf
  obtain ⟨W, hsW, hW⟩ := HomFamily.exists_open_actsBy_of_actsAtPoint
    (Iso.refl _) (Iso.refl _) (HomFamily.postcomposeFamily_isHomFamily f) hs
  exact ⟨W, hsW, coordinateBaseChangeHom_eq_of_actsBy_postcomposeFamily W.ι f m hW⟩

/-- Exponents for the permutation with target coordinate `j` equal to
source coordinate `σ j`. -/
def coordinatePermutationMatrix [DecidableEq I] (σ : J ≃ I) : Matrix J I ℤ :=
  fun j => Pi.single (σ j) 1

/-- The single-entry rows give the actual coordinate permutation. -/
theorem characterProjection_coordinatePermutationMatrix [DecidableEq I]
    (S : Scheme.{u}) (σ : J ≃ I) :
    characterProjection S (coordinatePermutationMatrix σ) =
      (coordinatePermutationIso S σ).hom := by
  apply hom_ext_points
  intro V x
  apply (pointsEquiv J V).injective
  funext j
  rw [characterProjection_points, coordinatePermutationIso_hom_points]
  simp [coordinatePermutationMatrix, Pi.single_apply]

/-- A fixed permutation of the actual residue-fibre coordinates holds
for the actual homomorphism on some open neighbourhood. -/
theorem exists_open_coordinatePermutation_of_residue_eq
    [DecidableEq I] [DecidableEq J]
    (f : splitTorus S I ⟶ splitTorus S J) (σ : J ≃ I) (s : S)
    (hf : coordinateBaseChangeGroupHom (S.fromSpecResidueField s) f =
      (coordinatePermutationIso _ σ).hom) :
    ∃ W : S.Opens, s ∈ W ∧
      coordinateBaseChangeGroupHom W.ι f = (coordinatePermutationIso W σ).hom := by
  have hm : coordinateBaseChangeGroupHom (S.fromSpecResidueField s) f =
      characterProjection _ (coordinatePermutationMatrix σ) := by
    rw [characterProjection_coordinatePermutationMatrix]
    exact hf
  simpa only [characterProjection_coordinatePermutationMatrix] using
    exists_open_coordinateBaseChangeHom_eq_of_residue_eq
      f (coordinatePermutationMatrix σ) s hm

/-- Choose an open neighbourhood retaining the supplied fibre permutation
as an equality of actual group-scheme homomorphisms. -/
def coordinatePermutationNeighbourhood [DecidableEq I] [DecidableEq J]
    (f : splitTorus S I ⟶ splitTorus S J) (σ : J ≃ I) (s : S)
    (hf : coordinateBaseChangeGroupHom (S.fromSpecResidueField s) f =
      (coordinatePermutationIso _ σ).hom) :
    {W : S.Opens // s ∈ W ∧
      coordinateBaseChangeGroupHom W.ι f = (coordinatePermutationIso W σ).hom} :=
  ⟨(exists_open_coordinatePermutation_of_residue_eq f σ s hf).choose,
    (exists_open_coordinatePermutation_of_residue_eq f σ s hf).choose_spec⟩

end splitTorus

end Langlands.GroupScheme
