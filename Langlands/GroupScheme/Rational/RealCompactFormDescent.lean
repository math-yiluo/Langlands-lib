import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.GroupScheme.Descent.GaloisHom
import Langlands.GroupScheme.IntegralModel.InnerSemilinearCoherence
import Langlands.GroupScheme.Rational.ConjugateSection
import Langlands.GroupScheme.Rational.RealCompactMatrixNormalizerRestriction
import Langlands.GroupScheme.Reductive.RationalPointDensityProof

/-! # Group-scheme descent of the adjusted complex isomorphism -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RealCompactForm

open GaloisPointComparison

section Descent

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {G H : GroupScheme (Spec (CommRingCat.of k))}

private theorem comp_eq_of_dense_through_iso
    {I : Type u} {X Y Z : GroupScheme (Spec (CommRingCat.of L))}
    [IsReduced X.X.left] [IsSeparated Z.X.hom]
    (d : Y ≅ X) (l : Y ⟶ Z) (r : X ⟶ Z)
    (p : I → rationalPoints X) (hp : HasDenseRationalPointFamily p)
    (q : I → rationalPoints Y)
    (hq : ∀ i, q i ≫ d.hom.hom.hom = p i)
    (h : ∀ i, q i ≫ l.hom.hom = p i ≫ r.hom.hom) :
    l = d.hom ≫ r := by
  have heq : d.inv ≫ l = r := by
    apply Grp.hom_ext
    apply hom_ext_of_denseRationalPointFamily p hp
    intro i
    have hinv : p i ≫ d.inv.hom.hom = q i := by
      rw [← hq i, Category.assoc, ← Grp.comp_hom_hom,
        Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
    change p i ≫ (d.inv.hom.hom ≫ l.hom.hom) = p i ≫ r.hom.hom
    rw [← Category.assoc, hinv]
    exact h i
  rw [← heq, Iso.hom_inv_id_assoc]

private theorem baseChangeBasePoint_comp_map
    {S S' : Scheme.{u}} (b : S' ⟶ S)
    {P Q : GroupScheme S} {R : GroupScheme S'}
    (f : P ⟶ Q) (g : (baseChange b).obj Q ⟶ R)
    (x : Over.mk (𝟙 S) ⟶ P.X) :
    baseChangeBasePoint b Q (x ≫ f.hom.hom) ≫ g.hom.hom =
      baseChangeBasePoint b P x ≫ ((baseChange b).map f ≫ g).hom.hom := by
  simpa only [GaloisPointComparison.baseChangeSectionHom_eq_baseChangeBasePoint] using
    baseChangeSectionHom_comp_map b f g x

private theorem rationalConjugate_extend (σ : L ≃ₐ[k] L) (x : rationalPoints H) :
    rationalConjugate k L H σ (rationalExtend k L H x) = rationalExtend k L H x := by
  apply (baseChangeCoeffEquiv k L H).injective
  rw [baseChangeCoeffEquiv_rationalConjugate, baseChangeCoeffEquiv_rationalExtend,
    GaloisPoint.conjugate_extend]

private theorem galois_compatible_named
    [IsReduced (baseChanged k L H).X.left] [IsSeparated (baseChanged k L G).X.hom]
    (e : baseChanged k L H ⟶ baseChanged k L G)
    (hd : HasDenseRationalPoints k H.X)
    (h : ∀ (x : rationalPoints H) (σ : L ≃ₐ[k] L),
      rationalConjugate k L G σ (rationalPoints.map e (rationalExtend k L H x)) =
        rationalPoints.map e (rationalExtend k L H x))
    (σ : L ≃ₐ[k] L) :
    (baseChange (galoisBaseMap k L σ)).map e ≫ (galoisDescentIso k L G σ).hom =
      (galoisDescentIso k L H σ).hom ≫ e := by
  let a := galoisBaseMap k L σ
  let dH := galoisDescentIso k L H σ
  let dG := galoisDescentIso k L G σ
  let p := rationalExtend k L H
  let q (x : rationalPoints H) := baseChangeBasePoint a (baseChanged k L H) (p x)
  have hq (x : rationalPoints H) : q x ≫ dH.hom.hom.hom = p x :=
    (IntegralModel.galoisDescentIso_baseChangeBasePoint k L H σ (p x)).trans
      (rationalConjugate_extend (H := H) σ x)
  have he (x : rationalPoints H) :
      q x ≫ ((baseChange a).map e ≫ dG.hom).hom.hom = p x ≫ e.hom.hom := by
    have hconj := IntegralModel.galoisDescentIso_baseChangeBasePoint k L G σ
      (rationalPoints.map e (p x))
    exact (baseChangeBasePoint_comp_map a e dG.hom (p x)).symm.trans (hconj.trans (h x σ))
  exact comp_eq_of_dense_through_iso (X := baseChanged k L H) (Z := baseChanged k L G)
    dH ((baseChange a).map e ≫ dG.hom) e
    p (RationalCharacterSeparation.dense_iUnion_range_rationalExtend k L H hd) q hq he

private theorem galois_compatible_of_fixed_on_extended_points
    [IsReduced (baseChanged k L H).X.left] [IsSeparated (baseChanged k L G).X.hom]
    (e : baseChanged k L H ⟶ baseChanged k L G)
    (hd : HasDenseRationalPoints k H.X)
    (h : ∀ (x : rationalPoints H) (σ : L ≃ₐ[k] L),
      rationalConjugate k L G σ (rationalPoints.map e (rationalExtend k L H x)) =
        rationalPoints.map e (rationalExtend k L H x))
    (σ : L ≃ₐ[k] L) :
    (baseChange (galoisBaseMap k L σ)).map e ≫
        (descentBaseChangeIso (baseMap k L) (galoisBaseMap k L σ)
          (galoisBaseMap_over k L σ) G).hom =
      (descentBaseChangeIso (baseMap k L) (galoisBaseMap k L σ)
        (galoisBaseMap_over k L σ) H).hom ≫ e := by
  simpa only [galoisDescentIso_def] using galois_compatible_named e hd h σ

private theorem rationalConjugate_eq_self_of_matrix {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) [Mono (ρ.baseChange (baseMap k L)).hom.hom]
    (σ : L ≃ₐ[k] L) (y : rationalPoints (baseChanged k L G))
    (hm : let m := (ρ.baseChange (baseMap k L)).rationalMatrix y
      Matrix.GeneralLinearGroup.map σ.toRingHom m = m) :
    rationalConjugate k L G σ y = y := by
  apply (ρ.baseChange (baseMap k L)).rationalMatrix_injective
  exact (rationalMatrix_baseChange_conjugate (k := k) (L := L) ρ σ y).trans hm

end Descent

/-- A normalizing matrix that makes the images of extended rational points Galois fixed
gives an isomorphism over the base field. -/
theorem exists_iso_of_matrix_conjugator
    {k L : Type u} [Field k] [Infinite k] [Field L] [IsAlgClosed L] [Algebra k L] [IsGalois k L]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    {n : Type} [Fintype n] [DecidableEq n]
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (e : baseChanged k L H ≅ baseChanged k L G)
    (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    (hconj : HasConjugatorToGaloisFixedPoints (k := k) (L := L) (G := G) (H := H)
      (ρ.baseChange (baseMap k L)) e.hom) :
    Nonempty (H ≅ G) := by
  obtain ⟨c, hc, hfixed⟩ := hconj
  let ρL := ρ.baseChange (baseMap k L)
  have hρL : IsClosedSubgroup ρL := ρ.isClosedSubgroup_baseChange (baseMap k L) hρ
  let : Smooth G.X.hom := hG.smooth
  let : Smooth H.X.hom := hH.smooth
  let : Smooth (baseChanged k L G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom (baseMap k L)))
  let : Smooth (baseChanged k L H).X.hom :=
    inferInstanceAs (Smooth (pullback.snd H.X.hom (baseMap k L)))
  let : IsReduced (baseChanged k L G).X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field L _
      (baseChanged k L G).X.hom
  let : IsReduced (baseChanged k L H).X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field L _
      (baseChanged k L H).X.hom
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : IsSeparated (baseChanged k L G).X.hom :=
    inferInstanceAs (IsSeparated (pullback.snd G.X.hom (baseMap k L)))
  obtain ⟨a, ha⟩ := exists_normalizer_iso ρL hρL hc
  let f := e ≪≫ a
  let : Mono ρL.hom.hom := hρL.mono_overHom
  have hfix (x : rationalPoints H) (σ : L ≃ₐ[k] L) :
      rationalConjugate k L G σ (rationalPoints.map f.hom (rationalExtend k L H x)) =
        rationalPoints.map f.hom (rationalExtend k L H x) := by
    let t := rationalExtend k L H x
    refine rationalConjugate_eq_self_of_matrix (k := k) (L := L) ρ σ
      (rationalPoints.map f.hom t) ?_
    have hmap : rationalPoints.map f.hom t =
        rationalPoints.map a.hom (rationalPoints.map e.hom t) := by
      simp only [f, Iso.trans_hom, rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
    let m := c * ρL.rationalMatrix (rationalPoints.map e.hom t) * c⁻¹
    have hm : ρL.rationalMatrix (rationalPoints.map f.hom t) = m :=
      (congrArg (fun y => ρL.rationalMatrix y) hmap).trans (ha _)
    have hfixed' : Matrix.GeneralLinearGroup.map σ.toRingHom m = m := hfixed x σ
    exact (congrArg (Matrix.GeneralLinearGroup.map σ.toRingHom) hm).trans (hfixed'.trans hm.symm)
  exact ⟨Descent.GaloisHom.iso (k := k) (L := L) f.hom
    (galois_compatible_of_fixed_on_extended_points (k := k) (L := L) f.hom
      (reductiveRationalPointDensity k H hH) hfix)⟩

end Langlands.GroupScheme.RealCompactForm
