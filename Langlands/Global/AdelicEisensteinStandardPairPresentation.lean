import Langlands.GroupScheme.Rational.DominantChamberMove
import Langlands.GroupScheme.Rational.ParabolicRootPresentationAmbientTransport
import Langlands.GroupScheme.Rational.CocharacterStandardFace
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.RelativeRootSignsProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.StandardCocharacterReduction

/-! # Putting an aligned parabolic pair in the same standard family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme

/-- If inverse conjugation by `w` identifies the two presentation tori, a
rational conjugation of the target makes it standard for the source torus and
generic cocharacter. The resulting representative is a point of the source
torus normalizer. The split-component factor is transported by the same torus
isomorphism. -/
def EisensteinStandardPairPresentationStatement : Prop :=
  ∀ (F : Type u) [Field F] (G P M Q M' : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (A A' : CommGroupScheme (Spec (CommRingCat.of F)))
    (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left]
    (q : Q ⟶ G) (l' : M' ⟶ Q) (a' : A'.toGrp ⟶ M') (r' : ParabolicRootPresentation q l' a')
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (e : r'.data.T ≅ r.data.T),
    IsConnectedReductive G →
    r'.data.i ≫ (G.innerIso w).inv = CommGroupScheme.groupHom e.hom ≫ r.data.i →
      ∃ (n : normalizerPoints r.data.i) (J : Set (characterLattice r.data.T)),
        let s := n.val * w⁻¹
        let e' := e ≪≫ normalizingAut r.data.i n
        r'.data.i ≫ (G.innerIso s).hom = CommGroupScheme.groupHom e'.hom ≫ r.data.i ∧
        ParabolicRootPresentationData.IsCompatible
          ⟨r.data.T, r.data.i, r.data.ν, J, r'.data.f ≫ e'.hom⟩
          (q ≫ (G.innerIso s).hom) l' a'

theorem eisensteinStandardPairPresentation : EisensteinStandardPairPresentationStatement.{u} := by
  intro F _ G P M Q M' _ A A' p l a r _ q l' a' r' w e hG hw
  let i := r.data.i
  let nu := r.data.ν
  have hi := r.isCompatible.maximalSplit
  have hnu := r.isCompatible.generic
  have hT := hi.isSplitSubtorus.1
  have hroot := relativeRootSystem F G hG r.data.T i hi
  obtain ⟨xi', _, hQ, hM'⟩ := r'.isCompatible.realization
  let xi := cocharacterLattice.congr e xi'
  obtain ⟨n, hn⟩ := hroot.exists_normalizerPoint_dominant i hT nu xi
  let zeta := cocharacterAut (normalizingAut i n) xi
  let J := simpleRootFace i nu zeta
  let s := n.val * w⁻¹
  let e' := e ≪≫ normalizingAut i n
  let E := G.innerIso s
  have hnorm : i ≫ (G.innerIso n.val).hom =
      CommGroupScheme.groupHom (normalizingAut i n).hom ≫ i :=
    isNormalizingPoint_normalizingAut i n
  have hs : r'.data.i ≫ E.hom = CommGroupScheme.groupHom e'.hom ≫ i := by
    change r'.data.i ≫ (G.innerIso (n.val * w⁻¹)).hom = _
    rw [innerIso_mul_hom, innerIso_inv_hom, ← Category.assoc, hw]
    change (CommGroupScheme.groupHom e.hom ≫ i) ≫ (G.innerIso n.val).hom =
      (CommGroupScheme.groupHom e.hom ≫ CommGroupScheme.groupHom (normalizingAut i n).hom) ≫ i
    rw [Category.assoc, hnorm, Category.assoc]
  let chi := CommGroupScheme.groupHom xi' ≫ r'.data.i
  have hchi : chi ≫ E.hom = CommGroupScheme.groupHom zeta ≫ i := by
    change (CommGroupScheme.groupHom xi' ≫ r'.data.i) ≫ E.hom = _
    rw [Category.assoc, hs]
    rfl
  have hQ' : SubgroupFunctor.range (q ≫ E.hom) =
      Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) := by
    rw [← hchi, SubgroupFunctor.range_comp_iso, hQ]
    simpa only [Iso.symm_hom, Iso.symm_inv, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      using (Dynamic.parabolic_eq_comap_of_iso (chi ≫ E.hom) E.symm).symm
  have hM'' : SubgroupFunctor.range (l' ≫ q ≫ E.hom) =
      Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) := by
    rw [← hchi, ← Category.assoc, SubgroupFunctor.range_comp_iso, hM']
    simpa only [Iso.symm_hom, Iso.symm_inv, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      using (Dynamic.centralizer_eq_comap_of_iso (chi ≫ E.hom) E.symm).symm
  have hzeta : IsStandardCocharacter i nu J zeta :=
    isStandardCocharacter_simpleRootFace i nu
      (fun α hα => hn α (simpleRelativeRoots_subset_positive i nu hα))
  have hstandard :=
    (hroot.standardCocharacterDynamicComparison i nu J hT hnu
      (relativeRootSignsDetermineDynamic F G hG r.data.T i hi)).standard_eq_dynamic i nu J hzeta
  have hmin : Dynamic.parabolic (CommGroupScheme.groupHom nu ≫ i) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) :=
    (relativeRootSignInclusions F G hG r.data.T i hi nu zeta).1.mpr
      (fun α hα hge => hn α ⟨hα, lt_of_le_of_ne hge (hnu α hα).symm⟩)
  have hfactor : CommGroupScheme.groupHom (r'.data.f ≫ e'.hom) ≫ i =
      a' ≫ l' ≫ q ≫ E.hom := by
    change (CommGroupScheme.groupHom r'.data.f ≫ CommGroupScheme.groupHom e'.hom) ≫ i = _
    rw [Category.assoc, ← hs, ← Category.assoc, r'.isCompatible.factor_comp]
    simp only [Category.assoc]
  refine ⟨n, J, hs, ?_⟩
  exact {
    parabolic := r'.isCompatible.parabolic.comp_iso E
    levi := r'.isCompatible.levi
    splitComponent := r'.isCompatible.splitComponent
    maximalSplit := hi
    generic := hnu
    subset_simpleRoots := simpleRootFace_subset i nu zeta
    parabolic_eq := hQ'.trans hstandard.1.symm
    levi_eq := hM''.trans hstandard.2.1.symm
    factor_comp := hfactor
    minimal := r.isCompatible.minimal
    minimal_le := hmin.trans hQ'.ge
    realization := ⟨zeta, hzeta, hQ', hM''⟩ }

end Langlands.Global
