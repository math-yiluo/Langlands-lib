import Langlands.GroupScheme.Rational.MinimalParabolicStatement
import Langlands.GroupScheme.Rational.RelativeRootNegationStatement
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsStatement
import Langlands.GroupScheme.Rational.MaximalSplitTorusStatement
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Rational.ParabolicConjugacyTransport
import Langlands.GroupScheme.Rational.StandardLeviLiftIndependence
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Dynamic.SmoothConnectedStatement
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Dynamic.AffineRepresentability

/-! # A structural reduction for generic minimal rational parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section RootSigns

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G)

/-- For a negation-stable actual root set, a generic nonnegative sign support
cannot properly contain another nonnegative sign support. -/
theorem nonnegative_relativeRoot_support_reverse_of_generic
    (ν eta : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    (hle : ∀ α ∈ relativeRoots i,
      0 ≤ latticePairing T α eta → 0 ≤ latticePairing T α ν) :
    ∀ α ∈ relativeRoots i,
      0 ≤ latticePairing T α ν → 0 ≤ latticePairing T α eta := by
  intro α hα hαν
  by_contra hαeta
  have hneta : 0 ≤ latticePairing T (-α) eta := by
    simp only [map_neg, LinearMap.neg_apply]
    omega
  have hnν := hle (-α) (hneg α hα) hneta
  have hne := hν α hα
  simp only [map_neg, LinearMap.neg_apply] at hnν
  omega

end RootSigns

/-- With the actual-root inclusion criterion and negation stability supplied,
the dynamic parabolic of a generic cocharacter is minimal among those on
the same maximal split torus. -/
theorem generic_dynamicParabolic_eq_of_le
    (hsign : RelativeRootSignInclusionsStatement.{u})
    (hneg : RelativeRootNegationStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (ν eta : cocharacterLattice T) :
    let := hG.isAffineHom
    IsGenericCocharacter i ν →
      Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ≤
        Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) →
      Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) =
        Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) := by
  let := hG.isAffineHom
  dsimp only
  intro hν hle
  apply le_antisymm hle
  apply (hsign k G hG T i hi ν eta).1.mpr
  exact nonnegative_relativeRoot_support_reverse_of_generic i ν eta hν
    (hneg k G hG T i hi) ((hsign k G hG T i hi eta ν).1.mp hle)

/-- Inner conjugation commutes with a homomorphism of group schemes, using the
image of its actual base point. -/
theorem innerIso_hom_comp_groupHom {S : Scheme.{u}} {H G : GroupScheme S}
    (j : H ⟶ G) (p : Over.mk (𝟙 S) ⟶ H.X) :
    (H.innerIso p).hom ≫ j =
      j ≫ (G.innerIso (p ≫ j.hom.hom)).hom := by
  apply hom_ext_points
  intro U x
  change (x ≫ (H.innerIso p).hom.hom.hom) ≫ j.hom.hom =
    (x ≫ j.hom.hom) ≫ (G.innerIso (p ≫ j.hom.hom)).hom.hom.hom
  conv_lhs => rw [comp_innerIso_hom]
  conv_rhs => rw [comp_innerIso_hom]
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, constantPoint_comp]

/-- If cocharacters lie in maximal split tori and these tori are conjugate in
smooth connected affine groups, a dynamic parabolic contained in a represented
smooth connected dynamic parabolic can be conjugated to a cocharacter of its
chosen ambient maximal split torus. The conjugating point lies in the larger
parabolic on the base test scheme. -/
theorem exists_conjugate_cocharacter_on_torus_of_parabolic_le
    (hcontain : CocharacterMaximalSplitTorusStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G)
    (hjc : IsClosedSubgroup j)
    (hj : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j)
    [Smooth P.X.hom] [ConnectedSpace P.X.left]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hle : Dynamic.parabolic χ ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
      (eta : cocharacterLattice T),
      g ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ∧
      χ ≫ (G.innerIso g).hom = CommGroupScheme.groupHom eta ≫ i := by
  obtain ⟨S, iS, zeta, hiS, hzeta⟩ := hcontain k G χ
  obtain ⟨iSP, hiSP, hSP⟩ :=
    hiS.exists_lift_of_parabolic_le zeta (CommGroupScheme.groupHom ν ≫ i)
      (by simpa only [hzeta] using hle) hj hjc
  obtain ⟨iTP, hiTP, hTP⟩ :=
    hi.exists_lift_of_parabolic_le ν (CommGroupScheme.groupHom ν ≫ i)
      le_rfl hj hjc
  let : IsAffineHom P.X.hom := hjc.isAffineHom
  obtain ⟨p, e, he⟩ := hconj k P S T iSP iTP hiSP hiTP
  refine ⟨p ≫ j.hom.hom, zeta ≫ Additive.ofMul e.hom, ?_, ?_⟩
  · rw [← hj.2]
    exact ⟨p, rfl⟩
  · change χ ≫ (G.innerIso (p ≫ j.hom.hom)).hom =
      (CommGroupScheme.groupHom zeta ≫ e.hom) ≫ i
    calc
      χ ≫ (G.innerIso (p ≫ j.hom.hom)).hom =
          (CommGroupScheme.groupHom zeta ≫ iSP) ≫
            j ≫ (G.innerIso (p ≫ j.hom.hom)).hom := by
        rw [← hzeta, ← hSP]
        simp only [Category.assoc]
      _ = (CommGroupScheme.groupHom zeta ≫ iSP) ≫ (P.innerIso p).hom ≫ j := by
        rw [innerIso_hom_comp_groupHom]
      _ = (CommGroupScheme.groupHom zeta ≫ e.hom) ≫ i := by
        rw [Category.assoc, ← Category.assoc iSP, he]
        simp only [Category.assoc, hTP]

section ConjugatingPoint

variable (hcontain : CocharacterMaximalSplitTorusStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G)
    (hjc : IsClosedSubgroup j)
    (hj : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j)
    [Smooth P.X.hom] [ConnectedSpace P.X.left]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hle : Dynamic.parabolic χ ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i))

/-- Choose a point in the larger dynamic parabolic that transports the smaller
cocharacter to its chosen maximal split torus. The structural inputs and the
smooth connected representative remain explicit hypotheses. -/
def parabolicConjugatingPoint :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X :=
  Classical.choose (exists_conjugate_cocharacter_on_torus_of_parabolic_le
    hcontain hconj k G T i hi ν P j hjc hj χ hle)

/-- The chosen point belongs to the larger parabolic and transports the
cocharacter to an actual cocharacter of the chosen torus. -/
theorem parabolicConjugatingPoint_spec :
    ∃ eta : cocharacterLattice T,
      parabolicConjugatingPoint hcontain hconj k G T i hi ν P j hjc hj χ hle ∈
        (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ∧
      χ ≫ (G.innerIso
        (parabolicConjugatingPoint hcontain hconj k G T i hi ν P j hjc hj χ hle)).hom =
          CommGroupScheme.groupHom eta ≫ i :=
  Classical.choose_spec (exists_conjugate_cocharacter_on_torus_of_parabolic_le
    hcontain hconj k G T i hi ν P j hjc hj χ hle)

end ConjugatingPoint

/-- The preceding common-torus reduction, negation stability, and root-sign
comparison imply all-test minimality for every smaller dynamic parabolic.
Smoothness and connectedness of the chosen representative are explicit here. -/
theorem generic_dynamicParabolic_eq_of_le_of_structural
    (hcontain : CocharacterMaximalSplitTorusStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hsign : RelativeRootSignInclusionsStatement.{u})
    (hneg : RelativeRootNegationStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G)
    (hjc : IsClosedSubgroup j)
    (hj : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j)
    [Smooth P.X.hom] [ConnectedSpace P.X.left] :
    let := hG.isAffineHom
    IsGenericCocharacter i ν →
      ∀ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
        Dynamic.parabolic χ ≤ Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) →
        Dynamic.parabolic χ = Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) := by
  let := hG.isAffineHom
  let := hG.smooth
  dsimp only
  intro hν χ hle
  let g := parabolicConjugatingPoint hcontain hconj k G T i hi ν P j hjc hj χ hle
  obtain ⟨eta, hg, hχ⟩ :=
    parabolicConjugatingPoint_spec hcontain hconj k G T i hi ν P j hjc hj χ hle
  have hinv :
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).comap (G.innerIso g).hom =
        Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) :=
    SubgroupFunctor.comap_innerIso_hom_eq_of_mem _ hg
  have hχcomap := Dynamic.parabolic_eq_comap_of_iso χ (G.innerIso g)
  rw [hχ] at hχcomap
  have heta :
      Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ≤
        Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) := by
    apply (SubgroupFunctor.comap_iso_le_comap_iso_iff (G.innerIso g)).mp
    rw [← hχcomap, hinv]
    exact hle
  have heq := generic_dynamicParabolic_eq_of_le hsign hneg k G hG T i hi ν eta hν heta
  rw [heq, hinv] at hχcomap
  exact hχcomap

end Langlands.GroupScheme
