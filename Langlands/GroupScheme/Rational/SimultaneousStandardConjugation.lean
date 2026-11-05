import Langlands.GroupScheme.Rational.DominantChamberMove
import Langlands.GroupScheme.Rational.CocharacterStandardFace
import Langlands.GroupScheme.Rational.StandardCocharacterReduction
import Langlands.GroupScheme.Rational.RelativeRootSignsProof
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyReduction
import Langlands.GroupScheme.Rational.ParabolicRootPresentation
import Langlands.GroupScheme.Rational.ParabolicCocharacterConjugacy

/-! # Simultaneous standard conjugation from a supplied dynamic realization

This internal adapter keeps the prescribed parabolic and Levi maps. Maximal
split torus conjugacy and the actual relative root system remain explicit
structural inputs.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Conjugate one supplied cocharacter into the standard chamber of the fixed
torus and generic cocharacter. The structural inputs are retained. -/
theorem exists_innerIso_comp_eq_standardCocharacter
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hG : IsConnectedReductive G) {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice T} :
    letI := hG.isAffineHom
    letI := hi.isSplitSubtorus.mono
    HasRelativeRootSystem i → IsGenericCocharacter i ν →
      ∀ z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
        ∃ (g : rationalPoints G) (J : Set (characterLattice T))
          (ζ : cocharacterLattice T),
          IsStandardCocharacter i ν J ζ ∧
            z ≫ (G.innerIso g).hom = CommGroupScheme.groupHom ζ ≫ i := by
  have := hG.isAffineHom
  have := hG.smooth
  have := hG.connectedSpace
  have := hi.isSplitSubtorus.mono
  intro hroot hν z
  obtain ⟨g, ξ, hg⟩ := exists_innerIso_comp_eq_cocharacter hconj hi z
  obtain ⟨n, hn⟩ :=
    hroot.exists_normalizerPoint_dominant i hi.isSplitSubtorus.1 ν ξ
  let ζ := cocharacterAut (normalizingAut i n) ξ
  refine ⟨(n : rationalPoints G) * g, simpleRootFace i ν ζ, ζ, ?_, ?_⟩
  · exact isStandardCocharacter_simpleRootFace i ν
      (fun α hα => hn α (simpleRelativeRoots_subset_positive i ν hα))
  · rw [innerIso_mul_hom, ← Category.assoc, hg]
    exact (groupHom_cocharacterAut_comp i n ξ).symm

section Ranges

variable {P M : GroupScheme (Spec (CommRingCat.of k))}

/-- One cocharacter simultaneously realizing the specified parabolic and Levi
is enough for standardizing both maps by the same rational conjugation. -/
theorem exists_simultaneousStandardConjugate_of_dynamicRealization
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hG : IsConnectedReductive G) {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice T} :
    letI := hG.isAffineHom
    letI := hi.isSplitSubtorus.mono
    HasRelativeRootSystem i → IsGenericCocharacter i ν →
      ∀ (p : P ⟶ G) (l : M ⟶ P)
        (z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G),
        SubgroupFunctor.range p = Dynamic.parabolic z →
        SubgroupFunctor.range (l ≫ p) = Dynamic.centralizer z →
        ∃ (g : rationalPoints G) (J : Set (characterLattice T))
          (ζ : cocharacterLattice T),
          IsStandardCocharacter i ν J ζ ∧
          SubgroupFunctor.range (p ≫ (G.innerIso g).hom) = standardParabolic i ν J ∧
          SubgroupFunctor.range (l ≫ p ≫ (G.innerIso g).hom) = standardLevi i ν J ∧
          SubgroupFunctor.range (p ≫ (G.innerIso g).hom) =
            Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) ∧
          SubgroupFunctor.range (l ≫ p ≫ (G.innerIso g).hom) =
            Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i) := by
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hroot hν p l z hP hM
  obtain ⟨g, J, ζ, hζ, hg⟩ :=
    exists_innerIso_comp_eq_standardCocharacter hconj hG hi hroot hν z
  have hPtransport :
      SubgroupFunctor.range (p ≫ (G.innerIso g).hom) =
        Dynamic.parabolic (z ≫ (G.innerIso g).hom) := by
    have hr := SubgroupFunctor.range_eq_comap_of_iso_square
      (G.innerIso g) (Iso.refl P) (i := p)
      (i' := p ≫ (G.innerIso g).hom) (by simp)
    exact ((SubgroupFunctor.eq_comap_iso_iff (G.innerIso g)).mp hr).symm.trans
      ((SubgroupFunctor.eq_comap_iso_iff (G.innerIso g)).mp
        (hP.trans (Dynamic.parabolic_eq_comap_of_iso z (G.innerIso g))))
  have hMtransport :
      SubgroupFunctor.range ((l ≫ p) ≫ (G.innerIso g).hom) =
        Dynamic.centralizer (z ≫ (G.innerIso g).hom) := by
    have hr := SubgroupFunctor.range_eq_comap_of_iso_square
      (G.innerIso g) (Iso.refl M) (i := l ≫ p)
      (i' := (l ≫ p) ≫ (G.innerIso g).hom) (by simp)
    exact ((SubgroupFunctor.eq_comap_iso_iff (G.innerIso g)).mp hr).symm.trans
      ((SubgroupFunctor.eq_comap_iso_iff (G.innerIso g)).mp
        (hM.trans (Dynamic.centralizer_eq_comap_of_iso z (G.innerIso g))))
  rw [hg] at hPtransport hMtransport
  have hstandard :=
    (hroot.standardCocharacterDynamicComparison i ν J hi.isSplitSubtorus.1 hν
      (relativeRootSignsDetermineDynamic k G hG T i hi)).standard_eq_dynamic i ν J hζ
  refine ⟨g, J, ζ, hζ, hPtransport.trans hstandard.1.symm, ?_, hPtransport, ?_⟩
  · simpa only [Category.assoc] using hMtransport.trans hstandard.2.1.symm
  · simpa only [Category.assoc] using hMtransport

/-- Choose a simultaneous standard conjugate while retaining all four all-test
image equalities and the actual standard cocharacter. -/
def simultaneousStandardConjugatingPoint
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hG : IsConnectedReductive G) {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice T}
    (hroot : letI := hG.isAffineHom
      letI := hi.isSplitSubtorus.mono
      HasRelativeRootSystem i)
    (hν : letI := hG.isAffineHom; IsGenericCocharacter i ν)
    (p : P ⟶ G) (l : M ⟶ P)
    (z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : SubgroupFunctor.range p = Dynamic.parabolic z)
    (hM : SubgroupFunctor.range (l ≫ p) = Dynamic.centralizer z) :
    letI := hG.isAffineHom
    {g : rationalPoints G //
      ∃ (J : Set (characterLattice T)) (ζ : cocharacterLattice T),
        IsStandardCocharacter i ν J ζ ∧
        SubgroupFunctor.range (p ≫ (G.innerIso g).hom) = standardParabolic i ν J ∧
        SubgroupFunctor.range (l ≫ p ≫ (G.innerIso g).hom) = standardLevi i ν J ∧
        SubgroupFunctor.range (p ≫ (G.innerIso g).hom) =
          Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) ∧
        SubgroupFunctor.range (l ≫ p ≫ (G.innerIso g).hom) =
          Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)} :=
  Classical.indefiniteDescription _
    (exists_simultaneousStandardConjugate_of_dynamicRealization
      hconj hG hi hroot hν p l z hP hM)

end Ranges

end Langlands.GroupScheme
