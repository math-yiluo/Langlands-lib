import Langlands.GroupScheme.Absolute.FixedTorusDynamicGalois
import Langlands.GroupScheme.Absolute.CocharacterDescentLattice
import Langlands.GroupScheme.Rational.RootSignParabolicLie
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.GeometricConnectedness

/-! # Finite Galois descent of fixed-torus dynamic presentations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Descent

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    {G P : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffineHom T.X.hom]
    (j : T.toGrp ⟶ G) (i : P ⟶ G) [Mono i.hom.hom]

namespace FixedTorusGaloisDescent

/-- The descended integral orbit sum presents the original subgroup whenever
the supplied cocharacter presents its scalar extension through a split torus. -/
theorem range_eq_parabolic_descendedOrbitSum
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)
    (ν : FixedTorusDynamicPresentations
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map j)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i)) :
    SubgroupFunctor.range i =
      Dynamic.parabolic
        (CommGroupScheme.groupHom (CocharacterAveraging.descendedOrbitSum k K T ν.val) ≫ j) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let b := algebraBaseMap k K
  let TK := (CommGroupScheme.baseChange b).obj T
  let GK := (GroupScheme.baseChange b).obj G
  let jK := (GroupScheme.baseChange b).map j
  have : IsAffineHom GK.X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : Smooth GK.X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have : ConnectedSpace GK.X.left :=
    G.connectedSpace_baseChange_of_smooth_affine b
  have horbit : ∀ (α : characterLattice TK), α ∈ relativeRoots jK →
      ∀ σ : K ≃ₐ[k] K,
        (0 ≤ latticePairing TK α
          (cocharacterLattice.galoisRepresentation k K T σ ν.val) ↔
        0 ≤ latticePairing TK α ν.val) := by
    intro α hα σ
    have hσ := fixedTorusDynamicPresentation_galois k K T j i ν σ
    have heq :
        Dynamic.parabolic
            (CommGroupScheme.groupHom
              (cocharacterLattice.galoisRepresentation k K T σ ν.val) ≫ jK) =
          Dynamic.parabolic (CommGroupScheme.groupHom ν.val ≫ jK) :=
      hσ.symm.trans ν.property
    exact ⟨
      RelativeRoot.nonnegative_rootSupport_of_parabolic_le hT jK _ _ heq.le α hα,
      RelativeRoot.nonnegative_rootSupport_of_parabolic_le hT jK _ _ heq.ge α hα⟩
  have hsum : ∀ (α : characterLattice TK), α ∈ relativeRoots jK →
      (0 ≤ latticePairing TK α (CocharacterAveraging.galoisOrbitSum k K T ν.val) ↔
        0 ≤ latticePairing TK α ν.val) := by
    intro α hα
    exact CocharacterAveraging.nonneg_orbitSum_iff
      (cocharacterLattice.galoisRepresentation k K T) ν.val
      (latticePairing TK α).toAddMonoidHom (horbit α hα)
  have heq :
      Dynamic.parabolic
          (CommGroupScheme.groupHom (CocharacterAveraging.galoisOrbitSum k K T ν.val) ≫ jK) =
        Dynamic.parabolic (CommGroupScheme.groupHom ν.val ≫ jK) := by
    apply le_antisymm
    · apply (RelativeRoot.parabolic_le_iff_nonnegative_rootSupport
        dynamicConnected hT jK _ _).mpr
      intro α hα
      exact (hsum α hα).mp
    · apply (RelativeRoot.parabolic_le_iff_nonnegative_rootSupport
        dynamicConnected hT jK _ _).mpr
      intro α hα
      exact (hsum α hα).mpr
  apply (range_eq_parabolic_iff_baseChange (K := K) T j i _).mpr
  rw [CocharacterAveraging.baseChange_descendedOrbitSum]
  exact ν.property.trans heq.symm

end FixedTorusGaloisDescent

/-- An actual presentation over the original field, constructed by descending
the integral Galois orbit sum of a supplied presentation over the splitting field. -/
def fixedTorusDynamicPresentationGaloisDescend
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)
    (ν : FixedTorusDynamicPresentations
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map j)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i)) :
    FixedTorusDynamicPresentations T j i :=
  ⟨CocharacterAveraging.descendedOrbitSum k K T ν.val,
    FixedTorusGaloisDescent.range_eq_parabolic_descendedOrbitSum k K T j i hT ν⟩

/-- Existence of a fixed-torus dynamic presentation can be tested over a finite
Galois extension that splits the torus. -/
theorem exists_range_eq_parabolic_iff_finiteGaloisBaseChange
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp) :
    (∃ mu : cocharacterLattice T,
      SubgroupFunctor.range i = Dynamic.parabolic (CommGroupScheme.groupHom mu ≫ j)) ↔
    (∃ ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T),
      SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap k K)).map i) =
        Dynamic.parabolic
          (CommGroupScheme.groupHom ν ≫ (GroupScheme.baseChange (algebraBaseMap k K)).map j)) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  constructor
  · rintro ⟨mu, hmu⟩
    exact ⟨cocharacterLattice.baseChange (algebraBaseMap k K) T mu,
      (range_eq_parabolic_iff_baseChange (K := K) T j i mu).mp hmu⟩
  · rintro ⟨ν, hν⟩
    let mu := fixedTorusDynamicPresentationGaloisDescend k K T j i hT ⟨ν, hν⟩
    exact ⟨mu.val, mu.property⟩

end Descent

end Langlands.GroupScheme
