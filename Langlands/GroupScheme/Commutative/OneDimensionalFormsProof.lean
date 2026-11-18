import Langlands.GroupScheme.Commutative.OneDimensionalFormsStatement
import Langlands.GroupScheme.HomogeneousQuotientDimension
import Langlands.GroupScheme.Lie.SplitTorusCoordinates
import Langlands.GroupScheme.Rational.VectorGroupDimension
import Langlands.GroupScheme.Torus.CentralRigidityReduction
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.NoTorusUnipotent
import Langlands.GroupScheme.Torus.SeparablyClosedSplitting
import Langlands.GroupScheme.Unipotent.OneDimensional.Proof
import Langlands.GroupScheme.VectorScalarKernel
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-! # Smooth connected affine groups of dimension one (Milne 16.16) -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

private theorem smoothOfRelativeDimension_one_baseChange
    {S S' : Scheme.{u}} (b : S' ⟶ S) (G : GroupScheme S)
    [SmoothOfRelativeDimension 1 G.X.hom] :
    SmoothOfRelativeDimension 1 ((baseChange b).obj G).X.hom := by
  let : MorphismProperty.IsStableUnderBaseChange
      (@SmoothOfRelativeDimension 1 : MorphismProperty Scheme.{u}) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  change SmoothOfRelativeDimension 1 (pullback.snd G.X.hom b)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := (@SmoothOfRelativeDimension 1 : MorphismProperty Scheme.{u}))
    (IsPullback.of_hasPullback G.X.hom b) ‹SmoothOfRelativeDimension 1 G.X.hom›

private theorem oneDimensional_isoGm_of_closed_splitTorus
    {k : Type u} [Field k] {G T : GroupScheme (Spec (CommRingCat.of k))}
    [SmoothOfRelativeDimension 1 G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hT : IsSplitTorus T) (i : T ⟶ G) (hi : IsClosedSubgroup i) (hi0 : i ≠ 0) :
    Nonempty (G ≅ (Gm (Spec (CommRingCat.of k))).toGrp) := by
  let S := Spec (CommRingCat.of k)
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  have hNonempty : Nonempty I := by
    by_contra h
    let : IsEmpty I := not_nonempty_iff.mp h
    let emptyIso : splitTorus S I ≅ splitTorus S PEmpty.{u + 1} :=
      Pi.reindex (Equiv.equivPEmpty I) (fun _ : PEmpty.{u + 1} => (Gm S).toGrp)
    have hZero : IsZero T := (Grp.isZero_trivial (Over S)).of_iso
      (e ≪≫ emptyIso ≪≫ TorusExistence.splitTorusEmptyIso)
    exact hi0 (hZero.eq_of_src i 0)
  let j := e.inv ≫ i
  have hj : IsClosedSubgroup j := IsClosedSubgroup.iso_comp e.symm hi
  let : IsAffineHom (splitTorus S I).X.hom := isAffineHom_splitTorus_spec _ I
  let : Smooth (splitTorus S I).X.hom := smooth_splitTorus I
  let : Smooth G.X.hom := SmoothOfRelativeDimension.smooth 1 G.X.hom
  have hGdim : Lie.dimension G = 1 :=
    Lie.dimension_eq_of_smoothOfRelativeDimension G inferInstance
  have hTdim : Lie.dimension (splitTorus S I) = Nat.card I :=
    splitTorus.finrank_lieKernel I k
  have hIso : IsIso j := by
    by_contra h
    have hlt := Lie.dimension_lt_of_proper_closedSubgroup j hj h
    rw [hTdim, hGdim] at hlt
    exact (not_le_of_gt (Nat.card_pos (α := I))) (Nat.lt_one_iff.mp hlt).le
  have hCard : Nat.card I = 1 :=
    hTdim.symm.trans (((Lie.targetEquiv (asIso j) k).finrank_eq).trans hGdim)
  have : Subsingleton I := (Nat.card_eq_one_iff_unique.mp hCard).1
  let : Unique I :=
    { default := Classical.choice hNonempty
      uniq := fun _ => Subsingleton.elim _ _ }
  exact ⟨(asIso j).symm ≪≫ productUniqueIso (fun _ : I => (Gm S).toGrp)⟩

private theorem oneDimensional_isoGa_of_unipotent
    {k : Type u} [Field k] [PerfectField k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hU : IsUnipotent G) : Nonempty (G ≅ VectorGroup.groupScheme (CommRingCat.of k) 1) :=
  RelativeRoot.isVectorGroupOfDimension_iff_nonempty_iso.mp
    (perfectFieldOneDimensionalUnipotent k G inferInstance hU)

private theorem oneDimensional_gaForm_of_unipotent
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hU : IsUnipotent G) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      FiniteDimensional k K ∧ IsPurelyInseparable k K ∧
        Nonempty ((baseChange (algebraBaseMap k K)).obj G ≅
          VectorGroup.groupScheme (CommRingCat.of K) 1) := by
  let P := perfectClosure k (AlgebraicClosure k)
  let b := algebraBaseMap k P
  let Gp := (baseChange b).obj G
  let : Smooth G.X.hom := SmoothOfRelativeDimension.smooth 1 G.X.hom
  let : SmoothOfRelativeDimension 1 Gp.X.hom := smoothOfRelativeDimension_one_baseChange b G
  let : IsAffineHom Gp.X.hom := TorusExistence.isAffineHom_baseChange P G
  let : ConnectedSpace Gp.X.left := G.connectedSpace_baseChange_of_smooth_affine b
  obtain ⟨e⟩ := oneDimensional_isoGa_of_unipotent Gp (IsUnipotent.baseChange hU)
  let V := VectorGroup.groupScheme (CommRingCat.of k) 1
  let : SmoothOfRelativeDimension 1 V.X.hom :=
    VectorGroup.smoothOfRelativeDimension (CommRingCat.of k) 1
  let : Smooth V.X.hom := SmoothOfRelativeDimension.smooth 1 V.X.hom
  obtain ⟨E, ⟨eE⟩⟩ := exists_finiteIntermediateField_iso k P G V
    (e ≪≫ (VectorGroup.baseChangeIso (n := 1) (CommRingCat.ofHom (algebraMap k P))).symm)
  let : FiniteDimensional k E.1 := E.2
  exact ⟨E.1, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨eE ≪≫ VectorGroup.baseChangeIso (n := 1) (CommRingCat.ofHom (algebraMap k E.1))⟩⟩

/-- **Milne 2017, Corollary 16.16.** The multiplicative and additive forms of smooth
connected affine groups of dimension one, including the split conclusion over an
algebraically closed ground field. -/
theorem oneDimensionalGroupForms : OneDimensionalGroupFormsStatement.{u} := by
  classical
  intro k _ G _ _ hConn
  let : Smooth G.X.hom := SmoothOfRelativeDimension.smooth 1 G.X.hom
  by_cases hTori : HasNoNontrivialClosedTorus G
  · have hU : IsUnipotent G := by
      apply noTorusUnipotent k G
      intro T hT f
      obtain ⟨Z, i, p, hZ, hi, hfac⟩ := torusImageClosedTorusStatement k G T.toGrp hT f
      have hi0 := SubgroupFunctor.eq_zero_of_range_eq_bot (hTori Z hZ i hi)
      rw [← hfac, hi0, comp_zero, SubgroupFunctor.range_zero]
    refine ⟨Or.inr (oneDimensional_gaForm_of_unipotent G hU), ?_⟩
    intro hClosed
    exact Or.inr (oneDimensional_isoGa_of_unipotent G hU)
  · unfold HasNoNontrivialClosedTorus at hTori
    push Not at hTori
    obtain ⟨T, hT, i, hi, hRange⟩ := hTori
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hRange SubgroupFunctor.range_zero
    constructor
    · obtain ⟨K, _, _, hFin, hGal, hSplit⟩ := torusFiniteGaloisSplitting k T.toGrp hT
      let b := algebraBaseMap k K
      let Gk := (baseChange b).obj G
      let iK := (baseChange b).map i
      let : SmoothOfRelativeDimension 1 Gk.X.hom := smoothOfRelativeDimension_one_baseChange b G
      let : IsAffineHom Gk.X.hom := TorusExistence.isAffineHom_baseChange K G
      let : ConnectedSpace Gk.X.left := G.connectedSpace_baseChange_of_smooth_affine b
      have hiK0 : iK ≠ 0 := by
        let := GaloisCocharacterDescent.faithful_algebraPullback k K
        intro hZero
        apply hi0 ((baseChange b).map_injective _)
        simpa only [CentralRigidity.baseChange_map_zero] using hZero
      exact Or.inl ⟨K, inferInstance, inferInstance, hFin, hGal.to_isSeparable,
        oneDimensional_isoGm_of_closed_splitTorus hSplit iK (hi.baseChange b) hiK0⟩
    · intro hClosed
      exact Or.inl (oneDimensional_isoGm_of_closed_splitTorus
        (toriAreSplit_of_isSepClosed k T.toGrp hT) i hi hi0)

end Langlands.GroupScheme
