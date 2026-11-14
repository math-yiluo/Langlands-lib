import Langlands.GroupScheme.OrthogonalMatrix.Reductive
import Langlands.GroupScheme.CentralIsogeny.MaximalTorusImageSmooth
import Langlands.GroupScheme.Rational.SplitTorusFppfImage
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.HomDescent

/-! # Transport of a supplied orthogonal-cover torus -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

/-- A character descends through an fpqc homomorphism exactly when it kills
its full kernel on every relative test scheme. -/
theorem characterLattice.exists_comp_eq_iff_kills_kernel
    {S : Scheme.{u}} {T Q : CommGroupScheme S} (q : T.toGrp ⟶ Q.toGrp)
    [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left]
    [Surjective q.hom.hom.left] (chi : characterLattice T) :
    (∃ psi : characterLattice Q, q ≫ CommGroupScheme.groupHom psi =
      CommGroupScheme.groupHom chi) ↔
      ∀ (U : Over S) (t : U ⟶ T.X), t ≫ q.hom.hom = 1 →
        t ≫ (CommGroupScheme.groupHom chi).hom.hom = 1 := by
  constructor
  · rintro ⟨psi, hpsi⟩ U t ht
    rw [← hpsi, Grp.comp_hom_hom, ← Category.assoc, ht, MonObj.one_comp]
  · intro h
    have hk : kernelι q ≫ CommGroupScheme.groupHom chi = 0 := by
      apply Grp.hom_ext
      exact h _ (kernelι q).hom.hom ((kernelPointsEquiv q _ (𝟙 _)).property)
    exact ⟨Additive.ofMul (FpqcHomDescent.hom q (CommGroupScheme.groupHom chi) hk),
      FpqcHomDescent.fac q (CommGroupScheme.groupHom chi) hk⟩

namespace OrthogonalMatrix

variable {k : Type u} [Field k]
  {l : Type} [Fintype l] [DecidableEq l] [Nontrivial l]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- After a rational inner automorphism of the target, the actual supplied
split maximal torus maps to the standard orthogonal torus by an fpqc map. -/
theorem exists_standardTorus_square
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    (pi : G ⟶ identityComponent (groupScheme l (CommRingCat.of k)))
    (hpi : IsCentralIsogeny pi) :
    ∃ (g : rationalPoints (identityComponent (groupScheme l (CommRingCat.of k))))
      (t : T ⟶ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)),
      i ≫ pi ≫ ((identityComponent (groupScheme l (CommRingCat.of k))).innerIso g).hom =
        CommGroupScheme.groupHom t ≫ identityTorus l k ∧
      Flat (CommGroupScheme.groupHom t).hom.hom.left ∧
      Surjective (CommGroupScheme.groupHom t).hom.hom.left ∧
      QuasiCompact (CommGroupScheme.groupHom t).hom.hom.left := by
  have := hG.smooth
  let H := identityComponent (groupScheme l (CommRingCat.of k))
  have hH := isConnectedReductive_identityComponent l k
  have := hH.isAffineHom
  have := hH.smooth
  have := hH.connectedSpace
  let E := hT.fppfImage (i ≫ pi)
  have hE : IsMaximalTorus E.inclusion :=
    hpi.isMaximalTorus_of_comp_eq (CommGroupScheme.groupHom E.projection) hi
      E.isSplitSubtorus.1.isTorus E.isSplitSubtorus.2 E.factorization.symm
  obtain ⟨g, e, he⟩ := smoothMaximalSplitTorusConjugacy k H E.torus
    (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l))
    E.inclusion (identityTorus l k) (hE.isMaximalSplitTorus E.isSplitSubtorus.1)
    ((isMaximalTorus_identityTorus l k).isMaximalSplitTorus
      (SymplecticMatrix.isSplitTorus_diagonalTorus l k))
  let t : T ⟶ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l) :=
    E.projection ≫ Additive.ofMul e.hom
  refine ⟨g, t, ?_, ?_, ?_, ?_⟩
  · change (i ≫ pi) ≫ (H.innerIso g).hom = _
    rw [← E.factorization, Category.assoc, he, ← Category.assoc]
    rfl
  · have := E.flat
    have : IsIso e.hom.hom.hom.left :=
      (Over.forget _).map_isIso ((Grp.forget _).map e.hom)
    change Flat ((CommGroupScheme.groupHom E.projection).hom.hom.left ≫ e.hom.hom.hom.left)
    infer_instance
  · have := E.surjective
    have : IsIso e.hom.hom.hom.left :=
      (Over.forget _).map_isIso ((Grp.forget _).map e.hom)
    change Surjective ((CommGroupScheme.groupHom E.projection).hom.hom.left ≫ e.hom.hom.hom.left)
    infer_instance
  · have := hT.isAffineHom
    have := (SymplecticMatrix.isSplitTorus_diagonalTorus l k).isAffineHom
    infer_instance

/-- A comparison of the supplied torus with the standard torus, including
the rational conjugation and fpqc properties of the comparison map. -/
structure StandardTorusTransport
    (i : T.toGrp ⟶ G)
    (pi : G ⟶ identityComponent (groupScheme l (CommRingCat.of k))) where
  point : rationalPoints (identityComponent (groupScheme l (CommRingCat.of k)))
  torusMap : T ⟶ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)
  square : i ≫ pi ≫
      ((identityComponent (groupScheme l (CommRingCat.of k))).innerIso point).hom =
    CommGroupScheme.groupHom torusMap ≫ identityTorus l k
  flat : Flat (CommGroupScheme.groupHom torusMap).hom.hom.left
  surjective : Surjective (CommGroupScheme.groupHom torusMap).hom.hom.left
  quasiCompact : QuasiCompact (CommGroupScheme.groupHom torusMap).hom.hom.left

/-- Choose an fpqc comparison with the standard torus over the original field. -/
def standardTorusTransport
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    (pi : G ⟶ identityComponent (groupScheme l (CommRingCat.of k)))
    (hpi : IsCentralIsogeny pi) : StandardTorusTransport i pi := by
  let ⟨g, hg⟩ := Classical.indefiniteDescription _
    (exists_standardTorus_square hG hT i hi pi hpi)
  let ⟨t, ht⟩ := Classical.indefiniteDescription _ hg
  exact ⟨g, t, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2⟩

end OrthogonalMatrix
end Langlands.GroupScheme
