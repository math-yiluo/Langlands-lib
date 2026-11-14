import Langlands.GroupScheme.Dynamic.PointedEtaleConjugacy
import Langlands.GroupScheme.Torus.FieldFibreIsomorphism
import Langlands.GroupScheme.Torus.HenselianSplitRank
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof

/-! # Integral conjugacy of closed split tori over a Henselian ring -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace PointwiseSchemeAction

variable {S : Scheme.{u}} {H G : GroupScheme S}
  {j₁ j₂ : H ⟶ G} {g : Over.mk (𝟙 S) ⟶ G.X}

/-- An equality of actual conjugated homomorphisms implies the transporter
relation on all test schemes and their refinements. -/
theorem isTransporter_of_comp_innerIso_eq
    (he : j₂ ≫ (G.innerIso g).hom = j₁) : IsTransporter j₁ j₂ g := by
  intro V a x
  have h := congrArg (fun f : H ⟶ G => x ≫ f.hom.hom) he
  rw [Grp.comp_hom_hom, ← Category.assoc, G.comp_innerIso_hom] at h
  have hc : G.constantPoint g V = a ≫ g := by
    unfold GroupScheme.constantPoint
    congr 1
    apply Over.OverMorphism.ext
    change V.hom = a.left
    have ha := Over.w a
    change a.left ≫ 𝟙 S = V.hom at ha
    exact ha.symm.trans (Category.comp_id _)
  rw [hc] at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

end PointwiseSchemeAction

section IntegralConjugacy

variable {R k : Type u} [CommRing R]
  [Field k] [Algebra R k]
  {G : GroupScheme (Spec (CommRingCat.of R))}
  {T T' : CommGroupScheme (Spec (CommRingCat.of R))}
  (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G)

/-- An actual integral section conjugating two torus inclusions, together with
its actual integral isomorphism of source tori and all-test equation. -/
structure SplitTorusConjugator where
  section_ : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X
  torusIso : T ≅ T'
  isTransporter : PointwiseSchemeAction.IsTransporter
    (CommGroupScheme.groupHom torusIso.hom ≫ i') i section_

/-- The recorded integral section conjugates the actual integral maps with
the specified isomorphism of the two commutative source groups. -/
theorem SplitTorusConjugator.comm (A : SplitTorusConjugator i i') :
    i ≫ (G.innerIso A.section_).hom =
      CommGroupScheme.groupHom A.torusIso.hom ≫ i' :=
  A.isTransporter.comp_innerIso_eq

variable [HenselianLocalRing R]

/-- Residue-maximal closed split tori in a smooth affine Henselian group with
connected residue fibre have an actual integral conjugator. -/
theorem exists_splitTorusConjugator_of_residue
    [IsAffineHom G.X.hom] (hG : Smooth G.X.hom)
    (hk : Function.Surjective (algebraMap R k))
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    [ConnectedSpace ((baseChange (Spec.algebraMap R k)).obj G).X.left]
    (hi : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T)
      ((baseChange (Spec.algebraMap R k)).map i))
    (hi' : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T')
      ((baseChange (Spec.algebraMap R k)).map i')) :
    Nonempty (SplitTorusConjugator i i') := by
  let b := Spec.algebraMap R k
  let : Smooth G.X.hom := hG
  let : Smooth ((baseChange b).obj G).X.hom :=
    inferInstanceAs (Smooth (Limits.pullback.snd G.X.hom b))
  let : IsAffineHom ((baseChange b).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom b))
  obtain ⟨g₀, e₀, he₀⟩ := smoothMaximalSplitTorusConjugacy k
    ((baseChange b).obj G) ((CommGroupScheme.baseChange b).obj T)
    ((CommGroupScheme.baseChange b).obj T')
    ((baseChange b).map i) ((baseChange b).map i') hi hi'
  let e₀C : (CommGroupScheme.baseChange b).obj T ≅
      (CommGroupScheme.baseChange b).obj T' := CommGroupScheme.isoOfGroupIso e₀
  obtain ⟨e, he⟩ := hT.iso_fieldBaseChange_surjective b hT' e₀C
  have hehom : (baseChange b).map (CommGroupScheme.groupHom e.hom) = e₀.hom := by
    exact congrArg (fun q => CommGroupScheme.groupHom q.hom) he
  have ht : PointwiseSchemeAction.IsTransporter
      ((baseChange b).map (CommGroupScheme.groupHom e.hom ≫ i'))
      ((baseChange b).map i) g₀ := by
    apply PointwiseSchemeAction.isTransporter_of_comp_innerIso_eq
    rw [Functor.map_comp, hehom]
    exact he₀
  let c : Over.mk b ⟶ (Over.map b).obj (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
    Over.homMk (𝟙 _) (by simp)
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨g, hg, -⟩ := PointwiseSchemeAction.exists_henselian_transporter_of_split
    (CommGroupScheme.groupHom e.hom ≫ i') i hT hG hk
    (c ≫ baseChangePointsEquiv b G _ g₀)
    ((ht.baseChangePointsEquiv b).restrict c)
  exact ⟨⟨g, e, hg⟩⟩

/-- Choose the integral conjugator supplied by residue maximality. -/
def henselianSplitTorusConjugatorOfResidue
    [IsAffineHom G.X.hom] (hG : Smooth G.X.hom)
    (hk : Function.Surjective (algebraMap R k))
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    [ConnectedSpace ((baseChange (Spec.algebraMap R k)).obj G).X.left]
    (hi : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T)
      ((baseChange (Spec.algebraMap R k)).map i))
    (hi' : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T')
      ((baseChange (Spec.algebraMap R k)).map i')) : SplitTorusConjugator i i' :=
  Classical.choice (exists_splitTorusConjugator_of_residue i i' hG hk hT hT' hi hi')

/-- Maximality on a connected reductive field fibre supplies the residue
maximality needed for actual integral conjugacy of two closed split tori. -/
def henselianSplitTorusConjugator
    {K : Type u} [Field K] [Algebra R K]
    [IsAffineHom G.X.hom] (hG : Smooth G.X.hom)
    (hk : Function.Surjective (algebraMap R k))
    (hGK : IsConnectedReductive ((baseChange (Spec.algebraMap R K)).obj G))
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    [ConnectedSpace ((baseChange (Spec.algebraMap R k)).obj G).X.left]
    (hi : IsClosedSubgroup i) (hi' : IsClosedSubgroup i')
    (hiK : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T)
      ((baseChange (Spec.algebraMap R K)).map i))
    (hiK' : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T')
      ((baseChange (Spec.algebraMap R K)).map i')) : SplitTorusConjugator i i' := by
  let : Smooth G.X.hom := hG
  exact henselianSplitTorusConjugatorOfResidue i i' hG hk hT hT'
    (isMaximalSplitTorus_residue_of_generic hk G hGK T hT i hi hiK)
    (isMaximalSplitTorus_residue_of_generic hk G hGK T' hT' i' hi' hiK')

end IntegralConjugacy

end Langlands.GroupScheme
