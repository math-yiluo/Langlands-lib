import Langlands.GroupScheme.CentralIsogeny.RootDatumOfComparisons
import Langlands.GroupScheme.CentralIsogeny.TorusRestrictionIsogeny
import Langlands.GroupScheme.CentralIsogeny.SplitRootDatumStatement
import Langlands.GroupScheme.Rational.CentralSurjectionMaximalSplitTorusImageProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerStatement
import Langlands.GroupScheme.Torus.WeylImageFiniteStatement

/-! # Reduction of the central-isogeny root-datum theorem to geometric inputs -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

section Restriction

variable {k : Type u} [Field k]
  {G G' : GroupScheme (Spec (CommRingCat.of k))}
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'} {φ : G ⟶ G'}

/-- The restriction of a central isogeny to supplied split maximal tori is an
isogeny, using the proved maximality theorem for split-torus images. -/
theorem IsCentralIsogeny.isIsogeny_torusRestriction
    (hφ : IsCentralIsogeny φ) (hG : IsConnectedReductive G)
    (hG' : IsConnectedReductive G')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i') (t : T ⟶ T')
    (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i') :
    IsIsogeny (CommGroupScheme.groupHom t) :=
  hφ.isIsogeny_torusRestriction_of_maximalImage
    centralSurjectionMaximalSplitTorusImage hG hG' hT hT' hi hi' t ht

/-- An actual reverse torus homomorphism up to multiplication by a nonzero
integer, with no separate maximal-image premise. -/
def IsCentralIsogeny.torusRestrictionQuasiInverse
    (hφ : IsCentralIsogeny φ) (hG : IsConnectedReductive G)
    (hG' : IsConnectedReductive G')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i') (t : T ⟶ T')
    (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i') :
    TorusRestrictionQuasiInverse t :=
  hφ.torusRestrictionQuasiInverseOfMaximalImage
    centralSurjectionMaximalSplitTorusImage hG hG' hT hT' hi hi' t ht

variable [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType G'.X.hom]
  {J : Type v} {J' : Type w}
  (P : RootDatum J (characterLattice T) (cocharacterLattice T))
  (P' : RootDatum J' (characterLattice T') (cocharacterLattice T'))

/-- The actual root-datum morphism for split maximal tori, retaining only the
self-centralizer, ambient Lie dimension and full Weyl-image finiteness inputs. -/
def IsCentralIsogeny.rootDatumHomOfMaximalTori
    (hφ : IsCentralIsogeny φ) (hG : IsConnectedReductive G)
    (hG' : IsConnectedReductive G')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i') (t : T ⟶ T')
    (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (hself : torusCentralizer i = SubgroupFunctor.range i)
    (hself' : torusCentralizer i' = SubgroupFunctor.range i')
    (hdim : Lie.dimension G = Lie.dimension G')
    (hweyl : haveI : IsClosedImmersion i'.hom.hom.left := hi'.2.1
      Finite (weylImage i'))
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P') :
    RootPairing.Hom P' P :=
  hφ.rootDatumHomOfComparisons P P' hT hT' hi.2.1 hi'.2.1 t ht
    (hφ.isIsogeny_torusRestriction hG hG' hT hT' hi hi' t ht)
    hself hself' hdim hweyl hP hP'

end Restriction

/-- The complete published target follows from the three remaining geometric
input families. None of those input families is asserted here. -/
theorem centralIsogenyRootDatumHom_of_geometric_inputs
    (hself : MaximalTorusCentralizerStatement.{u})
    (hweyl : SplitTorusWeylImageFiniteStatement.{u})
    (hdim : ∀ (k : Type u) [Field k]
      (G G' : GroupScheme (Spec (CommRingCat.of k)))
      (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
      (φ : G ⟶ G'), IsCentralIsogeny φ →
        (haveI := hG.isAffineHom
         haveI := hG'.isAffineHom
         Lie.dimension G = Lie.dimension G')) :
    CentralIsogenyRootDatumHomStatement.{u} := by
  intro k _ G G' hG hG' T T' hT hT' i i' hi hi' φ t hφ ht J J' P P' hP hP'
  have := hG.isAffineHom
  have := hG'.isAffineHom
  have := hG.smooth
  have := hG'.smooth
  have hselfi := hself k G hG T i hi
  have hselfi' := hself k G' hG' T' i' hi'
  have hdimφ := hdim k G G' hG hG' φ hφ
  have hweyli' := hweyl k G' T' hT' i' hi'.2.1
  refine ⟨hφ.rootDatumHomOfMaximalTori P P' hG hG' hT hT' hi hi' t ht
    hselfi hselfi' hdimφ hweyli' hP hP', ?_⟩
  exact hφ.rootDatumHomOfComparisons_spec P P' hT hT' hi hi'.2.1 t ht
    (hφ.isIsogeny_torusRestriction hG hG' hT hT' hi hi' t ht)
    hselfi hselfi' hdimφ hweyli' hP hP'

end Langlands.GroupScheme
