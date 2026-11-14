import Langlands.GroupScheme.Rational.RationalRootRestriction
import Langlands.GroupScheme.Rational.RootFixedTorusSplitting
import Langlands.GroupScheme.Rational.QuasiSplitSimplyLacedSplittingStatement
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Splitting from injective rational root restriction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  [hfin : FiniteDimensional k L] [hgal : IsGalois k L]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local notation "b" => algebraBaseMap k L
local notation "T_L" => Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_L" => Functor.obj (GroupScheme.baseChange b) G
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b)

local instance : IsAffineHom (G_L).X.hom :=
  MorphismProperty.baseChange_obj (P := @IsAffineHom) b G.X inferInstance

local instance : LocallyOfFiniteType (G_L).X.hom :=
  MorphismProperty.baseChange_obj (P := @LocallyOfFiniteType) b G.X inferInstance

namespace IsQuasiSplit

variable (hG : IsQuasiSplit G) (hss : IsSemisimple G)
  (a : S.toGrp ⟶ G) (j : T.toGrp ⟶ G) (f : S ⟶ T)
  (ha : IsMaximalSplitTorus a) (hj : IsMaximalTorus j)
  (hf : CommGroupScheme.groupHom f ≫ j = a)
  (hTL : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)

include hG hss a j f ha hj hf hTL hfin hgal

/-- Injective rational restriction fixes all actual roots, hence descends the
containing maximal torus as a split torus over the original field. -/
theorem isSplitTorus_of_rationalRootRestriction_injective
    (hinj : Function.Injective (hG.rationalRootRestriction (L := L) a j f ha hj hf hTL)) :
    IsSplitTorus T.toGrp := by
  let : Smooth G.X.hom := hss.isConnectedReductive.smooth
  have hjL : IsMaximalTorus (T := T_L) (G := G_L) (j_L j) :=
    (maximalTorusBaseChange k L G T j hj.1 hj.2.1).mp hj
  apply isSplitTorus_of_galoisFixed_roots
    (hss.baseChange_of_algebraicExtension (K := L)) j hjL hTL
  exact hG.root_galois_eq_self_of_rationalRootRestriction_injective
    (L := L) a j f ha hj hf hTL hinj

/-- The actual factor into the containing maximal torus is an isomorphism
once rational restriction is injective. -/
def torusFactorIsoOfRationalRootRestriction
    (hinj : Function.Injective (hG.rationalRootRestriction (L := L) a j f ha hj hf hTL)) :
    S.toGrp ≅ T.toGrp := by
  have hT := hG.isSplitTorus_of_rationalRootRestriction_injective
    hss a j f ha hj hf hTL hinj
  letI : IsIso (CommGroupScheme.groupHom f) := ha.2 T j ⟨hT, hj.2.1⟩ _ hf
  exact asIso (CommGroupScheme.groupHom f)

@[simp]
theorem torusFactorIsoOfRationalRootRestriction_hom
    (hinj : Function.Injective (hG.rationalRootRestriction (L := L) a j f ha hj hf hTL)) :
    (hG.torusFactorIsoOfRationalRootRestriction hss a j f ha hj hf hTL hinj).hom =
      CommGroupScheme.groupHom f := rfl

/-- The original maximal split torus is a maximal torus once rational root
restriction to it is injective. -/
theorem isMaximalTorus_of_rationalRootRestriction_injective
    (hinj : Function.Injective (hG.rationalRootRestriction (L := L) a j f ha hj hf hTL)) :
    IsMaximalTorus a := by
  have h := hj.iso_comp
    (hG.torusFactorIsoOfRationalRootRestriction hss a j f ha hj hf hTL hinj)
  simpa only [torusFactorIsoOfRationalRootRestriction_hom, hf] using h

variable {I J : Type*}
  (P : RootPairing I ℚ (relativeRootSpan a) (Module.Dual ℚ (relativeRootSpan a)))
  (Q : RootPairing J ℚ
    (relativeRootSpan
      (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j))
    (Module.Dual ℚ (relativeRootSpan
      (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j))))
  [P.IsRootSystem] [Q.IsRootSystem] [Q.IsIrreducible]
  (hP : Subtype.val '' Set.range P.root = toRat '' relativeRoots a)
  (hQ : Subtype.val '' Set.range Q.root =
    toRat '' relativeRoots
      (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j))
  (hs : ∀ i j, P.pairing i j = P.pairing j i)

include P Q hP hQ hs

/-- An irreducible actual source root system and a symmetric full target
root system force splitting of the containing maximal torus. -/
theorem isSplitTorus_of_rootSystems : IsSplitTorus T.toGrp :=
  hG.isSplitTorus_of_rationalRootRestriction_injective hss a j f ha hj hf hTL
    (hG.rationalRootRestriction_injective_of_rootSystems
      (L := L) a j f ha hj hf hTL P Q hP hQ hs)

/-- The same explicit root-system data make the original maximal split
torus a maximal torus. -/
theorem isMaximalTorus_of_rootSystems : IsMaximalTorus a :=
  hG.isMaximalTorus_of_rationalRootRestriction_injective hss a j f ha hj hf hTL
    (hG.rationalRootRestriction_injective_of_rootSystems
      (L := L) a j f ha hj hf hTL P Q hP hQ hs)

omit P hP hs in
/-- The published full reduced simply-laced target predicate supplies the
target data; the irreducible actual source root system remains explicit. -/
theorem isMaximalTorus_of_hasReducedSimplyLacedRelativeRootSystem
    (hroot : HasReducedSimplyLacedRelativeRootSystem a) : IsMaximalTorus a := by
  obtain ⟨I, _, P, hsys, _, _, _, hP, hs⟩ := hroot
  let := hsys
  exact hG.isMaximalTorus_of_rootSystems hss a j f ha hj hf hTL P Q hP hQ hs

end IsQuasiSplit

end Langlands.GroupScheme
