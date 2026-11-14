import Langlands.Geometry.Building.ActualRootHeisenbergSeparation
import Langlands.Geometry.Building.RootGroupTorusValueAction
import Langlands.Geometry.Building.QuasiSplitR1RootFieldCoordinatesReduction
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.QuasiSplitMaximalTorusCentralizerProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof

/-! # Actual unitary root coordinates over infinite fields -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

open Langlands.GroupScheme Langlands.GroupScheme.RelativeRoot

/-- The actual one-sign unitary root-coordinate assertion for quasi-split
 groups over infinite fields. -/
def InfiniteQuasiSplitR2RootUnitaryCoordinatesStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom],
    IsQuasiSplit G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
      ∀ (Z : GroupScheme (Spec (CommRingCat.of k))) (j : Z ⟶ G),
        (torusCentralizer i).IsRepresentedBy j →
        ∀ (s : S.toGrp ⟶ Z), s ≫ j = i →
        ∀ a : characterLattice S,
          a ∈ relativeRoots i → 2 • a ∈ relativeRoots i →
            Nonempty (RootUnitaryCoordinates i j s a)

section SplitPresentation

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (f : S ⟶ T) (j : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k L
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "T_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j

local instance : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- The actual structural hypotheses construct the root quotient, equivariant
normal form and unitary coordinates, without supplying any of these data. -/
theorem nonempty_rootUnitaryCoordinates_of_torusCentralizer [Infinite k]
    [FiniteDimensional k L] [IsGalois k L]
    [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hG : IsConnectedReductive G) (hjc : IsClosedSubgroup j)
    (hf : IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ j))
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (hT : IsSplitTorus (T_L).toGrp)
    {J : Type u} [Finite J]
    {P : RootDatum J (characterLattice T_L) (cocharacterLattice T_L)}
    (hP : IsRootDatumOf (T := T_L) j_L P)
    {a : characterLattice S}
    (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (h2a : 2 • a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j)) :
    Nonempty (RootUnitaryCoordinates (CommGroupScheme.groupHom f ≫ j) j
      (CommGroupScheme.groupHom f) a) := by
  have hS : IsSplitTorus S.toGrp := hf.1.1
  have ha0 : a ≠ 0 := (mem_relativeRoots.mp ha).1
  obtain ⟨Q⟩ := nonempty_quotientPackage k f j hS ha0 hhigh
  let : IsAffineHom Q.U.X.hom := Q.affineU
  let : IsAffineHom Q.C.V.X.hom := Q.affineV
  have h2a0 : 2 • a ≠ 0 := hS.nsmul_ne_zero ha0 (by omega)
  obtain ⟨m, e, he⟩ := weightVectorCoordinatesOfNoHigherRoots hS
    (CommGroupScheme.groupHom f ≫ j) h2a0 (hasNoHigherRoots_two_nsmul hhigh) Q.hj₂
  let : IsAffineHom Q.U₂.X.hom := IsVectorGroupOfDimension.isAffineHom ⟨e, he.1⟩
  have hfix := conjugation_act_of_torusCentralizer k f j hcent
  have hD : IsTorus T.toGrp := ⟨L, inferInstance, inferInstance, hT⟩
  have hs : ∀ (X : Over (Spec (CommRingCat.of k))) (t : X ⟶ S.X) (g : X ⟶ G.X),
      (AutomorphicAction.conjugation j).act (t ≫ (CommGroupScheme.groupHom f).hom.hom) g =
        (t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom) * g *
          (t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom)⁻¹ := by
    intro X t g
    rw [AutomorphicAction.conjugation_act, Grp.comp_hom_hom, Category.assoc]
  obtain ⟨N⟩ := nonempty_equivariantHeisenbergNormalForm Q.C hS ha0 hhigh hD
    (AutomorphicAction.conjugation j) hfix (CommGroupScheme.groupHom f) hs
  obtain ⟨R⟩ := hasActualRootHeisenbergSeparationData k L f j Q.C N hG hjc hf hcent hT hP
    ha h2a hhigh
  exact ⟨(R.toHeisenbergUnitaryData hS ha0 hhigh).rootUnitaryCoordinates⟩

end SplitPresentation

/-- Every multipliable root of an actual quasi-split group over an infinite
field has one-sign unitary coordinates, with no supplied splitting or coordinate data. -/
theorem infiniteQuasiSplitR2RootUnitaryCoordinates :
    InfiniteQuasiSplitR2RootUnitaryCoordinatesStatement.{u} := by
  intro k _ _ G _ hG S i hi Z j hj s hs a ha h2a
  subst hs
  have hZ : IsTorus Z := isTorus_of_quasiSplit_torusCentralizer
    quasiSplitTorusCentralizerExistence maximalSplitTorusConjugacy hG hi hj
  have hGr := hG.isConnectedReductive
  let : Smooth G.X.hom := hGr.smooth
  let : LocallyOfFiniteType G.X.hom := inferInstance
  have hjc : IsClosedSubgroup j := IsSplitTorus.isClosedSubgroup_torusCentralizer hi.1.1 _ hj
  let T : CommGroupScheme (Spec (CommRingCat.of k)) := { Z with comm := hZ.isCommMonObj }
  let jT : T.toGrp ⟶ G := j
  let f : S ⟶ T := Additive.ofMul s
  let : IsAffineHom T.toGrp.X.hom := hjc.isAffineHom
  let : LocallyOfFiniteType T.toGrp.X.hom := hjc.locallyOfFiniteType
  have hself : torusCentralizer jT = SubgroupFunctor.range jT :=
    le_antisymm ((torusCentralizer_le_of_factor jT (s ≫ j) s rfl).trans hj.2.symm.le)
      (range_le_torusCentralizer jT)
  obtain ⟨K, _, _, _, _, hK⟩ := torusFiniteGaloisSplitting k Z hZ
  let : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  obtain ⟨J, _, P, hP, -⟩ := rootDatumExistence K
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (hGr.baseChange_of_algebraicExtension (K := K))
    ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) hK
    ((GroupScheme.baseChange (algebraBaseMap k K)).map jT)
    (isMaximalTorus_baseChange_of_torusCentralizer_eq K hZ hjc hself)
  let : Mono (s ≫ j).hom.hom.left := hi.isSplitSubtorus.mono
  have hR := relativeRootSystem k G hGr S (s ≫ j) hi
  have hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (s ≫ j) :=
    fun _ hn => hR.nsmul_not_mem_of_three_le ha hn
  exact nonempty_rootUnitaryCoordinates_of_torusCentralizer k K f jT hGr hjc hi hj hK hP
    ha h2a hhigh

end Langlands.Geometry.Building
