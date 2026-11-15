import Langlands.GroupScheme.Rational.SimpleRootFiberCoordinates
import Langlands.GroupScheme.Rational.SimpleRootFiberCoroot
import Langlands.GroupScheme.Rational.SimpleRootFiberProducts
import Langlands.GroupScheme.Rational.OrthogonalOrbitWeylNormalizer
import Langlands.Geometry.Building.AlgebraicRankOneCoordinatesExistenceStatement
import Langlands.Geometry.Building.AlgebraicSU3RootCoordinatesExistenceStatement
import Langlands.Geometry.Building.QuasiSplitR1RootFieldCoordinatesReduction
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # Construction of algebraic SL2 rank-one coordinates at non-multipliable roots -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.GroupScheme.SimpleRootFiber

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
  (f : S ⟶ T) (j : T.toGrp ⟶ G)

local notation "bK" => algebraBaseMap k K

variable {J : Type u} [Finite J]
  {P : RootDatum J
    (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))}
  (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map j) P)
  (hf : IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ j))
  (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
  (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)
  [P.IsReduced]
  (ν : cocharacterLattice S)
  (hν : IsGenericCocharacter (CommGroupScheme.groupHom f ≫ j) ν)
  [FiniteDimensional k K]
  (hGK : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
  (hi : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map j))
  [IsGalois k K] (hjc : IsClosedSubgroup j) [Smooth G.X.hom]
  {a : characterLattice S} (ha : a ∈ simpleRelativeRoots (CommGroupScheme.groupHom f ≫ j) ν)
  (h2a : 2 • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
  [Mono (CommGroupScheme.groupHom f ≫ j).hom.hom.left]
  (hR : HasRelativeRootSystem (CommGroupScheme.groupHom f ≫ j))
  [Fintype (fiberSet k K f j hP hf hcent hT ν hν hGK hi a)]
  (hProd : Langlands.Geometry.Building.SplitRelativeRootGroupProductStatement.{u})

/-- Algebraic `SL₂` coordinates at a simple relative root `a` with `2 • a` not a relative
root, built over the fiber field from the fiber pinning. -/
def fiberSL2Coordinates :
    Langlands.Geometry.Building.AlgebraicSL2RootCoordinates (CommGroupScheme.groupHom f ≫ j) j
      (CommGroupScheme.groupHom f) a where
  extension := fiberField k K f j hP hf hcent hT ν hν hGK hi ha
  positive := positiveCoordinates k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a
    (fiber_hprodp k K f j hP hf hcent hT ν hν hGK hi ha h2a hR hProd)
    (fiber_huniqp k K f j hP hf hcent hT ν hν hGK hi ha h2a hR hProd)
  negative := negativeCoordinates k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a
    (fiber_hprodm k K f j hP hf hcent hT ν hν hGK hi ha h2a hR hProd)
    (fiber_huniqm k K f j hP hf hcent hT ν hν hGK hi ha h2a hR hProd)
  rho := SplitPinning.fieldSL2 k K j (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).pinning
    (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).torusIso
    (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).inclusion_eq
    (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).rootMaps
    (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).rootMaps_compatible
    (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).action_root
    (fiberSet k K f j hP hf hcent hT ν hν hGK hi a)
    (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a)
    (fiberSet_isOrthogonal k K f j hP hf hcent hT ν hν hGK hi ha h2a)
    (fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha)
    (fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha)
  rho_upper _ := rfl
  rho_lower _ := rfl
  coroot := CommGroupScheme.groupHom (fiberCoroot k K f j hP hf hcent hT ν hν hGK hi hjc ha)
  coroot_points t := fiberCoroot_points k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a t

include hjc in
/-- The Weyl matrix of the constructed coordinates normalizes the maximal split torus. -/
theorem fiberSL2Coordinates_weyl :
    (fiberSL2Coordinates k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd).rho
        SpecialLinear.BinaryUpper.weylMatrix ∈
      normalizerPoints (CommGroupScheme.groupHom f ≫ j) := by
  have : IsClosedImmersion j.hom.hom.left := hjc
  apply IsMaximalSplitTorus.mem_normalizerPoints_of_mem_normalizerPoints _ j hf
  exact SplitPinning.fieldSL2_weylMatrix_mem k K j
    (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).pinning
    (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).torusIso
    (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).inclusion_eq
    (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).rootMaps
    (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).rootMaps_compatible
    (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).action_root
    (fiberSet k K f j hP hf hcent hT ν hν hGK hi a)
    (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a)
    (fiberSet_isOrthogonal k K f j hP hf hcent hT ν hν hGK hi ha h2a)
    (fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha)
    (fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha)

end Langlands.GroupScheme.SimpleRootFiber

namespace Langlands.Geometry.Building

/-- **The SL2 clause, given the split product statement.** Under the hypotheses of
`AlgebraicRankOneCoordinatesExistenceStatement`, every indivisible relative root `b` with
`2 • b` not a relative root has algebraic `SL₂` coordinates whose Weyl matrix normalizes the
maximal split torus, provided `SplitRelativeRootGroupProductStatement` holds. -/
theorem exists_algebraicSL2RootCoordinates_of_product
    (hProd : SplitRelativeRootGroupProductStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) [IsAffineHom G.X.hom]
    (S Z : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : S.toGrp ⟶ G) (j : Z.toGrp ⟶ G) (s : S.toGrp ⟶ Z.toGrp)
    (hi : IsMaximalSplitTorus i) (hZ : IsTorus Z.toGrp)
    (hj : (torusCentralizer i).IsRepresentedBy j) (hs : s ≫ j = i)
    (b : characterLattice S) (hb : b ∈ RelativeRoot.indivisibleRoots i)
    (h2 : 2 • b ∉ relativeRoots i) :
    ∃ C : AlgebraicSL2RootCoordinates i j s b,
      C.rho SpecialLinear.BinaryUpper.weylMatrix ∈ normalizerPoints i := by
  subst hs
  let : Smooth G.X.hom := hG.smooth
  let : LocallyOfFiniteType G.X.hom := inferInstance
  have hjc : IsClosedSubgroup j := IsSplitTorus.isClosedSubgroup_torusCentralizer hi.1.1 _ hj
  let : IsAffineHom Z.toGrp.X.hom := hjc.isAffineHom
  let : LocallyOfFiniteType Z.toGrp.X.hom := hjc.locallyOfFiniteType
  let f : S ⟶ Z := Additive.ofMul s
  have hself : torusCentralizer j = SubgroupFunctor.range j :=
    le_antisymm ((torusCentralizer_le_of_factor j (s ≫ j) s rfl).trans hj.2.symm.le)
      (range_le_torusCentralizer j)
  obtain ⟨K, _, _, _, _, hK⟩ := torusFiniteGaloisSplitting k Z.toGrp hZ
  have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  have hGK : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) :=
    hG.baseChange_of_algebraicExtension (K := K)
  have hiK : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj Z)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map j) :=
    isMaximalTorus_baseChange_of_torusCentralizer_eq K hZ hjc hself
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence K
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) hGK
    ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj Z) hK
    ((GroupScheme.baseChange (algebraBaseMap k K)).map j) hiK
  let : Finite J := hJ
  let : P.IsReduced := hred
  let : Mono (s ≫ j).hom.hom.left := hi.isSplitSubtorus.mono
  let : Mono (CommGroupScheme.groupHom f ≫ j).hom.hom.left := hi.isSplitSubtorus.mono
  have hR : HasRelativeRootSystem (s ≫ j) := relativeRootSystem k G hG S (s ≫ j) hi
  obtain ⟨ν, hν, hbν⟩ :=
    RelativeRoot.exists_isGenericCocharacter_mem_simpleRelativeRoots (s ≫ j) hR hi.1.1 hb
  let : Fintype (SimpleRootFiber.fiberSet k K f j hP hi hj hK ν hν hGK hiK b) :=
    Fintype.ofFinite _
  exact ⟨SimpleRootFiber.fiberSL2Coordinates k K f j hP hi hj hK ν hν hGK hiK hjc hbν h2 hR hProd,
    SimpleRootFiber.fiberSL2Coordinates_weyl k K f j hP hi hj hK ν hν hGK hiK hjc hbν h2 hR
      hProd⟩

/-- **Reduction of the rank-one coordinate existence to two statements.** The SL2 clause
follows from `SplitRelativeRootGroupProductStatement`, and the SU3 clause is
`AlgebraicSU3RootCoordinatesExistenceStatement`. -/
theorem algebraicRankOneCoordinatesExistence_of_product_of_su3
    (hProd : SplitRelativeRootGroupProductStatement.{u})
    (hSU3 : AlgebraicSU3RootCoordinatesExistenceStatement.{u}) :
    AlgebraicRankOneCoordinatesExistenceStatement.{u} := by
  intro k _ G hG S Z i j s hi hZ hj hs b hb
  have : IsAffineHom G.X.hom := hG.isAffineHom
  exact ⟨fun h2 => exists_algebraicSL2RootCoordinates_of_product hProd k G hG S Z i j s hi hZ hj
      hs b hb h2,
    fun h2 => hSU3 k G hG S Z i j s hi hZ hj hs b hb h2⟩

end Langlands.Geometry.Building
