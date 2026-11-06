import Langlands.GroupScheme.Rational.TorusCentralizerRootData
import Langlands.GroupScheme.Rational.GeometricSubgroupTorus
import Langlands.GroupScheme.Rational.CoweightCocenterCharacters
import Langlands.GroupScheme.Rational.CoweightCharacterBaseChange
import Langlands.GroupScheme.Reductive.RootDatumBaseChangeProof
import Langlands.GroupScheme.Derived.MaximalTorusIntersectionReduction
import Langlands.GroupScheme.Derived.MaximalTorusProductSurjectivityStatement
import Langlands.GroupScheme.Derived.SemisimpleStatement
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof

/-! # Actual Levi cocenter root-model assembly from structural inputs -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

local instance assemblyBaseChangeAffine
    {k K : Type u} [Field k] [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom] :
    IsAffineHom ((GroupScheme.baseChange b).obj H).X.hom :=
  MorphismProperty.baseChange_obj (P := @IsAffineHom) b H.X inferInstance

local instance assemblyBaseChangeFiniteType
    {k K : Type u} [Field k] [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (H : GroupScheme (Spec (CommRingCat.of k))) [LocallyOfFiniteType H.X.hom] :
    LocallyOfFiniteType ((GroupScheme.baseChange b).obj H).X.hom :=
  MorphismProperty.baseChange_obj (P := @LocallyOfFiniteType) b H.X inferInstance

namespace characterLattice

/-- Derive the full actual character comparison by constructing the compatible
derived torus only over an algebraic closure, then reflecting the result. -/
theorem cocenter_coweight_comparison_of_structuralInputs
    (hroot : RootDatumExistenceStatement.{u})
    (hsemi : DerivedSubgroupSemisimpleStatement.{u})
    (hproduct : DerivedMaximalTorusProductSurjectivityStatement.{u})
    (hintersection : DerivedMaximalTorusIntersectionStatement.{u})
    {k : Type u} [Field k]
    {G M D : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom M.X.hom] [LocallyOfFiniteType M.X.hom]
    {T Q : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} {t : T.toGrp ⟶ M}
    {J : Type v} {L : Type w}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    {R : RootDatum L (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i P) (hR : IsRootDatumOf t R)
    (j : M ⟶ G) (hcomp : t ≫ j = i)
    (hM : IsConnectedReductive M) (d : D ⟶ M) (hd : IsDerivedSubgroup d)
    (ht : IsMaximalTorus t) (hi : IsClosedSubgroup i)
    (q : M ⟶ Q.toGrp)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q)
    (hT : IsSplitTorus T.toGrp) (hQ : IsSplitTorus Q.toGrp)
    (ν : cocharacterLattice T)
    (hroots : relativeRoots t =
      {α | α ∈ relativeRoots i ∧ latticePairing T α ν = 0}) :
    Function.Injective (precompose (Additive.ofMul (t ≫ q) : T ⟶ Q)) ∧
      ∀ χ, χ ∈ (precompose (Additive.ofMul (t ≫ q) : T ⟶ Q)).toIntLinearMap.range ↔
        ∀ p, P.root' p ν = 0 → P.toLinearMap χ (P.coroot p) = 0 := by
  let K := AlgebraicClosure k
  let b := algebraBaseMap k K
  let B := GroupScheme.baseChange b
  let T' := (CommGroupScheme.baseChange b).obj T
  have hM' : IsConnectedReductive (B.obj M) :=
    connectedReductiveFieldExtensionStatement k K M hM
  let : Smooth M.X.hom := hM.smooth
  let : Smooth (B.obj M).X.hom := hM'.smooth
  let : ConnectedSpace (B.obj M).X.left := hM'.connectedSpace
  have hd' : IsDerivedSubgroup (B.map d) :=
    hd.baseChange_of_eq b (derivedSubgroup_baseChange_eq_of_field b M)
  have hD' : IsConnectedReductive (B.obj D) := hd'.isConnectedReductive hM'
  let : IsAffineHom (B.obj D).X.hom := hD'.isAffineHom
  let : Smooth (B.obj D).X.hom := hD'.smooth
  have ht' : IsMaximalTorus (T := T') (B.map t) :=
    (maximalTorusBaseChange k K M T t ht.1 ht.2.1).mp ht
  let S := hd'.geometricSubgroupTorus (T := T') (B.map t) ht'
  obtain ⟨N, hN, U, hU, _⟩ :=
    hroot K (B.obj D) hD' S.torus S.isSplit S.subgroup S.isMaximal
  have hP' := hP.baseChange (K := K) G T hT i
  have hR' := hR.baseChange (K := K) M T hT t
  have hroots' : relativeRoots (B.map t) =
      {α | α ∈ relativeRoots (B.map i) ∧
        latticePairing T' α (cocharacterLattice.baseChange b T ν) = 0} := by
    ext χ'
    obtain ⟨χ, rfl⟩ := (baseChangeEquiv b T hT).surjective χ'
    simp only [baseChangeEquiv_apply]
    dsimp only [B, b, T']
    simpa only [Set.mem_ofPred_eq, relativeRoots_eq_roots,
      mem_roots_baseChange_iff (K := K) G T hT i,
      mem_roots_baseChange_iff (K := K) M T hT t, latticePairing_baseChange] using
        Set.ext_iff.mp hroots χ
  have hq' : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (B.map d)) (B.map q) := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hq.baseChange b
  have hc := cocenter_coweight_character_comparison
    (T := T') (Q := (CommGroupScheme.baseChange b).obj Q) hP' hR' (B.map j)
    (by rw [← Functor.map_comp, hcomp]) hM' (B.map d) hd'
    (hsemi K (B.obj M) (B.obj D) (B.map d) hM' hd')
    S.subgroup S.isMaximal ht' S.inclusion S.inclusion_comp
    (B.map q) hq' (hT.baseChange b) S.isSplit (hQ.baseChange b)
    (hi.baseChange b) hU
    (hproduct K (B.obj M) (B.obj D) T' (B.map d) (B.map t) hM' hd' ht')
    (hintersection K (B.obj M) (B.obj D) T' (B.map d) (B.map t) hM' hd' ht')
    (cocharacterLattice.baseChange b T ν) hroots'
  apply (coweight_character_comparison_baseChange_iff
    b hT hQ (Additive.ofMul (t ≫ q) : T ⟶ Q) P ν).mp
  have hmap :
      (CommGroupScheme.baseChange b).map (Additive.ofMul (t ≫ q) : T ⟶ Q) =
        (Additive.ofMul (B.map t ≫ B.map q) :
          T' ⟶ (CommGroupScheme.baseChange b).obj Q) := by
    change Additive.ofMul (B.map (t ≫ q)) = _
    rw [Functor.map_comp]
    rfl
  rw [hmap]
  exact hc

end characterLattice

namespace TorusCentralizerFiniteGaloisModel

variable {k : Type u} [Field k]
    {G M : GroupScheme (Spec (CommRingCat.of k))}
    {A Q : CommGroupScheme (Spec (CommRingCat.of k))}
    {a : A.toGrp ⟶ G} {j : M ⟶ G}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom M.X.hom] [LocallyOfFiniteType M.X.hom]
    (C : TorusCentralizerFiniteGaloisModel a j Q)

/-- Construct based descent on the retained actual finite-field root datum.
All unproved global structural statements remain explicit arguments. -/
def cocenterRootDescent
    (hroot : RootDatumExistenceStatement.{u})
    (hsemi : DerivedSubgroupSemisimpleStatement.{u})
    (hproduct : DerivedMaximalTorusProductSurjectivityStatement.{u})
    (hintersection : DerivedMaximalTorusIntersectionStatement.{u})
    (hG : IsConnectedReductive G) (hM : IsConnectedReductive M)
    (hA : IsSplitTorus A.toGrp) (hj : (torusCentralizer a).IsRepresentedBy j)
    (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ M)
    (hd : IsDerivedSubgroup d) (q : M ⟶ Q.toGrp)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q) :
    let R := C.rootData hroot hG hM
    {B : R.ambientDatum.Base //
      CocenterRootDescentData k C.splitting.carrier
        (Additive.ofMul (C.rational.centralizer ≫ q) : C.rational.torus ⟶ Q)
        R.ambientDatum B
        {p : B.support | R.ambientDatum.root' p (C.separatingCocharacter hA) = 0}} := by
  let E := C.splitting.carrier
  let b := algebraBaseMap k E
  let F := GroupScheme.baseChange b
  let R := C.rootData hroot hG hM
  have hd' : IsDerivedSubgroup (F.map d) :=
    hd.baseChange_of_eq b (derivedSubgroup_baseChange_eq_of_field b M)
  have hq' : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (F.map d)) (F.map q) := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hq.baseChange b
  have hroots := C.rational.relativeRoots_baseChange_eq_pairing b hA hj
  rw [← C.rational.centralizer_comp] at hroots
  have hc := characterLattice.cocenter_coweight_comparison_of_structuralInputs
    hroot hsemi hproduct hintersection
    (T := (CommGroupScheme.baseChange b).obj C.rational.torus)
    (Q := (CommGroupScheme.baseChange b).obj Q)
    R.ambient_isRootDatum R.centralizer_isRootDatum (F.map j)
    (by rw [← Functor.map_comp]) (C.centralizer_connectedReductive hM)
    (F.map d) hd' C.centralizer_maximal C.composite_maximal.2.1 (F.map q) hq'
    C.splitting.split_left C.splitting.split_right (C.separatingCocharacter hA) hroots
  have hmap :
      (CommGroupScheme.baseChange b).map
          (Additive.ofMul (C.rational.centralizer ≫ q) : C.rational.torus ⟶ Q) =
        (Additive.ofMul (F.map C.rational.centralizer ≫ F.map q) :
          (CommGroupScheme.baseChange b).obj C.rational.torus ⟶
            (CommGroupScheme.baseChange b).obj Q) := by
    change Additive.ofMul (F.map (C.rational.centralizer ≫ q)) = _
    rw [Functor.map_comp]
    rfl
  apply coweightCocenterRootDescent k E
    (Additive.ofMul (C.rational.centralizer ≫ q) : C.rational.torus ⟶ Q)
    (C.rational.centralizer ≫ j) R.ambientDatum
    C.splitting.split_left C.composite_maximal.2.1 R.ambient_isRootDatum
    (C.separatingCocharacter hA) (C.separatingCocharacter_galois hA)
  · change Function.Injective (characterLattice.precompose
      ((CommGroupScheme.baseChange b).map
        (Additive.ofMul (C.rational.centralizer ≫ q) : C.rational.torus ⟶ Q)))
    rw [hmap]
    exact hc.1
  · change ∀ χ, χ ∈ (characterLattice.precompose
      ((CommGroupScheme.baseChange b).map
        (Additive.ofMul (C.rational.centralizer ≫ q) :
          C.rational.torus ⟶ Q))).toIntLinearMap.range ↔
        ∀ p, R.ambientDatum.root' p (C.separatingCocharacter hA) = 0 →
          R.ambientDatum.toLinearMap χ (R.ambientDatum.coroot p) = 0
    rw [hmap]
    exact hc.2

end TorusCentralizerFiniteGaloisModel

/-- Conditional assembly of the exact public arbitrary-universe target.
This theorem does not discharge its four structural premises. -/
theorem splitTorusCentralizerCocenterRootModel_of_structuralInputs
    (hroot : RootDatumExistenceStatement.{u})
    (hsemi : DerivedSubgroupSemisimpleStatement.{u})
    (hproduct : DerivedMaximalTorusProductSurjectivityStatement.{u})
    (hintersection : DerivedMaximalTorusIntersectionStatement.{u}) :
    SplitTorusCentralizerCocenterRootModelStatement.{u} := by
  intro k _ G hG A a ha M j hj hM D d hd Q q hq hQ
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth M.X.hom := hM.smooth
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let C := torusCentralizerFiniteGaloisModel maximalTorusBaseChange ha hj hQ
  let R := C.rootData hroot hG hM
  let B := C.cocenterRootDescent hroot hsemi hproduct hintersection
    hG hM ha.1 hj D d hd q hq
  exact ⟨C.rational.torus, C.rational.centralizer, C.rational.centralizer_maximal,
    C.splitting.carrier, inferInstance, inferInstance,
    inferInstance, inferInstance, C.splitting.split_left, C.splitting.split_right,
    C.composite_maximal, R.ambientIndex, inferInstance, R.ambientDatum,
    R.ambient_isRootDatum, inferInstance, B.val,
    {p : B.val.support | R.ambientDatum.root' p (C.separatingCocharacter ha.1) = 0},
    B.property⟩

end Langlands.GroupScheme
