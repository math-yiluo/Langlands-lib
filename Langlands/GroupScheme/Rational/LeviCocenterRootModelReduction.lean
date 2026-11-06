import Langlands.GroupScheme.Rational.LeviCocenterRootModelAssembly
import Langlands.GroupScheme.Rational.DerivedTorusFiniteCenter
import Langlands.GroupScheme.Reductive.FiniteCenterReflection
import Langlands.GroupScheme.Torus.ExistenceProof

/-! # Removing derived semisimplicity from the Levi cocenter root-model inputs -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Root existence and maximal-torus product surjectivity give the full finite
derived centre after passing to an algebraic closure and reflecting finiteness. -/
theorem IsDerivedSubgroup.hasFiniteCenter_of_rootDatum_product
    (hroot : RootDatumExistenceStatement.{u})
    (hproduct : DerivedMaximalTorusProductSurjectivityStatement.{u})
    {k : Type u} [Field k]
    {G D : GroupScheme (Spec (CommRingCat.of k))} {d : D ⟶ G}
    (hd : IsDerivedSubgroup d) (hG : IsConnectedReductive G) : HasFiniteCenter D := by
  let K := AlgebraicClosure k
  let b := algebraBaseMap k K
  let B := GroupScheme.baseChange b
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have hG' : IsConnectedReductive (B.obj G) :=
    connectedReductiveFieldExtensionStatement k K G hG
  let : IsAffineHom (B.obj G).X.hom := hG'.isAffineHom
  let : Smooth (B.obj G).X.hom := hG'.smooth
  let : ConnectedSpace (B.obj G).X.left := hG'.connectedSpace
  have hd' : IsDerivedSubgroup (B.map d) :=
    hd.baseChange_of_eq b (derivedSubgroup_baseChange_eq_of_field b G)
  obtain ⟨T, t, ht⟩ := TorusExistence.exists_isMaximalTorus (B.obj G)
  have hT : IsSplitTorus T.toGrp :=
    ht.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  let S := hd'.geometricSubgroupTorus t ht
  obtain ⟨J, hJ, P, hP, _⟩ := hroot K (B.obj G) hG' T hT t ht
  let C := derivedTorusCentralComplement S.inclusion S.subgroup t (B.map d)
    hG' hd' (ht.isMaximalSplitTorus hT)
    (S.isMaximal.isMaximalSplitTorus S.isSplit) S.inclusion_comp.symm hP
  have hfinite : HasFiniteCenter (B.obj D) :=
    (C.finiteDerivedCenter (B.map d) hG' hd' S.subgroup S.inclusion_comp.symm
      (hproduct K (B.obj G) (B.obj D) T (B.map d) t hG' hd' ht)).hasFiniteCenter
  exact hfinite.of_fieldExtension (hd'.isConnectedReductive hG').isAffineHom

/-- Construct an actual finite full derived centre over the original arbitrary field. -/
def finiteDerivedCenter_of_rootDatum_product
    (hroot : RootDatumExistenceStatement.{u})
    (hproduct : DerivedMaximalTorusProductSurjectivityStatement.{u})
    {k : Type u} [Field k]
    {G D : GroupScheme (Spec (CommRingCat.of k))} {d : D ⟶ G}
    (hd : IsDerivedSubgroup d) (hG : IsConnectedReductive G) : FiniteCenter D := by
  let h := hd.hasFiniteCenter_of_rootDatum_product hroot hproduct hG
  exact ⟨h.choose, h.choose_spec.choose,
    h.choose_spec.choose_spec.1, h.choose_spec.choose_spec.2⟩

/-- The global derived semisimplicity proposition follows from these two
explicit structural propositions, with no field restriction. -/
theorem derivedSubgroupSemisimple_of_rootDatum_product
    (hroot : RootDatumExistenceStatement.{u})
    (hproduct : DerivedMaximalTorusProductSurjectivityStatement.{u}) :
    DerivedSubgroupSemisimpleStatement.{u} := by
  intro k _ G D d hG hd
  exact ⟨hd.isConnectedReductive hG,
    (finiteDerivedCenter_of_rootDatum_product hroot hproduct hd hG).hasFiniteCenter⟩

namespace TorusCentralizerFiniteGaloisModel

variable {k : Type u} [Field k]
    {G M : GroupScheme (Spec (CommRingCat.of k))}
    {A Q : CommGroupScheme (Spec (CommRingCat.of k))}
    {a : A.toGrp ⟶ G} {j : M ⟶ G}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom M.X.hom] [LocallyOfFiniteType M.X.hom]
    (C : TorusCentralizerFiniteGaloisModel a j Q)

/-- Construct the same retained actual based descent from only three global inputs. -/
def cocenterRootDescent_of_rootDatum_product_intersection
    (hroot : RootDatumExistenceStatement.{u})
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
        {p : B.support | R.ambientDatum.root' p (C.separatingCocharacter hA) = 0}} :=
  C.cocenterRootDescent hroot (derivedSubgroupSemisimple_of_rootDatum_product hroot hproduct)
    hproduct hintersection hG hM hA hj D d hd q hq

end TorusCentralizerFiniteGaloisModel

/-- The exact arbitrary-universe host target needs only root existence, product
surjectivity and the full-intersection torus assertion as remaining structural inputs. -/
theorem splitTorusCentralizerCocenterRootModel_of_rootDatum_product_intersection
    (hroot : RootDatumExistenceStatement.{u})
    (hproduct : DerivedMaximalTorusProductSurjectivityStatement.{u})
    (hintersection : DerivedMaximalTorusIntersectionStatement.{u}) :
    SplitTorusCentralizerCocenterRootModelStatement.{u} :=
  splitTorusCentralizerCocenterRootModel_of_structuralInputs hroot
    (derivedSubgroupSemisimple_of_rootDatum_product hroot hproduct) hproduct hintersection

end Langlands.GroupScheme
