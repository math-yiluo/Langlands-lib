import Langlands.GroupScheme.Rational.TorusCentralizerRationalModel
import Langlands.GroupScheme.Torus.CommonFiniteGaloisSplitting
import Langlands.GroupScheme.Torus.MaximalBaseChangeStatement
import Langlands.GroupScheme.Reductive.FieldExtensionProof

/-! # A common splitting field for compatible centralizer tori -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G M : GroupScheme (Spec (CommRingCat.of k))}
    {A Q : CommGroupScheme (Spec (CommRingCat.of k))}
    {a : A.toGrp ⟶ G} {j : M ⟶ G}

/-- An actual rational centralizer torus with one finite Galois field splitting
it and the supplied quotient torus, and preserving both maximal-torus maps. -/
structure TorusCentralizerFiniteGaloisModel
    (a : A.toGrp ⟶ G) (j : M ⟶ G)
    (Q : CommGroupScheme (Spec (CommRingCat.of k))) where
  rational : TorusCentralizerRationalModel a j
  splitting : TorusCommonFiniteGaloisSplittingData k rational.torus.toGrp Q.toGrp
  ambient_maximal : IsMaximalTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap k splitting.carrier)).obj rational.torus)
    ((GroupScheme.baseChange (algebraBaseMap k splitting.carrier)).map rational.ambient)
  centralizer_maximal : IsMaximalTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap k splitting.carrier)).obj rational.torus)
    ((GroupScheme.baseChange (algebraBaseMap k splitting.carrier)).map rational.centralizer)

namespace TorusCentralizerRationalModel

/-- Retain the given rational model and choose a common splitting field.
Maximality ascent is supplied separately from finite Galois splitting. -/
def finiteGaloisModel
    (C : TorusCentralizerRationalModel a j)
    (hbase : MaximalTorusBaseChangeStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [Smooth M.X.hom] [IsAffineHom M.X.hom]
    (hQ : IsTorus Q.toGrp) : TorusCentralizerFiniteGaloisModel a j Q := by
  let F := C.ambient_maximal.1.commonFiniteGaloisSplitting hQ
  exact {
    rational := C
    splitting := F
    ambient_maximal :=
      (hbase k F.carrier G C.torus C.ambient
        C.ambient_maximal.1 C.ambient_maximal.2.1).mp C.ambient_maximal
    centralizer_maximal :=
      (hbase k F.carrier M C.torus C.centralizer
        C.centralizer_maximal.1 C.centralizer_maximal.2.1).mp C.centralizer_maximal }

end TorusCentralizerRationalModel

/-- Choose the compatible original-field torus and one finite Galois field
splitting it and the actual supplied quotient torus. -/
def torusCentralizerFiniteGaloisModel
    (hbase : MaximalTorusBaseChangeStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [Smooth M.X.hom] [IsAffineHom M.X.hom]
    (ha : IsSplitSubtorus a) (hj : (torusCentralizer a).IsRepresentedBy j)
    (hQ : IsTorus Q.toGrp) : TorusCentralizerFiniteGaloisModel a j Q :=
  (torusCentralizerRationalModel a ha j hj).finiteGaloisModel hbase hQ

namespace TorusCentralizerFiniteGaloisModel

variable (C : TorusCentralizerFiniteGaloisModel a j Q)

/-- The split ambient maximal-torus map is the actual composite through the
centralizer, as required by the cocenter root-model statement. -/
theorem composite_maximal :
    IsMaximalTorus
      (T := (CommGroupScheme.baseChange
        (algebraBaseMap k C.splitting.carrier)).obj C.rational.torus)
      ((GroupScheme.baseChange (algebraBaseMap k C.splitting.carrier)).map
        (C.rational.centralizer ≫ j)) := by
  rw [C.rational.centralizer_comp]
  exact C.ambient_maximal

/-- The actual ambient group remains connected reductive over the chosen
common splitting field. -/
theorem ambient_connectedReductive (hG : IsConnectedReductive G) :
    IsConnectedReductive
      ((GroupScheme.baseChange (algebraBaseMap k C.splitting.carrier)).obj G) :=
  connectedReductiveFieldExtensionStatement k C.splitting.carrier G hG

/-- The actual centralizer remains connected reductive over the same chosen
common splitting field. -/
theorem centralizer_connectedReductive (hM : IsConnectedReductive M) :
    IsConnectedReductive
      ((GroupScheme.baseChange (algebraBaseMap k C.splitting.carrier)).obj M) :=
  connectedReductiveFieldExtensionStatement k C.splitting.carrier M hM

end TorusCentralizerFiniteGaloisModel

end Langlands.GroupScheme
