import Langlands.GroupScheme.Torus.FiniteGaloisSplitMaximal
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent
import Langlands.GroupScheme.BaseChangeReflection

/-! # Actual finite Galois fields with split maximal tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- An actual finite Galois field over which the given group has a split maximal torus. -/
structure FiniteGaloisSplitMaximalModel (G : GroupScheme (Spec (CommRingCat.of k))) where
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra k carrier]
  [finiteDimensional : FiniteDimensional k carrier]
  [isGalois : IsGalois k carrier]
  torus : CommGroupScheme (Spec (CommRingCat.of carrier))
  inclusion : torus.toGrp ⟶ (baseChange (algebraBaseMap k carrier)).obj G
  isSplitTorus : IsSplitTorus torus.toGrp
  isMaximalTorus : IsMaximalTorus inclusion

attribute [instance] FiniteGaloisSplitMaximalModel.field
  FiniteGaloisSplitMaximalModel.algebra FiniteGaloisSplitMaximalModel.finiteDimensional
  FiniteGaloisSplitMaximalModel.isGalois

/-- The published splitting and maximality theorems discharge both inputs of the
finite Galois split-maximal-torus helper. -/
theorem nonempty_finiteGaloisSplitMaximalModel
    (G : GroupScheme (Spec (CommRingCat.of k))) [Smooth G.X.hom] [IsAffineHom G.X.hom] :
    Nonempty (FiniteGaloisSplitMaximalModel G) := by
  obtain ⟨L, _, _, hfin, hgal, T, i, hT, hi⟩ :=
    exists_finiteGalois_hasSplitMaximalTorus torusFiniteGaloisSplitting
      maximalTorusBaseChange G
  exact ⟨{ carrier := L
           finiteDimensional := hfin
           isGalois := hgal
           torus := T
           inclusion := i
           isSplitTorus := hT
           isMaximalTorus := hi }⟩

/-- Choose an actual finite Galois splitting field and a split maximal torus over it. -/
def finiteGaloisSplitMaximalModel
    (G : GroupScheme (Spec (CommRingCat.of k))) [Smooth G.X.hom] [IsAffineHom G.X.hom] :
    FiniteGaloisSplitMaximalModel G :=
  Classical.choice (nonempty_finiteGaloisSplitMaximalModel G)

namespace FiniteGaloisSplitMaximalModel

variable {G : GroupScheme (Spec (CommRingCat.of k))} (D : FiniteGaloisSplitMaximalModel G)

/-- The constructed field extension is an actual fpqc cover of the original field. -/
theorem fpqc :
    Surjective (algebraBaseMap k D.carrier) ∧
      Flat (algebraBaseMap k D.carrier) ∧ QuasiCompact (algebraBaseMap k D.carrier) :=
  fieldExtension_fpqc k D.carrier

/-- The bundle supplies the existing split-maximal-torus predicate. -/
theorem hasSplitMaximalTorus :
    HasSplitMaximalTorus ((baseChange (algebraBaseMap k D.carrier)).obj G) :=
  ⟨D.torus, D.inclusion, D.isSplitTorus, D.isMaximalTorus⟩

/-- Connected reductivity of the original group persists at this finite Galois stage. -/
theorem isConnectedReductive (hG : IsConnectedReductive G) :
    IsConnectedReductive ((baseChange (algebraBaseMap k D.carrier)).obj G) :=
  hG.baseChange_of_algebraicExtension

end FiniteGaloisSplitMaximalModel

end Langlands.GroupScheme
