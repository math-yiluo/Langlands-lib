import Langlands.GroupScheme.SimplyConnected.CoverExistenceStatement
import Langlands.GroupScheme.SimplyConnected.SplitCoverExistenceAssembly
import Langlands.GroupScheme.SimplyConnected.UniversalPropertyStatement
import Langlands.GroupScheme.Torus.FiniteGaloisSplitMaximal
import Langlands.GroupScheme.Descent.TensorFullCoverStatement
import Langlands.FieldTheory.FiniteGaloisTensorDecompositionStatement

/-! # Reduction of cover existence to finite Galois splitting and full cover descent -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The semisimplicity ascent needed in the finite Galois existence reduction.
Only finite Galois extensions are quantified over. -/
def SemisimpleFiniteGaloisAscentStatement : Prop :=
  ∀ (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsSemisimple G →
      IsSemisimple
        ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj G)

/-- The seven explicit inputs of the finite Galois reduction. This bundle
neither asserts nor proves any of its components without an argument. -/
def FiniteGaloisCoverExistenceInputsStatement : Prop :=
  TorusFiniteGaloisSplittingStatement.{u} ∧
    MaximalTorusBaseChangeStatement.{u} ∧
    SemisimpleFiniteGaloisAscentStatement.{u} ∧
    SplitSimplyConnectedCoverExistenceStatement.{u} ∧
    SimplyConnectedCentralCoverUniversalProperty.{u} ∧
    Langlands.FieldTheory.FiniteGaloisTensorDecompositionStatement.{u} ∧
    SimplyConnectedCoverTensorDescentStatement.{u, u}

/-- The explicit splitting and descent inputs imply the full cover-existence
statement over arbitrary fields. No component of the input bundle is proved here. -/
theorem simplyConnectedCoverExistence_of_finiteGaloisInputs
    (h : FiniteGaloisCoverExistenceInputsStatement.{u}) :
    SimplyConnectedCoverExistenceStatement.{u} := by
  obtain ⟨hsplit, hmax, hsemi, hcover, hup, htensor, hdescent⟩ := h
  intro k _ G hG
  have : Smooth G.X.hom := hG.isConnectedReductive.smooth
  have : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  obtain ⟨L, _, _, hfin, hgal, T, i, hT, hi⟩ :=
    exists_finiteGalois_hasSplitMaximalTorus hsplit hmax G
  let : FiniteDimensional k L := hfin
  let : IsGalois k L := hgal
  let p := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have hGL : IsSemisimple ((baseChange p).obj G) := hsemi k L G hG
  obtain ⟨C, π, hC, hπ⟩ := hcover L ((baseChange p).obj G) T hGL hT i hi
  have hfull : IsSimplyConnectedCover π :=
    ⟨hGL, hC, hπ, hup L C ((baseChange p).obj G) π hC hGL hπ⟩
  obtain ⟨e, he⟩ := htensor k L
  let : Fintype (Gal(L/k)) := Fintype.ofFinite _
  obtain ⟨D, a, _, ha, _⟩ :=
    hdescent k L (Gal(L/k)) e (fun σ => σ) he G C π hfull
  exact ⟨D, a, ha⟩

/-- The split classification assembly can supply the fourth input of the
finite Galois reduction. Its five structural premises remain explicit. -/
theorem simplyConnectedCoverExistence_of_splitClassificationAndDescent
    (hsplit : TorusFiniteGaloisSplittingStatement.{u})
    (hmax : MaximalTorusBaseChangeStatement.{u})
    (hsemi : SemisimpleFiniteGaloisAscentStatement.{u})
    (hclassification : SplitSimplyConnectedCoverInputsStatement.{u})
    (hup : SimplyConnectedCentralCoverUniversalProperty.{u})
    (htensor : Langlands.FieldTheory.FiniteGaloisTensorDecompositionStatement.{u})
    (hdescent : SimplyConnectedCoverTensorDescentStatement.{u, u}) :
    SimplyConnectedCoverExistenceStatement.{u} :=
  simplyConnectedCoverExistence_of_finiteGaloisInputs
    ⟨hsplit, hmax, hsemi, splitSimplyConnectedCoverExistence_of_inputs hclassification,
      hup, htensor, hdescent⟩

end Langlands.GroupScheme
