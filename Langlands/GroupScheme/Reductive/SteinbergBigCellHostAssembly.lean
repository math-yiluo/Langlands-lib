import Langlands.GroupScheme.Reductive.CanonicalRhoSteinbergAssembly
import Langlands.GroupScheme.Reductive.RootPinningFromSplitTorus
import Langlands.GroupScheme.SimplyConnected.SplitNecessityStatement
import Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction

/-! # Global assembly of Steinberg big-cell data from explicit inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The global per-height input for the full canonical covariant spaces of
supplied finite split pinnings. This proposition asserts no proof of that input. -/
def SplitSteinbergHeightIrreducibilityStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G) [Fintype p.rootIndex]
    (hspan : p.rootDatum.corootSpan ℤ = ⊤)
    (q : ℕ) [ExpChar k q], q.Prime →
      p.CanonicalRhoSteinbergHeightIrreducibility hspan q

/-- Exactly the unresolved structural and representation-theoretic inputs used
by this global assembly. None of the four fields is proved by this structure. -/
structure SteinbergBigCellInputs : Prop where
  rootDatumExistence : RootDatumExistenceStatement.{u}
  corootSpan : SplitSimplyConnectedCorootSpanStatement.{u}
  highestWeightExistence : SplitDominantHighestWeightRepresentationsExistStatement.{u}
  heightIrreducibility : SplitSteinbergHeightIrreducibilityStatement.{u}

/-- Construct complete data for the original simply connected group from the
explicit inputs. A split maximal torus and its root-line trivializations are
obtained from proved theorems. -/
def steinbergBigCellDataOfInputs
    (h : SteinbergBigCellInputs.{u})
    (k : Type u) [Field k] [IsAlgClosed k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (hG : IsSimplyConnected G) :
    SteinbergBigCellData G :=
  Classical.choice <| by
    let hred := hG.isSemisimple.isConnectedReductive
    let : Smooth G.X.hom := hred.smooth
    obtain ⟨T, i, hi, hT⟩ := exists_isMaximalTorus_isSplitTorus_of_isSepClosed G
    let p := SplitPinning.ofRootDatumExistence h.rootDatumExistence hred hT i hi
      (splitRootLieLine k G hred T hT i hi)
    let : Fintype p.rootIndex := Fintype.ofFinite _
    have hspan : p.rootDatum.corootSpan ℤ = ⊤ :=
      h.corootSpan k G hG p.torus p.isSplitTorus p.inclusion p.isMaximalTorus
        p.rootIndex p.rootDatum p.isRootDatum p.isReduced
    exact ⟨p.canonicalRhoSteinbergBigCellData hspan q Fact.out
      h.highestWeightExistence (h.heightIrreducibility k G p hspan q Fact.out)⟩

/-- Unpack the constructed data into the exact published host proposition.
All four unresolved inputs remain an explicit antecedent. -/
theorem steinbergBigCell_of_inputs
    (h : SteinbergBigCellInputs.{u}) :
    SteinbergBigCellStatement.{u} := by
  intro k _ _ q _ _ G _ hG
  exact (steinbergBigCellDataOfInputs h k q G hG).exists_data

end Langlands.GroupScheme
