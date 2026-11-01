import Langlands.HarmonicAnalysis.Distribution.TensorProduct
import Langlands.HarmonicAnalysis.Distribution.TopologicalSupport
import Langlands.Topology.LocallyProfinite

/-!
# Renard II.1.3: product spaces, tensor products of tests and distributions

Renard, 9 July 2026, II.1.3, printed p.32 / PDF p.38. Statements only, over the
published test-function, distribution-tensor and topological-support maps.
-/

set_option autoImplicit false

open scoped BigOperators TensorProduct

universe uX uY

namespace Langlands.HarmonicAnalysis.Distribution.TensorProductStatements

open Langlands.Hecke.TestFunction (characteristic)

/-- The product of two t.d. spaces, with the product topology, is a t.d. space. -/
def ProductLocallyProfinite : Prop :=
  ∀ (X : Type uX) (Y : Type uY) [TopologicalSpace X] [TopologicalSpace Y],
    Langlands.Topology.IsLocallyProfinite X → Langlands.Topology.IsLocallyProfinite Y →
      Langlands.Topology.IsLocallyProfinite (X × Y)

/-- The rectangles `U × V` with `U` and `V` compact open form a basis of the
product topology. -/
def CompactOpenRectangleBasis : Prop :=
  ∀ (X : Type uX) (Y : Type uY) [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
    [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y],
    TopologicalSpace.IsTopologicalBasis
      {W : Set (X × Y) | ∃ (U : Set X) (V : Set Y),
        IsOpen U ∧ IsCompact U ∧ IsOpen V ∧ IsCompact V ∧ W = U ×ˢ V}

/-- Every compact open subset of `X × Y` is a finite disjoint union of
compact-open rectangles `U × V`. -/
def CompactOpenRectanglePartition : Prop :=
  ∀ (X : Type uX) (Y : Type uY) [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
    [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]
    (K : Set (X × Y)), IsOpen K → IsCompact K →
      ∃ (n : ℕ) (U : Fin n → Set X) (V : Fin n → Set Y),
        (∀ i, IsOpen (U i) ∧ IsCompact (U i)) ∧
        (∀ i, IsOpen (V i) ∧ IsCompact (V i)) ∧
        Pairwise (fun i j => Disjoint (U i ×ˢ V i) (U j ×ˢ V j)) ∧
        (⋃ i, U i ×ˢ V i) = K

/-- Every test on `X × Y` is a finite linear combination of characteristic
functions of disjoint compact-open rectangles; each such characteristic
function is the external product of the two coordinate characteristic
functions. -/
def RectangleIndicatorDecomposition : Prop :=
  ∀ (X : Type uX) (Y : Type uY) [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
    [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]
    (f : SchwartzBruhat (X × Y)),
      ∃ (n : ℕ) (U : Fin n → Set X) (V : Fin n → Set Y)
        (hUo : ∀ i, IsClopen (U i)) (hUc : ∀ i, IsCompact (U i))
        (hVo : ∀ i, IsClopen (V i)) (hVc : ∀ i, IsCompact (V i)) (c : Fin n → ℂ),
        Pairwise (fun i j => Disjoint (U i ×ˢ V i) (U j ×ˢ V j)) ∧
        f = ∑ i, c i • characteristic ((hUo i).prod (hVo i)) ((hUc i).prod (hVc i)) ∧
        f = ∑ i, c i •
          SchwartzBruhat.tensor (characteristic (hUo i) (hUc i))
            (characteristic (hVo i) (hVc i))

/-- The canonical algebraic map `D(X) ⊗ D(Y) → D(X × Y)`,
`f ⊗ g ↦ [(x, y) ↦ f x * g y]`, is bijective. -/
def TensorLinearMapBijective : Prop :=
  ∀ (X : Type uX) (Y : Type uY) [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
    [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y],
    Function.Bijective
      (SchwartzBruhat.tensorLinearMap :
        SchwartzBruhat X ⊗[ℂ] SchwartzBruhat Y →ₗ[ℂ] SchwartzBruhat (X × Y))

/-- `Distribution.tensor T S` satisfies `⟨T ⊗ S, f ⊗ g⟩ = ⟨T, f⟩⟨S, g⟩`, and
it is the only distribution on `X × Y` with this property. -/
def TensorExistsUnique : Prop :=
  ∀ (X : Type uX) (Y : Type uY) [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
    [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]
    (T : Distribution X) (S : Distribution Y),
    (∀ (f : SchwartzBruhat X) (g : SchwartzBruhat Y),
        Distribution.tensor T S (SchwartzBruhat.tensor f g) = T f * S g) ∧
      ∀ D : Distribution (X × Y),
        (∀ (f : SchwartzBruhat X) (g : SchwartzBruhat Y),
            D (SchwartzBruhat.tensor f g) = T f * S g) →
          D = Distribution.tensor T S

/-- Both Fubini formulas for every test on `X × Y`. -/
def Fubini : Prop :=
  ∀ (X : Type uX) (Y : Type uY) [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
    [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]
    (T : Distribution X) (S : Distribution Y) (f : SchwartzBruhat (X × Y)),
    Distribution.tensor T S f = T (Distribution.partialApplySnd S f) ∧
      Distribution.tensor T S f = S (Distribution.partialApplyFst T f)

/-- `Supp (T ⊗ S) = Supp T × Supp S` for the topological supports. -/
def SupportTensor : Prop :=
  ∀ (X : Type uX) (Y : Type uY) [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
    [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]
    (T : Distribution X) (S : Distribution Y),
    Distribution.support (Distribution.tensor T S) =
      Distribution.support T ×ˢ Distribution.support S

/-- The tensor product of two compactly supported distributions is compactly
supported, also as membership in `compactlySupported`. -/
def CompactSupportTensor : Prop :=
  ∀ (X : Type uX) (Y : Type uY) [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
    [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]
    (T : Distribution X) (S : Distribution Y),
    (IsCompact (Distribution.support T) → IsCompact (Distribution.support S) →
        IsCompact (Distribution.support (Distribution.tensor T S))) ∧
      (T ∈ Distribution.compactlySupported → S ∈ Distribution.compactlySupported →
        Distribution.tensor T S ∈ Distribution.compactlySupported)

/-- All assertions of Renard II.1.3. -/
def Assertions : Prop :=
  ProductLocallyProfinite.{uX, uY} ∧ CompactOpenRectangleBasis.{uX, uY} ∧
    CompactOpenRectanglePartition.{uX, uY} ∧
    RectangleIndicatorDecomposition.{uX, uY} ∧ TensorLinearMapBijective.{uX, uY} ∧
    TensorExistsUnique.{uX, uY} ∧ Fubini.{uX, uY} ∧ SupportTensor.{uX, uY} ∧
    CompactSupportTensor.{uX, uY}

end Langlands.HarmonicAnalysis.Distribution.TensorProductStatements
