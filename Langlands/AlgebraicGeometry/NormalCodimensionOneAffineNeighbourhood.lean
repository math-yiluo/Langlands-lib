import Langlands.AlgebraicGeometry.StalkIntersectionNeighbourhood
import Langlands.AlgebraicGeometry.NormalAffineNeighbourhoodComponentReduction
import Langlands.CommutativeAlgebra.ValuationSubringIntersection

/-! # Common affine neighbourhoods of finite normal codimension-one points -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry

open _root_.Langlands.CommutativeAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- The integral case of BLR, Néron Models, §6.4 Lemma 4. -/
def integralNormalCodimensionOneAffineNeighbourhood
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    [IsIntegral X] [X.IsSeparated] [IsLocallyNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation p]
    (hn : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (E : Set X) (hE : E.Finite)
    (hd : ∀ x ∈ E, ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    {U : X.Opens // IsAffineOpen U ∧ E ⊆ U} := by
  classical
  by_cases hempty : E = ∅
  · exact affineNeighbourhoodOfSubsetGenericPoint E (by simp [hempty])
  letI : Finite E := hE.to_subtype
  letI : Nonempty E := (Set.nonempty_iff_ne_empty.mpr hempty).to_subtype
  let V := normalStalkValuations E (fun x _ ↦ (hn x).2) hd
  have hA : ∀ z : X.functionField,
      z ∈ stalkIntersection X E ↔ ∀ x : E, z ∈ V x := by
    intro z
    change z ∈ (⨅ x : E, stalkImageSubring X x) ↔
      ∀ x : E, z ∈ stalkImageSubring X x
    exact Subring.mem_iInf
  have : IsFractionRing (stalkIntersection X E) X.functionField :=
    ValuationSubringIntersection.isFractionRing V hA
  have hlocal : StalkIntersectionLocalizations E := by
    intro m hm
    have := hm
    obtain ⟨x, hx⟩ :=
      ValuationSubringIntersection.exists_isLocalization_atPrime_of_isMaximal V hA m.asIdeal
        (fun x : E ↦ stalkIntersectionToStalk E x x.property)
        (fun x : E ↦ algebraMap (X.presheaf.stalk x) X.functionField)
        (fun x : E ↦ IsFractionRing.injective (X.presheaf.stalk x) X.functionField)
        (fun (x : E) a ↦ algebraMap_stalkIntersectionToStalk E x x.property a)
        (fun (x : E) z ↦ by rfl)
    exact ⟨x, x.property, hx⟩
  exact affineNeighbourhoodOfStalkIntersectionLocalizations p E hE hlocal

/-- **BLR, Néron Models, §6.4 Lemma 4.**
A finite set of normal points of codimension at most one on a normal,
separated finite-type scheme over an affine noetherian base has an actual
common affine open neighbourhood. -/
def normalCodimensionOneAffineNeighbourhood
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p]
    (hn : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (E : Set X) (hE : E.Finite)
    (hd : ∀ x ∈ E, ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    {U : X.Opens // IsAffineOpen U ∧ E ⊆ U} :=
  normalAffineNeighbourhoodOfIntegralConstructor
    (fun _ _ _ _ q _ hY F hF hdF ↦
      integralNormalCodimensionOneAffineNeighbourhood q hY F hF hdF)
    p hn E hE hd

end Langlands.AlgebraicGeometry
