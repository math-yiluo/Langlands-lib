import Langlands.Group.GL.HeadTailBlocks
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof
import Langlands.Representation.Parabolic.ThreeBlockRegroupingAssembly

/-! Actual normalized product induction split into its first factor and ordered tail. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000

namespace Langlands.PadicField.TopologicalData

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n k : ℕ} (B : BlockShape n) (h : B.length = k + 2)

private theorem familyRankCast_eq {ι : Type*} {size : ι → ℕ} {A : ℕ → Type*}
    (σ : ∀ i, A (size i)) {i j : ι} (hij : i = j) (hr : size i = size j) :
    hr ▸ σ i = σ j := by
  subst j
  rfl

/-- The first factor, lifted to the induced carrier universe, and the actual tail product. -/
abbrev headTailProductFactors
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    ∀ i : Fin 2, SmoothRep.{0,uF,max uF uV} ℂ
      (GeneralLinear ((B.headTailShape h).size i) F.Carrier) :=
  letI := T.topology
  fun i => match i with
    | 0 => SmoothRep.universeLift.{uF} (σ (B.headIndex h))
    | 1 => (T.normalizedProductInductionFunctor (B.tailShape h)).obj
      (fun j => σ (B.tailIndex h j))

/-- The transported head family is the singleton family of the original first factor. -/
theorem headTailRefinedFactors_head
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    (fun j : Fin (B.headShape h).length =>
      (B.headTailBlock_size h ⟨0,j⟩).symm ▸ σ (B.headTailBlockEquiv h ⟨0,j⟩)) =
    (fun j => ((B.headShape h).singleBlock_size rfl j).symm ▸ σ (B.headIndex h)) := by
  let := T.topology
  funext j
  exact familyRankCast_eq (size := B.size)
    (A := fun r => SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier))
    σ (B.headTailBlockEquiv_head h j) _

/-- The transported tail family is exactly the original family restricted to tail labels. -/
theorem headTailRefinedFactors_tail
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    (fun j : Fin (B.tailShape h).length =>
      (B.headTailBlock_size h ⟨1,j⟩).symm ▸ σ (B.headTailBlockEquiv h ⟨1,j⟩)) =
    (fun j => σ (B.tailIndex h j)) := by
  let := T.topology
  funext j
  exact familyRankCast_eq (size := B.size)
    (A := fun r => SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier))
    σ (B.headTailBlockEquiv_tail h j) _

private def singletonProductLiftEquiv {r : ℕ} (C : BlockShape r) (hC : C.length = 1)
    (A : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    Representation.Equiv
      (((T.normalizedProductInductionFunctor C).obj
        (fun j => (C.singleBlock_size hC j).symm ▸ A)).representation)
      (SmoothRep.universeLift.{uF} A).representation := by
  letI := T.topology
  exact Parabolic.equivTrans
    (T.normalizedProductInductionObjEquiv C
      (fun j => (C.singleBlock_size hC j).symm ▸ A))
    (Parabolic.equivTrans (T.singleBlockTransportedProductEquiv C hC A)
      (SmoothRep.universeLiftEquiv.{uF} A))

private def singletonProductLiftIso {r : ℕ} (C : BlockShape r) (hC : C.length = 1)
    (A : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    ((T.normalizedProductInductionFunctor C).obj
      (fun j => (C.singleBlock_size hC j).symm ▸ A)) ≅
      SmoothRep.universeLift.{uF} A :=
  letI := T.topology
  SmoothRep.mkIso (singletonProductLiftEquiv T C hC A)

private abbrev headTailInnerFactors
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    ∀ (i : Fin 2) (j : Fin (B.headTailRefinement h i).length),
      SmoothRep.{0,uF,uV} ℂ
        (GeneralLinear ((B.headTailRefinement h i).size j) F.Carrier) :=
  letI := T.topology
  fun i => match i with
    | 0 => fun j => ((B.headShape h).singleBlock_size rfl j).symm ▸ σ (B.headIndex h)
    | 1 => fun j => σ (B.tailIndex h j)

private theorem headTailRefinedFactors_eq
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    (fun (i : Fin 2) (j : Fin (B.headTailRefinement h i).length) =>
      (B.headTailBlock_size h ⟨i,j⟩).symm ▸
        σ (B.headTailBlockEquiv h ⟨i,j⟩)) =
      headTailInnerFactors T B h σ := by
  let := T.topology
  funext i
  fin_cases i
  · exact T.headTailRefinedFactors_head B h σ
  · exact T.headTailRefinedFactors_tail B h σ

private abbrev headTailInnerProducts
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    ∀ i : Fin 2, SmoothRep.{0,uF,max uF uV} ℂ
      (GeneralLinear ((B.headTailShape h).size i) F.Carrier) :=
  letI := T.topology
  fun i => match i with
    | 0 => (T.normalizedProductInductionFunctor (B.headShape h)).obj
      (fun j => ((B.headShape h).singleBlock_size rfl j).symm ▸ σ (B.headIndex h))
    | 1 => (T.normalizedProductInductionFunctor (B.tailShape h)).obj
      (fun j => σ (B.tailIndex h j))

private theorem headTailInnerProducts_eq
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    (fun i : Fin 2 => (T.normalizedProductInductionFunctor
      (B.headTailRefinement h i)).obj (headTailInnerFactors T B h σ i)) =
      headTailInnerProducts T B h σ := by
  let := T.topology
  funext i
  fin_cases i <;> rfl

private def headTailProductFactorIso
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    ∀ i : Fin 2,
      headTailInnerProducts T B h σ i ≅ T.headTailProductFactors B h σ i :=
  letI := T.topology
  fun i => match i with
    | 0 => singletonProductLiftIso T (B.headShape h) rfl (σ (B.headIndex h))
    | 1 => Iso.refl _

private def composeProductRegroupingIso {m : ℕ} (C D : BlockShape m)
    (S : Geometric.BlockRefinement D)
    (e : ((j : Fin D.length) × Fin (S j).length) ≃ Fin C.length)
    (hs : ∀ a, (S a.1).size a.2 = C.size (e a))
    (hc : ∀ j k (x : Fin ((S j).size k)),
      D.index j ((S j).index k x) = C.index (e ⟨j,k⟩) (Fin.cast (hs ⟨j,k⟩) x))
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (C.size i) F.Carrier))
    (inner : letI := T.topology
      ∀ i j, SmoothRep.{0,uF,uV} ℂ (GeneralLinear ((S i).size j) F.Carrier))
    (hinner : letI := T.topology
      (fun i j => (hs ⟨i,j⟩).symm ▸ σ (e ⟨i,j⟩)) = inner)
    (products : letI := T.topology
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (D.size i) F.Carrier))
    (hproducts : letI := T.topology
      (fun i => (T.normalizedProductInductionFunctor (S i)).obj (inner i)) = products)
    (τ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (D.size i) F.Carrier))
    (f : letI := T.topology; products ≅ τ) :
    letI := T.topology
    (T.normalizedProductInductionFunctor C).obj σ ≅
      (T.normalizedProductInductionFunctor D).obj τ := by
  letI := T.topology
  let hfamily := congrArg
    (fun υ => fun i => (T.normalizedProductInductionFunctor (S i)).obj (υ i)) hinner
  let g := eqToIso (hfamily.trans hproducts) ≪≫ f
  exact Classical.choice (Parabolic.orderedProductRegrouping F T m C D S e hs hc σ) ≪≫
    (T.normalizedProductInductionFunctor D).mapIso g

/-- The categorical first/tail product isomorphism. -/
def headTailProductInductionIso
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    (T.normalizedProductInductionFunctor B).obj σ ≅
      (T.normalizedProductInductionFunctor (B.headTailShape h)).obj
        (T.headTailProductFactors B h σ) := by
  letI := T.topology
  exact composeProductRegroupingIso T B (B.headTailShape h) (B.headTailRefinement h)
    (B.headTailBlockEquiv h) (B.headTailBlock_size h) (B.headTail_index h) σ
    (headTailInnerFactors T B h σ) (headTailRefinedFactors_eq T B h σ)
    (headTailInnerProducts T B h σ) (headTailInnerProducts_eq T B h σ)
    (T.headTailProductFactors B h σ)
    (CategoryTheory.Pi.isoMk (headTailProductFactorIso T B h σ))

/-- Split an arbitrary normalized product into its original first factor and nonempty tail. -/
def headTailProductInductionEquiv
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    Representation.Equiv
      (T.normalizedProductInduced B (fun i => (σ i).representation))
      (T.normalizedProductInduced (B.headTailShape h)
        (fun i => (T.headTailProductFactors B h σ i).representation)) :=
  letI := T.topology
  SmoothRep.equivOfIso (T.headTailProductInductionIso B h σ)

end Langlands.PadicField.TopologicalData
