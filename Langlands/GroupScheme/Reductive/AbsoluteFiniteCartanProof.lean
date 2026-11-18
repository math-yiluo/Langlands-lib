import Langlands.GroupScheme.Reductive.AbsoluteFiniteCartanStatement
import Langlands.GroupScheme.Reductive.RootDatumRationalBase
import Langlands.GroupScheme.Rational.FullRelativeRootPairing
import Langlands.GroupScheme.Rational.QuasiSplitSplittingReduction

/-! # Finite indecomposable actual absolute Cartan matrices -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

private theorem finiteCartan_of_equiv
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {M : Matrix I I ℤ} {N : Matrix J J ℤ}
    (e : I ≃ J) (he : ∀ i j, M i j = N (e i) (e j))
    (hN : N.IsFiniteCartan) : M.IsFiniteCartan := by
  refine ⟨fun i => (he i i).trans (hN.diag _),
    fun i j hij => ?_, fun i j => ?_, ?_⟩
  · rw [he]
    exact hN.offDiag_nonpos _ _ (e.injective.ne hij)
  · rw [he, he]
    exact hN.zero_comm _ _
  · obtain ⟨d, hd, hpos⟩ := hN.exists_posDef
    refine ⟨d ∘ e, fun i => hd (e i), ?_⟩
    convert hpos.submatrix e.injective using 1
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.submatrix_apply, Function.comp_apply, he]

private theorem indecomposable_of_equiv
    {I J : Type*} {M : Matrix I I ℤ} {N : Matrix J J ℤ}
    (e : I ≃ J) (he : ∀ i j, M i j = N (e i) (e j))
    (hN : N.IsIndecomposable) : M.IsIndecomposable := by
  intro i j A B D f hf
  apply hN i j A B D (f.trans e)
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [← he, hf]
  change Matrix.fromBlocks A B 0 D (f.symm a) (f.symm b) =
    Matrix.fromBlocks A B 0 D (f.symm (e.symm (e a))) (f.symm (e.symm (e b)))
  simp

namespace IsRootDatumOf

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [Mono i.hom.hom.left]
  {J : Type*} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  (hP : IsRootDatumOf i P) [P.IsReduced]

include hP

/-- An almost-simple group gives a nonempty, finite and indecomposable Cartan
matrix on the supplied integral simple base, with its exact integral entries. -/
theorem finiteIndecomposableCartan (hG : IsAlmostSimple G)
    (hT : IsSplitTorus T.toGrp) (hi : IsMaximalTorus i) (b : P.Base) :
    let : Fintype b.support := Fintype.ofFinite _
    let : DecidableEq b.support := Classical.decEq _
    Nonempty b.support ∧ b.cartanMatrix.IsFiniteCartan ∧
      b.cartanMatrix.IsIndecomposable := by
  classical
  let : Fintype b.support := Fintype.ofFinite _
  let : DecidableEq b.support := Classical.decEq _
  have hf := hT.finite_relativeRoots i
  let : Finite (relativeRoots i) := hf.to_subtype
  have hne := hG.relativeRoots_nonempty_of_split_maximalTorus i hT hi
  let : Nonempty J := ⟨hP.relativeRootIndex ⟨hne.choose, hne.choose_spec⟩⟩
  let Q := hP.relativeRootReflectionData.rootPairing hT hf
  let bQ : Q.Base := hP.rationalBase hT hf b
  let e : b.support ≃ bQ.support := hP.rationalBaseSupportEquiv hT hf b
  let : Q.IsRootSystem := hP.relativeRootReflectionData.rootPairing_isRootSystem hT hf
  let : Q.IsCrystallographic :=
    hP.relativeRootReflectionData.rootPairing_isCrystallographic hT hf
  let : Q.IsReduced :=
    Langlands.LinearAlgebra.IntegralRationalRootBase.isReduced P Q toRat
      (relativeRootSpan i).subtype hP.relativeRootEquiv
      hT.character_toRat_injective Subtype.val_injective (fun _ => rfl)
  let : Q.IsIrreducible := isIrreducible_fullRelativeRootPairing i Q
    (hP.relativeRootReflectionData.rootPairing_root_image hT hf)
    hG (hi.isMaximalSplitTorus hT) hne
  have he (a c : b.support) : b.cartanMatrix a c = bQ.cartanMatrix (e a) (e c) :=
    (hP.cartanMatrix_rationalBaseSupportEquiv hT hf b a c).symm
  exact ⟨b.support_nonempty.to_subtype,
    finiteCartan_of_equiv e he bQ.cartanMatrix_isFiniteCartan,
    indecomposable_of_equiv e he bQ.cartanMatrix_isIndecomposable⟩

end IsRootDatumOf

/-- The exact internal bridge from absolute almost-simplicity to the full
actual finite indecomposable integral Cartan matrix, in every universe. -/
theorem absolutelyAlmostSimpleFiniteCartan :
    AbsolutelyAlmostSimpleFiniteCartanStatement.{u} := by
  intro k _ G _ _ d hG
  classical
  let : Fintype d.Vertex := Fintype.ofFinite _
  let : DecidableEq d.Vertex := Classical.decEq _
  let p := d.pinning
  let : IsAffineHom
      ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G).X.hom :=
    p.isConnectedReductive.isAffineHom
  let : LocallyOfFiniteType
      ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G).X.hom := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom _)
    infer_instance
  let : IsClosedImmersion ((GroupScheme.baseChange
      (algebraBaseMap k (SeparableClosure k))).map p.inclusion).hom.hom.left :=
    p.isMaximalTorus.2.1
  let := p.isReduced
  have h :=
    p.isRootDatum.finiteIndecomposableCartan
      (hG.baseChange_of_algebraicExtension (K := SeparableClosure k)).1
      p.isSplitTorus p.isMaximalTorus p.base
  have hc : p.base.cartanMatrix = Matrix.of d.cartan := by
    ext a b
    change p.rootDatum.pairingIn ℤ a.val b.val = p.rootDatum.pairing a.val b.val
    simpa using p.rootDatum.algebraMap_pairingIn ℤ a.val b.val
  change Nonempty d.Vertex ∧ (Matrix.of d.cartan).IsFiniteCartan ∧
    (Matrix.of d.cartan).IsIndecomposable
  rw [← hc]
  exact h

end Langlands.GroupScheme
