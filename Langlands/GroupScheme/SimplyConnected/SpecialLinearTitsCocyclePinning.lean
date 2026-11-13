import Langlands.GroupScheme.Reductive.SpecialLinearPinningProof
import Langlands.GroupScheme.Reductive.PinnedIsomorphismProof
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.LinearAlgebra.CorootSpanCartanEquivProof

/-! # Coordinate pinned presentations of simply connected groups of type A -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.SpecialLinearTitsCocycle

variable {k : Type u} [Field k] (n : ℕ)

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin n))

/-- The pinning constructed on the fixed determinant-one diagonal torus from its
actual root datum and a chosen base. -/
def coordinatePinning {J : Type u} [Finite J]
    (P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻))
    (hP : IsRootDatumOf (SpecialLinear.FinSucc.diagonalTorus n (CommRingCat.of k)) P)
    (hred : P.IsReduced) (B : P.Base) :
    SplitPinning (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of k)) where
  isConnectedReductive := SpecialLinear.isConnectedReductive k (Fin (n + 1)) 0
  torus := 𝔻
  inclusion := SpecialLinear.FinSucc.diagonalTorus n (CommRingCat.of k)
  isSplitTorus := SpecialLinear.FinSucc.isSplitTorus_diagonalTorus n k
  isMaximalTorus := SpecialLinear.FinSucc.isMaximalTorus_diagonalTorus n k
  rootIndex := J
  rootDatum := P
  isRootDatum := hP
  isReduced := hred
  base := B
  pinning := RootPinning.ofSplitMaximalTorus
    (SpecialLinear.isConnectedReductive k (Fin (n + 1)) 0)
    (SpecialLinear.FinSucc.isSplitTorus_diagonalTorus n k) _
    (SpecialLinear.FinSucc.isMaximalTorus_diagonalTorus n k) P hP B

variable {n} {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]

/-- A pinned presentation with the fixed coordinate torus and the prescribed numbering
of the target simple roots. -/
structure CoordinatePinnedIso (q : SplitPinning H) (eG : q.base.support ≃ Fin n) where
  rootIndex : Type u
  [finiteRootIndex : Finite rootIndex]
  rootDatum : RootDatum rootIndex (characterLattice 𝔻) (cocharacterLattice 𝔻)
  isRootDatum : IsRootDatumOf (SpecialLinear.FinSucc.diagonalTorus n (CommRingCat.of k))
    rootDatum
  isReduced : rootDatum.IsReduced
  base : rootDatum.Base
  numbering : base.support ≃ Fin n
  root_eq : ∀ a : base.support, rootDatum.root a =
    SpecialLinear.FinSucc.rootChar n k (numbering a).castSucc (numbering a).succ
  pinningIso : SplitPinning.Iso (coordinatePinning n rootDatum isRootDatum isReduced base) q
  index_eq : ∀ a : base.support, pinningIso.indexEquiv a.val = eG.symm (numbering a)

attribute [instance] CoordinatePinnedIso.finiteRootIndex

/-- The pullback of a target simple root is exactly the corresponding adjacent
coordinate character of the determinant-one diagonal torus. -/
theorem CoordinatePinnedIso.simpleRoot_pullback {q : SplitPinning H}
    {eG : q.base.support ≃ Fin n} (c : CoordinatePinnedIso q eG) (i : Fin n) :
    c.pinningIso.torusIso.hom ≫ q.rootDatum.root (eG.symm i).val =
      SpecialLinear.FinSucc.rootChar n k i.castSucc i.succ := by
  have h := c.pinningIso.root_eq (c.numbering.symm i).val
  rw [c.index_eq (c.numbering.symm i), Equiv.apply_symm_apply] at h
  have h' := congrArg (characterLattice.congr c.pinningIso.torusIso).symm h
  simpa only [AddEquiv.symm_apply_apply, characterLattice.congr_symm_apply, coordinatePinning,
    c.root_eq, Equiv.apply_symm_apply] using h'.symm

/-- Every simply connected split group whose numbered simple pairings are `A_n`
admits an actual pinned isomorphism from `SL_(n+1)` retaining that numbering and
its coordinate simple-root characters. -/
theorem exists_coordinatePinnedIso (q : SplitPinning H) (hH : IsSimplyConnected H)
    (eG : q.base.support ≃ Fin n)
    (hcartan : ∀ a b : q.base.support,
      q.rootDatum.pairing a b = CartanMatrix.A n (eG a) (eG b)) :
    Nonempty (CoordinatePinnedIso q eG) := by
  classical
  obtain ⟨J, hJ, P, hP, hred, B, eP, hspan, hroot, hcartanP⟩ :=
    SpecialLinear.FinSucc.exists_coordinateRootDatum n k
  have : Finite J := hJ
  have : P.IsReduced := hred
  have : q.rootDatum.IsReduced := q.isReduced
  have hspanQ : q.rootDatum.corootSpan ℤ = ⊤ :=
    splitSimplyConnectedCorootSpan k H hH q.torus q.isSplitTorus q.inclusion
      q.isMaximalTorus q.rootIndex q.rootDatum q.isRootDatum q.isReduced
  let e := eP.trans eG.symm
  have he : ∀ a b : B.support, q.rootDatum.pairing (e a) (e b) = P.pairing a b := by
    intro a b
    rw [hcartan, hcartanP]
    simp [e]
  obtain ⟨r, hr⟩ := Langlands.LinearAlgebra.corootSpanCartanEquiv J _ _ q.rootIndex _ _
    P q.rootDatum B q.base hspan hspanQ e he
  have hbase : ∀ a, a ∈ B.support ↔ r.indexEquiv a ∈ q.base.support := by
    intro a
    constructor
    · intro ha
      rw [hr ⟨a, ha⟩]
      exact (e ⟨a, ha⟩).property
    · intro ha
      obtain ⟨b, hb⟩ := e.surjective ⟨r.indexEquiv a, ha⟩
      have hba : r.indexEquiv b.val = r.indexEquiv a := by
        rw [hr b]
        exact congrArg Subtype.val hb
      exact (r.indexEquiv.injective hba) ▸ b.property
  let p := coordinatePinning n P hP hred B
  obtain ⟨f, hf, _⟩ := pinnedIsomorphism k _ H p q r hbase
  refine ⟨{ rootIndex := J
            rootDatum := P
            isRootDatum := hP
            isReduced := hred
            base := B
            numbering := eP
            root_eq := hroot
            pinningIso := f
            index_eq := ?_ }⟩
  intro a
  rw [hf.2.2]
  exact hr a

end Langlands.GroupScheme.SpecialLinearTitsCocycle
