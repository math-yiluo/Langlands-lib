import Langlands.GroupScheme.Reductive.RootDatumRationalBase
import Langlands.GroupScheme.Rational.RelativeRootSystemIrreducibleProof
import Mathlib.Logic.Relation

/-! # Connectedness of actual integral Cartan diagrams for split almost-simple groups -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {t : T.toGrp ⟶ G} {J : Type u}
  {P : RootDatum J (characterLattice T) (cocharacterLattice T)}

/-- Every pair of simple vertices in an actual root datum of a split
almost-simple group lies in one integral Cartan component, over any field. -/
theorem cartanConnected_of_splitAlmostSimple
    (hG : IsAlmostSimple G) (hT : IsSplitTorus T.toGrp) (ht : IsMaximalTorus t)
    (hP : IsRootDatumOf t P) [P.IsReduced] (b : P.Base) (a c : b.support) :
    Relation.EqvGen (fun x y : b.support => x ≠ y ∧ P.pairing x y ≠ 0) a c := by
  let : Smooth G.X.hom := hG.isSemisimple.isConnectedReductive.smooth
  let : Mono t.hom.hom.left := ht.2.1.mono
  let hf := hT.finite_relativeRoots t
  let : Finite (relativeRoots t) := hf.to_subtype
  let R := hP.relativeRootReflectionData
  let Q := R.rootPairing hT hf
  let : Q.IsRootSystem := R.rootPairing_isRootSystem hT hf
  let : Q.IsCrystallographic := R.rootPairing_isCrystallographic hT hf
  let : Q.IsReduced := Langlands.LinearAlgebra.IntegralRationalRootBase.isReduced
    P Q toRat (relativeRootSpan t).subtype hP.relativeRootEquiv
    hT.character_toRat_injective Subtype.val_injective (fun _ => rfl)
  let : Q.IsIrreducible := relativeRootSystemIrreducible k G hG T t
    (ht.isMaximalSplitTorus hT)
    ⟨P.root a.val, by
      rw [relativeRoots_eq_roots, ← hP.2.1]
      exact Set.mem_range_self a.val⟩
    (relativeRoots t) Q (R.rootPairing_toLinearMap hT hf)
      (R.rootPairing_root_image hT hf)
  let B := hP.rationalBase hT hf b
  let e := hP.rationalBaseSupportEquiv hT hf b
  let path := fun x y : b.support =>
    Relation.EqvGen (fun x y : b.support => x ≠ y ∧ P.pairing x y ≠ 0) x y
  have hs : ∀ z : B.support, path a (e.symm z) := by
    intro z
    apply B.induction_on_cartanMatrix (fun z => path a (e.symm z))
      (i := e a) (j := z) (by simpa only [Equiv.symm_apply_apply] using Relation.EqvGen.refl a)
    intro x y hx hyx
    have hyx' : b.cartanMatrix (e.symm y) (e.symm x) ≠ 0 := by
      intro hz
      apply hyx
      have he := hP.cartanMatrix_rationalBaseSupportEquiv hT hf b (e.symm y) (e.symm x)
      change B.cartanMatrix (e (e.symm y)) (e (e.symm x)) =
        b.cartanMatrix (e.symm y) (e.symm x) at he
      simpa only [Equiv.apply_symm_apply, hz] using he
    have hp : P.pairing (e.symm y) (e.symm x) ≠ 0 := fun hzero =>
      hyx' (b.cartanMatrix_apply_eq_zero_iff_pairing.mpr hzero)
    by_cases heq : e.symm x = e.symm y
    · simpa only [← heq] using hx
    · exact Relation.EqvGen.trans _ _ _ hx
        (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨Ne.symm heq, hp⟩))
  simpa only [Equiv.symm_apply_apply] using hs (e c)

/-- Universal connectedness assertion for the actual reduced integral simple
Cartan diagram at a split maximal torus of an almost-simple group. -/
def SplitAlmostSimpleCartanConnectedStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (t : T.toGrp ⟶ G) (J : Type u)
    (P : RootDatum J (characterLattice T) (cocharacterLattice T)),
    IsAlmostSimple G → IsSplitTorus T.toGrp → IsMaximalTorus t → IsRootDatumOf t P →
    ∀ [P.IsReduced] (b : P.Base) (a c : b.support),
      Relation.EqvGen (fun x y : b.support => x ≠ y ∧ P.pairing x y ≠ 0) a c

/-- The universal assertion is proved by actual relative-root irreducibility. -/
theorem splitAlmostSimpleCartanConnected : SplitAlmostSimpleCartanConnectedStatement.{u} := by
  intro k _ G _ T t J P hG hT ht hP _ b a c
  exact cartanConnected_of_splitAlmostSimple hG hT ht hP b a c

end Langlands.GroupScheme
