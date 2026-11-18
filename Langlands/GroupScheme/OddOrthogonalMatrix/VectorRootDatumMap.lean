import Langlands.GroupScheme.OddOrthogonalMatrix.NumberedBase
import Langlands.GroupScheme.OddOrthogonalMatrix.CorootLattice
import Langlands.LinearAlgebra.SimplyConnectedRootDatumBase
import Langlands.LinearAlgebra.CorootSpanCartanEquivProof

/-! # The vector morphism from the actual odd root datum -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix.TypeBNumbering

open Langlands.LinearAlgebra

variable {n : ℕ} {K : Type u} [Field K]

local notation "𝔗" => splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift (Fin n))

variable {J : Type u} [Finite J]
    (Q : RootDatum J
      (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift (Fin n))))
      (cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift (Fin n)))))
    (hQ : IsRootDatumOf (identityTorus (Fin n) K) Q)
    {I X Y : Type u} [Finite I] [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum I X Y) [Q.IsReduced] [P.IsReduced]
    (B : P.Base) (hspan : P.corootSpan ℤ = ⊤)
    (hn : 2 ≤ n) (e : B.support ≃ Fin n)
    (he : ∀ a b : B.support, P.pairing a.val b.val = CartanMatrix.B n (e a) (e b))

include hQ hspan hn he in
/-- The actual odd datum maps injectively to a full-coroot type-B datum,
matching every simple-root index under the supplied numbering. -/
theorem exists_numberedHom :
    ∃ f : RootPairing.Hom Q P,
      Function.Injective f.weightMap ∧ Function.Injective f.coweightMap ∧
      ∀ a : (base Q hQ).support,
        f.indexEquiv a.val = (e.symm (numbering Q hQ a)).val := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  let hfinite : Finite (cocharacterLattice 𝔗 ⧸ Q.corootSpan ℤ) :=
    Finite.of_injective _ (corootQuotientEquiv hQ).injective
  let C := SimplyConnectedRootDatum.base Q (base Q hQ) hfinite
  let eC : C.support ≃ B.support := (numbering Q hQ).trans e.symm
  obtain ⟨c, hc⟩ := corootSpanCartanEquiv J _ _ I X Y
    (SimplyConnectedRootDatum.rootDatum Q) P C B
    (SimplyConnectedRootDatum.corootSpan_rootDatum Q) hspan eC (by
      intro a b
      change P.pairing (e.symm (numbering Q hQ a)).val
        (e.symm (numbering Q hQ b)).val = Q.pairing a.val b.val
      rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact (pairing_numbering Q hQ hn a b).symm)
  let f := c.toHom.comp (SimplyConnectedRootDatum.toRootDatum Q)
  refine ⟨f, ?_, ?_, ?_⟩
  · exact c.bijective_weightMap.injective.comp
      (SimplyConnectedRootDatum.injective_toRootDatum_weightMap Q hfinite)
  · exact (SimplyConnectedRootDatum.injective_toRootDatum_coweightMap Q).comp
      c.bijective_coweightMap.injective
  · intro a
    exact hc a

omit [Finite J] [Finite I] [Q.IsReduced] [P.IsReduced] in
/-- A root-datum morphism maps the integral root span onto the integral root span. -/
theorem map_rootSpan (f : RootPairing.Hom Q P) :
    (Q.rootSpan ℤ).map f.weightMap = P.rootSpan ℤ := by
  change (Submodule.span ℤ (Set.range Q.root)).map _ =
    Submodule.span ℤ (Set.range P.root)
  rw [Submodule.map_span, ← Set.range_comp, f.root_weightMap,
    Set.range_comp, Equiv.range_eq_univ, Set.image_univ]

omit [Finite J] [Finite I] [Q.IsReduced] [P.IsReduced] in
include hQ in
/-- The character image of any morphism from the actual odd datum is exactly
its target's integral root lattice. -/
theorem range_weightMap (f : RootPairing.Hom Q P) :
    LinearMap.range f.weightMap = P.rootSpan ℤ := by
  have h := map_rootSpan Q P f
  rw [rootSpan_eq_top Q hQ.2.1, Submodule.map_top] at h
  exact h

include hQ hspan hn he in
/-- The injective numbered vector morphism has exactly the full integral root image. -/
theorem exists_vectorHom :
    ∃ f : RootPairing.Hom Q P,
      Function.Injective f.weightMap ∧ Function.Injective f.coweightMap ∧
      (∀ a : (base Q hQ).support,
        f.indexEquiv a.val = (e.symm (numbering Q hQ a)).val) ∧
      LinearMap.range f.weightMap = P.rootSpan ℤ := by
  obtain ⟨f, hfw, hfc, hf⟩ := exists_numberedHom Q hQ P B hspan hn e he
  exact ⟨f, hfw, hfc, hf, range_weightMap Q hQ P f⟩

omit [Finite J] [Q.IsReduced] in
include hspan hn he in
/-- An actual finite reduced odd datum and its injective morphism to the
supplied full-coroot type-B datum exist over every field. -/
theorem exists_vectorRootDatum :
    ∃ (J' : Type u) (_ : Finite J')
      (Q' : RootDatum J' (characterLattice 𝔗) (cocharacterLattice 𝔗))
      (f : RootPairing.Hom Q' P),
      IsRootDatumOf (identityTorus (Fin n) K) Q' ∧ Q'.IsReduced ∧
      Function.Injective f.weightMap ∧ Function.Injective f.coweightMap ∧
      LinearMap.range f.weightMap = P.rootSpan ℤ := by
  obtain ⟨J', hJ', Q', hQ', hred, _⟩ := exists_numberedRootDatum (K := K) hn
  have : Finite J' := hJ'
  have : Q'.IsReduced := hred
  obtain ⟨f, hfw, hfc, _, hrange⟩ := exists_vectorHom Q' hQ' P B hspan hn e he
  exact ⟨J', hJ', Q', f, hQ', hred, hfw, hfc, hrange⟩

end Langlands.GroupScheme.OddOrthogonalMatrix.TypeBNumbering
