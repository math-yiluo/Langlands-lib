import Langlands.LinearAlgebra.CartanBNumbering
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.Hom

/-! # Rigidity of based type-B automorphisms with full root span -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.TypeBBasedAutomorphism

variable {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum J X Y) (B : P.Base)

/-- The permutation of the simple support induced by a based automorphism. -/
def simplePermutation (θ : P.Aut) (hθ : ∀ i, i ∈ B.support ↔ θ.indexEquiv i ∈ B.support) :
    B.support ≃ B.support := θ.indexEquiv.subtypeEquiv hθ

/-- A based type-B automorphism fixes every simple root index. -/
theorem simplePermutation_eq_refl {n : ℕ} (hn : 2 ≤ n) (e : B.support ≃ Fin n)
    (he : ∀ a b : B.support, P.pairing a.val b.val = CartanMatrix.B n (e a) (e b))
    (θ : P.Aut) (hθ : ∀ i, i ∈ B.support ↔ θ.indexEquiv i ∈ B.support) :
    simplePermutation P B θ hθ = Equiv.refl _ := by
  let f := simplePermutation P B θ hθ
  have hf : ∀ i j, CartanMatrix.B n (e (f (e.symm i))) (e (f (e.symm j))) =
      CartanMatrix.B n i j := by
    intro i j
    rw [← he]
    change P.pairing (θ.indexEquiv (e.symm i).val) (θ.indexEquiv (e.symm j).val) = _
    rw [θ.toHom.pairing, he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have h := CartanBNumbering.rigid hn (fun i => e (f (e.symm i))) hf
  apply Equiv.ext
  intro a
  apply e.injective
  change e (f a) = e a
  simpa only [Equiv.symm_apply_apply] using h (e a)

/-- When roots generate the full character lattice, every based type-B
root-datum automorphism is the identity on both lattices and all indices. -/
theorem eq_one_of_full_rootSpan {n : ℕ} (hn : 2 ≤ n) (e : B.support ≃ Fin n)
    (he : ∀ a b : B.support, P.pairing a.val b.val = CartanMatrix.B n (e a) (e b))
    (hspan : P.rootSpan ℤ = ⊤)
    (θ : P.Aut) (hθ : ∀ i, i ∈ B.support ↔ θ.indexEquiv i ∈ B.support) : θ = 1 := by
  have hfix (a : B.support) : θ.indexEquiv a.val = a.val :=
    congrArg Subtype.val (Equiv.congr_fun (simplePermutation_eq_refl P B hn e he θ hθ) a)
  have hw : θ.toHom.weightMap = (1 : P.Aut).toHom.weightMap := by
    apply LinearMap.ext_on (B.span_root_support.trans hspan)
    rintro _ ⟨a, ha, rfl⟩
    change θ.weightMap (P.root a) = P.root a
    rw [θ.root_weightMap_apply, hfix ⟨a, ha⟩]
  apply RootPairing.Equiv.weightHom_injective P
  ext x
  exact LinearMap.congr_fun hw x

end Langlands.TypeBBasedAutomorphism
