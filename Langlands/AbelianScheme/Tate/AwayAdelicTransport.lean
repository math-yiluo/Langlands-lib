import Langlands.AbelianScheme.Tate.AwayRationalScalars
import Langlands.AbelianScheme.Tate.AdelicTransport

/-! # Prime-to-modulus adelic transport along rational homomorphisms -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AbelianScheme.Tate

universe u
variable {S : Scheme.{u}} (T : Over S)
variable {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
variable (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
variable {A B C : AbelianScheme S}

/-- An invertible rational homomorphism gives a prime-to-modulus adelic linear equivalence. -/
def primeToFiniteAdeleIso (e : Rationalization.of A ≅ Rationalization.of B) :
    let := primeToFiniteAdeleModule A T hAway
    let := primeToFiniteAdeleModule B T hAway
    RationalAway A T m ≃ₗ[Global.PrimeToFiniteAdeles m] RationalAway B T m := by
  let := primeToFiniteAdeleModule A T hAway
  let := primeToFiniteAdeleModule B T hAway
  exact { (rationalIso T (fun n => Nat.Coprime n m) e).toEquiv with
    map_add' := (rationalIso T (fun n => Nat.Coprime n m) e).map_add
    map_smul' := rationalHomMap_primeToFiniteAdeleAction T hAway e.hom }

@[simp] theorem primeToFiniteAdeleIso_apply (e : Rationalization.of A ≅ Rationalization.of B)
    (x : RationalAway A T m) :
    primeToFiniteAdeleIso T hAway e x = rationalHomMap T (fun n => Nat.Coprime n m) e.hom x := rfl

@[simp] theorem primeToFiniteAdeleIso_symm (e : Rationalization.of A ≅ Rationalization.of B) :
    let := primeToFiniteAdeleModule A T hAway
    let := primeToFiniteAdeleModule B T hAway
    (primeToFiniteAdeleIso T hAway e).symm = primeToFiniteAdeleIso T hAway e.symm := by
  let := primeToFiniteAdeleModule A T hAway
  let := primeToFiniteAdeleModule B T hAway
  rfl

@[simp] theorem primeToFiniteAdeleIso_refl :
    let := primeToFiniteAdeleModule A T hAway
    primeToFiniteAdeleIso T hAway (Iso.refl (Rationalization.of A)) =
      LinearEquiv.refl (Global.PrimeToFiniteAdeles m) _ := by
  let := primeToFiniteAdeleModule A T hAway
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_identity T (fun n => Nat.Coprime n m)) x

theorem primeToFiniteAdeleIso_trans (e : Rationalization.of A ≅ Rationalization.of B)
    (f : Rationalization.of B ≅ Rationalization.of C) :
    let := primeToFiniteAdeleModule A T hAway
    let := primeToFiniteAdeleModule B T hAway
    let := primeToFiniteAdeleModule C T hAway
    primeToFiniteAdeleIso T hAway (e.trans f) =
      (primeToFiniteAdeleIso T hAway e).trans (primeToFiniteAdeleIso T hAway f) := by
  let := primeToFiniteAdeleModule A T hAway
  let := primeToFiniteAdeleModule B T hAway
  let := primeToFiniteAdeleModule C T hAway
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_comp T (fun n => Nat.Coprime n m) e.hom f.hom) x

variable {D : Type*} [Ring D] [Algebra ℚ D]
variable (iA : D →ₐ[ℚ] Rationalization.End A) (iB : D →ₐ[ℚ] Rationalization.End B)

/-- Intertwining extends to the constructed tensor-product algebra action. -/
theorem rationalHomMap_primeToFiniteAdeleAlgebraAction (f : Rationalization.Hom A B)
    (hf : ∀ d, Rationalization.comp A A B (iA d) f =
      Rationalization.comp A B B f (iB d))
    (a : D ⊗[ℚ] Global.PrimeToFiniteAdeles m) (x : RationalAway A T m) :
    rationalHomMap T (fun n => Nat.Coprime n m) f (primeToFiniteAdeleAlgebraAction A T hAway iA a x) =
      primeToFiniteAdeleAlgebraAction B T hAway iB a (rationalHomMap T (fun n => Nat.Coprime n m) f x) := by
  induction a using TensorProduct.inductionOn with
  | tmul d a =>
    rw [primeToFiniteAdeleAlgebraAction_tmul, primeToFiniteAdeleAlgebraAction_tmul,
      rationalHomMap_intertwines T (fun n => Nat.Coprime n m) iA iB f hf,
      rationalHomMap_primeToFiniteAdeleAction]
  | add a b ha hb => simp_all

/-- An intertwining rational homomorphism is linear over D tensored with the away adeles. -/
def primeToFiniteAdeleAlgebraHomMap (f : Rationalization.Hom A B)
    (hf : ∀ d, Rationalization.comp A A B (iA d) f =
      Rationalization.comp A B B f (iB d)) :
    let := primeToFiniteAdeleAlgebraModule A T hAway iA
    let := primeToFiniteAdeleAlgebraModule B T hAway iB
    RationalAway A T m →ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m] RationalAway B T m := by
  let := primeToFiniteAdeleAlgebraModule A T hAway iA
  let := primeToFiniteAdeleAlgebraModule B T hAway iB
  exact { (rationalHomMap T (fun n => Nat.Coprime n m) f).toAddHom with
    map_smul' := rationalHomMap_primeToFiniteAdeleAlgebraAction T hAway iA iB f hf }

@[simp] theorem primeToFiniteAdeleAlgebraHomMap_apply (f : Rationalization.Hom A B)
    (hf : ∀ d, Rationalization.comp A A B (iA d) f =
      Rationalization.comp A B B f (iB d)) (x : RationalAway A T m) :
    primeToFiniteAdeleAlgebraHomMap T hAway iA iB f hf x = rationalHomMap T (fun n => Nat.Coprime n m) f x := rfl

/-- An invertible intertwining rational homomorphism gives tensor-algebra transport. -/
def primeToFiniteAdeleAlgebraIso (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d)) :
    let := primeToFiniteAdeleAlgebraModule A T hAway iA
    let := primeToFiniteAdeleAlgebraModule B T hAway iB
    RationalAway A T m ≃ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m] RationalAway B T m := by
  let := primeToFiniteAdeleAlgebraModule A T hAway iA
  let := primeToFiniteAdeleAlgebraModule B T hAway iB
  exact { (rationalIso T (fun n => Nat.Coprime n m) e).toEquiv with
    map_add' := (rationalIso T (fun n => Nat.Coprime n m) e).map_add
    map_smul' := rationalHomMap_primeToFiniteAdeleAlgebraAction T hAway iA iB e.hom he }

@[simp] theorem primeToFiniteAdeleAlgebraIso_apply
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d)) (x : RationalAway A T m) :
    primeToFiniteAdeleAlgebraIso T hAway iA iB e he x = rationalHomMap T (fun n => Nat.Coprime n m) e.hom x := rfl

@[simp] theorem primeToFiniteAdeleAlgebraHomMap_identity :
    let := primeToFiniteAdeleAlgebraModule A T hAway iA
    primeToFiniteAdeleAlgebraHomMap T hAway iA iA (Rationalization.identity A)
      (rationalIntertwines_identity iA) = LinearMap.id := by
  let := primeToFiniteAdeleAlgebraModule A T hAway iA
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_identity T (fun n => Nat.Coprime n m)) x

theorem primeToFiniteAdeleAlgebraHomMap_comp (iC : D →ₐ[ℚ] Rationalization.End C)
    (f : Rationalization.Hom A B) (g : Rationalization.Hom B C)
    (hf : ∀ d, Rationalization.comp A A B (iA d) f =
      Rationalization.comp A B B f (iB d))
    (hg : ∀ d, Rationalization.comp B B C (iB d) g =
      Rationalization.comp B C C g (iC d)) :
    let := primeToFiniteAdeleAlgebraModule A T hAway iA
    let := primeToFiniteAdeleAlgebraModule B T hAway iB
    let := primeToFiniteAdeleAlgebraModule C T hAway iC
    primeToFiniteAdeleAlgebraHomMap T hAway iA iC (Rationalization.comp A B C f g)
      (rationalIntertwines_comp iA iB iC f g hf hg) =
      (primeToFiniteAdeleAlgebraHomMap T hAway iB iC g hg).comp
        (primeToFiniteAdeleAlgebraHomMap T hAway iA iB f hf) := by
  let := primeToFiniteAdeleAlgebraModule A T hAway iA
  let := primeToFiniteAdeleAlgebraModule B T hAway iB
  let := primeToFiniteAdeleAlgebraModule C T hAway iC
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_comp T (fun n => Nat.Coprime n m) f g) x

@[simp] theorem primeToFiniteAdeleAlgebraIso_refl :
    let := primeToFiniteAdeleAlgebraModule A T hAway iA
    primeToFiniteAdeleAlgebraIso T hAway iA iA (Iso.refl (Rationalization.of A))
      (rationalIntertwines_identity iA) =
      LinearEquiv.refl (D ⊗[ℚ] Global.PrimeToFiniteAdeles m) _ := by
  let := primeToFiniteAdeleAlgebraModule A T hAway iA
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_identity T (fun n => Nat.Coprime n m)) x

@[simp] theorem primeToFiniteAdeleAlgebraIso_symm
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d)) :
    let := primeToFiniteAdeleAlgebraModule A T hAway iA
    let := primeToFiniteAdeleAlgebraModule B T hAway iB
    (primeToFiniteAdeleAlgebraIso T hAway iA iB e he).symm =
      primeToFiniteAdeleAlgebraIso T hAway iB iA e.symm
        (rationalIntertwines_inverse iA iB e he) := by
  let := primeToFiniteAdeleAlgebraModule A T hAway iA
  let := primeToFiniteAdeleAlgebraModule B T hAway iB
  rfl

theorem primeToFiniteAdeleAlgebraIso_trans (iC : D →ₐ[ℚ] Rationalization.End C)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (f : Rationalization.of B ≅ Rationalization.of C)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : ∀ d, Rationalization.comp B B C (iB d) f.hom =
      Rationalization.comp B C C f.hom (iC d)) :
    let := primeToFiniteAdeleAlgebraModule A T hAway iA
    let := primeToFiniteAdeleAlgebraModule B T hAway iB
    let := primeToFiniteAdeleAlgebraModule C T hAway iC
    primeToFiniteAdeleAlgebraIso T hAway iA iC (e.trans f)
      (rationalIntertwines_comp iA iB iC e.hom f.hom he hf) =
      (primeToFiniteAdeleAlgebraIso T hAway iA iB e he).trans
        (primeToFiniteAdeleAlgebraIso T hAway iB iC f hf) := by
  let := primeToFiniteAdeleAlgebraModule A T hAway iA
  let := primeToFiniteAdeleAlgebraModule B T hAway iB
  let := primeToFiniteAdeleAlgebraModule C T hAway iC
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_comp T (fun n => Nat.Coprime n m) e.hom f.hom) x

end Langlands.AbelianScheme.Tate
