import Langlands.AbelianScheme.Tate.RationalScalars

/-! # Finite-adelic transport along rational homomorphisms -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AbelianScheme.Tate

universe u
variable {S : Scheme.{u}} (T : Over S) (P : ℕ → Prop)
variable (h : Global.RationalProfiniteIntegerAdeleComparison)
variable {A B C : AbelianScheme S}

/-- An invertible rational homomorphism gives a finite-adelic linear equivalence. -/
def finiteAdeleIso (e : Rationalization.of A ≅ Rationalization.of B) :
    let := finiteAdeleModule A T P h
    let := finiteAdeleModule B T P h
    Rational A T P ≃ₗ[Global.FiniteAdeles ℚ] Rational B T P := by
  let := finiteAdeleModule A T P h
  let := finiteAdeleModule B T P h
  exact { (rationalIso T P e).toEquiv with
    map_add' := (rationalIso T P e).map_add
    map_smul' := rationalHomMap_finiteAdeleAction T P h e.hom }

@[simp] theorem finiteAdeleIso_apply (e : Rationalization.of A ≅ Rationalization.of B)
    (x : Rational A T P) :
    finiteAdeleIso T P h e x = rationalHomMap T P e.hom x := rfl

@[simp] theorem finiteAdeleIso_symm (e : Rationalization.of A ≅ Rationalization.of B) :
    let := finiteAdeleModule A T P h
    let := finiteAdeleModule B T P h
    (finiteAdeleIso T P h e).symm = finiteAdeleIso T P h e.symm := by
  let := finiteAdeleModule A T P h
  let := finiteAdeleModule B T P h
  rfl

@[simp] theorem finiteAdeleIso_refl :
    let := finiteAdeleModule A T P h
    finiteAdeleIso T P h (Iso.refl (Rationalization.of A)) =
      LinearEquiv.refl (Global.FiniteAdeles ℚ) _ := by
  let := finiteAdeleModule A T P h
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_identity T P) x

theorem finiteAdeleIso_trans (e : Rationalization.of A ≅ Rationalization.of B)
    (f : Rationalization.of B ≅ Rationalization.of C) :
    let := finiteAdeleModule A T P h
    let := finiteAdeleModule B T P h
    let := finiteAdeleModule C T P h
    finiteAdeleIso T P h (e.trans f) =
      (finiteAdeleIso T P h e).trans (finiteAdeleIso T P h f) := by
  let := finiteAdeleModule A T P h
  let := finiteAdeleModule B T P h
  let := finiteAdeleModule C T P h
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_comp T P e.hom f.hom) x

variable {D : Type*} [Ring D] [Algebra ℚ D]
variable (iA : D →ₐ[ℚ] Rationalization.End A) (iB : D →ₐ[ℚ] Rationalization.End B)

/-- Identity morphisms intertwine each rational endomorphism action. -/
theorem rationalIntertwines_identity (d : D) :
    Rationalization.comp A A A (iA d) (Rationalization.identity A) =
      Rationalization.comp A A A (Rationalization.identity A) (iA d) := by
  simp

/-- Intertwining is preserved by composition of rational homomorphisms. -/
theorem rationalIntertwines_comp (iC : D →ₐ[ℚ] Rationalization.End C)
    (f : Rationalization.Hom A B) (g : Rationalization.Hom B C)
    (hf : ∀ d, Rationalization.comp A A B (iA d) f =
      Rationalization.comp A B B f (iB d))
    (hg : ∀ d, Rationalization.comp B B C (iB d) g =
      Rationalization.comp B C C g (iC d)) (d : D) :
    Rationalization.comp A A C (iA d) (Rationalization.comp A B C f g) =
      Rationalization.comp A C C (Rationalization.comp A B C f g) (iC d) := by
  rw [← Rationalization.comp_assoc, hf, Rationalization.comp_assoc, hg,
    ← Rationalization.comp_assoc]

/-- The inverse of an intertwining rational isomorphism also intertwines. -/
theorem rationalIntertwines_inverse (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d)) (d : D) :
    Rationalization.comp B B A (iB d) e.inv =
      Rationalization.comp B A A e.inv (iA d) := by
  change (iB d : Rationalization.of B ⟶ Rationalization.of B) ≫ e.inv = e.inv ≫ iA d
  have hd : (iA d : Rationalization.of A ⟶ Rationalization.of A) ≫ e.hom =
      e.hom ≫ iB d := he d
  apply (cancel_epi e.hom).1
  rw [← Category.assoc, ← hd, Category.assoc, e.hom_inv_id,
    Category.comp_id, e.hom_inv_id_assoc]

/-- Intertwining the actual rational endomorphisms intertwines their Tate actions. -/
theorem rationalHomMap_intertwines (f : Rationalization.Hom A B)
    (hf : ∀ d, Rationalization.comp A A B (iA d) f =
      Rationalization.comp A B B f (iB d)) (d : D) (x : Rational A T P) :
    rationalHomMap T P f (rationalEndAction A T P (iA d) x) =
      rationalEndAction B T P (iB d) (rationalHomMap T P f x) := by
  have he := congrArg (rationalHomMap T P) (hf d)
  rw [rationalHomMap_comp, rationalHomMap_comp] at he
  exact LinearMap.congr_fun he x

/-- Intertwining extends to the constructed tensor-product algebra action. -/
theorem rationalHomMap_finiteAdeleAlgebraAction (f : Rationalization.Hom A B)
    (hf : ∀ d, Rationalization.comp A A B (iA d) f =
      Rationalization.comp A B B f (iB d))
    (a : D ⊗[ℚ] Global.FiniteAdeles ℚ) (x : Rational A T P) :
    rationalHomMap T P f (finiteAdeleAlgebraAction A T P h iA a x) =
      finiteAdeleAlgebraAction B T P h iB a (rationalHomMap T P f x) := by
  induction a using TensorProduct.inductionOn with
  | tmul d a =>
    rw [finiteAdeleAlgebraAction_tmul, finiteAdeleAlgebraAction_tmul,
      rationalHomMap_intertwines T P iA iB f hf,
      rationalHomMap_finiteAdeleAction]
  | add a b ha hb => simp_all

/-- An intertwining rational homomorphism is linear over D tensor_Q A_f. -/
def finiteAdeleAlgebraHomMap (f : Rationalization.Hom A B)
    (hf : ∀ d, Rationalization.comp A A B (iA d) f =
      Rationalization.comp A B B f (iB d)) :
    let := finiteAdeleAlgebraModule A T P h iA
    let := finiteAdeleAlgebraModule B T P h iB
    Rational A T P →ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ] Rational B T P := by
  let := finiteAdeleAlgebraModule A T P h iA
  let := finiteAdeleAlgebraModule B T P h iB
  exact { (rationalHomMap T P f).toAddHom with
    map_smul' := rationalHomMap_finiteAdeleAlgebraAction T P h iA iB f hf }

@[simp] theorem finiteAdeleAlgebraHomMap_apply (f : Rationalization.Hom A B)
    (hf : ∀ d, Rationalization.comp A A B (iA d) f =
      Rationalization.comp A B B f (iB d)) (x : Rational A T P) :
    finiteAdeleAlgebraHomMap T P h iA iB f hf x = rationalHomMap T P f x := rfl

/-- An invertible intertwining rational homomorphism gives tensor-algebra transport. -/
def finiteAdeleAlgebraIso (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d)) :
    let := finiteAdeleAlgebraModule A T P h iA
    let := finiteAdeleAlgebraModule B T P h iB
    Rational A T P ≃ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ] Rational B T P := by
  let := finiteAdeleAlgebraModule A T P h iA
  let := finiteAdeleAlgebraModule B T P h iB
  exact { (rationalIso T P e).toEquiv with
    map_add' := (rationalIso T P e).map_add
    map_smul' := rationalHomMap_finiteAdeleAlgebraAction T P h iA iB e.hom he }

@[simp] theorem finiteAdeleAlgebraIso_apply
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d)) (x : Rational A T P) :
    finiteAdeleAlgebraIso T P h iA iB e he x = rationalHomMap T P e.hom x := rfl

@[simp] theorem finiteAdeleAlgebraHomMap_identity :
    let := finiteAdeleAlgebraModule A T P h iA
    finiteAdeleAlgebraHomMap T P h iA iA (Rationalization.identity A)
      (rationalIntertwines_identity iA) = LinearMap.id := by
  let := finiteAdeleAlgebraModule A T P h iA
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_identity T P) x

theorem finiteAdeleAlgebraHomMap_comp (iC : D →ₐ[ℚ] Rationalization.End C)
    (f : Rationalization.Hom A B) (g : Rationalization.Hom B C)
    (hf : ∀ d, Rationalization.comp A A B (iA d) f =
      Rationalization.comp A B B f (iB d))
    (hg : ∀ d, Rationalization.comp B B C (iB d) g =
      Rationalization.comp B C C g (iC d)) :
    let := finiteAdeleAlgebraModule A T P h iA
    let := finiteAdeleAlgebraModule B T P h iB
    let := finiteAdeleAlgebraModule C T P h iC
    finiteAdeleAlgebraHomMap T P h iA iC (Rationalization.comp A B C f g)
      (rationalIntertwines_comp iA iB iC f g hf hg) =
      (finiteAdeleAlgebraHomMap T P h iB iC g hg).comp
        (finiteAdeleAlgebraHomMap T P h iA iB f hf) := by
  let := finiteAdeleAlgebraModule A T P h iA
  let := finiteAdeleAlgebraModule B T P h iB
  let := finiteAdeleAlgebraModule C T P h iC
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_comp T P f g) x

@[simp] theorem finiteAdeleAlgebraIso_refl :
    let := finiteAdeleAlgebraModule A T P h iA
    finiteAdeleAlgebraIso T P h iA iA (Iso.refl (Rationalization.of A))
      (rationalIntertwines_identity iA) =
      LinearEquiv.refl (D ⊗[ℚ] Global.FiniteAdeles ℚ) _ := by
  let := finiteAdeleAlgebraModule A T P h iA
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_identity T P) x

@[simp] theorem finiteAdeleAlgebraIso_symm
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d)) :
    let := finiteAdeleAlgebraModule A T P h iA
    let := finiteAdeleAlgebraModule B T P h iB
    (finiteAdeleAlgebraIso T P h iA iB e he).symm =
      finiteAdeleAlgebraIso T P h iB iA e.symm
        (rationalIntertwines_inverse iA iB e he) := by
  let := finiteAdeleAlgebraModule A T P h iA
  let := finiteAdeleAlgebraModule B T P h iB
  rfl

theorem finiteAdeleAlgebraIso_trans (iC : D →ₐ[ℚ] Rationalization.End C)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (f : Rationalization.of B ≅ Rationalization.of C)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : ∀ d, Rationalization.comp B B C (iB d) f.hom =
      Rationalization.comp B C C f.hom (iC d)) :
    let := finiteAdeleAlgebraModule A T P h iA
    let := finiteAdeleAlgebraModule B T P h iB
    let := finiteAdeleAlgebraModule C T P h iC
    finiteAdeleAlgebraIso T P h iA iC (e.trans f)
      (rationalIntertwines_comp iA iB iC e.hom f.hom he hf) =
      (finiteAdeleAlgebraIso T P h iA iB e he).trans
        (finiteAdeleAlgebraIso T P h iB iC f hf) := by
  let := finiteAdeleAlgebraModule A T P h iA
  let := finiteAdeleAlgebraModule B T P h iB
  let := finiteAdeleAlgebraModule C T P h iC
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_comp T P e.hom f.hom) x

end Langlands.AbelianScheme.Tate
