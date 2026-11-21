import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Morphisms of quasi-coherent modules on an affine spectrum from global sections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.SpecQuasicoherentHoms

variable {R : CommRingCat.{u}} (M N : (Spec R).Modules) [M.IsQuasicoherent]
  [N.IsQuasicoherent]

/-- Global sections identify morphisms between quasi-coherent modules on `Spec R` with
`R`-linear maps of their global sections. -/
def homEquiv : (M ⟶ N) ≃ (moduleSpecΓFunctor.obj M ⟶ moduleSpecΓFunctor.obj N) :=
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let M' : P.FullSubcategory := ⟨M, ‹_›⟩
  let N' : P.FullSubcategory := ⟨N, ‹_›⟩
  (P.fullyFaithfulι.homEquiv (X := M') (Y := N')).symm.trans
    ((tildeEquiv (R := R)).fullyFaithfulInverse.homEquiv)

lemma homEquiv_apply (φ : M ⟶ N) : homEquiv M N φ = moduleSpecΓFunctor.map φ := rfl

variable {M N}

/-- Morphisms out of a quasi-coherent module on `Spec R` are determined by their action
on global sections. -/
lemma hom_ext {φ ψ : M ⟶ N} (h : ∀ x, φ.app ⊤ x = ψ.app ⊤ x) : φ = ψ := by
  apply (homEquiv M N).injective
  rw [homEquiv_apply, homEquiv_apply]
  ext x
  exact h x

/-- The morphism of quasi-coherent modules with prescribed morphism of global sections. -/
def lift (ℓ : moduleSpecΓFunctor.obj M ⟶ moduleSpecΓFunctor.obj N) : M ⟶ N :=
  (homEquiv M N).symm ℓ

lemma lift_app (ℓ : moduleSpecΓFunctor.obj M ⟶ moduleSpecΓFunctor.obj N) (x : Γ(M, ⊤)) :
    (lift ℓ).app ⊤ x = ℓ.hom x := by
  have h := (homEquiv M N).apply_symm_apply ℓ
  rw [homEquiv_apply] at h
  exact congrArg (fun f => f.hom x) h

/-- The isomorphism of quasi-coherent modules with prescribed isomorphism of global
sections. -/
def isoOfIso (e : moduleSpecΓFunctor.obj M ≅ moduleSpecΓFunctor.obj N) : M ≅ N where
  hom := lift e.hom
  inv := lift e.inv
  hom_inv_id := hom_ext fun x => by
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
    erw [lift_app, lift_app]
    exact congrArg (fun f => f.hom x) e.hom_inv_id
  inv_hom_id := hom_ext fun x => by
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
    erw [lift_app, lift_app]
    exact congrArg (fun f => f.hom x) e.inv_hom_id

lemma isoOfIso_hom_app (e : moduleSpecΓFunctor.obj M ≅ moduleSpecΓFunctor.obj N)
    (x : Γ(M, ⊤)) : (isoOfIso e).hom.app ⊤ x = e.hom.hom x :=
  lift_app _ x

end Langlands.AlgebraicGeometry.Modules.SpecQuasicoherentHoms
