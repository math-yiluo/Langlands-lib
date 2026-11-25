/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatAffineTensorReassociation
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Canonical base change of sections on an affine open

Source: Stacks Project, Tags 02KG and 02KH.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {X : Scheme.{u}}

/-- Base change of sections on one affine open, with its canonical pure-tensor formula.
Source: Stacks Project, Tag 02KG, used in the separated-case proof of Tag 02KH.
(blueprint: lem-pc-flat-affine-base-change-sections)

Proof: The inverse image of W is the fibre product of W with Spec S over Spec R,
hence affine. Its ring of sections is S tensor_R Gamma(W, O_X), by the affine
cartesian ring formula. Apply exists_tensorPullback_affine_sections to W and its
inverse image. Uniqueness of left adjoints identifies tensorPullback with pullback;
the conjugate-isomorphism unit equation preserves the pure-tensor formula.
Tensor associativity then identifies the sections with S tensor_R Gamma(W, M).
Transport through W' = g inverse W and restrict the unit along h. The resulting
S-linear equivalence sends b tensor s to the restricted scalar b times the
restricted adjunction unit of s. This works for the empty affine open as well:
both section modules are zero and the same canonical formula holds. -/
theorem exists_baseChange_affine_section_equiv (f : X ⟶ Spec (.of R))
    (W : X.Opens) (hW : IsAffineOpen W) (M : X.Modules) [M.IsQuasicoherent]
    (W' : (baseChangedScheme (S := S) f).Opens)
    (hW' : W' = baseChangeFst (S := S) f ⁻¹ᵁ W)
    (h : W' ≤ baseChangeFst (S := S) f ⁻¹ᵁ W) :
    let N := baseChangedModule (S := S) f M
    let P := M.presheafModuleCat ⋙
      ModuleCat.restrictScalars (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
    let Q := N.presheafModuleCat ⋙ ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom)
    ∃ e : TensorProduct R S (P.obj (op W)) ≃ₗ[S] Q.obj (op W'),
      ∀ (b : S) (s : P.obj (op W)),
        e (b ⊗ₜ[R] s) =
          ((baseChangedScheme (S := S) f).presheaf.map
            (homOfLE (le_top : W' ≤ ⊤)).op).hom
            (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom b) •
          N.presheaf.map (homOfLE h).op
            ((baseChangeUnit (S := S) f M).val.app (op W) s) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  classical
  dsimp only
  let g := baseChangeFst (S := S) f
  let Z := baseChangedScheme (S := S) f
  let N := baseChangedModule (S := S) f M
  let Q := N.presheafModuleCat ⋙ ModuleCat.restrictScalars
    (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom)
  let β := ((Z.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op).hom).comp
    (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom)
  let : IsAffineHom (baseChangeMap R S) := by infer_instance
  have hg : IsAffineHom g := by
    dsimp [g, baseChangeFst]
    exact MorphismProperty.pullback_fst _ _ inferInstance
  have hU : IsAffineOpen W' := by
    rw [hW']
    exact hW.preimage g
  let V : X.affineOpens := ⟨W, hW⟩
  let U : Z.affineOpens := ⟨W', hU⟩
  let : Algebra Γ(X, W) Γ(Z, W') := (g.appLE W W' h).hom.toAlgebra
  let : ∀ G : X.Modules, Module Γ(X, W) Γ((tensorPullback g).obj G, W') :=
    fun G ↦ Module.compHom _ (g.appLE W W' h).hom
  obtain ⟨c, hc, hb, hp, _⟩ := exists_tensorPullback_affine_sections g V U h
  let adj := Classical.choose (exists_tensorPullbackAdjunction g)
  let k := adj.leftAdjointUniq (pullbackPushforwardAdjunction g)
  let T := TensorProduct Γ(X, W) Γ(Z, W') Γ(M, W)
  let : Module S T := Module.compHom _ β
  obtain ⟨e₀, he₀⟩ :=
    exists_baseChange_affine_tensor_reassociation (S := S) f W hW M W' hW' h
  let hM : M.IsQuasicoherent := inferInstance
  let d : T →ₗ[S] Q.obj (op W') :=
    { toFun := fun t ↦ ((k.hom.app M).app W')
        (c M hM (TensorProduct.comm Γ(X, W) Γ(Z, W') Γ(M, W) t))
      map_add' := by
        intro t t'
        rw [map_add, map_add, map_add]
      map_smul' := by
        intro b t
        change ((k.hom.app M).app W')
            (c M hM (TensorProduct.comm Γ(X, W) Γ(Z, W') Γ(M, W) (β b • t))) =
          β b • ((k.hom.app M).app W')
            (c M hM (TensorProduct.comm Γ(X, W) Γ(Z, W') Γ(M, W) t))
        rw [← Hom.app_smul]
        congr 1
        have hb' := hb M hM (β b)
          ((TensorProduct.comm Γ(X, W) Γ(M, W) Γ(Z, W')).symm t)
        change c M hM
            ((TensorProduct.comm Γ(X, W) Γ(M, W) Γ(Z, W')).symm
              (β b • TensorProduct.comm Γ(X, W) Γ(M, W) Γ(Z, W')
                ((TensorProduct.comm Γ(X, W) Γ(M, W) Γ(Z, W')).symm t))) = _ at hb'
        rw [LinearEquiv.apply_symm_apply] at hb'
        simpa only [TensorProduct.comm_symm] using hb' }
  have hd : Function.Bijective d :=
    (ConcreteCategory.bijective_of_isIso ((k.hom.app M).app W')).comp
      ((hc M hM).comp (TensorProduct.comm Γ(X, W) Γ(Z, W') Γ(M, W)).bijective)
  refine ⟨e₀.trans (LinearEquiv.ofBijective d hd), ?_⟩
  intro b s
  change d (e₀ (b ⊗ₜ[R] s)) = _
  rw [he₀]
  change ((k.hom.app M).app W') (c M hM (s ⊗ₜ[Γ(X, W)] β b)) = _
  rw [hp M hM s (β b), Hom.app_smul]
  congr 1
  have hn := (k.hom.app M).val.naturality (homOfLE h).op
  have hv := Adjunction.unit_leftAdjointUniq_hom_app adj
    (pullbackPushforwardAdjunction g) M
  exact (congrArg (fun q ↦ q ((adj.unit.app M).val.app (op W) s)) hn).trans
    (congrArg (fun z ↦ N.presheaf.map (homOfLE h).op z)
      (congrArg (fun q ↦ q.val.app (op W) s) hv))

end AlgebraicGeometry.Scheme.Modules
