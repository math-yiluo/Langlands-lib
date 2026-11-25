/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeTargetOpenEdge
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeChartCohomologyTransport

/-! # Affine target Leray comparison in module cohomology

Source: Stacks Project, Tags 01XK, 01E4 and 01FB.
(blueprint: new-flat-base-change-module-leray-comparison)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives
attribute [local irreducible] moduleCohomologyFMap cohomologyOpenRestriction

private theorem linearEquiv_from_scalar_transports
    {R A B C D : Type*} [CommRing R]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [Module R A] [Module R D]
    (e : B ≃+ A) (t : B ≃+ C) (d : C ≃+ D)
    (ρ : R → B → B) (σ : R → C → C)
    (he : ∀ a x, e (ρ a x) = a • e x)
    (ht : ∀ a x, t (ρ a x) = σ a (t x))
    (hd : ∀ a x, d (σ a x) = a • d x) :
    ∃ b : A ≃ₗ[R] D, ∀ x : B, b (e x) = d (t x) := by
  let bAdd := e.symm.trans (t.trans d)
  let l : A →ₗ[R] D :=
    { toFun := bAdd
      map_add' := bAdd.map_add
      map_smul' := fun a y ↦ by
        have hi : e.symm (a • y) = ρ a (e.symm y) := by
          apply e.injective
          rw [AddEquiv.apply_symm_apply, he, AddEquiv.apply_symm_apply]
        change d (t (e.symm (a • y))) = a • d (t (e.symm y))
        rw [hi, ht, hd] }
  refine ⟨LinearEquiv.ofBijective l bAdd.bijective, ?_⟩
  intro x
  change d (t (e.symm (e x))) = d (t x)
  rw [AddEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Combining the two geometric transports compares explicit module cohomology functors.
/-- The target Leray identification commutes with module cohomology pullback.
The displayed algebra is required to be the canonical map on sections.
Only a natural coefficient comparison on the target chart is supplied; no
comparison on the source and no Ext pullback compatibility are assumed.

Source: Stacks Project, Tag 01XK, Lemma 30.4.6; Tag 01E4, Lemma 20.7.3;
Tag 01FB, Remark 20.14.2; the affine chart dictionary in Tag 02KH.
(blueprint: new-flat-base-change-module-leray-comparison)

Proof: The affine chart fibre product is the inverse image of W under f prime.
Pullback composition identifies its coefficient with the restriction of g prime
pullback F. The two coefficient maps from F restricted to f inverse V agree:
apply the adjunction to the restriction-unit equation D.unit_square and the
composition-unit equations. Functoriality of module cohomology therefore identifies
the chart pullback with restriction to W of the map defined by D.psi.
The base-changed morphism is qcqs and its coefficient is quasi-coherent. Its higher
images are quasi-coherent and have vanishing positive cohomology on affine W.
The cocycle-normalized Leray edge is consequently an isomorphism. The comparison
with J is fixed by D.target.augmentation and D.target.components; the cocycle edge
is sectionCohomologyTheta followed by J's right-derived comparison. Thus the edge
of the restricted class is the restriction of D.targetClass. Compose the chart
identification and this edge with the inverse of E at the chart coefficient.
Naturality of E for scalar endomorphisms makes this composite B-linear. This
constructs b and proves the formula. Empty opens, zero coefficients and p = 0
use the same complexes. No pullback is assumed invertible or exact. -/
theorem exists_flatBaseChange_module_leray_comparison
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent]
    (I : InjectiveResolution F)
    (J : InjectiveResolution
      ((Scheme.Modules.tensorPullback (pullback.snd g f)).obj F))
    (p : ℕ) (V : S.Opens) (W : S'.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (eVW : W ≤ g ⁻¹ᵁ V)
    (D : Scheme.Modules.FlatBaseChangeOpenChoices f g F I J V)
    [Algebra Γ(S, V) Γ(S', W)]
    (hAlgebra : algebraMap Γ(S, V) Γ(S', W) = (g.appLE V W eVW).hom) :
    let h := f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ
    let N := (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F
    let Q := ((Scheme.Modules.pushforward (pullback.fst g f)).rightDerived p).obj
      ((Scheme.Modules.tensorPullback (pullback.snd g f)).obj F)
    ∀ E : ∀ M : (baseChangedScheme (S := Γ(S', W)) h).Modules,
        ((RingedSpace.moduleCohomology
          (baseChangedScheme (S := Γ(S', W)) h).toRingedSpace p).obj M) ≃+ H M p,
      (∀ (M M' : (baseChangedScheme (S := Γ(S', W)) h).Modules) (φ : M ⟶ M')
        (x : (RingedSpace.moduleCohomology
          (baseChangedScheme (S := Γ(S', W)) h).toRingedSpace p).obj M),
        E M' (((RingedSpace.moduleCohomology
          (baseChangedScheme (S := Γ(S', W)) h).toRingedSpace p).map φ).hom x) =
          H.map φ p (E M x)) →
      ∃ b : HOver (baseChangeSnd (S := Γ(S', W)) h)
          (baseChangedModule (S := Γ(S', W)) h N) p ≃ₗ[Γ(S', W)] Γ(Q, W),
        ∀ x : (RingedSpace.moduleCohomology
          (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
            ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F),
          b (E (baseChangedModule (S := Γ(S', W)) h N)
            (moduleCohomologyFMap (baseChangeFst (S := Γ(S', W)) h)
              (baseChangeUnit (S := Γ(S', W)) h N) p
              (((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).map
                ((restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app F).hom).hom x))) =
            Q.presheaf.map (homOfLE eVW).op
              (D.targetClass p
                (moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
                  ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi p x)) := by
  classical
  intro h N Q E hE
  let T := baseChangedScheme (S := Γ(S', W)) h
  let A := baseChangedModule (S := Γ(S', W)) h N
  let C := RingedSpace.moduleCohomology T.toRingedSpace p
  -- Name the existence proofs before eliminating them, avoiding expensive generalization.
  have htransport := exists_flatBaseChange_chart_cohomology_transport
    f g F I J p V W hV hW eVW D hAlgebra
  rcases htransport with ⟨t, ht, hunit⟩
  have hedge := exists_flatBaseChange_target_open_edge f g F I J p V W hW eVW D
  rcases hedge with ⟨d, hd, hres⟩
  let ρ (a : Γ(S', W)) (x : C.obj A) :=
    (C.map (A.smulHom (((Scheme.ΓSpecIso Γ(S', W)).inv ≫
      (baseChangeSnd (S := Γ(S', W)) h).appTop).hom a))).hom x
  have hscalar (a : Γ(S', W)) (x : C.obj A) :
      E A (ρ a x) =
        a • (show HOver (baseChangeSnd (S := Γ(S', W)) h) A p from E A x) := by
    exact hE A A (A.smulHom (((Scheme.ΓSpecIso Γ(S', W)).inv ≫
      (baseChangeSnd (S := Γ(S', W)) h).appTop).hom a)) x
  have hlinear := linearEquiv_from_scalar_transports
    (A := HOver (baseChangeSnd (S := Γ(S', W)) h) A p)
    (E A) t d ρ _ hscalar ht hd
  rcases hlinear with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  intro x
  exact (hb _).trans ((congrArg d (hunit x)).trans (hres _))

end AlgebraicGeometry.Scheme.Modules
