/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import WeilConjectures.AlgebraicGeometry.Modules.DeterminantSplitChartComparison
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.TensorProduct.Basis
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafLocalFreeComparison
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafRankWedgeZero
import WeilConjectures.LinearAlgebra.ExteriorTopDirectSum

/-!
# Local bijectivity of split determinant linear maps
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

private noncomputable def topIndexEquiv (n : ℕ) :
    Set.powersetCard (Fin n) n ≃ Unit where
  toFun := fun _ ↦ ()
  invFun := fun _ ↦ ⟨Finset.univ, by simp⟩
  left_inv := by
    intro a
    apply Subtype.ext
    symm
    apply Finset.eq_univ_of_card
    simpa only [Fintype.card_fin] using Set.powersetCard.card_eq a
  right_inv := by intro a; cases a; rfl

private noncomputable def topBasis
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (b : Module.Basis (Fin n) R M) :
    Module.Basis Unit R (⋀[R]^n M) :=
  (b.exteriorPower n).reindex (topIndexEquiv n)

private theorem topBasis_apply
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (b : Module.Basis (Fin n) R M) (i : Unit) :
    topBasis n b i = _root_.exteriorPower.ιMulti R n b := by
  rw [topBasis, Module.Basis.reindex_apply, _root_.exteriorPower.basis_apply]
  unfold _root_.exteriorPower.ιMulti_family
  congr 1
  funext j
  exact congrArg b
    ((Set.powersetCard.ofFinEmbEquiv.symm ((topIndexEquiv n).symm i)).strictMono.apply_eq)

private theorem split_wedge_bijective
    {R A B C : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (r s : ℕ) (a : Module.Basis (Fin r) R A) (c : Module.Basis (Fin s) R C)
    (e : B ≃ₗ[R] A × C) (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : ∀ x, e (f x) = (x, 0)) (hg : ∀ x, (e x).2 = g x)
    (l : C → B) (hl : ∀ x, g (l x) = x)
    (d : ((⋀[R]^r A) ⊗[R] (⋀[R]^s C)) →ₗ[R] ⋀[R]^(r + s) B)
    (hd : ∀ x y, d (_root_.exteriorPower.ιMulti R r x ⊗ₜ[R] _root_.exteriorPower.ιMulti R s y) =
      _root_.exteriorPower.ιMulti R (r + s) (Fin.append (fun i ↦ f (x i)) (fun j ↦ l (y j)))) :
    Function.Bijective d := by
  classical
  -- Only basis vectors need lifts; their linear extension gives a new splitting.
  let t : C →ₗ[R] B := c.constr R (fun j ↦ l (c j))
  have ht : g.comp t = LinearMap.id := by
    apply c.ext
    intro j
    simp [t, hl]
  have ht' (x : C) : g (t x) = x := LinearMap.congr_fun ht x
  let q : (A × C) →ₗ[R] B := f.coprod t
  have hq (x : A × C) : e (q x) = (x.1 + (e (t x.2)).1, x.2) := by
    apply Prod.ext
    · simp [q, hf]
    · simp [q, hf, hg, ht']
  have hbij : Function.Bijective q := by
    constructor
    · intro x y h
      have h' := congrArg e h
      rw [hq, hq] at h'
      have hc : x.2 = y.2 := (Prod.mk.inj h').2
      apply Prod.ext
      · have ha := congrArg Prod.fst h'
        change x.1 + (e (t x.2)).1 = y.1 + (e (t y.2)).1 at ha
        rw [hc] at ha
        exact add_right_cancel ha
      · exact hc
    · intro b
      refine ⟨((e b).1 - (e (t (e b).2)).1, (e b).2), e.injective ?_⟩
      rw [hq]
      simp
  let qe := LinearEquiv.ofBijective q hbij
  let b := ((a.prod c).reindex finSumFinEquiv).map qe
  let src := (topBasis r a).tensorProduct (topBasis s c)
  let dst := topBasis (r + s) b
  let idx : Unit × Unit ≃ Unit :=
    { toFun := fun _ ↦ ()
      invFun := fun _ ↦ ((), ())
      left_inv := by rintro ⟨⟨⟩, ⟨⟩⟩; rfl
      right_inv := by rintro ⟨⟩; rfl }
  have heq : d = (src.equiv dst idx).toLinearMap := by
    apply src.ext
    rintro ⟨i, j⟩
    rw [LinearEquiv.coe_toLinearMap, Module.Basis.equiv_apply]
    simp only [src, Module.Basis.tensorProduct_apply, topBasis_apply, hd, dst]
    congr 1
    funext k
    refine Fin.addCases ?_ ?_ k
    · intro i
      simp [b, Module.Basis.map_apply, Module.Basis.reindex_apply,
        Module.Basis.prod_apply, qe, q]
    · intro j
      simp [b, Module.Basis.map_apply, Module.Basis.reindex_apply,
        Module.Basis.prod_apply, qe, q, t]
  rw [heq]
  exact (src.equiv dst idx).bijective

set_option backward.isDefEq.respectTransparency false in
/-- The wedge formula makes given linear maps bijective on common free charts. -/
theorem determinant_split_linear_maps_locally_bijective {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₃.IsFiniteLocallyFreeOfRank r₃]
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g)
    (l : ∀ (W : X.Opens), W ≤ U → S.X₃.val.obj (op W) → S.X₂.val.obj (op W))
    (hl : ∀ W hW b, S.g.val.app (op W) (l W hW b) = b)
    (d : ∀ (W : X.Opens), W ≤ U →
      (exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃).val.obj (op W)
        →ₗ[X.presheaf.obj (op W)] (exteriorPower S.X₂ r₂).val.obj (op W))
    (hd : ∀ W hW (a : Fin r₁ → S.X₁.val.obj (op W))
        (b : Fin r₃ → S.X₃.val.obj (op W)),
        d W hW (tmulSection (wedge (M := S.X₁) (r := r₁) (U := W) a)
          (wedge (M := S.X₃) (r := r₃) (U := W) b)) =
        wedge (M := S.X₂) (r := r₂) (U := W)
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op W) (a j))
            (fun j ↦ l W hW (b j)) (Fin.cast hr i))) :
    ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∀ (W : X.Opens) (hW : W ≤ V), Function.Bijective (d W (hW.trans hVU)) := by
  intro x hx
  subst r₂
  obtain ⟨V, hVU, hxV, hV⟩ := determinant_split_chart_comparison S r₁ r₃ U e hf hg x hx
  refine ⟨V, hVU, hxV, ?_⟩
  intro W hW
  obtain ⟨a, c, eW, hfW, hgW, hqB, hqT⟩ := hV W hW
  let qB := (((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app
    ((S.X₂.val.exteriorPower (R := X.presheaf) (r₁ + r₃)))).app (op W)).hom
  let qA := (((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app (S.X₁.val.exteriorPower (R := X.presheaf) r₁)).app (op W)).hom
  let qC := (((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app (S.X₃.val.exteriorPower (R := X.presheaf) r₃)).app (op W)).hom
  let qT := (tensorSectionsMap (exteriorPower S.X₁ r₁) (exteriorPower S.X₃ r₃) W).comp
    (TensorProduct.map (R := X.presheaf.obj (op W))
      (R₂ := X.presheaf.obj (op W)) (σ₁₂ := RingHom.id _) qA qC)
  let b := LinearEquiv.ofBijective qB hqB
  let d' := b.symm.toLinearMap.comp ((d W (hW.trans hVU)).comp qT)
  have hd' : ∀ z t,
      d' (_root_.exteriorPower.ιMulti (X.presheaf.obj (op W)) r₁ z ⊗ₜ[
        X.presheaf.obj (op W)] _root_.exteriorPower.ιMulti (X.presheaf.obj (op W)) r₃ t) =
      _root_.exteriorPower.ιMulti (X.presheaf.obj (op W)) (r₁ + r₃)
        (Fin.append (fun i ↦ S.f.val.app (op W) (z i))
          (fun j ↦ l W (hW.trans hVU) (t j))) := by
    intro z t
    apply b.injective
    change b (b.symm (d W (hW.trans hVU)
      (qT (_root_.exteriorPower.ιMulti (X.presheaf.obj (op W)) r₁ z ⊗ₜ[
        X.presheaf.obj (op W)] _root_.exteriorPower.ιMulti (X.presheaf.obj (op W)) r₃ t)))) = _
    rw [LinearEquiv.apply_symm_apply]
    change d W (hW.trans hVU)
      (qT (_root_.exteriorPower.ιMulti (X.presheaf.obj (op W)) r₁ z ⊗ₜ[
        X.presheaf.obj (op W)] _root_.exteriorPower.ιMulti (X.presheaf.obj (op W)) r₃ t)) = _
    simp only [qT, LinearMap.comp_apply, TensorProduct.map_tmul, tensorSectionsMap_tmul]
    change d W (hW.trans hVU)
      (tmulSection (wedge (M := S.X₁) (r := r₁) (U := W) z)
        (wedge (M := S.X₃) (r := r₃) (U := W) t)) =
      wedge (M := S.X₂) (r := (r₁ + r₃)) (U := W)
        (Fin.append (fun i ↦ S.f.val.app (op W) (z i))
          (fun j ↦ l W (hW.trans hVU) (t j)))
    simpa only [Fin.cast_refl, id_eq] using hd W (hW.trans hVU) z t
  have hb := split_wedge_bijective r₁ r₃ a c eW
    (S.f.val.app (op W)).hom (S.g.val.app (op W)).hom hfW hgW
    (l W (hW.trans hVU)) (hl W (hW.trans hVU)) d' hd'
  have hcomp : Function.Bijective ((d W (hW.trans hVU)).comp qT) := by
    have heq : ⇑((d W (hW.trans hVU)).comp qT) = b ∘ d' := by
      funext z
      change (d W (hW.trans hVU)) (qT z) =
        b (b.symm ((d W (hW.trans hVU)) (qT z)))
      exact (b.apply_symm_apply _).symm
    rw [heq]
    exact b.bijective.comp hb
  exact ⟨fun z t h ↦ by
      obtain ⟨z', rfl⟩ := hqT.2 z
      obtain ⟨t', rfl⟩ := hqT.2 t
      exact congrArg qT (hcomp.1 h),
    fun z ↦ by
      obtain ⟨t, ht⟩ := hcomp.2 z
      exact ⟨qT t, ht⟩⟩

end AlgebraicGeometry.Scheme.Modules
