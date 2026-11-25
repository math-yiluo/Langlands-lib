/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage

public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
import WeilConjectures.AlgebraicGeometry.Picard.Affine.PicardAffineTargetNormalization
import WeilConjectures.AlgebraicGeometry.Picard.Residue.PicardResidueHomologySourceResidueComparison
import WeilConjectures.AlgebraicGeometry.PicardDescendedFibreCoefficientTrivial
import WeilConjectures.AlgebraicGeometry.Affine.AffineBettiModelResidueMinimality
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Joint degree-one comparison for a fixed minimal source model

## References

* Stacks Project, Tag 0BF2, the displayed chain maps and their residue comparison
* Stacks Project, Tag 0BF2, the finite free degree-one calculation
* Stacks Project, Tag 0BF2, displayed chain maps
* Tags 08CR and 0B91
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

/-- Joint coordinates of finitely many maps into finite free modules. -/
private theorem joint_free_coordinates
    (A : Type v) [CommRing A] (m n : ℕ) (r : Fin n → ℕ)
    (d : A → (Fin m → A))
    (t : ∀ i, (Fin m → A) →ₗ[A] (ULift.{v} (Fin (r i)) → A))
    (ht : ∀ i a, t i (d a) = 0) :
    ∃ (q : ℕ) (b : (Fin m → A) →ₗ[A] (Fin q → A)),
      (∀ a, b (d a) = 0) ∧
      ∃ π : ∀ i, (Fin q → A) →ₗ[A] (ULift.{v} (Fin (r i)) → A),
        ∀ i, (π i).comp b = t i := by
  classical
  let J := Σ i : Fin n, ULift.{v} (Fin (r i))
  let q := Fintype.card J
  let e : (J → A) ≃ₗ[A] (Fin q → A) :=
    LinearEquiv.piCongrLeft A (fun _ ↦ A) (Fintype.equivFin J)
  let bJ : (Fin m → A) →ₗ[A] (J → A) :=
    LinearMap.pi fun j ↦ (LinearMap.proj j.2).comp (t j.1)
  let b := e.toLinearMap.comp bJ
  let π (i : Fin n) : (Fin q → A) →ₗ[A] (ULift.{v} (Fin (r i)) → A) :=
    (LinearMap.pi fun j ↦ LinearMap.proj (⟨i, j⟩ : J)).comp e.symm.toLinearMap
  refine ⟨q, b, ?_, π, ?_⟩
  · intro a
    change e (bJ _) = 0
    rw [← e.map_zero]
    congr 1
    ext j
    change t j.1 _ j.2 = 0
    rw [ht _ a]
    rfl
  · intro i
    apply LinearMap.ext
    intro x
    funext j
    change (e.symm (e (bJ x))) ⟨i, j⟩ = _
    rw [LinearEquiv.symm_apply_apply]
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The tensor and quotient comparison contains several dependent module instances.
/-- The residue square yields joint finite free coordinates. -/
private theorem residue_joint_coordinates
    (W : Scheme.{v}) (U : W.Opens) (p : Ideal Γ(W, U)) [p.IsPrime]
    {n : ℕ} (m : ℕ)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (C : Fin n → CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hC : ∀ i, IsStrictlyPerfect W U (C i))
    (hCzero : ∀ i, (C i).d 0 1 = 0)
    (e0 : (K.X 0).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] Γ(W, U))
    (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U)))
    (B : Type v) (D : Fin n → Type v)
    [AddCommGroup B] [∀ i, AddCommGroup (D i)]
    (g : ∀ i, B → D i)
    (eK : affineResidueCycleHomology W U p K ≃+ B)
    (eC : ∀ i, affineResidueCycleHomology W U p (C i) ≃+ D i)
    (φ : ∀ i, K ⟶ C i)
    (hmaps : ∀ i z, eC i (affineResidueCycleHomologyMap (φ i) z) = g i (eK z))
    (hreszero : ∀ j : ℤ, affineResidueDifferential W U p K j (j + 1) = 0) :
    ∃ (q : ℕ) (b : (Fin m → Γ(W, U)) →ₗ[Γ(W, U)] (Fin q → Γ(W, U))),
      (∀ a : Γ(W, U),
        b (e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) (e0.symm a))) = 0) ∧
      ∃ (α : (p.ResidueField ⊗[Γ(W, U)] (Fin m → Γ(W, U))) ≃+ B)
        (β : (p.ResidueField ⊗[Γ(W, U)] (Fin q → Γ(W, U))) →+ (∀ i, D i)),
        ∀ z, β (b.baseChange p.ResidueField z) = fun i ↦ g i (α z) := by
  classical
  let qK := affineResidueCycleClass W U p K
  let src := eK.toAddMonoidHom.comp qK
  have hsurj : Function.Surjective src :=
    eK.surjective.comp (affineResidueCycleClass_surjective_kernel W U p K).1
  have hinj : Function.Injective src := by
    apply (injective_iff_map_eq_zero src).mpr
    intro x hx
    have hx0 : qK x = 0 := eK.injective (hx.trans eK.map_zero.symm)
    obtain ⟨y, hy⟩ := (affineResidueCycleClass_surjective_kernel W U p K).2 x |>.mp hx0
    apply Subtype.ext
    change x.val = 0
    rw [show affineResidueDifferential W U p K 0 1 = 0 from hreszero 0] at hy
    exact hy.symm
  let toCycles : affineResidueTerm W U p K 1 ≃+ affineResidueCycles W U p K :=
    { toFun := fun x ↦ ⟨x, by
        change affineResidueDifferential W U p K 1 2 x = 0
        rw [show affineResidueDifferential W U p K 1 2 = 0 from hreszero 1]
        rfl⟩
      invFun := fun x ↦ x.val
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  let coords : (p.ResidueField ⊗[Γ(W, U)] (Fin m → Γ(W, U))) ≃+
      affineResidueTerm W U p K 1 := by
    set_option backward.isDefEq.respectTransparency false in
      exact (e1.symm.baseChange Γ(W, U) p.ResidueField).toAddEquiv
  let α := coords.trans (toCycles.trans (AddEquiv.ofBijective src ⟨hinj, hsurj⟩))
  let Z := fun i ↦ affineResidueCycles W U p (C i)
  let βcycles := fun i ↦ (eC i).toAddMonoidHom.comp
    (affineResidueCycleClass W U p (C i))
  let bi := fun i ↦ (((φ i).f 1).val.app (.op (Over.mk (𝟙 U)))).hom.comp
    e1.symm.toLinearMap
  let t := LinearMap.pi bi
  have hc (i) (z : p.ResidueField ⊗[Γ(W, U)] (Fin m → Γ(W, U))) :
      ∃ hz : (bi i).baseChange p.ResidueField z ∈ Z i,
        βcycles i ⟨(bi i).baseChange p.ResidueField z, hz⟩ =
          g i (α z) := by
    let x := toCycles (coords z)
    let y := affineResidueCycleMap (φ i) x
    have hval : (bi i).baseChange p.ResidueField z = y.val :=
      LinearMap.congr_fun (LinearMap.baseChange_comp e1.symm.toLinearMap
        (((φ i).f 1).val.app (.op (Over.mk (𝟙 U)))).hom) z
    have hz : (bi i).baseChange p.ResidueField z ∈ Z i := by
      rw [hval]
      exact y.property
    refine ⟨hz, ?_⟩
    have hcycle : (⟨(bi i).baseChange p.ResidueField z, hz⟩ : Z i) = y :=
      Subtype.ext hval
    rw [hcycle]
    exact (congrArg (eC i)
      (affineResidueCycleHomologyMap_class (W := W) (U := U) (p := p) (φ i) x)).symm.trans
        (hmaps i (qK x))
  obtain ⟨T, hT⟩ : ∃ T : ∀ i, Submodule p.ResidueField (affineResidueTerm W U p (C i) 1),
      ∀ i, IsCompl (Z i) (T i) :=
    Classical.axiom_of_choice (fun i ↦ (Z i).exists_isCompl)
  let pr := fun i ↦ (LinearMap.proj i :
    (∀ i, ((C i).X 1).val.obj (.op (Over.mk (𝟙 U)))) →ₗ[Γ(W, U)]
      ((C i).X 1).val.obj (.op (Over.mk (𝟙 U))))
  let γ := AddMonoidHom.pi fun i ↦ (βcycles i).comp
    (((Z i).projectionOnto (T i) (hT i)).toAddMonoidHom.comp
      ((pr i).baseChange p.ResidueField).toAddMonoidHom)
  have hγ (z) : γ (t.baseChange p.ResidueField z) = fun i ↦
      g i (α z) := by
    funext i
    obtain ⟨hz, heq⟩ := hc i z
    have hcoord : (pr i).baseChange p.ResidueField (t.baseChange p.ResidueField z) =
        (bi i).baseChange p.ResidueField z := by
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      rfl
    have hproj : (Z i).projectionOnto (T i) (hT i)
        ((pr i).baseChange p.ResidueField (t.baseChange p.ResidueField z)) =
          ⟨(bi i).baseChange p.ResidueField z, hz⟩ := by
      rw [hcoord]
      exact Submodule.projectionOnto_apply_of_mem_left (hT i) hz
    exact (congrArg (βcycles i) hproj).trans heq
  have ht (a) : t (e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) (e0.symm a))) = 0 := by
    ext i
    have hc : K.d 0 1 ≫ (φ i).f 1 = 0 := by
      rw [← (φ i).comm 0 1, hCzero i, comp_zero]
    have he := congrArg
      (fun q ↦ (q.val.app (.op (Over.mk (𝟙 U)))) (e0.symm a)) hc
    have hz : (0 : K.X 0 ⟶ (C i).X 1).val = 0 := rfl
    simpa [t, bi, SheafOfModules.comp_val, PresheafOfModules.comp_app, hz] using he
  choose r ι π hιπ using fun i ↦ (hC i).2 (1 : ℤ)
  let A := Γ(W, U)
  let V := Opposite.op (Over.mk (𝟙 U))
  let E := fun i ↦ SheafOfModules.freeSectionsLinearEquiv
    (R := (moduleRings W.toRingedSpace).over U) (ULift.{v} (Fin (r i))) V
  let inc : ∀ i, ((C i).X 1).val.obj V →ₗ[A] (ULift.{v} (Fin (r i)) → A) :=
    fun i ↦ (E i).toLinearMap.comp ((ι i).val.app V).hom
  let ret : ∀ i, (ULift.{v} (Fin (r i)) → A) →ₗ[A] ((C i).X 1).val.obj V :=
    fun i ↦ ((π i).val.app V).hom.comp (E i).symm.toLinearMap
  have hret (i) : (ret i).comp (inc i) = LinearMap.id := by
    ext x
    change ((π i).val.app V).hom ((E i).symm ((E i) (((ι i).val.app V).hom x))) = x
    rw [LinearEquiv.symm_apply_apply]
    change ((ι i ≫ π i).val.app V) x = x
    rw [hιπ i]
    rfl
  let ti := fun i ↦ (LinearMap.proj i).comp t
  let d := fun a ↦ e1 ((K.d 0 1).val.app V (e0.symm a))
  have hv (i) (a) : ((inc i).comp (ti i)) (d a) = 0 := by
    change inc i ((t (d a)) i) = 0
    rw [ht a]
    exact (inc i).map_zero
  obtain ⟨q, b, hb, proj, hproj⟩ := joint_free_coordinates A m n r d
    (fun i ↦ (inc i).comp (ti i)) hv
  let ρ := LinearMap.pi fun i ↦ (ret i).comp (proj i)
  have hρ : ρ.comp b = t := by
    apply LinearMap.ext
    intro x
    funext i
    have hi : ((ret i).comp (proj i)).comp b = ti i := by
      rw [LinearMap.comp_assoc, hproj, ← LinearMap.comp_assoc, hret, LinearMap.id_comp]
    exact LinearMap.congr_fun hi x
  let β := γ.comp (ρ.baseChange p.ResidueField).toAddMonoidHom
  refine ⟨q, b, hb, α, β, ?_⟩
  intro z
  change γ (ρ.baseChange p.ResidueField (b.baseChange p.ResidueField z)) = _
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hρ]
  exact hγ z

attribute [local irreducible] structureSheafAb structureSheafCohomologyPullback
  derivedFiberBetti

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedVariables false in
/-- On an affine with trivial target bundles, construct the joint degree-one map
out of a supplied minimal source complex and identify its residue map geometrically.
-/
theorem picard_h1_fixed_model_comparison
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (hOi : ∀ i, ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd (fi i) g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (hLs : ∃ (N : (Spec (S.residueField s)).Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N))
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (htrivial : ∀ i, Nonempty
      ((Modules.tensorPullback (pullback.fst (fi i) (U.ι ≫ k))).obj
        ((Modules.tensorPullback (ui i)).obj L) ≅
        SheafOfModules.unit (pullback (fi i) (U.ι ≫ k)).ringCatSheaf))
    (m : ℕ) (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hnegative : ∀ j : ℤ, j < 0 → IsZero (K.X j))
    (hrank : ∀ j : ℤ, Nonempty (K.X j ≅ SheafOfModules.free
      (R := (moduleRings W.toRingedSpace).over U)
      (ULift.{v} (Fin (derivedFiberBetti W ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) j w)))))
    (e0 : (K.X 0).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] Γ(W, U))
    (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U)))
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
        DerivedCategory.Q.obj K)) :
    ∃ (q : ℕ) (b : (Fin m → Γ(W, U)) →ₗ[Γ(W, U)] (Fin q → Γ(W, U))),
      (∀ a : Γ(W, U),
        b (e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) (e0.symm a))) = 0) ∧
          let p := RingHom.ker (W.evaluation U w hwU).hom
          letI : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
            ∃ (α : (p.ResidueField ⊗[Γ(W, U)] (Fin m → Γ(W, U))) ≃+
                Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
              (β : (p.ResidueField ⊗[Γ(W, U)] (Fin q → Γ(W, U))) →+
                (∀ i, Sheaf.H
                  (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1)),
              ∀ z, β ((b.baseChange p.ResidueField) z) = fun i ↦
                structureSheafCohomologyPullback
                  (((Over.pullback (S.fromSpecResidueField s)).map
                    (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                      (ui i) (hui i))).left) 1 (α z) := by
  set_option backward.isDefEq.respectTransparency true in
    classical
    -- Share the types of the geometric data before eliminating the existentials.
    have htargets := Classical.axiomOfChoice fun i ↦
      picard_affine_target_normalization (fi i) (hOi i)
        ((Modules.tensorPullback (ui i)).obj L) W k U hU (htrivial i)
    obtain ⟨C, hC⟩ := htargets
    let p := RingHom.ker (W.evaluation U w hwU).hom
    let : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
    let τ := Classical.choice (picard_descended_fibre_coefficient_trivial f hO L s hLs)
    have hcompare := picard_residue_homology_chosen_geometric_maps
      f Xi fi ui hui L W k w s hw τ U hwU hU p rfl K hK hE.some C
      (fun i ↦ (hC i).1) (fun i ↦ (hC i).2.2.2.some)
    obtain ⟨φ, e, ei, hmaps⟩ := hcompare
    have hreszero := affine_betti_model_residue_minimality W _ w U hwU hU K hK.1 hrank hE
    let B := Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1
    let D := fun i ↦ Sheaf.H
      (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1
    let g : ∀ i, B → D i := fun i ↦ structureSheafCohomologyPullback
      (((Over.pullback (S.fromSpecResidueField s)).map
        (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
          (ui i) (hui i))).left) 1
    exact residue_joint_coordinates W U p m K C (fun i ↦ (hC i).1)
      (fun i ↦ (hC i).2.2.1) e0 e1 B D g _ _ φ (fun i ↦ (hmaps i).2.2) hreszero

end AlgebraicGeometry.Scheme
