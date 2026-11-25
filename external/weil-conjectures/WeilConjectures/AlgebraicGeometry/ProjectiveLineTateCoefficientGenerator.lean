/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Kummer
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.ProjectiveLineConstantCoefficientGenerator
import WeilConjectures.AlgebraicGeometry.ProjectiveLineGenusZero
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClassGenerator
import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.Topology.RingedSpaceModuleCohomology

/-! # Finite Tate coefficients from the normalized projective-line Kummer class

Source: the coefficient extension in blueprint lemma-cohomology-projective-line-trace.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
attribute [local irreducible] Scheme.finiteEtaleTateLine ordinaryFiniteRootMap
  Scheme.lineHomEquiv Scheme.rootsOfUnitySheaf ProjectiveSpace.twist
  AlgebraicGeometry.ProjectiveSpace

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem kummer_transferred_generator
    {C D : Type*} [Category C] [Category D]
    (K : D ⥤ C) (H : C ⥤ AddCommGrpCat.{u + 1})
    {Z W : C} {B B' : D} (e : Z ≅ K.obj B) (τ : W ≅ K.obj B')
    (δ : H.obj Z)
    (h : Function.Surjective (fun φ : B ⟶ B' ↦
      (H.map (K.map φ)).hom ((H.map e.hom).hom δ))) :
    Function.Surjective (fun f : Z ⟶ W ↦ (H.map f).hom δ) := by
  intro y
  obtain ⟨φ, hφ⟩ := h ((H.map τ.hom).hom y)
  refine ⟨e.hom ≫ K.map φ ≫ τ.inv, ?_⟩
  simp only [Functor.map_comp, AddCommGrpCat.comp_apply]
  change (H.map τ.inv).hom ((H.map (K.map φ)).hom ((H.map e.hom).hom δ)) = y
  change (H.map (K.map φ)).hom ((H.map e.hom).hom δ) = _ at hφ
  rw [hφ]
  change ((H.map τ.hom ≫ H.map τ.inv).hom y) = y
  rw [← H.map_comp, τ.hom_inv_id, H.map_id]
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem kummer_scalar_generator_from_factor
    {C D : Type*} [Category C] [Preadditive C] [Category D]
    (R : Type*) [CommRing R] [Linear R C]
    (U : C ⥤ D) (H : D ⥤ AddCommGrpCat.{u + 1})
    (L : C) {Z : D} (r : Z ⟶ U.obj L) (δ : H.obj Z)
    (hf : Function.Surjective (fun a : R ↦ r ≫ U.map (a • 𝟙 L)))
    (hh : Function.Surjective (fun f : Z ⟶ U.obj L ↦ (H.map f).hom δ)) :
    Function.Surjective (fun a : R ↦ (H.map (U.map (a • 𝟙 L))).hom
      ((H.map r).hom δ)) := by
  simpa only [Function.comp_def, Functor.map_comp, AddCommGrpCat.comp_apply]
    using hh.comp hf

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem kummer_scalar_generator_bijective_from_factor
    {C D : Type*} [Category C] [Preadditive C] [Category D]
    (R : Type*) [CommRing R] [Finite R] [Linear R C]
    (U : C ⥤ D) (H : D ⥤ AddCommGrpCat.{u + 1})
    (L : C) {Z : D} (r : Z ⟶ U.obj L) (δ : H.obj Z)
    (E : H.obj (U.obj L) ≃ R)
    (hf : Function.Surjective (fun a : R ↦ r ≫ U.map (a • 𝟙 L)))
    (hh : Function.Surjective (fun f : Z ⟶ U.obj L ↦ (H.map f).hom δ)) :
    Function.Bijective (fun a : R ↦ (H.map (U.map (a • 𝟙 L))).hom
      ((H.map r).hom δ)) := by
  have : Finite (H.obj (U.obj L)) := Finite.of_equiv R E.symm
  exact Function.Surjective.bijective_of_nat_card_le
    (kummer_scalar_generator_from_factor R U H L r δ hf hh)
    (le_of_eq (Nat.card_congr E).symm)

private theorem kummer_scheme_scalar_generator
    (N : ℕ) (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (P : Scheme.{u}) [ConnectedSpace P]
    (e : P.constantZMod N ≅ P.rootsOfUnitySheaf N)
    (σ : Scheme.finiteEtaleTateLine P N A hA ≅ ordinaryFiniteConstant A P)
    (δ : Sheaf.H (P.rootsOfUnitySheaf N) 2)
    (hη : Function.Bijective ((sheafHConstantSheafNatTrans P N 2
      (Sheaf.H.map e.inv 2 δ)).app
        ((forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).obj (ModuleCat.of A A))))
    (hLine : ∀ f : Scheme.finiteEtaleTateLine P N A hA ⟶
        Scheme.finiteEtaleTateLine P N A hA,
      Scheme.lineHomEquiv P N A hA (Scheme.finiteEtaleTateLine P N A hA) f =
        ordinaryFiniteRootMap A N hA P ≫ (moduleAbelianForget A P).map f) :
    Function.Bijective (fun a : A ↦ Sheaf.H.map
      ((moduleAbelianForget A P).map (a • 𝟙 (Scheme.finiteEtaleTateLine P N A hA))) 2
      (Sheaf.H.map (ordinaryFiniteRootMap A N hA P) 2 δ)) := by
  let F := Scheme.finiteEtaleTateLine P N A hA
  let U := moduleAbelianForget A P
  let B := (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).obj (ModuleCat.of A A)
  have hB : ∀ b : B, N • b = 0 := fun b ↦ by
    rw [nsmul_eq_mul, hA, zero_mul]
  let τ := U.mapIso σ ≪≫ forget₂SheafConstantSheafIso A P
  let E : Sheaf.H (U.obj F) 2 ≃ A :=
    ((Sheaf.functorH P.smallEtaleTopology 2).mapIso τ).addCommGroupIsoToAddEquiv.toEquiv.trans
      ((Equiv.ofBijective _ hη).symm.trans (AddCommGrpCat.zmodHomEquiv B hB))
  have hf : Function.Surjective (fun a : A ↦
      ordinaryFiniteRootMap A N hA P ≫ U.map (a • 𝟙 F)) := by
    intro f
    let g := (Scheme.lineHomEquiv P N A hA F).symm f
    obtain ⟨a, ha⟩ := exists_eq_smul_id_of_iso A σ g
    refine ⟨a, ?_⟩
    have hh := (Scheme.lineHomEquiv P N A hA F).apply_symm_apply f
    rw [hLine] at hh
    change ordinaryFiniteRootMap A N hA P ≫ U.map g = f at hh
    rwa [ha] at hh
  have hs := kummer_transferred_generator
    (constantSheaf P.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Sheaf.functorH P.smallEtaleTopology 2) e.symm τ δ hη.2
  exact kummer_scalar_generator_bijective_from_factor A U
    (Sheaf.functorH P.smallEtaleTopology 2) F (ordinaryFiniteRootMap A N hA P) δ E hf hs

private theorem kummer_root_map_apply
    (N : ℕ) (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (T : Scheme.{u}) (W : T.Etaleᵒᵖ) (z : (T.rootsOfUnitySheaf N).obj.obj W) :
    (ordinaryFiniteRootMap A N hA T).hom.app W z =
      Scheme.finiteEtaleTateOneGenerator A N T hA W 1 z := by
  unfold ordinaryFiniteRootMap ordinaryFiniteRootGenerator
    Scheme.finiteEtaleTateOneGenerator
    ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
  rfl

private theorem kummer_line_as_constant
    (N : ℕ) (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
     (hNk : (N : k) ≠ 0) :
    Nonempty (Scheme.finiteEtaleTateLine X N A hA ≅ ordinaryFiniteConstant A X) := by
  have : NeZero (N : k) := ⟨hNk⟩
  have : NeZero N := ⟨by intro hz; simp [hz] at hNk⟩
  obtain ⟨_, _, ζ, hζ, _⟩ := IsSepClosed.exists_isPrimitiveRoot.{u, u} k N
  exact ⟨Scheme.finiteEtaleLineAbIso X N A hA ≪≫
    (extendScalars A X).mapIso (X.constantZModIsoRootsOfUnitySheaf N p hζ).symm ≪≫
    extendScalarsConstantZModIso X hA⟩

private theorem kummer_lineHomEquiv_eq
    (N : ℕ) (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
      (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : Scheme.finiteEtaleTateLine X N A hA ⟶ F) :
    Scheme.lineHomEquiv X N A hA F f =
      ordinaryFiniteRootMap A N hA X ≫ (moduleAbelianForget A X).map f := by
  ext W z
  rw [Scheme.lineHomEquiv_generator]
  change f.hom.app W _ = f.hom.app W _
  exact congrArg (fun z ↦ f.hom.app W z) ((kummer_root_map_apply N A hA) X W z).symm

/-- The actual scalar-extended Kummer class generates the Tate-line H² once
its roots-of-unity class is normalized to one by an additive isomorphism.
Source: blueprint lemma-cohomology-projective-line-trace, finite coefficient extension.
(auxiliary; not a blueprint node).

Proof: choose a primitive root to identify the root sheaf with constant Z/N.
The supplied normalization makes the corresponding constant H² class a cyclic
generator. The finite constant-coefficient generator theorem identifies H² for
the underlying additive group of A. A primitive root also trivializes the Tate
line over A. Its universal property and the scalar description of endomorphisms
of a constant rank-one module identify all coefficient maps with scalar maps.
Consequently the scalar orbit of the actual class is surjective. Both its source
and target have cardinality card(A), so it is bijective, including for A=0. -/
theorem ordinaryFiniteP1KummerClass_scalar_bijective_of_normalization
    (N : ℕ) (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (k : Type u) [Field k] [IsAlgClosed k] (hNk : (N : k) ≠ 0)
    (hP : IsUnit (N : Γ(ProjectiveLine (Spec (.of k)), ⊤)))
    (hNorm : ∃ e :
      Sheaf.H ((ProjectiveLine (Spec (.of k))).rootsOfUnitySheaf N) 2 ≃+ ZMod N,
      e ((ProjectiveLine (Spec (.of k))).kummerδ₁ N hP
        (Scheme.Pic.toCohomologicalPicardGroup (ProjectiveLine (Spec (.of k)))
          (Scheme.Pic.ofIsInvertible
            (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) 1)))) = 1) :
    Function.Bijective (fun a : A ↦ Sheaf.H.map
      ((moduleAbelianForget A (ProjectiveLine (Spec (.of k)))).map
        (a • 𝟙 (Scheme.finiteEtaleTateLine (ProjectiveLine (Spec (.of k))) N A hA))) 2
      (ordinaryFiniteP1KummerClass A N hA (Spec (.of k)) hP)) := by
  let P := ProjectiveLine (Spec (.of k))
  let F := Scheme.finiteEtaleTateLine P N A hA
  let U := moduleAbelianForget A P
  have : NeZero (N : k) := ⟨hNk⟩
  have : NeZero N := ⟨by intro hz; simp [hz] at hNk⟩
  obtain ⟨hcurve, -, -, -, -⟩ :=
    ProjectiveSpace.isConnectedCurve_smooth_proper_genus_zero k
  have := hcurve
  have : ConnectedSpace P := IsConnectedCurve.connectedSpace (P ↘ Spec (.of k))
  obtain ⟨_, _, ζ, hζ, _⟩ := IsSepClosed.exists_isPrimitiveRoot.{u, u} k N
  let e := P.constantZModIsoRootsOfUnitySheaf N (P ↘ Spec (.of k)) hζ
  let δ := P.kummerδ₁ N hP (Scheme.Pic.toCohomologicalPicardGroup P
    (Scheme.Pic.ofIsInvertible (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) 1)))
  let θ := Sheaf.H.map e.inv 2 δ
  obtain ⟨eδ, heδ⟩ := hNorm
  have hθ : ∀ y : Sheaf.H (P.constantZMod N) 2, ∃ c : ℕ, y = c • θ := by
    let d := ((Sheaf.functorH P.smallEtaleTopology 2).mapIso e).addCommGroupIsoToAddEquiv.trans eδ
    have hd : d θ = 1 := by
      change eδ (Sheaf.H.map e.hom 2 (Sheaf.H.map e.inv 2 δ)) = 1
      rw [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply]
      exact heδ
    intro y
    refine ⟨(d y).val, d.injective ?_⟩
    rw [map_nsmul, hd, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  let B := (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).obj (ModuleCat.of A A)
  have hB : ∀ b : B, N • b = 0 := fun b ↦ by
    rw [nsmul_eq_mul, hA, zero_mul]
  have hη := projectiveLine_constant_coefficient_generator k N hNk θ hθ B hB
  obtain ⟨σ⟩ := (kummer_line_as_constant N A hA) k (P ↘ Spec (.of k)) hNk
  unfold ordinaryFiniteP1KummerClass
  exact (kummer_scheme_scalar_generator N A hA) P e σ δ hη
    ((kummer_lineHomEquiv_eq N A hA) P F)

end AlgebraicGeometry.Etale
