/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentOpenMapTensorExtension
import WeilConjectures.AlgebraicGeometry.IdealPowerTensorImageLift
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # HOM ideal-power comparison over an open complement

Source: Stacks Project, Cohomology of Schemes, Lemma 01YB.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

-- The following affine-basis helpers follow ClosedImmersionIdealPowerImage and
-- ModulePullbackIdealPowerProductImage, without importing their unrelated geometric results.
private theorem hom_zero_of_affine {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (h : ∀ V : X.affineOpens, ∀ s : Γ(M, V.1), φ.app V.1 s = 0) :
    φ = 0 := by
  apply Modules.hom_ext
  intro W
  ext s
  change φ.app W s = 0
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun i : {V : X.affineOpens // V.1 ≤ W} ↦ i.1.1) W
    (fun i ↦ homOfLE i.2) ?_ _ _ ?_
  · intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
  · intro i
    rw [← Modules.Hom.app_presheaf_map, map_zero]
    exact h i.1 _

/-- Factor an inclusion through a monomorphism by vanishing of its cokernel projection.
Source: Stacks Project, proof of Lemma 01YP
(blueprint: lem-weil-pbc-closed-immersion-ideal-power-image). -/
private theorem subobject_le_of_affine_range {X : Scheme.{u}} {M N P : X.Modules}
    (i : M ⟶ P) (j : N ⟶ P) [Mono i] [Mono j]
    (h : ∀ V : X.affineOpens, Set.range (i.app V.1) ⊆ Set.range (j.app V.1)) :
    Subobject.mk i ≤ Subobject.mk j := by
  have hz : i ≫ cokernel.π j = 0 := by
    apply hom_zero_of_affine
    intro V s
    obtain ⟨t, ht⟩ := h V ⟨s, rfl⟩
    change (cokernel.π j).app V.1 (i.app V.1 s) = 0
    rw [← ht]
    exact congrArg (fun q ↦ q.app V.1 t) (cokernel.condition j)
  let k : M ⟶ Abelian.image j := kernel.lift (cokernel.π j) i hz
  let l : M ⟶ N := k ≫ inv (Abelian.factorThruImage j)
  apply Subobject.mk_le_mk_of_comm l
  change k ≫ inv (Abelian.factorThruImage j) ≫ j = i
  calc
    k ≫ inv (Abelian.factorThruImage j) ≫ j =
        k ≫ inv (Abelian.factorThruImage j) ≫
          Abelian.factorThruImage j ≫ Abelian.image.ι j :=
      congrArg (fun q ↦ k ≫ inv (Abelian.factorThruImage j) ≫ q)
        (Abelian.image.fac j).symm
    _ = k ≫ Abelian.image.ι j := by rw [IsIso.inv_hom_id_assoc]
    _ = i := kernel.lift_ι _ _ hz

private theorem power_mono {X : Scheme.{u}} (J : X.IdealSheafData) (n : ℕ) :
    Mono (Scheme.idealSheafPower J.toModulesι n).2 := by
  induction n using Nat.twoStepInduction with
  | zero => change Mono (𝟙 _); infer_instance
  | one => change Mono J.toModulesι; infer_instance
  | more n ih₁ ih₂ =>
    change Mono (Scheme.idealModuleProductι J.toModulesι _ ≫ _)
    have : Mono (Scheme.idealModuleProductι J.toModulesι
        (Scheme.idealSheafPower J.toModulesι (n + 1)).1) := by
      dsimp [Scheme.idealModuleProductι]
      infer_instance
    exact mono_comp _ _

/-- Recursive powers and ideal-data powers agree as subobjects of the structure sheaf.
The affine section ranges agree, including at zero; the affine basis detects equality. -/
private theorem power_subobject_eq {X : Scheme.{u}} (J : X.IdealSheafData) (n : ℕ) :
    let j := (Scheme.idealSheafPower J.toModulesι n).2
    let k := (J ^ n).toModulesι
    ∃ e : (Scheme.idealSheafPower J.toModulesι n).1 ≅ (J ^ n).toModules,
      e.hom ≫ k = j := by
  classical
  dsimp only
  have := power_mono J n
  have hr (U : X.affineOpens) :
      Set.range ((Scheme.idealSheafPower J.toModulesι n).2.app U.1) =
        Set.range ((J ^ n).toModulesι.app U.1) := by
    rw [Scheme.IdealSheafData.range_toModulesι_app]
    cases n with
    | zero => simp [Scheme.idealSheafPower]
    | succ n =>
      have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
        @SheafOfModules.isQuasicoherent_unit _ _ _ _ X.ringCatSheaf _ _ _ _
      exact ((Scheme.Modules.ideal_times_quasiCoherent_affine_sections J
        (SheafOfModules.unit X.ringCatSheaf)).2.2.2.1 U).2.2.2 (n + 1) (by omega)
  have h : Subobject.mk (Scheme.idealSheafPower J.toModulesι n).2 =
      Subobject.mk (J ^ n).toModulesι :=
    le_antisymm
      (subobject_le_of_affine_range _ _ (fun U ↦ (hr U).subset))
      (subobject_le_of_affine_range _ _ (fun U ↦ (hr U).symm.subset))
  exact ⟨Subobject.isoOfMkEqMk _ _ h, by simp⟩

open MonoidalCategory in
set_option backward.isDefEq.respectTransparency false in
/-- An isomorphism over the structure sheaf induces an isomorphism of product inclusions. -/
private theorem product_iso {X : Scheme.{u}} {P Q : X.Modules}
    (ι : P ⟶ SheafOfModules.unit X.ringCatSheaf)
    (κ : Q ⟶ SheafOfModules.unit X.ringCatSheaf)
    (e : P ≅ Q) (he : e.hom ≫ κ = ι) (F : X.Modules) :
    ∃ a : Scheme.idealModuleProduct ι F ≅ Scheme.idealModuleProduct κ F,
      a.hom ≫ Scheme.idealModuleProductι κ F = Scheme.idealModuleProductι ι F := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  have hi : Mono (Scheme.idealModuleProductι ι F) := by
    dsimp [Scheme.idealModuleProductι]; infer_instance
  have hk : Mono (Scheme.idealModuleProductι κ F) := by
    dsimp [Scheme.idealModuleProductι]; infer_instance
  have h : Subobject.mk (Scheme.idealModuleProductι ι F) =
      Subobject.mk (Scheme.idealModuleProductι κ F) := by
    change imageSubobject (ι ▷ F ≫ (λ_ F).hom) =
      imageSubobject (κ ▷ F ≫ (λ_ F).hom)
    have hm : ι ▷ F ≫ (λ_ F).hom = (e.hom ▷ F) ≫ (κ ▷ F ≫ (λ_ F).hom) := by
      rw [← he, comp_whiskerRight, Category.assoc]
    calc
      _ = imageSubobject ((e.hom ▷ F) ≫ (κ ▷ F ≫ (λ_ F).hom)) :=
        congrArg (fun m : P ⊗ F ⟶ F ↦ imageSubobject m) hm
      _ = _ := imageSubobject_iso_comp (e.hom ▷ F) _
  exact ⟨Subobject.isoOfMkEqMk _ _ h, by simp⟩

set_option backward.isDefEq.respectTransparency false in
/-- A morphism on the complement extends after multiplying its coherent source by an
ideal power. This is only the surjectivity assertion, with the complement fixed in advance.

Proof: X is Noetherian, so it is quasi-separated, U is quasi-compact, and I is of finite
type. First treat G = O_X and write s for the image of 1. The image of the map defined
by s on U is quasi-coherent of finite type. Extend it to a finite-type quasi-coherent
submodule E of F; E is coherent and s belongs to E(U). The increasing submodules E_N
annihilated by I^N stabilize at H = E_a, with I^a H = 0. Artin--Rees gives c such that
I^b E meets H in a submodule of I^(b-c) H for b >= c. Taking b = a+c gives
E' = I^b E with E' intersect H = 0 and E'|U = E|U. Every ideal-power annihilator
of E' is zero, since E_N is contained in H for every N. The sections-over-a-quasi-
compact-open comparison identifies the colimit of Hom(I^N, E'/E'_N) with E'(U).
Here E'_N = 0, so a finite-stage representative of s gives I^N -> E' -> E -> F,
with value s on 1 over U. For general coherent G, its internal
Hom into F is quasi-coherent because G is finitely presented. Apply the structure-sheaf
case to this internal Hom and use tensor--Hom adjunction to obtain a map from I^n ⊗ G.
The multiplication map to G has image I^n G, and its kernel K is killed by I^n,
as follows on affines: put J = I^n and write z = sum b_i ⊗ m_i in the kernel,
so sum b_i m_i = 0. For a in J, tensor balancing gives
 a z = sum a ⊗ (b_i m_i) = a ⊗ 0 = 0.
Artin--Rees gives an m for which I^m(I^n ⊗ G) meets K in
zero. Multiplication identifies that submodule with I^(n+m)G; restricting the lifted
map to it gives the required extension. On U multiplication by 1 shows that its
restriction is the original map. Empty complements and zero modules obey the same
argument; the exponent may be zero.
Source: Stacks Project, Cohomology of Schemes, Lemma 01YB, surjectivity paragraphs.
(blueprint: lem-weil-pbc-coherent-hom-ideal-power-extension). -/
theorem coherent_hom_ideal_power_extension {X : Scheme.{u}} [IsLocallyNoetherian X]
    [CompactSpace X] (I : X.IdealSheafData) (F G : X.Modules) [F.IsQuasicoherent]
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) (U : X.Opens)
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map I.toModulesι).hom) :
    ∀ ψ : (SheafOfModules.overFunctor X.ringCatSheaf U).obj G ⟶
        (SheafOfModules.overFunctor X.ringCatSheaf U).obj F,
      ∃ (n : ℕ) (χ : idealModuleProduct (idealSheafPower I.toModulesι n).2 G ⟶ F),
        (SheafOfModules.overFunctor X.ringCatSheaf U).map
            (idealModuleProductι (idealSheafPower I.toModulesι n).2 G) ≫ ψ =
          (SheafOfModules.overFunctor X.ringCatSheaf U).map χ := by
  classical
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let : IsNoetherian X := ⟨⟩
  intro ψ
  have hI : (I.support : Set X) = (U : Set X)ᶜ := by
    have hs := (quasi_coherent_ideal_zero_set_affine X I).2.2.2.2
      I.subscheme I.subschemeι I.ker_subschemeι
    rw [IdealSheafData.range_subschemeι] at hs
    ext x
    change x ∈ (I.support : Set X) ↔ x ∉ U
    simpa only [Set.mem_ofPred_eq, ← hU x] using (Set.ext_iff.mp hs x)
  let H := SheafOfModules.overFunctor X.ringCatSheaf U
  let E := Modules.overEquiv (X := X) U
  let R := Modules.restrictFunctor U.ι
  let e := Modules.overFunctorEquiv (X := X) U
  let φ : R.obj G ⟶ R.obj F := e.inv.app G ≫ E.functor.map ψ ≫ e.hom.app F
  obtain ⟨n, β, hβ⟩ := Modules.coherent_open_map_tensor_extension I G F hG U hI φ
  obtain ⟨m, a, ha⟩ := Modules.ideal_power_tensor_image_lift I G hG n
  obtain ⟨p, hp⟩ := power_subobject_eq I (n + m)
  obtain ⟨q, hq⟩ := product_iso _ _ p hp G
  refine ⟨n + m, q.hom ≫ a ≫ β, ?_⟩
  have hr : R.map (q.hom ≫ a ≫ β) =
      R.map (idealModuleProductι (idealSheafPower I.toModulesι (n + m)).2 G) ≫ φ := by
    calc
      _ = R.map q.hom ≫ R.map a ≫ R.map β := by simp only [Functor.map_comp]
      _ = R.map q.hom ≫ R.map a ≫
          R.map (MonoidalCategoryStruct.whiskerRight (I ^ n).toModulesι G ≫
            (MonoidalCategoryStruct.leftUnitor G).hom) ≫ φ := by rw [hβ]
      _ = R.map (q.hom ≫ (a ≫
          (MonoidalCategoryStruct.whiskerRight (I ^ n).toModulesι G ≫
            (MonoidalCategoryStruct.leftUnitor G).hom))) ≫ φ := by
        simp only [Functor.map_comp, Category.assoc]
      _ = _ := by rw [ha, hq]
  apply E.functor.map_injective
  apply (cancel_mono (e.hom.app F)).mp
  have hj := e.hom.naturality
    (idealModuleProductι (idealSheafPower I.toModulesι (n + m)).2 G)
  have hχ := e.hom.naturality (q.hom ≫ a ≫ β)
  change E.functor.map (H.map _ ≫ ψ) ≫ e.hom.app F =
    E.functor.map (H.map _) ≫ e.hom.app F
  dsimp only [Functor.comp_map] at hj hχ
  rw [Functor.map_comp, Category.assoc, hχ]
  rw [hr]
  dsimp only [φ]
  simp only [← Category.assoc]
  rw [← hj]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rfl

end AlgebraicGeometry.Scheme
