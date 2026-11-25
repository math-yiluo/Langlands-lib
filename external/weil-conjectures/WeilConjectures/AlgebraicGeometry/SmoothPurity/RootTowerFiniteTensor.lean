/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tate.TateTwistLocallyFree
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualTowerCore
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistRootTransitions
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.AlgebraicGeometry.ProEtaleReplete

/-! # Root tower projections and normalized finite tensor reduction

Source: Stacks Project, proetale.tex Tag 0990, etale-cohomology.tex Tag 03PL,
and sites-modules.tex Section 03EK and Tag 03CY. Kernel division and the normalized
inverse are the agent arguments in the node (blueprint: lem-amb-root-tower-finite-tensor).

The natural-number level `r` denotes the positive exponent `r + 1`.
All tensors are ordinary sheafified tensors. No flatness or finiteness of B is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The existing limit projection, indexed by positive exponent `r + 1`.
Source: Stacks Tags 03DB and 03CO (blueprint: lem-amb-root-tower-finite-tensor). -/
abbrev rootTowerProjection (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (r : ℕ) :=
  limit.π (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op r)

/-- The constant scalar map induced by the given Z_l-algebra structure.
Source: node scalar-action paragraph (blueprint: lem-amb-root-tower-finite-tensor). -/
def rootTowerTensorScalar (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (B : Type (u + 1)) [CommRing B] [Algebra ℤ_[l] B] :
    purTwistZlConstant T l ⟶ tateFiniteCoefficient T B :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom ((algebraMap ℤ_[l] B).comp ULift.ringEquiv.toRingHom))

/-- The unique residue-ring scalar homomorphism, using only annihilation.
Source: node proof step 3, Stacks 03EK (blueprint: lem-amb-root-tower-finite-tensor). -/
def rootTowerResidueScalar (l : ℕ) (r : ℕ) (B : Type (u + 1)) [CommRing B]
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) : ZMod (l ^ (r + 1)) →+* B :=
  ZMod.castHom ((CharP.cast_eq_zero_iff B (ringChar B) (l ^ (r + 1))).mp hB) B

/-- H = L tensor B over discrete constant Z_l, using the existing coordinate action
restricted along the constant-to-completed scalar map.
Source: node scalar-action paragraph and proof step 3
(blueprint: lem-amb-root-tower-finite-tensor). -/
def rootTowerTensor (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (B : Type (u + 1)) [CommRing B] [Algebra ℤ_[l] B] :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (rootTowerTensorScalar T l B)
    ((SheafOfModules.restrictScalars
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (purTwistZlCompletionMap T l))).obj (purTwistZlModule T l))

/-- A pure tensor x tensor b in H, with the scalar written first by change of rings.
Source: Stacks 03EK and node proof step 3 (blueprint: lem-amb-root-tower-finite-tensor). -/
def rootTowerTensorPure (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (B : Type (u + 1)) [CommRing B] [Algebra ℤ_[l] B] (U : T.ProEt)
    (b : (tateFiniteCoefficient T B).obj.obj (op U))
    (x : (purTwistZlOne T l).obj.obj (op U)) :
    (rootTowerTensor T l B).val.obj (op U) :=
  purScalarSection (purTwistZlConstant T l) (tateFiniteCoefficient T B)
    (rootTowerTensorScalar T l B)
    ((SheafOfModules.restrictScalars
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (purTwistZlCompletionMap T l))).obj (purTwistZlModule T l)) U b x

private theorem rootInclusion_injective (T : Scheme.{u}) (N : ℕ) (U : T.ProEtᵒᵖ) :
    Function.Injective ((proEtaleRootsOfUnityInclusion T N).hom.app U) := by
  have : Mono (proEtaleRootsOfUnityInclusion T N) := by
    dsimp [proEtaleRootsOfUnityInclusion]
    infer_instance
  have : Mono (proEtaleRootsOfUnityInclusion T N).hom :=
    (sheafToPresheaf _ _).map_mono _
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance

private def rootCoordinate (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (U : T.ProEtᵒᵖ) (x : (purTwistZlOne T l).obj.obj U) (n : ℕ) :=
  (proEtaleRootsOfUnityInclusion T (l ^ (n + 1))).hom.app U
    ((rootTowerProjection T l n).hom.app U x)

private theorem rootCoordinate_step (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (U : T.ProEtᵒᵖ) (x : (purTwistZlOne T l).obj.obj U) (n : ℕ) :
    l • rootCoordinate T l U x (n + 1) = rootCoordinate T l U x n := by
  have h := congrArg (fun f ↦ f.hom.app U x)
    (limit.w (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime))
      (homOfLE (Nat.le_succ n)).op)
  rw [show (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)).map
      (homOfLE (Nat.le_succ n)).op =
    proEtaleRootsOfUnityTransition T (l ^ (n + 1)) (l ^ (n + 2))
      (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
      (pow_dvd_pow l (Nat.le_succ (n + 1))) from
        Functor.ofOpSequence_map_homOfLE_succ _ n] at h
  exact (proEtaleRootsOfUnityTransition_prime T l (Fact.out : l.Prime) n U _).symm.trans
    (congrArg ((proEtaleRootsOfUnityInclusion T (l ^ (n + 1))).hom.app U) h)

private theorem rootCoordinate_shift (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (U : T.ProEtᵒᵖ) (x : (purTwistZlOne T l).obj.obj U) (n k : ℕ) :
    l ^ k • rootCoordinate T l U x (n + k) = rootCoordinate T l U x n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_smul, show n + (k + 1) = (n + k) + 1 by omega,
      rootCoordinate_step, ih]

private def rootOfKilled (T : Scheme.{u}) (N : ℕ) (U : T.ProEtᵒᵖ)
    (z : (proEtaleUnitsSheaf T).obj.obj U) (hz : N • z = 0) :
    (proEtaleRootsOfUnitySheaf T N).obj.obj U :=
  (proEtaleRootsOfUnitySections T N U).symm
    (Additive.ofMul ⟨z.down.toMul, (mem_rootsOfUnity N _).mpr
      (congrArg (fun y ↦ y.down.toMul) hz)⟩)

private theorem rootOfKilled_inclusion (T : Scheme.{u}) (N : ℕ) (U : T.ProEtᵒᵖ)
    (z : (proEtaleUnitsSheaf T).obj.obj U) (hz : N • z = 0) :
    (proEtaleRootsOfUnityInclusion T N).hom.app U (rootOfKilled T N U z hz) = z := by
  have h := (existsUnique_proEtaleRootsOfUnitySections T N U).exists.choose_spec
    (rootOfKilled T N U z hz)
  change ULift.up (Additive.ofMul
    ((proEtaleRootsOfUnitySections T N U) (rootOfKilled T N U z hz)).toMul.val) = _ at h
  rw [rootOfKilled, AddEquiv.apply_symm_apply] at h
  exact h.symm

private theorem rootCoordinate_ext (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (U : T.ProEtᵒᵖ) (x y : (purTwistZlOne T l).obj.obj U)
    (h : ∀ n, rootCoordinate T l U x n = rootCoordinate T l U y n) : x = y := by
  let ev := sheafToPresheaf (ProEt.topology T) AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation T.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj U
  exact Concrete.isLimit_ext (_ ⋙ ev)
    (isLimitOfPreserves ev (limit.isLimit _)) x y
    (fun n ↦ rootInclusion_injective T _ U (h n.unop))

private theorem rootKernelDivision (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (r : ℕ) :
    ∃ d : ∀ (U : T.ProEtᵒᵖ)
        (x : (purTwistZlOne T l).obj.obj U),
        (rootTowerProjection T l r).hom.app U x = 0 →
          (purTwistZlOne T l).obj.obj U,
      ∀ U x hx n, rootCoordinate T l U (d U x hx) n =
        rootCoordinate T l U x (n + r + 1) := by
  classical
  let D := proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)
  let ev (U : T.ProEtᵒᵖ) := sheafToPresheaf (ProEt.topology T) AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation T.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj U
  have killed (U : T.ProEtᵒᵖ) (x : (purTwistZlOne T l).obj.obj U)
      (hx : (rootTowerProjection T l r).hom.app U x = 0) (n : ℕ) :
      l ^ (n + 1) • rootCoordinate T l U x (n + r + 1) = 0 := by
    have h := rootCoordinate_shift T l U x r (n + 1)
    rw [show r + (n + 1) = n + r + 1 by omega] at h
    rw [h]
    change (proEtaleRootsOfUnityInclusion T _).hom.app U
      ((rootTowerProjection T l r).hom.app U x) = 0
    rw [hx, map_zero]
  let y (U : T.ProEtᵒᵖ) (x : (purTwistZlOne T l).obj.obj U)
      (hx : (rootTowerProjection T l r).hom.app U x = 0) (n : ℕ) :=
    rootOfKilled T (l ^ (n + 1)) U
      (rootCoordinate T l U x (n + r + 1)) (killed U x hx n)
  have hy (U : T.ProEtᵒᵖ) (x : (purTwistZlOne T l).obj.obj U)
      (hx : (rootTowerProjection T l r).hom.app U x = 0) (n : ℕ) :
      (proEtaleRootsOfUnityInclusion T (l ^ (n + 1))).hom.app U (y U x hx n) =
        rootCoordinate T l U x (n + r + 1) := rootOfKilled_inclusion T _ U _ _
  have hycompat (U : T.ProEtᵒᵖ) (x : (purTwistZlOne T l).obj.obj U)
      (hx : (rootTowerProjection T l r).hom.app U x = 0) (n : ℕ) :
      (proEtaleRootsOfUnityTransition T (l ^ (n + 1)) (l ^ (n + 2))
        (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
        (pow_dvd_pow l (Nat.le_succ (n + 1)))).hom.app U (y U x hx (n + 1)) =
          y U x hx n := by
    apply rootInclusion_injective T _ U
    calc
      _ = l • (proEtaleRootsOfUnityInclusion T (l ^ (n + 2))).hom.app U
          (y U x hx (n + 1)) :=
        proEtaleRootsOfUnityTransition_prime T l (Fact.out : l.Prime) n U _
      _ = l • rootCoordinate T l U x ((n + 1) + r + 1) :=
        congrArg (fun z ↦ l • z) (hy U x hx (n + 1))
      _ = l • rootCoordinate T l U x ((n + r + 1) + 1) := by
        rw [show (n + 1) + r + 1 = (n + r + 1) + 1 by omega]
      _ = rootCoordinate T l U x (n + r + 1) := rootCoordinate_step T l U x _
      _ = _ := (hy U x hx n).symm
  let c (U : T.ProEtᵒᵖ) (x : (purTwistZlOne T l).obj.obj U)
      (hx : (rootTowerProjection T l r).hom.app U x = 0) :
      Cone (D ⋙ ev U ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    { pt := PUnit
      π := NatTrans.ofOpSequence (fun n ↦ ↾fun _ ↦ y U x hx n) (by
        intro n
        ext z
        change y U x hx n = (D.map (homOfLE (Nat.le_succ n)).op).hom.app U
          (y U x hx (n + 1))
        rw [show D.map (homOfLE (Nat.le_succ n)).op =
          proEtaleRootsOfUnityTransition T (l ^ (n + 1)) (l ^ (n + 2))
            (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
            (pow_dvd_pow l (Nat.le_succ (n + 1))) from
              Functor.ofOpSequence_map_homOfLE_succ _ n]
        exact (hycompat U x hx n).symm) }
  let hc (U : T.ProEtᵒᵖ) := isLimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{u + 1})
    (isLimitOfPreserves (ev U) (limit.isLimit D))
  refine ⟨fun U x hx ↦ (hc U).lift (c U x hx) PUnit.unit, ?_⟩
  intro U x hx n
  have h := ConcreteCategory.congr_hom ((hc U).fac (c U x hx) (op n)) PUnit.unit
  exact (congrArg ((proEtaleRootsOfUnityInclusion T _).hom.app U) h).trans (hy U x hx n)

private theorem rootProjection_locallySurjective (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (hT : ∀ x : T, IsUnit (l : T.presheaf.stalk x)) (r : ℕ) :
    Sheaf.IsLocallySurjective (rootTowerProjection T l r) := by
  classical
  let : ∀ x : T, Invertible (l : T.residueField x) := fun x ↦
    ((show IsUnit (l : T.residueField x) by
      simpa only [map_natCast] using (hT x).map (T.residue x).hom)).invertible
  let D := proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)
  let F := sheafCompose (ProEt.topology T) (CategoryTheory.forget AddCommGrpCat.{u + 1})
  have ht (n : ℕ) : Sheaf.IsLocallySurjective (D.map (homOfLE (Nat.le_succ n)).op) := by
    rw [show D.map (homOfLE (Nat.le_succ n)).op =
      proEtaleRootsOfUnityTransition T (l ^ (n + 1)) (l ^ (n + 2))
        (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
        (pow_dvd_pow l (Nat.le_succ (n + 1))) from
          Functor.ofOpSequence_map_homOfLE_succ _ n]
    have := purTwistRootTransitions_epi T l n
    apply (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1}
      (proEtaleRootsOfUnityTransition T (l ^ (n + 1)) (l ^ (n + 2))
        (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
        (pow_dvd_pow l (Nat.le_succ (n + 1))))).mpr
    exact purTwistRootTransitions_epi T l n
  have hF (n : ℕ) : Epi ((D ⋙ F).map (homOfLE (Nat.le_succ n)).op) := by
    apply (Sheaf.isLocallySurjective_iff_epi _).mp
    exact ⟨(ht n).1⟩
  have := isReplete_proEtale.{u, 0} T (D ⋙ F) hF r
  have hs := (Sheaf.isLocallySurjective_iff_epi (limit.π (D ⋙ F) (op r))).mpr
    inferInstance
  let : PreservesLimit D F := by
    change PreservesLimit D (sheafCompose _ _)
    let G := sheafToPresheaf (ProEt.topology T) (Type (u + 1))
    have : PreservesLimit D (F ⋙ G) := by
      change PreservesLimit D (sheafToPresheaf _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat.{u + 1}))
      infer_instance
    exact preservesLimit_of_reflects_of_preserves F G
  have h : F.map (rootTowerProjection T l r) =
      (preservesLimitIso F D).hom ≫ limit.π (D ⋙ F) (op r) := by
    simp only [rootTowerProjection, preservesLimitIso_hom_π]
    rfl
  have hi : Sheaf.IsLocallySurjective (F.map (rootTowerProjection T l r)) := by
    rw [h]
    have := hs
    infer_instance
  exact ⟨hi.1⟩

private def rootDiscreteModule (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (purTwistZlCompletionMap T l))).obj (purTwistZlModule T l)

private def rootFiniteDiscreteModule (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (r : ℕ) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (purTwistZlReduction T l r))).obj (purTwistRootsModule T l r)

private def rootDiscreteProjection (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (r : ℕ) :
    rootDiscreteModule T l ⟶ rootFiniteDiscreteModule T l r := by
  refine ⟨PresheafOfModules.homMk (rootTowerProjection T l r).hom ?_⟩
  intro U a x
  have h := (purTwistZlAction_existsUnique T l).exists.choose_spec.2 r U
    ((purTwistZlCompletionMap T l).hom.app U a) x
  have he := congrArg (fun f ↦ f.hom.app U a)
    ((purTwistZlCompletionMap_existsUnique T l).exists.choose_spec r)
  exact h.trans (congrArg (fun b ↦ b •
    (@id ((purTwistRootsModule T l r).val.obj U)
      ((rootTowerProjection T l r).hom.app U x))) he)

private theorem rootScalar_factor (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (r : ℕ)
    (B : Type (u + 1)) [CommRing B] [Algebra ℤ_[l] B]
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) :
    purTwistZlReduction T l r ≫ tateFiniteScalar T l B r
      (rootTowerResidueScalar l r B hB) = rootTowerTensorScalar T l B := by
  have hker : RingHom.ker (PadicInt.toZModPow (r + 1) : ℤ_[l] →+* _) ≤
      RingHom.ker (algebraMap ℤ_[l] B) := by
    rw [PadicInt.ker_toZModPow, Ideal.span_le, Set.singleton_subset_iff]
    change algebraMap ℤ_[l] B ((l : ℤ_[l]) ^ (r + 1)) = 0
    simpa only [map_pow, map_natCast, Nat.cast_pow] using hB
  let q := (PadicInt.toZModPow (r + 1) : ℤ_[l] →+* _).liftOfSurjective
    (ZMod.ringHom_surjective _) ⟨algebraMap ℤ_[l] B, hker⟩
  have hq : q = rootTowerResidueScalar l r B hB := Subsingleton.elim _ _
  have he : (rootTowerResidueScalar l r B hB).comp (PadicInt.toZModPow (r + 1)) =
      algebraMap ℤ_[l] B := by
    rw [← hq]
    exact RingHom.liftOfSurjective_comp _ _ _
  change (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map _ ≫
    (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map _ = _
  rw [← Functor.map_comp]
  congr 1
  ext z
  exact DFunLike.congr_fun he z.down

private theorem rootCoefficient_killed (T : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (N : ℕ) (hB : (N : B) = 0) (U : T.ProEtᵒᵖ) :
    (N : (tateFiniteCoefficient T B).obj.obj U) = 0 := by
  let η := (toSheafify (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of B))).app U
  exact (map_natCast η.hom N).symm.trans ((congrArg η.hom hB).trans (map_zero η.hom))

private def rootTensorEmbedding (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (B : Type (u + 1)) [CommRing B] [Algebra ℤ_[l] B] :
    rootDiscreteModule T l ⟶
      (SheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (rootTowerTensorScalar T l B))).obj (rootTowerTensor T l B) :=
  SheafOfModules.scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1}
    (rootTowerTensorScalar T l B) (rootDiscreteModule T l)

private def rootFiniteEmbedding (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (r : ℕ)
    (B : Type (u + 1)) [CommRing B] (q : ZMod (l ^ (r + 1)) →+* B) :
    purTwistRootsModule T l r ⟶
      (SheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (tateFiniteScalar T l B r q))).obj (tateFiniteLine T l B r q) :=
  SheafOfModules.scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1} (tateFiniteScalar T l B r q)
    (purTwistRootsModule T l r)

private theorem rootProjection_kernel_zero (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (r : ℕ) (B : Type (u + 1)) [CommRing B] [Algebra ℤ_[l] B]
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) :
    kernel.ι (rootTowerProjection T l r) ≫
      (SheafOfModules.toSheaf _).map (rootTensorEmbedding T l B) = 0 := by
  obtain ⟨d, hd⟩ := rootKernelDivision T l r
  ext U z
  let x := (kernel.ι (rootTowerProjection T l r)).hom.app U z
  have hx : (rootTowerProjection T l r).hom.app U x = 0 := by
    exact congrArg (fun f ↦ f.hom.app U z) (kernel.condition (rootTowerProjection T l r))
  have he : l ^ (r + 1) • d U x hx = x := by
    apply rootCoordinate_ext T l U
    intro n
    calc
      _ = l ^ (r + 1) • rootCoordinate T l U (d U x hx) n := by
        simp only [rootCoordinate, map_nsmul]
      _ = l ^ (r + 1) • rootCoordinate T l U x (n + r + 1) :=
        congrArg (fun z ↦ l ^ (r + 1) • z) (hd U x hx n)
      _ = _ := rootCoordinate_shift T l U x n (r + 1)
  change (rootTensorEmbedding T l B).val.app U x = 0
  rw [← he, map_nsmul]
  let H := rootTowerTensor T l B
  have hz : ((l ^ (r + 1) : ℕ) : (tateFiniteCoefficient T B).obj.obj U) = 0 :=
    rootCoefficient_killed T B _ hB U
  exact (@Nat.cast_smul_eq_nsmul ((tateFiniteCoefficient T B).obj.obj U)
    (H.val.obj U) _ _ (H.val.obj U).isModule _ _).symm.trans
    (by rw [hz, zero_smul])

private noncomputable def rootResidueLinearLift (X : Scheme.{u}) (ℓ n : ℕ)
    (M P : SheafOfModules.{u + 1} (purTwistRing X (purTwistFiniteRing X ℓ n)))
    (f : (SheafOfModules.toSheaf _).obj M ⟶ (SheafOfModules.toSheaf _).obj P) : M ⟶ P := by
  let a := Functor.whiskerRight (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have : Presheaf.IsLocallySurjective (ProEt.topology X) a := by
    apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
    change Presheaf.IsLocallySurjective (ProEt.topology X)
      (Functor.whiskerRight (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))))
        (CategoryTheory.forget CommRingCat.{u + 1}))
    infer_instance
  let g : (PresheafOfModules.restrictScalars a).obj M.val ⟶
      (PresheafOfModules.restrictScalars a).obj P.val :=
    PresheafOfModules.homMk f.hom (by
      intro V b x
      obtain ⟨b⟩ := b
      obtain ⟨z, rfl⟩ := ZMod.intCast_surjective b
      change f.hom.app V
          (@SMul.smul _ _ (M.val.obj V).isModule.toSMul
            (a.app V (z : ULift.{u + 1} (ZMod (ℓ ^ (n + 1))))) x) =
        @SMul.smul _ _ (P.val.obj V).isModule.toSMul
          (a.app V (z : ULift.{u + 1} (ZMod (ℓ ^ (n + 1))))) (f.hom.app V x)
      rw [map_intCast]
      calc
        _ = f.hom.app V (z • (x : M.val.obj V)) := congrArg (f.hom.app V)
          (@Int.cast_smul_eq_zsmul ((purTwistRing X (purTwistFiniteRing X ℓ n)).obj.obj V)
            (M.val.obj V) _ _ (M.val.obj V).isModule z x)
        _ = z • f.hom.app V x := (f.hom.app V).hom.map_zsmul z x
        _ = _ := (@Int.cast_smul_eq_zsmul
          ((purTwistRing X (purTwistFiniteRing X ℓ n)).obj.obj V)
          (P.val.obj V) _ _ (P.val.obj V).isModule z (f.hom.app V x)).symm)
  exact ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective a P.isSheaf).symm g⟩

private def rootForwardBase (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (r : ℕ)
    (B : Type (u + 1)) [CommRing B] [Algebra ℤ_[l] B]
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) :
    rootDiscreteModule T l ⟶
      (SheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (rootTowerTensorScalar T l B))).obj
        (tateFiniteLine T l B r (rootTowerResidueScalar l r B hB)) := by
  let ρ := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (purTwistZlReduction T l r)
  let f := rootDiscreteProjection T l r ≫ (SheafOfModules.restrictScalars ρ).map
    (rootFiniteEmbedding T l r B (rootTowerResidueScalar l r B hB))
  refine ⟨PresheafOfModules.homMk
    ((rootTowerProjection T l r) ≫ (SheafOfModules.toSheaf _).map
      (rootFiniteEmbedding T l r B (rootTowerResidueScalar l r B hB))).hom ?_⟩
  intro U a x
  have hf := (f.val.app U).hom.map_smul a x
  have he := congrArg (fun g ↦ g.hom.app U a) (rootScalar_factor T l r B hB)
  exact hf.trans (congrArg (fun b ↦ b •
    (show (tateFiniteLine T l B r (rootTowerResidueScalar l r B hB)).val.obj U from
      f.val.app U x)) he)

attribute [local irreducible] SheafOfModules.scalarExtensionLift

private def rootTensorForward (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (r : ℕ)
    (B : Type (u + 1)) [CommRing B] [Algebra ℤ_[l] B]
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) :
    rootTowerTensor T l B ⟶ tateFiniteLine T l B r (rootTowerResidueScalar l r B hB) :=
  SheafOfModules.scalarExtensionLift.{u + 1, u, u + 1, u + 1}
    (rootTowerTensorScalar T l B) (rootDiscreteModule T l)
    _ (rootForwardBase T l r B hB)

private theorem rootTensorForward_pure (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (r : ℕ)
    (B : Type (u + 1)) [CommRing B] [Algebra ℤ_[l] B]
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) (U : T.ProEt)
    (b : (tateFiniteCoefficient T B).obj.obj (op U))
    (x : (purTwistZlOne T l).obj.obj (op U)) :
    (rootTensorForward T l r B hB).val.app (op U) (rootTowerTensorPure T l B U b x) =
      tateFiniteTensor T l B r (rootTowerResidueScalar l r B hB) U b
        ((rootTowerProjection T l r).hom.app (op U) x) := by
  unfold rootTensorForward
  change (SheafOfModules.scalarExtensionLift.{u + 1, u, u + 1, u + 1}
    (rootTowerTensorScalar T l B) (rootDiscreteModule T l) _
    (rootForwardBase T l r B hB)).val.app (op U)
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        (rootTowerTensorScalar T l B)
        (rootDiscreteModule T l) (op U) b x) = _
  erw [SheafOfModules.scalarExtensionLift_tmul.{u + 1, u, u + 1, u + 1}]
  change b • SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
    (tateFiniteScalar T l B r (rootTowerResidueScalar l r B hB))
    (purTwistRootsModule T l r) (op U) 1 _ = _
  rw [SheafOfModules.scalarExtensionSection_smul.{u + 1, u, u + 1, u + 1}, mul_one]
  rfl

private def rootTensorDescent (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (hT : ∀ x : T, IsUnit (l : T.presheaf.stalk x)) (r : ℕ)
    (B : Type (u + 1)) [CommRing B] [Algebra ℤ_[l] B]
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) :
    proEtaleRootsOfUnitySheaf T (l ^ (r + 1)) ⟶
      (SheafOfModules.toSheaf _).obj (rootTowerTensor T l B) := by
  have := rootProjection_locallySurjective T l hT r
  have : Epi (rootTowerProjection T l r) :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1}
      (rootTowerProjection T l r)).mp inferInstance
  exact Abelian.epiDesc (rootTowerProjection T l r)
    ((SheafOfModules.toSheaf _).map (rootTensorEmbedding T l B))
    (rootProjection_kernel_zero T l r B hB)

private theorem rootTensorDescent_projection (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (hT : ∀ x : T, IsUnit (l : T.presheaf.stalk x)) (r : ℕ)
    (B : Type (u + 1)) [CommRing B] [Algebra ℤ_[l] B]
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) :
    rootTowerProjection T l r ≫ rootTensorDescent T l hT r B hB =
      (SheafOfModules.toSheaf _).map (rootTensorEmbedding T l B) := by
  have := rootProjection_locallySurjective T l hT r
  have : Epi (rootTowerProjection T l r) :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1}
      (rootTowerProjection T l r)).mp inferInstance
  unfold rootTensorDescent
  exact Abelian.comp_epiDesc _ _ _

private def rootTensorBackward (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (hT : ∀ x : T, IsUnit (l : T.presheaf.stalk x)) (r : ℕ)
    (B : Type (u + 1)) [CommRing B] [Algebra ℤ_[l] B]
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) :
    tateFiniteLine T l B r (rootTowerResidueScalar l r B hB) ⟶ rootTowerTensor T l B :=
  SheafOfModules.scalarExtensionLift.{u + 1, u, u + 1, u + 1}
    (tateFiniteScalar T l B r (rootTowerResidueScalar l r B hB)) (purTwistRootsModule T l r)
    (rootTowerTensor T l B)
    (rootResidueLinearLift T l r _ _ (rootTensorDescent T l hT r B hB))

private theorem rootTensorBackward_pure (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (hT : ∀ x : T, IsUnit (l : T.presheaf.stalk x)) (r : ℕ)
    (B : Type (u + 1)) [CommRing B] [Algebra ℤ_[l] B]
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) (U : T.ProEt)
    (b : (tateFiniteCoefficient T B).obj.obj (op U))
    (x : (proEtaleRootsOfUnitySheaf T (l ^ (r + 1))).obj.obj (op U)) :
    (rootTensorBackward T l hT r B hB).val.app (op U)
      (tateFiniteTensor T l B r (rootTowerResidueScalar l r B hB) U b x) =
      b • (show (rootTowerTensor T l B).val.obj (op U) from
        (rootTensorDescent T l hT r B hB).hom.app (op U) x) := by
  unfold rootTensorBackward
  change (SheafOfModules.scalarExtensionLift.{u + 1, u, u + 1, u + 1}
    (tateFiniteScalar T l B r (rootTowerResidueScalar l r B hB))
    (purTwistRootsModule T l r) _ _).val.app (op U)
      (SheafOfModules.scalarExtensionSection
        (tateFiniteScalar T l B r (rootTowerResidueScalar l r B hB))
        (purTwistRootsModule T l r) (op U) b x) = _
  erw [SheafOfModules.scalarExtensionLift_tmul.{u + 1, u, u + 1, u + 1}]
  rfl

private theorem rootTensorBackward_projection (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (hT : ∀ x : T, IsUnit (l : T.presheaf.stalk x)) (r : ℕ)
    (B : Type (u + 1)) [CommRing B] [Algebra ℤ_[l] B]
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) (U : T.ProEt)
    (b : (tateFiniteCoefficient T B).obj.obj (op U))
    (x : (purTwistZlOne T l).obj.obj (op U)) :
    (rootTensorBackward T l hT r B hB).val.app (op U)
      (tateFiniteTensor T l B r (rootTowerResidueScalar l r B hB) U b
        ((rootTowerProjection T l r).hom.app (op U) x)) =
      rootTowerTensorPure T l B U b x := by
  rw [rootTensorBackward_pure]
  have h := congrArg (fun f ↦ f.hom.app (op U) x)
    (rootTensorDescent_projection T l hT r B hB)
  change (rootTensorDescent T l hT r B hB).hom.app (op U)
    ((rootTowerProjection T l r).hom.app (op U) x) =
      (rootTensorEmbedding T l B).val.app (op U) x at h
  rw [h]
  change b • SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
    (rootTowerTensorScalar T l B) (rootDiscreteModule T l) (op U) 1 x = _
  rw [SheafOfModules.scalarExtensionSection_smul.{u + 1, u, u + 1, u + 1}, mul_one]
  rfl

private def rootTensorIso (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (hT : ∀ x : T, IsUnit (l : T.presheaf.stalk x)) (r : ℕ)
    (B : Type (u + 1)) [CommRing B] [Algebra ℤ_[l] B]
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) :
    rootTowerTensor T l B ≅ tateFiniteLine T l B r (rootTowerResidueScalar l r B hB) where
  hom := rootTensorForward T l r B hB
  inv := rootTensorBackward T l hT r B hB
  hom_inv_id := by
    apply SheafOfModules.scalarExtension_hom_ext.{u + 1, u, u + 1, u + 1}
      (rootTowerTensorScalar T l B) (rootDiscreteModule T l)
    intro U b x
    change (rootTensorBackward T l hT r B hB).val.app U
      ((rootTensorForward T l r B hB).val.app U
        (rootTowerTensorPure T l B U.unop b x)) = rootTowerTensorPure T l B U.unop b x
    rw [rootTensorForward_pure, rootTensorBackward_projection]
  inv_hom_id := by
    have := rootProjection_locallySurjective T l hT r
    have : Epi (rootTowerProjection T l r) :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1}
        (rootTowerProjection T l r)).mp inferInstance
    have hd : rootTensorDescent T l hT r B hB ≫
        (SheafOfModules.toSheaf _).map (rootTensorForward T l r B hB) =
        (SheafOfModules.toSheaf _).map
          (rootFiniteEmbedding T l r B (rootTowerResidueScalar l r B hB)) := by
      apply (cancel_epi (rootTowerProjection T l r)).mp
      rw [← Category.assoc, rootTensorDescent_projection]
      ext U x
      exact rootTensorForward_pure T l r B hB U.unop 1 x
    apply SheafOfModules.scalarExtension_hom_ext.{u + 1, u, u + 1, u + 1}
      (tateFiniteScalar T l B r (rootTowerResidueScalar l r B hB)) (purTwistRootsModule T l r)
    intro U b x
    change (rootTensorForward T l r B hB).val.app U
      ((rootTensorBackward T l hT r B hB).val.app U
        (tateFiniteTensor T l B r (rootTowerResidueScalar l r B hB) U.unop b x)) =
      tateFiniteTensor T l B r (rootTowerResidueScalar l r B hB) U.unop b x
    rw [rootTensorBackward_pure, map_smul]
    have h := congrArg (fun f ↦ f.hom.app U x) hd
    change (rootTensorForward T l r B hB).val.app U
      ((rootTensorDescent T l hT r B hB).hom.app U x) =
        (rootFiniteEmbedding T l r B (rootTowerResidueScalar l r B hB)).val.app U x at h
    rw [h]
    change b • SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} _ _ U 1 x =
      SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} _ _ U b x
    erw [SheafOfModules.scalarExtensionSection_smul.{u + 1, u, u + 1, u + 1}, mul_one]

/-- Root projections, their sectionwise shift division, and normalized finite tensor reduction.
Source: Stacks 0990, 03PL, 03EK, 03CY and 00WK; agent extraction, proof steps 1--6
(blueprint: lem-amb-root-tower-finite-tensor).

Proof:
1. Use the proved epimorphic root transitions and pro-etale repleteness, after forgetting
additive structure and transporting the limit. The local-surjectivity criterion gives
local surjectivity of every root projection.
2. In positive-exponent notation, if x_r = 0, set d(x)_s = x_(s+r). Iterating the
transition equation shows that this unit is killed by l^s and that these roots are
compatible. The sectionwise limit constructs d; its coordinates give l^r d(x) = x.
Root-group annihilation gives the converse. Coordinate extensionality and naturality
of projections prove that d commutes with restrictions.
3. Restrict the completed action to constant Z_l. The coordinate action makes p_r
linear for reduction to Z/l^r. PadicInt.ker_toZModPow and the annihilation of B
factor its scalar map through this quotient. Scalar extension then constructs the
forward B-linear map with the asserted pure-tensor formula.
4. The tensor embedding kills ker(p_r): step 2 expresses its sections as l^r y,
and l^r vanishes in the constant coefficient sheaf. Since p_r is epic, Abelian.epiDesc
produces the unique additive map from finite roots to the tensor with composite equal
to the tensor embedding. This is the categorical form of gluing local lifts.
5. Every additive map between modules over the constant residue-ring sheaf is linear:
restrict to the constant presheaf, represent each residue by an integer, use preservation
of integer multiplication, then descend along the locally surjective sheafification
unit. Applying this to the descended map and extending scalars gives the inverse.
6. One composite is the identity on pure tensors by the descent equation. For the other,
cancel the epic projection to identify the descended map followed by the forward map
with the finite tensor embedding, then use pure-tensor extensionality. Naturality and
the separatedness axiom identify the inverse with exactly the stated gluing for every
covering sieve and family of lifts. No flatness is used. -/
theorem rootTower_finite_tensor (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (hT : ∀ x : T, IsUnit (l : T.presheaf.stalk x)) (r : ℕ) :
    Sheaf.IsLocallySurjective (rootTowerProjection T l r) ∧
    (∀ (U : T.ProEt) (x : (purTwistZlOne T l).obj.obj (op U)),
      (rootTowerProjection T l r).hom.app (op U) x = 0 ↔
        ∃ y : (purTwistZlOne T l).obj.obj (op U), l ^ (r + 1) • y = x) ∧
    (∃ d : ∀ U : T.ProEt,
        {x : (purTwistZlOne T l).obj.obj (op U) //
          (rootTowerProjection T l r).hom.app (op U) x = 0} →
            (purTwistZlOne T l).obj.obj (op U),
      (∀ (U : T.ProEt) (x : {x : (purTwistZlOne T l).obj.obj (op U) //
          (rootTowerProjection T l r).hom.app (op U) x = 0}) (s : ℕ),
        (proEtaleRootsOfUnityInclusion T (l ^ (s + 1))).hom.app (op U)
            ((rootTowerProjection T l s).hom.app (op U) (d U x)) =
          (proEtaleRootsOfUnityInclusion T (l ^ (s + r + 2))).hom.app (op U)
            ((rootTowerProjection T l (s + r + 1)).hom.app (op U) x.val)) ∧
      (∀ (U : T.ProEt) (x : {x : (purTwistZlOne T l).obj.obj (op U) //
          (rootTowerProjection T l r).hom.app (op U) x = 0}),
        l ^ (r + 1) • d U x = x.val) ∧
      ∀ (U V : T.ProEt) (f : V ⟶ U)
        (x : {x : (purTwistZlOne T l).obj.obj (op U) //
          (rootTowerProjection T l r).hom.app (op U) x = 0})
        (y : {y : (purTwistZlOne T l).obj.obj (op V) //
          (rootTowerProjection T l r).hom.app (op V) y = 0}),
        y.val = (purTwistZlOne T l).obj.map f.op x.val →
          d V y = (purTwistZlOne T l).obj.map f.op (d U x)) ∧
    ∀ (B : Type (u + 1)) [CommRing B] [Algebra ℤ_[l] B] (hB : ((l ^ (r + 1) : ℕ) : B) = 0),
      ∃ e : rootTowerTensor T l B ≅
          tateFiniteLine T l B r (rootTowerResidueScalar l r B hB),
        (∀ (U : T.ProEt) (b : (tateFiniteCoefficient T B).obj.obj (op U))
          (x : (purTwistZlOne T l).obj.obj (op U)),
          e.hom.val.app (op U) (rootTowerTensorPure T l B U b x) =
            tateFiniteTensor T l B r (rootTowerResidueScalar l r B hB) U b
              ((rootTowerProjection T l r).hom.app (op U) x)) ∧
        ∀ (U : T.ProEt)
          (a : (proEtaleRootsOfUnitySheaf T (l ^ (r + 1))).obj.obj (op U))
          (b : (tateFiniteCoefficient T B).obj.obj (op U))
          (S : Sieve U) (_hS : S ∈ ProEt.topology T U)
          (x : ∀ (V : T.ProEt) (f : V ⟶ U), S f → (purTwistZlOne T l).obj.obj (op V))
          (_hx : ∀ (V : T.ProEt) (f : V ⟶ U) (hf : S f),
            (rootTowerProjection T l r).hom.app (op V) (x V f hf) =
              (proEtaleRootsOfUnitySheaf T (l ^ (r + 1))).obj.map f.op a)
          (h : (rootTowerTensor T l B).val.obj (op U)),
          (∀ (V : T.ProEt) (f : V ⟶ U) (hf : S f),
            (rootTowerTensor T l B).val.map f.op h = rootTowerTensorPure T l B V
              ((tateFiniteCoefficient T B).obj.map f.op b) (x V f hf)) ↔
            h = e.inv.val.app (op U)
              (tateFiniteTensor T l B r (rootTowerResidueScalar l r B hB) U b a) := by
  classical
  obtain ⟨d, hd⟩ := rootKernelDivision T l r
  have hdiv (U : T.ProEtᵒᵖ) (x : (purTwistZlOne T l).obj.obj U)
      (hx : (rootTowerProjection T l r).hom.app U x = 0) :
      l ^ (r + 1) • d U x hx = x := by
    apply rootCoordinate_ext T l U
    intro n
    change (proEtaleRootsOfUnityInclusion T _).hom.app U
      ((rootTowerProjection T l n).hom.app U (l ^ (r + 1) • d U x hx)) = _
    calc
      _ = l ^ (r + 1) • rootCoordinate T l U (d U x hx) n := by
        simp only [rootCoordinate, map_nsmul]
      _ = l ^ (r + 1) • rootCoordinate T l U x (n + r + 1) :=
        congrArg (fun z ↦ l ^ (r + 1) • z) (hd U x hx n)
      _ = _ := rootCoordinate_shift T l U x n (r + 1)
  refine ⟨rootProjection_locallySurjective T l hT r, ?_, ?_, ?_⟩
  · intro U x
    constructor
    · intro hx
      exact ⟨d (op U) x hx, hdiv (op U) x hx⟩
    · rintro ⟨y, rfl⟩
      rw [map_nsmul, proEtaleRootsOfUnity_nsmul]
  · refine ⟨fun U x ↦ d (op U) x.val x.property,
      fun U x n ↦ hd (op U) x.val x.property n, ?_, ?_⟩
    · intro U x
      exact hdiv (op U) x.val x.property
    · intro U V f x y hy
      apply rootCoordinate_ext T l (op V)
      intro n
      rw [hd]
      change rootCoordinate T l (op V) y.val (n + r + 1) =
        (proEtaleRootsOfUnityInclusion T _).hom.app (op V)
          ((rootTowerProjection T l n).hom.app (op V)
            ((purTwistZlOne T l).obj.map f.op (d (op U) x.val x.property)))
      have hn (m : ℕ) (z : (purTwistZlOne T l).obj.obj (op U)) :
          rootCoordinate T l (op V) ((purTwistZlOne T l).obj.map f.op z) m =
            (proEtaleUnitsSheaf T).obj.map f.op (rootCoordinate T l (op U) z m) := by
        exact (congrArg ((proEtaleRootsOfUnityInclusion T _).hom.app (op V))
          (NatTrans.naturality_apply (rootTowerProjection T l m).hom f.op z)).trans
          (NatTrans.naturality_apply (proEtaleRootsOfUnityInclusion T _).hom f.op _)
      exact (congrArg (fun z ↦ rootCoordinate T l (op V) z (n + r + 1)) hy).trans
        ((hn _ x.val).trans
          ((congrArg ((proEtaleUnitsSheaf T).obj.map f.op)
            (hd (op U) x.val x.property n)).symm.trans
            (hn n (d (op U) x.val x.property)).symm))
  · intro B _ _ hB
    let e := rootTensorIso T l hT r B hB
    refine ⟨e, rootTensorForward_pure T l r B hB, ?_⟩
    intro U a b S hS x hx h
    have ht (V W : T.ProEt) (f : W ⟶ V)
        (b : (tateFiniteCoefficient T B).obj.obj (op V))
        (a : (proEtaleRootsOfUnitySheaf T (l ^ (r + 1))).obj.obj (op V)) :
        (tateFiniteLine T l B r (rootTowerResidueScalar l r B hB)).val.map f.op
          (tateFiniteTensor T l B r (rootTowerResidueScalar l r B hB) V b a) =
          tateFiniteTensor T l B r (rootTowerResidueScalar l r B hB) W
            ((tateFiniteCoefficient T B).obj.map f.op b)
            ((proEtaleRootsOfUnitySheaf T (l ^ (r + 1))).obj.map f.op a) :=
      SheafOfModules.scalarExtensionSection_naturality.{u + 1, u, u + 1, u + 1}
        (tateFiniteScalar T l B r (rootTowerResidueScalar l r B hB))
        (purTwistRootsModule T l r) f.op b a
    constructor
    · intro hh
      have heh : e.hom.val.app (op U) h =
          tateFiniteTensor T l B r (rootTowerResidueScalar l r B hB) U b a := by
        apply (tateFiniteLine T l B r (rootTowerResidueScalar l r B hB)).isSheaf.isSeparated
          _ _ hS
        intro V f hf
        calc
          _ = e.hom.val.app (op V) ((rootTowerTensor T l B).val.map f.op h) :=
            (PresheafOfModules.naturality_apply e.hom.val f.op h).symm
          _ = e.hom.val.app (op V) (rootTowerTensorPure T l B V
              ((tateFiniteCoefficient T B).obj.map f.op b) (x V f hf)) :=
            congrArg (e.hom.val.app (op V)) (hh V f hf)
          _ = tateFiniteTensor T l B r (rootTowerResidueScalar l r B hB) V
              ((tateFiniteCoefficient T B).obj.map f.op b)
              ((rootTowerProjection T l r).hom.app (op V) (x V f hf)) :=
            rootTensorForward_pure T l r B hB V _ _
          _ = _ := (congrArg (tateFiniteTensor T l B r
            (rootTowerResidueScalar l r B hB) V
              ((tateFiniteCoefficient T B).obj.map f.op b)) (hx V f hf)).trans
                (ht U V f b a).symm
      have hid := congrArg (fun g ↦ g.val.app (op U) h) e.hom_inv_id
      exact hid.symm.trans (congrArg (e.inv.val.app (op U)) heh)
    · intro hh V f hf
      rw [hh, ← PresheafOfModules.naturality_apply e.inv.val, ht, ← hx V f hf]
      exact rootTensorBackward_projection T l hT r B hB V _ _

end AlgebraicGeometry.Scheme
