/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import WeilConjectures.AlgebraicGeometry.AffineKoszulFiniteFreeResolution
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import WeilConjectures.RingTheory.KoszulBaseChangeIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-! # A locally augmented Koszul carrier

Source: Stacks Project, Tags 0BQY and 068C.
(blueprint: new-s1-local-koszul-augmented-carrier). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem differential_zero_of_iso {C : Type*} [Category C] [HasZeroMorphisms C]
    {ι : Type*} {s : ComplexShape ι} {K L : HomologicalComplex C s}
    (e : K ≅ L) (hL : ∀ x y, L.d x y = 0) (x y : ι) : K.d x y = 0 := by
  apply (cancel_mono (e.hom.f y)).mp
  rw [← e.hom.comm, hL, comp_zero, zero_comp]

private theorem zero_koszul_differential (B : Type u) [CommRing B] (m : ℕ)
    (x y : ℕ) : (ExteriorAlgebra.koszulComplex B m (fun _ ↦ 0)).d x y = 0 := by
  by_cases h : x = y + 1
  · subst x
    simp only [ExteriorAlgebra.koszulComplex, ChainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.val_injective
    change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm B (Fin m →₀ B)))
      (Finsupp.linearCombination B (fun _ ↦ 0)) (z : ExteriorAlgebra B (Fin m →₀ B)) = 0
    have hz : Finsupp.linearCombination B (fun _ : Fin m ↦ (0 : B)) = 0 := by
      ext v
      simp [Finsupp.linearCombination_apply]
    rw [hz]
    simp
  · exact (ExteriorAlgebra.koszulComplex B m (fun _ ↦ 0)).shape x y
      (by simpa [eq_comm] using h)

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_koszul_differential_zero (A B : Type u)
    [CommRing A] [CommRing B] (φ : A →+* B) (m : ℕ) (f : Fin m → A)
    (hf : ∀ j, φ (f j) = 0) :
    let L := ExteriorAlgebra.koszulComplex A m f
    let H := ModuleCat.extendScalars φ
    ∀ x y : ℤ, ((H.mapHomologicalComplex (.up ℤ)).obj
      (L.extend ComplexShape.embeddingDownNat)).d x y = 0 := by
  dsimp only
  classical
  let := φ.toAlgebra
  obtain ⟨c⟩ := ExteriorAlgebra.nonempty_koszulBaseChangeIso A B m f
  have heq : algebraMap A B ∘ f = fun _ ↦ 0 := funext hf
  have hc (x y : ℕ) :
      (ModuleCat.extendScalars φ).map
        ((ExteriorAlgebra.koszulComplex A m f).d x y) = 0 := by
    apply differential_zero_of_iso c
    rw [heq]
    exact zero_koszul_differential B m
  intro x y
  let L := ExteriorAlgebra.koszulComplex A m f
  let H := ModuleCat.extendScalars φ
  change H.map ((L.extend ComplexShape.embeddingDownNat).d x y) = 0
  by_cases hx : 0 < x
  · have hz := L.isZero_extend_X ComplexShape.embeddingDownNat x
      (fun q ↦ by change -(q : ℤ) ≠ x; omega)
    rw [hz.eq_of_src ((L.extend ComplexShape.embeddingDownNat).d x y) 0, H.map_zero]
  · by_cases hy : 0 < y
    · have hz := L.isZero_extend_X ComplexShape.embeddingDownNat y
        (fun q ↦ by change -(q : ℤ) ≠ y; omega)
      rw [hz.eq_of_tgt ((L.extend ComplexShape.embeddingDownNat).d x y) 0, H.map_zero]
    · obtain ⟨q, hq⟩ := Int.exists_eq_neg_ofNat (by omega : x ≤ 0)
      obtain ⟨p, hp⟩ := Int.exists_eq_neg_ofNat (by omega : y ≤ 0)
      rw [L.extend_d_eq ComplexShape.embeddingDownNat hq.symm hp.symm,
        H.map_comp, H.map_comp, hc, zero_comp, comp_zero]

private noncomputable def tensorPullbackRestrictIso {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] :
    Scheme.Modules.tensorPullback g ≅ Scheme.Modules.restrictFunctor g :=
  (Scheme.Modules.nonempty_tensorPullbackAdjunction g).some.leftAdjointUniq
    (Scheme.Modules.restrictAdjunction g)

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

private noncomputable def tensorFreeIso {X Y : Scheme.{u}} (g : X ⟶ Y) (I : Type u) :
    (Scheme.Modules.tensorPullback g).obj (SheafOfModules.free (R := Y.ringCatSheaf) I) ≅
      SheafOfModules.free (R := X.ringCatSheaf) I := by
  classical
  let := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).isLeftAdjoint
  have := (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso g).1
  let e := asIso (Scheme.Modules.tensorPullbackObjUnitToUnit g)
  exact (SheafOfModules.mapFreeIso (Scheme.Modules.tensorPullback g) I e.symm).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem affine_pullback_koszul_zero {Y X : Scheme.{u}} [IsAffine X]
    (U : Y.affineOpens) (g : X ⟶ U.1.toScheme) (m : ℕ) (f : Fin m → Γ(Y, U.1))
    (hf : ∀ j, ((Scheme.ΓSpecIso Γ(Y, U.1)).inv ≫
      (g ≫ U.2.isoSpec.hom).appTop) (f j) = 0) :
    let E := ((tilde.functor Γ(Y, U.1) ⋙
      Scheme.Modules.restrictFunctor U.2.isoSpec.hom).mapHomologicalComplex (.up ℤ)).obj
        ((ExteriorAlgebra.koszulComplex (Γ(Y, U.1) : Type u) m f).extend
          ComplexShape.embeddingDownNat)
    let : (Scheme.Modules.tensorPullback g).Additive := by
      let : (Scheme.Modules.tensorPullback g).IsLeftAdjoint :=
        ⟨_, Scheme.Modules.nonempty_tensorPullbackAdjunction g⟩
      exact CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
        (by rw [CategoryTheory.rightExactFunctor_iff]; infer_instance)
    ∀ x y : ℤ, (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj
      E).d x y = 0 := by
  dsimp only
  classical
  let A := Γ(Y, U.1)
  let B := Γ(X, ⊤)
  let φ := (Scheme.ΓSpecIso A).inv ≫ (g ≫ U.2.isoSpec.hom).appTop
  let S := Spec.map φ
  let RY := Scheme.Modules.restrictFunctor U.2.isoSpec.hom
  let RX := Scheme.Modules.restrictFunctor X.isoSpec.hom
  let TY := tilde.functor A
  let TX := tilde.functor B
  let H := ModuleCat.extendScalars φ.hom
  let L := (ExteriorAlgebra.koszulComplex (A : Type u) m f).extend
    ComplexShape.embeddingDownNat
  let : (Scheme.Modules.tensorPullback g).Additive := by
    let : (Scheme.Modules.tensorPullback g).IsLeftAdjoint :=
      ⟨_, Scheme.Modules.nonempty_tensorPullbackAdjunction g⟩
    exact CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
      (by rw [CategoryTheory.rightExactFunctor_iff]; infer_instance)
  let : (Scheme.Modules.tensorPullback S).Additive := by
    let : (Scheme.Modules.tensorPullback S).IsLeftAdjoint :=
      ⟨_, Scheme.Modules.nonempty_tensorPullbackAdjunction S⟩
    exact CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
      (by rw [CategoryTheory.rightExactFunctor_iff]; infer_instance)
  let : (Scheme.Modules.tensorPullback X.isoSpec.hom).Additive := by
    let : (Scheme.Modules.tensorPullback X.isoSpec.hom).IsLeftAdjoint :=
      ⟨_, Scheme.Modules.nonempty_tensorPullbackAdjunction X.isoSpec.hom⟩
    exact CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
      (by rw [CategoryTheory.rightExactFunctor_iff]; infer_instance)
  let : (Scheme.Modules.tensorPullback U.2.isoSpec.hom).Additive := by
    let : (Scheme.Modules.tensorPullback U.2.isoSpec.hom).IsLeftAdjoint :=
      ⟨_, Scheme.Modules.nonempty_tensorPullbackAdjunction U.2.isoSpec.hom⟩
    exact CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
      (by rw [CategoryTheory.rightExactFunctor_iff]; infer_instance)
  have h : g ≫ U.2.isoSpec.hom = X.isoSpec.hom ≫ S := by
    dsimp [S, φ]
    rw [Spec.map_comp]
    change _ = X.toSpecΓ ≫ Spec.map (g ≫ U.2.isoSpec.hom).appTop ≫
      Spec.map (Scheme.ΓSpecIso A).inv
    rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  let sq : RY ⋙ Scheme.Modules.tensorPullback g ≅
      Scheme.Modules.tensorPullback S ⋙ RX :=
    Functor.isoWhiskerRight (tensorPullbackRestrictIso U.2.isoSpec.hom).symm _ ≪≫
      (Scheme.Modules.nonempty_tensorPullbackComp g U.2.isoSpec.hom).some.symm ≪≫
      eqToIso (congrArg Scheme.Modules.tensorPullback h) ≪≫
      (Scheme.Modules.nonempty_tensorPullbackComp X.isoSpec.hom S).some ≪≫
      Functor.isoWhiskerLeft _ (tensorPullbackRestrictIso X.isoSpec.hom)
  obtain ⟨θ, _⟩ := Scheme.Modules.exists_tensorPullback_tilde_iso φ
  let comparison : (TY ⋙ RY) ⋙ Scheme.Modules.tensorPullback g ≅ (H ⋙ TX) ⋙ RX :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft TY sq ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight θ RX
  let e := (NatIso.mapHomologicalComplex comparison (.up ℤ)).app L
  intro x y
  apply differential_zero_of_iso e
  intro a b
  change RX.map (TX.map (H.map (L.d a b))) = 0
  have hz := scalar_koszul_differential_zero (A : Type u) (B : Type u) φ.hom m f hf a b
  change H.map (L.d a b) = 0 at hz
  rw [hz, TX.map_zero, RX.map_zero]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem local_tensor_free {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    (V : Z.Opens) (U : Y.Opens) (M : Y.Modules) (r : ℕ)
    (e : (Scheme.Modules.restrictFunctor U.ι).obj M ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))) :
    Nonempty (((Scheme.Modules.restrictFunctor V.ι ⋙
      SheafOfModules.overFunctor V.toScheme.ringCatSheaf (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U))).obj
        ((Scheme.Modules.tensorPullback i).obj M)) ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf.over (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U)))
        (ULift.{u} (Fin r))) := by
  classical
  let W := V.ι ⁻¹ᵁ (i ⁻¹ᵁ U)
  let j := W.ι ≫ V.ι
  let a := (V.ι ≫ i).resLE U W (by rfl)
  have h : j ≫ i = a ≫ U.ι := by
    dsimp [j, a]
    simp only [Scheme.Hom.resLE_comp_ι, Category.assoc]
  let sq : Scheme.Modules.tensorPullback i ⋙ Scheme.Modules.restrictFunctor j ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.tensorPullback a :=
    (Functor.isoWhiskerLeft _ (tensorPullbackRestrictIso j)).symm ≪≫
      (Scheme.Modules.nonempty_tensorPullbackComp j i).some.symm ≪≫
      eqToIso (congrArg Scheme.Modules.tensorPullback h) ≪≫
      (Scheme.Modules.nonempty_tensorPullbackComp a U.ι).some ≪≫
      Functor.isoWhiskerRight (tensorPullbackRestrictIso U.ι) _
  let e' := ((Scheme.Modules.restrictFunctorComp W.ι V.ι).app
      ((Scheme.Modules.tensorPullback i).obj M)).symm ≪≫ sq.app M ≪≫
      (Scheme.Modules.tensorPullback a).mapIso e ≪≫
      tensorFreeIso a (ULift.{u} (Fin r))
  exact ⟨(Scheme.Modules.overIsoFreeEquiv
    ((Scheme.Modules.restrictFunctor V.ι).obj ((Scheme.Modules.tensorPullback i).obj M))
      W (ULift.{u} (Fin r))).symm e'⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Several natural isomorphisms transport the complex across charts and the over site.
private theorem local_koszul_pullback_zero {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] [(Scheme.Modules.tensorPullback i).Additive]
    (V : Z.Opens) (U : Y.affineOpens) (m : ℕ) (f : Fin m → Γ(Y, U.1))
    (hf : Ideal.span (Set.range f) = i.ker.ideal U) :
    let E := ((tilde.functor Γ(Y, U.1) ⋙
      Scheme.Modules.restrictFunctor U.2.isoSpec.hom).mapHomologicalComplex (.up ℤ)).obj
        ((ExteriorAlgebra.koszulComplex (Γ(Y, U.1) : Type u) m f).extend
          ComplexShape.embeddingDownNat)
    let K := ((Scheme.Modules.pushforward U.1.ι).mapHomologicalComplex (.up ℤ)).obj E
    let G := (Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ) ⋙
      moduleOpenOverComplexFunctor Z V (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1))
    ∀ x y : ℤ, (G.obj K).d x y = 0 := by
  dsimp only
  classical
  let E := ((tilde.functor Γ(Y, U.1) ⋙
    Scheme.Modules.restrictFunctor U.2.isoSpec.hom).mapHomologicalComplex (.up ℤ)).obj
      ((ExteriorAlgebra.koszulComplex (Γ(Y, U.1) : Type u) m f).extend
        ComplexShape.embeddingDownNat)
  let K := ((Scheme.Modules.pushforward U.1.ι).mapHomologicalComplex (.up ℤ)).obj E
  let X := i ⁻¹ᵁ U.1
  let W := V.ι ⁻¹ᵁ X
  let j := W.ι ≫ V.ι
  let a := (V.ι ≫ i).resLE U.1 W (by rfl)
  let g := V.ι.resLE X W le_rfl
  let t := i ∣_ U.1
  have ha : a = g ≫ t := by
    apply (cancel_mono U.1.ι).mp
    change (V.ι ≫ i).resLE U.1 W (by rfl) ≫ U.1.ι =
      V.ι.resLE X W le_rfl ≫ (i ∣_ U.1) ≫ U.1.ι
    rw [Scheme.Hom.resLE_comp_ι, morphismRestrict_ι]
    simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ i)
      (V.ι.resLE_comp_ι (U := X) (V := W) le_rfl).symm
  let : IsAffine X.toScheme := U.2.preimage i
  let : (Scheme.Modules.tensorPullback t).Additive := by
    let : (Scheme.Modules.tensorPullback t).IsLeftAdjoint :=
      ⟨_, Scheme.Modules.nonempty_tensorPullbackAdjunction t⟩
    exact CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
      (by rw [CategoryTheory.rightExactFunctor_iff]; infer_instance)
  let : (Scheme.Modules.tensorPullback a).Additive := by
    let : (Scheme.Modules.tensorPullback a).IsLeftAdjoint :=
      ⟨_, Scheme.Modules.nonempty_tensorPullbackAdjunction a⟩
    exact CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
      (by rw [CategoryTheory.rightExactFunctor_iff]; infer_instance)
  let : (Scheme.Modules.tensorPullback g).Additive := by
    let : (Scheme.Modules.tensorPullback g).IsLeftAdjoint :=
      ⟨_, Scheme.Modules.nonempty_tensorPullbackAdjunction g⟩
    exact CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
      (by rw [CategoryTheory.rightExactFunctor_iff]; infer_instance)
  have ht (j : Fin m) : ((Scheme.ΓSpecIso Γ(Y, U.1)).inv ≫
      (t ≫ U.2.isoSpec.hom).appTop) (f j) = 0 := by
    have hφ : (Scheme.ΓSpecIso Γ(Y, U.1)).inv ≫
        (t ≫ U.2.isoSpec.hom).appTop = i.app U.1 ≫ X.topIso.inv := by
      change (Scheme.ΓSpecIso Γ(Y, U.1)).inv ≫
        (i ∣_ U.1 ≫ U.2.isoSpec.hom).appTop = _
      rw [Scheme.Hom.comp_appTop, U.2.isoSpec_hom_appTop]
      rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appTop,
        Scheme.Hom.resLE_app_top]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [Scheme.Hom.appLE_eq_app]
    rw [hφ]
    have hmem : f j ∈ i.ker.ideal U := hf ▸ Ideal.subset_span (Set.mem_range_self _)
    have hz : i.app U.1 (f j) = 0 := by
      change f j ∈ RingHom.ker (i.app U.1).hom
      simpa only [Scheme.Hom.ker_apply] using hmem
    change X.topIso.inv (i.app U.1 (f j)) = 0
    rw [hz, map_zero]
  have hE := affine_pullback_koszul_zero U t m f ht
  let c : ((Scheme.Modules.restrictFunctor U.1.ι).mapHomologicalComplex (.up ℤ)).obj
      K ≅ E :=
    (NatIso.mapHomologicalComplex
      (Scheme.Modules.restrictFunctorAdjCounitIso U.1.ι) (.up ℤ)).app E ≪≫
      (Functor.mapHomologicalComplexIdIso U.1.toScheme.Modules (.up ℤ)).app E
  -- The restricted immersion kills f, so its affine scalar extension has zero differential.
  let d := (NatIso.mapHomologicalComplex
    ((eqToIso (congrArg Scheme.Modules.tensorPullback ha)) ≪≫
      (Scheme.Modules.nonempty_tensorPullbackComp g t).some) (.up ℤ)).app E
  have hA (x y : ℤ) :
      (((Scheme.Modules.tensorPullback a).mapHomologicalComplex (.up ℤ)).obj E).d x y = 0 := by
    apply differential_zero_of_iso d
    intro p q
    change (Scheme.Modules.tensorPullback g).map
      ((((Scheme.Modules.tensorPullback t).mapHomologicalComplex (.up ℤ)).obj E).d p q) = 0
    rw [hE, Functor.map_zero]
  let O := Scheme.Modules.restrictFunctor V.ι ⋙
    SheafOfModules.overFunctor V.toScheme.ringCatSheaf W
  let := moduleOpenOver_preservesZeroMorphisms Z V W
  let R := (Scheme.Modules.overEquiv W).functor
  let H := Scheme.Modules.tensorPullback i ⋙ O
  let h : j ≫ i = a ≫ U.1.ι := by
    dsimp [j, a]
    simp only [Scheme.Hom.resLE_comp_ι, Category.assoc]
  let sq : Scheme.Modules.tensorPullback i ⋙ Scheme.Modules.restrictFunctor j ≅
      Scheme.Modules.restrictFunctor U.1.ι ⋙ Scheme.Modules.tensorPullback a :=
    (Functor.isoWhiskerLeft _ (tensorPullbackRestrictIso j)).symm ≪≫
      (Scheme.Modules.nonempty_tensorPullbackComp j i).some.symm ≪≫
      eqToIso (congrArg Scheme.Modules.tensorPullback h) ≪≫
      (Scheme.Modules.nonempty_tensorPullbackComp a U.1.ι).some ≪≫
      Functor.isoWhiskerRight (tensorPullbackRestrictIso U.1.ι) _
  -- The over-site equivalence detects zero morphisms after the open pullback square.
  let overComp : O ⋙ R ≅ Scheme.Modules.restrictFunctor j :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Scheme.Modules.overFunctorEquiv W) ≪≫
      (Scheme.Modules.restrictFunctorComp W.ι V.ι).symm
  let comparison : H ⋙ R ≅
      Scheme.Modules.restrictFunctor U.1.ι ⋙ Scheme.Modules.tensorPullback a :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ overComp ≪≫ sq
  let e := (NatIso.mapHomologicalComplex comparison (.up ℤ)).app K ≪≫
    ((Scheme.Modules.tensorPullback a).mapHomologicalComplex (.up ℤ)).mapIso c
  intro x y
  apply R.map_injective
  rw [R.map_zero]
  exact differential_zero_of_iso e hA x y

/-- A specified algebraic Koszul resolution gives a local K-flat resolution whose
restricted tensor pullback has bounded finite-free terms and zero differential.

Source: Stacks Project, Tag 068C, finite-free Koszul resolution; Tag 0BQY,
proof's local Koszul construction and quotient calculation.
(blueprint: new-s1-local-koszul-augmented-carrier).

Proof: Put A = Gamma(Y,U) and I = ker(i)(U). The closed immersion on U identifies
its source with Spec(A/I). Extend Q.pi to integer degrees and replace Q.complex
by the Koszul complex using hQ. Apply affine_koszul_finite_free_resolution to
this augmentation; it incorporates the quotient identification and sheafification.
The reindexing sends degree n to -n, with zero terms in positive cochain degrees.
This gives a complex B on U and a quasi-isomorphism to the
restriction of i_*O_Z in degree zero. Each exterior basis makes B^{-n} free of
rank binomial(m,n); exterior powers vanish for n > m. Thus B is bounded and
termwise flat, hence K-flat by the finite filtration by its single-degree terms.
Take K to be the termwise module pushforward of B along U.ι. The restriction of
this pushforward back to U is naturally isomorphic to B: sections over an open
of U are unchanged by the pushforward and restriction. Transport the augmentation
and K-flatness along this isomorphism. This construction needs no exactness or
K-flatness of the pushforward on all of Y.
On W = V intersect i^{-1}(U), restriction of i^*K is the tensor pullback of B
along the restricted immersion, followed by restriction to W's over site.
This follows termwise from the inverse-image and extension-of-scalars formula
for tensorPullback. Every generator f_j has zero image in the quotient, by hf,
so the pulled-back contraction differential is zero. Scalar extension and open
restriction take each displayed exterior basis to a basis over the new ring
sheaf. The bounds [-m,0] are preserved. For m=0 this is the degree-zero unit
complex; for an empty open or zero quotient the same bases describe zero
modules over the zero ring. No arbitrary choice of a zero model is used. -/
theorem exists_local_koszul_augmented_carrier
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [(Scheme.Modules.tensorPullback i).Additive]
    (V : Z.Opens) (U : Y.affineOpens) (m : ℕ) (f : Fin m → Γ(Y, U.1))
    (hf : Ideal.span (Set.range f) = i.ker.ideal U)
    (Q : ProjectiveResolution (ModuleCat.of (Γ(Y, U.1) : Type u)
      ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U)))
    (hQ : Q.complex = ExteriorAlgebra.koszulComplex (Γ(Y, U.1) : Type u) m f) :
    let F := (Scheme.Modules.restrictFunctor U.1.ι).mapHomologicalComplex (.up ℤ)
    let S := (HomologicalComplex.single Y.Modules (.up ℤ) 0).obj
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
    let G := (Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ) ⋙
      moduleOpenOverComplexFunctor Z V (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1))
    ∃ (K : CochainComplex Y.Modules ℤ) (b : F.obj K ⟶ F.obj S),
      CochainComplex.IsKFlatTensorResolution (R := U.1.toScheme.sheaf) b ∧
      (∀ x y : ℤ, (G.obj K).d x y = 0) ∧
      (∃ x y : ℤ, ∀ k : ℤ, k < x ∨ y < k → IsZero ((G.obj K).X k)) ∧
      (∀ k : ℤ, ∃ r : ℕ, Nonempty ((G.obj K).X k ≅
        SheafOfModules.free (R := V.toScheme.ringCatSheaf.over
          (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1))) (ULift.{u} (Fin r)))) := by
  classical
  let A := (Γ(Y, U.1) : Type u)
  let L := ExteriorAlgebra.koszulComplex A m f
  let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
  let E := (T.mapHomologicalComplex (.up ℤ)).obj
    (L.extend ComplexShape.embeddingDownNat)
  let P := (Scheme.Modules.pushforward U.1.ι).mapHomologicalComplex (.up ℤ)
  let F := (Scheme.Modules.restrictFunctor U.1.ι).mapHomologicalComplex (.up ℤ)
  let S := (HomologicalComplex.single Y.Modules (.up ℤ) 0).obj
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
  -- Extend the actual affine complex to Y; restriction recovers it by the open counit.
  let K := P.obj E
  let c : F.obj K ≅ E :=
    (NatIso.mapHomologicalComplex
      (Scheme.Modules.restrictFunctorAdjCounitIso U.1.ι) (.up ℤ)).app E ≪≫
      (Functor.mapHomologicalComplexIdIso U.1.toScheme.Modules (.up ℤ)).app E
  -- Extend the supplied augmentation, then use finite-free affine sheafification.
  let εQ := HomologicalComplex.extendMap Q.π ComplexShape.embeddingDownNat ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
      (ModuleCat.of A (A ⧸ i.ker.ideal U)) 0 0 (by simp)).hom
  have : QuasiIso εQ := by dsimp [εQ]; infer_instance
  have hL : Q.complex = L := hQ
  let ε : L.extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (ModuleCat A) 0).obj
        (ModuleCat.of A (A ⧸ i.ker.ideal U)) :=
    eqToHom (congrArg (fun C ↦ C.extend ComplexShape.embeddingDownNat) hL.symm) ≫ εQ
  have : QuasiIso ε := by dsimp [ε]; infer_instance
  obtain ⟨hbounded, hfree, a, ha⟩ := affine_koszul_finite_free_resolution i U m f ε
  let s := (HomologicalComplex.singleMapHomologicalComplex
    (Scheme.Modules.restrictFunctor U.1.ι) (.up ℤ) 0).app
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
  let b : F.obj K ⟶ F.obj S := c.hom ≫ a ≫ s.inv
  have : QuasiIso a := ha
  have hb : QuasiIso b := by dsimp [b]; infer_instance
  have hflat : ∀ k : ℤ, SheafOfModules.IsFlat (R := U.1.toScheme.sheaf)
      ((F.obj K).X k) := by
    intro k
    set_option synthInstance.maxSize 2048 in
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    have finiteFree_flat (Y : Scheme.{u})
        (M : Y.Modules)
        (hf : ∃ n : ℕ, Nonempty (M ≅ SheafOfModules.free
          (R := Y.ringCatSheaf) (ULift.{u} (Fin n)))) :
        SheafOfModules.IsFlat (R := Y.sheaf) M := by
      let := SheafOfModules.monoidalCategory Y.sheaf
      let := SheafOfModules.symmetricCategory Y.sheaf
      obtain ⟨n, ⟨e⟩⟩ := hf
      have hunit : SheafOfModules.IsFlat (R := Y.sheaf)
          (SheafOfModules.unit Y.ringCatSheaf) :=
        (ObjectProperty.flat_of_tensorIso
          (MonoidalCategory.leftUnitor (MonoidalCategory.tensorUnit
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))).2
      have hfree := SheafOfModules.isFlat_coproduct Y.sheaf
        (fun _ : ULift.{u} (Fin n) ↦ SheafOfModules.unit Y.ringCatSheaf)
        (fun _ ↦ hunit)
      exact (exactFunctor _ _).prop_of_iso
        ((MonoidalCategory.curriedTensor _).flip.mapIso e.symm) hfree
    apply finiteFree_flat U.1.toScheme
    obtain ⟨r, ⟨e⟩⟩ := hfree k
    exact ⟨r, ⟨(HomologicalComplex.eval U.1.toScheme.Modules (.up ℤ) k).mapIso c ≪≫ e⟩⟩
  have hbounded' : ∃ N : ℤ, ∀ k : ℤ, N < k → IsZero ((F.obj K).X k) := by
    obtain ⟨N, hN⟩ := hbounded
    exact ⟨N, fun k hk ↦ (hN k hk).of_iso
      ((HomologicalComplex.eval _ _ k).mapIso c)⟩
  refine ⟨K, b, ⟨hb, CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
    U.1.toScheme.toRingedSpace (F.obj K) hbounded' hflat⟩, ?_, ?_, ?_⟩
  · exact local_koszul_pullback_zero i V U m f hf
  · let H := (Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ) ⋙
      moduleOpenOverComplexFunctor Z V (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1))
    refine ⟨-(m : ℤ), 0, ?_⟩
    intro k hk
    have hz : IsZero (E.X k) := by
      change IsZero (T.obj ((L.extend ComplexShape.embeddingDownNat).X k))
      apply T.map_isZero
      by_cases hp : 0 < k
      · apply L.isZero_extend_X
        intro q
        change -(q : ℤ) ≠ k
        omega
      · obtain ⟨q, hq⟩ := Int.exists_eq_neg_ofNat (by omega : k ≤ 0)
        have hm : m < q := by omega
        have hzero : IsZero (ModuleCat.of A (⋀[A]^q (Fin m →₀ A))) := by
          classical
          let b := (Finsupp.basisSingleOne :
            Module.Basis (Fin m) A (Fin m →₀ A)).exteriorPower q
          have hempty : IsEmpty (Set.powersetCard (Fin m) q) :=
            ⟨fun s ↦ by
              have hcard := Finset.card_le_univ s.val
              have hs : s.val.card = q := s.property
              simp only [Fintype.card_fin, hs] at hcard
              omega⟩
          have hsub : Subsingleton (⋀[A]^q (Fin m →₀ A)) :=
            b.repr.injective.subsingleton
          exact ModuleCat.isZero_of_subsingleton _
        exact hzero.of_iso (L.extendXIso ComplexShape.embeddingDownNat hq.symm)
    let := moduleOpenOver_preservesZeroMorphisms Z V (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1))
    exact ((Scheme.Modules.restrictFunctor V.ι ⋙
      SheafOfModules.overFunctor V.toScheme.ringCatSheaf
        (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1))).map_isZero
      ((Scheme.Modules.tensorPullback i).map_isZero
        ((Scheme.Modules.pushforward U.1.ι).map_isZero hz)))
  · intro k
    obtain ⟨r, ⟨e⟩⟩ := hfree k
    let e' := (HomologicalComplex.eval _ _ k).mapIso c ≪≫ e
    exact ⟨r, local_tensor_free i V U.1 (K.X k) r e'⟩

end AlgebraicGeometry
