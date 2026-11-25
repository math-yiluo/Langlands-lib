/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.AlgebraicGeometry.PoincareDuality.CompatiblePrimitiveRoots
import all WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueQuotient
import all WeilConjectures.AlgebraicGeometry.PoincareDuality.CompatibleIntegralRootBases
import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

/-! # Tensoring the finite root-power cokernel

Source: finite Kummer level, compatible root tower and tensor-cokernel argument.
(blueprint: lem-pur-finite-root-power-tensor).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory MonObj Limits Opposite
open scoped CategoryTheory.Obj
namespace AddCommGrpCat
private def intResidue (n : ℕ) : 𝟙_ Ab.{u + 1} ⟶ of (ULift.{u + 1} (ZMod n)) :=
  ofHom ((AddEquiv.ulift.symm.toAddMonoidHom).comp
    ((Int.castAddHom (ZMod n)).comp AddEquiv.ulift.toAddMonoidHom))
private theorem intResidue_condition (n : ℕ) : (n • 𝟙 (𝟙_ Ab.{u + 1})) ≫ intResidue n = 0 := by
  ext x
  change ((n • x.down : ℤ) : ZMod n) = 0
  simp
private noncomputable def intResidueCokernel (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (intResidue.{u} n) (intResidue_condition n)) := by
  have : Epi (intResidue.{u} n) := by
    rw [epi_iff_surjective]
    intro a
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective a.down
    exact ⟨ULift.up b, congrArg ULift.up hb⟩
  let S := ShortComplex.mk (n • 𝟙 (𝟙_ Ab.{u + 1})) (intResidue.{u} n)
    (intResidue_condition n)
  have hS : S.Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro a ha
    have h : (a.down : ZMod n) = 0 := congrArg ULift.down ha
    obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
    refine ⟨ULift.up b, ?_⟩
    apply ULift.ext
    exact (show (n : ℤ) * b = a.down from hb.symm)
  exact hS.gIsCokernel
end AddCommGrpCat

namespace AlgebraicGeometry.ProEtale

private def freeUnitIso {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    (Mod.freeFunctor R).obj (𝟙_ _) ≅ Mod.regular R :=
  Mod.isoMk (ρ_ R) (by
    change ((α_ R R (𝟙_ _)).inv ≫ μ[R] ▷ (𝟙_ _)) ≫ (ρ_ R).hom =
      R ◁ (ρ_ R).hom ≫ μ[R]
    rw [Category.assoc, rightUnitor_naturality]
    monoidal)

private instance freeFunctorAdditive {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    (Mod.freeFunctor R).Additive :=
  { map_add := by
      intro A B f g
      apply Mod.hom_ext
      exact MonoidalPreadditive.whiskerLeft_add f g }

private theorem freeConstantResidue_isIso {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (n : ℕ) (hR : n • 𝟙 R = 0) :
    IsIso ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙ Mod.freeFunctor R).map
      (AddCommGrpCat.intResidue n)) := by
  let F := constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙ Mod.freeFunctor R
  let e : F.obj (𝟙_ Ab.{u + 1}) ≅ Mod.regular R :=
    (Mod.freeFunctor R).mapIso
      (Functor.Monoidal.εIso (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1})).symm ≪≫
        freeUnitIso R
  have : (Mod.freeFunctor R).IsLeftAdjoint := ⟨_, ⟨Mod.freeForgetAdjunction R⟩⟩
  let c := CokernelCofork.ofπ (AddCommGrpCat.intResidue.{u} n)
    (AddCommGrpCat.intResidue_condition n)
  have hzero : F.map (n • 𝟙 (𝟙_ Ab.{u + 1})) = 0 := by
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    apply (cancel_mono e.hom).mp
    rw [Preadditive.nsmul_comp, Category.id_comp, zero_comp]
    have hh : n • 𝟙 (Mod.regular R) = 0 := by
      apply (Mod.forget R).map_injective
      rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
      change n • 𝟙 R = 0
      exact hR
    calc
      n • e.hom = e.hom ≫ (n • 𝟙 _) := by
        rw [Preadditive.comp_nsmul, Category.comp_id]
      _ = 0 := by rw [hh, comp_zero]
  have : IsIso (F.map (AddCommGrpCat.intResidue n)) :=
    CokernelCofork.IsColimit.isIso_π (c.map F)
      (c.mapIsColimit (AddCommGrpCat.intResidueCokernel n) F) hzero
  infer_instance

private def freePullIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    Mod.freeFunctor R ⋙ (upperStar Ab.{u + 1} f).mapMod R ≅
      upperStar Ab.{u + 1} f ⋙ Mod.freeFunctor ((upperStar Ab.{u + 1} f).obj R) := by
  let adj := upperStarLowerStarAdjunction Ab.{u + 1} f
  exact ((Mod.freeForgetAdjunction R).comp (adj.mapModAdjunction R)).leftAdjointUniq
    (adj.comp (Mod.freeForgetAdjunction ((upperStar Ab.{u + 1} f).obj R)))


private theorem freeResidueReduction_isIso {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (l j : ℕ) (hj : (l ^ j) • 𝟙 R = 0) :
    IsIso ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙ Mod.freeFunctor R).map
      (integralResidueAbTransition l j)) := by
  let F := constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙ Mod.freeFunctor R
  have hz (n : ℕ) (hn : n • 𝟙 R = 0) : IsIso (F.map (AddCommGrpCat.intResidue n)) := by
    exact freeConstantResidue_isIso R n hn
  have hj' : l ^ (j + 1) • 𝟙 R = 0 := by
    rw [pow_succ', mul_smul, hj, smul_zero]
  have := hz (l ^ j) hj
  have := hz (l ^ (j + 1)) hj'
  have hc : AddCommGrpCat.intResidue.{u} (l ^ (j + 1)) ≫
      integralResidueAbTransition l j = AddCommGrpCat.intResidue (l ^ j) := by
    ext x
    change ZMod.castHom (pow_dvd_pow l (Nat.le_add_right j 1)) _
      (x.down : ZMod (l ^ (j + 1))) = (x.down : ZMod (l ^ j))
    simp
  have he : F.map (AddCommGrpCat.intResidue (l ^ (j + 1))) ≫
      F.map (integralResidueAbTransition l j) =
      F.map (AddCommGrpCat.intResidue (l ^ j)) := by rw [← F.map_comp, hc]
  have : IsIso (F.map (AddCommGrpCat.intResidue (l ^ (j + 1))) ≫
      F.map (integralResidueAbTransition l j)) := he ▸ inferInstance
  exact IsIso.of_isIso_comp_left (F.map (AddCommGrpCat.intResidue (l ^ (j + 1)))) _

private def rawPower (X : Scheme.{u}) (l r k : ℕ) :
    rootsOfUnityPresheaf X (l ^ (r + k)) ⟶ rootsOfUnityPresheaf X (l ^ r) :=
  eqToHom (congrArg (rootsOfUnityPresheaf X)
    (by rw [pow_add, Nat.mul_comm] : l ^ (r + k) = l ^ k * l ^ r)) ≫
      Functor.whiskerLeft ((Scheme.ProEt.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ)
        (CommRingCat.rootsOfUnityPow (l ^ r) (l ^ k))

private theorem rootCast_val {X : Scheme.{u}} {a b : ℕ} (h : a = b)
    (U : X.ProEtᵒᵖ) (x : (rootsOfUnityPresheaf X a).obj U) :
    ((eqToHom (congrArg (rootsOfUnityPresheaf X) h)).app U x).down.toMul.val.val =
      x.down.toMul.val.val := by
  subst b
  rfl

private theorem rawPower_val (X : Scheme.{u}) (l r k : ℕ)
    (U : X.ProEtᵒᵖ) (x : (rootsOfUnityPresheaf X (l ^ (r + k))).obj U) :
    ((rawPower X l r k).app U x).down.toMul.val.val =
      x.down.toMul.val.val ^ (l ^ k) := by
  change (((eqToHom (congrArg (rootsOfUnityPresheaf X)
    (by rw [pow_add, Nat.mul_comm] : l ^ (r + k) = l ^ k * l ^ r))).app U x
      ).down.toMul.val.val) ^ (l ^ k) = _
  exact congrArg (fun z ↦ z ^ (l ^ k))
    (rootCast_val (by rw [pow_add, Nat.mul_comm] : l ^ (r + k) = l ^ k * l ^ r) U x)

private theorem rawPower_zero (X : Scheme.{u}) (l r : ℕ) :
    rawPower X l r 0 = 𝟙 _ := by
  ext U x
  apply ULift.ext
  apply Subtype.ext
  apply Units.ext
  change ((rawPower X l r 0).app U x).down.toMul.val.val = x.down.toMul.val.val
  simpa only [pow_zero, pow_one] using rawPower_val X l r 0 U x

private theorem rawPower_succ (X : Scheme.{u}) (l r k : ℕ) :
    rawPower X l r (k + 1) = rawPower X l (r + k) 1 ≫ rawPower X l r k := by
  ext U x
  apply ULift.ext
  apply Subtype.ext
  apply Units.ext
  change ((rawPower X l r (k + 1)).app U x).down.toMul.val.val =
    ((rawPower X l r k).app U ((rawPower X l (r + k) 1).app U x)).down.toMul.val.val
  rw [rawPower_val, rawPower_val, rawPower_val, pow_one, ← pow_mul, pow_succ']
  rfl

private def rawDiagram (X : Scheme.{u}) (l : ℕ) :
    ℕᵒᵖ ⥤ X.ProEtᵒᵖ ⥤ Ab.{u + 1} :=
  Functor.ofOpSequence (X := fun r ↦ rootsOfUnityPresheaf X (l ^ r))
    (fun r ↦ rawPower X l r 1)

private theorem rawDiagram_map (X : Scheme.{u}) (l r k : ℕ) :
    (rawDiagram X l).map (homOfLE (show r ≤ r + k by omega)).op =
      rawPower X l r k := by
  induction k with
  | zero =>
    change (rawDiagram X l).map (𝟙 (op r)) = _
    rw [CategoryTheory.Functor.map_id, rawPower_zero]
    rfl
  | succ k ih =>
    have hm : (homOfLE (show r ≤ r + (k + 1) by omega)).op =
        (homOfLE (show r + k ≤ r + k + 1 by omega)).op ≫
          (homOfLE (show r ≤ r + k by omega)).op := Subsingleton.elim _ _
    rw [hm, Functor.map_comp, ih]
    simp only [rawDiagram, Functor.ofOpSequence_map_homOfLE_succ]
    change rawPower X l (r + k) 1 ≫ rawPower X l r k = _
    exact (rawPower_succ X l r k).symm

private def rawStep (X : Scheme.{u}) (l r : ℕ) :
    rootsOfUnityPresheaf X (l ^ (r + 1)) ⟶ rootsOfUnityPresheaf X (l ^ r) :=
  eqToHom (congrArg (rootsOfUnityPresheaf X) (pow_succ' l r)) ≫
    Functor.whiskerLeft ((Scheme.ProEt.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ)
      (CommRingCat.rootsOfUnityPow (l ^ r) l)

private theorem rawStep_val (X : Scheme.{u}) (l r : ℕ)
    (U : X.ProEtᵒᵖ) (x : (rootsOfUnityPresheaf X (l ^ (r + 1))).obj U) :
    ((rawStep X l r).app U x).down.toMul.val.val = x.down.toMul.val.val ^ l := by
  change (((eqToHom (congrArg (rootsOfUnityPresheaf X) (pow_succ' l r))).app U x
    ).down.toMul.val.val) ^ l = _
  exact congrArg (fun z ↦ z ^ l) (rootCast_val (pow_succ' l r) U x)

private theorem rawPower_one (X : Scheme.{u}) (l r : ℕ) :
    rawPower X l r 1 = rawStep X l r := by
  ext U x
  apply ULift.ext
  apply Subtype.ext
  apply Units.ext
  change ((rawPower X l r 1).app U x).down.toMul.val.val =
    ((rawStep X l r).app U x).down.toMul.val.val
  rw [rawPower_val, rawStep_val, pow_one]

private def rawDiagramIso (X : Scheme.{u}) (l : ℕ) :
    rawDiagram X l ⋙ presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1} ≅
      tateRootsSystem X l := by
  let t : rawDiagram X l ⋙ presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⟶
      tateRootsSystem X l := NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (fun n ↦ by
        simp only [rawDiagram, tateRootsSystem, Functor.comp_map,
          Functor.ofOpSequence_map_homOfLE_succ, Category.id_comp, Category.comp_id]
        rw [rawPower_one]
        simp [rawStep, rootsOfUnitySheafPow, Functor.map_comp, eqToHom_map])
  have : ∀ n, IsIso (t.app n) := fun _ ↦ inferInstanceAs (IsIso (𝟙 _))
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

private theorem rootPower_map {X : Scheme.{u}} (l r k : ℕ) :
    (tateRootsSystem X l).map (homOfLE (show r ≤ r + k by omega)).op =
      eqToHom (by rw [← pow_add, Nat.add_comm] :
        rootsOfUnitySheaf X (l ^ (r + k)) = rootsOfUnitySheaf X (l ^ k * l ^ r)) ≫
          rootsOfUnitySheafPow X (l ^ r) (l ^ k) := by
  have h := (rawDiagramIso X l).hom.naturality
    (homOfLE (show r ≤ r + k by omega)).op
  change (presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
      ((rawDiagram X l).map _) ≫ 𝟙 _ = 𝟙 _ ≫ _ at h
  rw [Category.comp_id, Category.id_comp, rawDiagram_map] at h
  rw [← h]
  simp only [rawPower, Functor.map_comp, eqToHom_map, rootsOfUnitySheafPow]

/-- The specified root-power map becomes invertible after tensoring with coefficients
annihilated by its target exponent.

Source: lem-pur-finite-kummer-level.proof.md, root-tower exact sequence and its tensor
cokernel. Proof: a compatible-root cover identifies the whole root diagram with the
constant residue diagram. Integer reduction presents each cyclic group as a cokernel.
The free coefficient module functor preserves this cokernel. Its relation is zero when
the modulus kills the coefficient ring. Thus both integer-to-cyclic quotient arrows are
isomorphisms after applying that functor, and their commuting triangle makes every
residue transition an isomorphism. Naturality of the diagram basis gives the assertion
on the cover. The monoidal free-module pullback comparison and conservativity of
covering restrictions descend it. This includes k=0 and the empty scheme.
(blueprint: lem-pur-finite-root-power-tensor). -/
theorem free_rootPower_isIso (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (hl : IsUnit (l : Γ(X, ⊤)))
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (m r k : ℕ) (hm : m = (r + 1) + k) (hR : (l ^ (r + 1)) • 𝟙 R = 0) :
    IsIso ((Mod.freeFunctor R).map
      (eqToHom (by rw [hm, ← pow_add]; congr 2; omega :
        rootsOfUnitySheaf X (l ^ m) =
          rootsOfUnitySheaf X (l ^ k * l ^ (r + 1))) ≫
            rootsOfUnitySheafPow X (l ^ (r + 1)) (l ^ k))) := by
  subst m
  rw [← rootPower_map]
  let q := (tateRootsSystem X l).map
    (homOfLE (show r + 1 ≤ (r + 1) + k by omega)).op
  obtain ⟨𝒰, h𝒰⟩ := exists_compatible_roots_diagram_basis X l hl
  have hweak (i : 𝒰.I₀) : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk i)
  suffices IsIso ((Mod.forget R).map ((Mod.freeFunctor R).map q)) from
    isIso_of_reflects_iso _ (Mod.forget R)
  apply isIso_of_isIso_localizationRestriction Ab.{u + 1} _ 𝒰.f 𝒰.mem₀
  intro i
  let F := upperStar Ab.{u + 1} (𝒰.f i)
  let G := Mod.freeFunctor (F.obj R)
  let D := constantTateResidueSystem X l ⋙ F ⋙ G
  have hstep (j : ℕ) (hj : r + 1 ≤ j) :
      IsIso (D.map (homOfLE (show j ≤ j + 1 by omega)).op) := by
    have hjR : l ^ j • 𝟙 R = 0 := by
      obtain ⟨d, hd⟩ := pow_dvd_pow l hj
      rw [hd, mul_comm, mul_smul, hR, smul_zero]
    let s := (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
      (integralResidueAbTransition l j)
    have : IsIso ((Mod.freeFunctor R).map s) := freeResidueReduction_isIso R l j hjR
    have hs : IsIso ((Mod.freeFunctor R ⋙ F.mapMod R).map s) := by
      change IsIso ((F.mapMod R).map ((Mod.freeFunctor R).map s))
      infer_instance
    have ht := (NatIso.isIso_map_iff (freePullIso (𝒰.f i) R) s).1 hs
    simpa only [D, constantTateResidueSystem, Functor.comp_map,
      Functor.ofOpSequence_map_homOfLE_succ] using ht
  have hres (a : ℕ) :
      IsIso (D.map (homOfLE (show r + 1 ≤ (r + 1) + a by omega)).op) := by
    induction a with
    | zero =>
      change IsIso (D.map (𝟙 (op (r + 1))))
      infer_instance
    | succ a ih =>
      have hm : (homOfLE (show r + 1 ≤ (r + 1) + (a + 1) by omega)).op =
          (homOfLE (show (r + 1) + a ≤ (r + 1) + a + 1 by omega)).op ≫
            (homOfLE (show r + 1 ≤ (r + 1) + a by omega)).op := Subsingleton.elim _ _
      rw [hm, Functor.map_comp]
      have := hstep ((r + 1) + a) (by omega)
      infer_instance
  obtain ⟨e⟩ := h𝒰 i
  have hroot : IsIso ((tateRootsSystem X l ⋙ F ⋙ G).map
      (homOfLE (show r + 1 ≤ (r + 1) + k by omega)).op) :=
    (NatIso.isIso_map_iff (Functor.isoWhiskerRight e G)
      (homOfLE (show r + 1 ≤ (r + 1) + k by omega)).op).2 (hres k)
  have hfree : IsIso (((Mod.freeFunctor R ⋙ F.mapMod R)).map q) :=
    (NatIso.isIso_map_iff (freePullIso (𝒰.f i) R) q).2 hroot
  have hfree' : IsIso ((F.mapMod R).map ((Mod.freeFunctor R).map q)) := hfree
  have hab : IsIso (F.map ((Mod.freeFunctor R).map q).hom) :=
    inferInstanceAs (IsIso ((Mod.forget _).map
      (((F.mapMod R)).map ((Mod.freeFunctor R).map q))))
  exact (NatIso.isIso_map_iff
    (upperStarIsoLocalizationRestriction Ab.{u + 1} (𝒰.f i) (hweak i)) _).1 hab

end AlgebraicGeometry.ProEtale
