import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicBundlePolarizationDeterminationStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicBundleMumfordProof
import Langlands.AbelianScheme.MultiplicationIsogenyProof
import Langlands.AbelianScheme.IsogenyInverse
import Mathlib.Tactic.Abel

/-! # The cubic bundle determines the polarization -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Picard.LineBundle (IsoClasses isoClass pullbackHom)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} {A B : AbelianScheme S}
variable (P : Prerequisites.{u})

private abbrev overHom (f : A ⟶ B) : A.X ⟶ B.X := (groupHom f).hom.hom

/-- The four-term class, with the unit term making it invariant under twisting by
bundles from the base even when the base has nontrivial Picard group. -/
private def bundleCoboundary (q : IsoClasses P.preservation A.X.left)
    {Z : Over S} (x y : Z ⟶ A.X) : IsoClasses P.preservation Z.left :=
  pullbackHom P.preservation (x * y).left q *
    (pullbackHom P.preservation x.left q)⁻¹ *
    (pullbackHom P.preservation y.left q)⁻¹ *
    pullbackHom P.preservation (1 : Z ⟶ A.X).left q

private lemma bundleCoboundary_twist {Z : Over S} (x y : Z ⟶ A.X)
    (q : IsoClasses P.preservation A.X.left) (r : IsoClasses P.preservation S) :
    bundleCoboundary P (q * pullbackHom P.preservation A.X.hom r) x y =
      bundleCoboundary P q x y := by
  simp only [bundleCoboundary, map_mul, LineBundle.pullbackHom_comp, Over.w]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private lemma bundleCoboundary_pow {Z : Over S} (x y : Z ⟶ A.X)
    (q : IsoClasses P.preservation A.X.left) (k : ℕ) :
    bundleCoboundary P (q ^ k) x y = bundleCoboundary P q x y ^ k := by
  simp only [bundleCoboundary, map_pow, mul_pow, inv_pow]

private lemma bundleCoboundary_pullback (f : A ⟶ B) {Z : Over S} (x y : Z ⟶ A.X)
    (q : IsoClasses P.preservation B.X.left) :
    bundleCoboundary P (pullbackHom P.preservation (hom f) q) x y =
      bundleCoboundary P q (x ≫ overHom f) (y ≫ overHom f) := by
  have hmul := MonObj.mul_comp x y (overHom f)
  have hunit := MonObj.one_comp (X := Z) (overHom f)
  simp only [bundleCoboundary, LineBundle.pullbackHom_comp, ← Over.comp_left,
    hmul, hunit]

/-- Expanding the normalization, the Poincaré family of a Mumford map is given by
this four-term class over the original base. -/
private lemma familyPointClass_mumford_eq_coboundary (W : DualWitness A)
    (L : LineBundle A.X.left) (N : LineBundle S)
    (evN : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) N.obj ≅
      structureSheaf S)
    (M : LineBundle A.X.left)
    (evM : tensorObj (LineBundle.normalize P.preservation A.X.hom (unitSection A)
      (unitSection_comp A) L N evN).obj.carrier M.obj ≅ structureSheaf A.X.left)
    {Z : Over S} (x y : Z ⟶ A.X) :
    familyPointClass P.preservation A (poincareFamily A W.hasDual)
      (x ≫ mumfordSchemeMapOfLineBundle P.preservation A L N evN M evM P.square W.hasDual) y =
      bundleCoboundary P (isoClass P.preservation L) x y := by
  have hN : isoClass P.preservation N =
      (pullbackHom P.preservation (unitSection A) (isoClass P.preservation L))⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    exact LineBundle.isoClass_eq_of_iso (ObjectProperty.isoMk _ evN :
      LineBundle.tensor P.preservation ((LineBundle.pullback (unitSection A)).obj L) N ≅
        LineBundle.trivial S)
  have hM : isoClass P.preservation M =
      (isoClass P.preservation L *
        pullbackHom P.preservation A.X.hom (isoClass P.preservation N))⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    exact LineBundle.isoClass_eq_of_iso (ObjectProperty.isoMk _ evM :
      LineBundle.tensor P.preservation
        (LineBundle.tensor P.preservation L ((LineBundle.pullback A.X.hom).obj N)) M ≅
          LineBundle.trivial A.X.left)
  rw [← familyPointClass_relativePullback,
    familyPointClass_eq_of_iso P.preservation A
      (mumfordSchemeMapOfLineBundlePullbackIso P.preservation A L N evN M evM P.square
        W.hasDual), familyPointClass_mumfordFamily, isoClass_pullback_tensor]
  simp only [bundleCoboundary, ← LineBundle.pullbackHom_isoClass, hM, hN,
    map_mul, map_inv, LineBundle.pullbackHom_comp, ← Category.assoc, Over.w, unitPoint_left]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private lemma familyPointClass_cubic {g d n : ℕ} [QuasiSeparatedSpace S]
    (a : Datum P S g d n) {Z : Over S} (x y : Z ⟶ a.abelian.X) :
    familyPointClass P.preservation a.abelian (poincareFamily a.abelian a.dualWitness.hasDual)
      (x ≫ overHom (6 • a.polarization)) y =
      bundleCoboundary P (isoClass P.preservation a.cubicBundle) x y := by
  obtain ⟨N, evN, M, evM, hmap⟩ :=
    polarizationDiagonalMumford P.preservation P.square P.universality P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability S a.abelian
      a.dualWitness.hasDual a.dualWitness.geometry a.dualWitness.inverseBundle
      a.dualWitness.evaluation a.polarization a.polarized
  have h := familyPointClass_mumford_eq_coboundary P a.dualWitness
    a.canonicalBundle N evN M evM x y
  change mumfordSchemeMapOfLineBundle P.preservation a.abelian a.canonicalBundle N evN M evM
    P.square a.dualWitness.hasDual = overHom (2 • a.polarization) at hmap
  rw [hmap] at h
  have hcube : isoClass P.preservation a.cubicBundle =
      isoClass P.preservation a.canonicalBundle ^ 3 :=
    isoClass_tensorPow P.preservation a.canonicalBundle 3
  rw [hcube, bundleCoboundary_pow, ← h]
  simp only [overHom, groupHom_nsmul_hom, MonObj.comp_pow,
    familyPointClass_poincareFamily_pow_left P a.abelian a.dualWitness, ← pow_mul]

/-- The universal Poincaré comparison interprets the dual map as pullback in the
abelian variable. -/
private lemma familyPointClass_dualMap (WA : DualWitness A) (WB : DualWitness B)
    (f : A ⟶ B) {Z : Over S} (z : Z ⟶ (WB.dual P).X) (x : Z ⟶ A.X) :
    familyPointClass P.preservation A (poincareFamily A WA.hasDual)
      (z ≫ overHom (WA.map P WB f)) x =
    familyPointClass P.preservation B (poincareFamily B WB.hasDual) z (x ≫ overHom f) := by
  change familyPointClass P.preservation A (poincareFamily A WA.hasDual)
    (z ≫ dualSchemeMap homPicardZeroPullback f WA.hasDual WB.hasDual) x = _
  rw [← familyPointClass_relativePullback,
    familyPointClass_eq_of_iso P.preservation A
      (dualSchemeMapPullbackIso homPicardZeroPullback f WA.hasDual WB.hasDual)]
  let T := dualScheme B WB.hasDual
  change Z ⟶ T at z
  have hpair : (pairOver A z x).left ≫ (homFamilySpaceMap f).app T =
      (pairOver B z (x ≫ overHom f)).left := by
    apply pullback.hom_ext
    · rw [Category.assoc, homFamilySpaceMap_fst, pairOver_left, pairOver_left,
        pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, homFamilySpaceMap_snd, pairOver_left, pairOver_left,
        pullback.lift_snd_assoc, pullback.lift_snd, Over.comp_left]
  change isoClass P.preservation ((LineBundle.pullback (pairOver A z x).left).obj
    ((LineBundle.pullback ((homFamilySpaceMap f).app T)).obj
      ((RigidifiedLineBundle.forget _).obj (poincareFamily B WB.hasDual)))) = _
  exact isoClass_pullback_pullback P.preservation _ _ hpair _

private lemma eq_of_familyPointClass_eq (W : DualWitness A)
    (p q : A.X ⟶ (W.dual P).X)
    (h : ∀ {Z : Over S} (x y : Z ⟶ A.X),
      familyPointClass P.preservation A (poincareFamily A W.hasDual) (x ≫ p) y =
        familyPointClass P.preservation A (poincareFamily A W.hasDual) (x ≫ q) y) : p = q := by
  apply eq_of_nonempty_relativePullback_poincareFamily_iso A W.hasDual P.stability
  have hc := h (relativeFst A A.X) (relativeSnd A A.X)
  rw [← familyPointClass_relativePullback, ← familyPointClass_relativePullback,
    ← isoClass_forget_eq_familyPointClass, ← isoClass_forget_eq_familyPointClass] at hc
  obtain ⟨I⟩ := LineBundle.isoClass_eq_iff.mp hc
  exact RigidifiedLineBundle.nonempty_iso_of_forget_iso P.preservation
    ((relativeProjection A.X.hom).app A.X)
    (relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) A.X) I

/-- The polarization of a polarized finite-level datum is determined by its
cubic bundle up to a twist from the base. -/
theorem cubicBundlePolarizationDetermination : CubicBundlePolarizationDeterminationStatement.{u} := by
  intro P S _ g d n a b e N ⟨I⟩
  let f := e.hom
  let fDual := a.dualWitness.map P b.dualWitness f
  let lam : a.abelian ⟶ a.dualWitness.dual P := f ≫ b.polarization ≫ fDual
  have hc : pullbackHom P.preservation (hom f) (isoClass P.preservation b.cubicBundle) =
      isoClass P.preservation a.cubicBundle *
        pullbackHom P.preservation a.abelian.X.hom (isoClass P.preservation N) :=
    LineBundle.isoClass_eq_of_iso I
  have h6 : overHom (6 • a.polarization) = overHom (6 • lam) := by
    apply eq_of_familyPointClass_eq P a.dualWitness
    intro Z x y
    have hm : overHom (6 • lam) = overHom f ≫ overHom (6 • b.polarization) ≫ overHom fDual := by
      dsimp only [lam]
      rw [← Preadditive.comp_nsmul f (b.polarization ≫ fDual),
        ← Preadditive.nsmul_comp b.polarization fDual]
      rfl
    rw [hm, ← Category.assoc, ← Category.assoc, familyPointClass_dualMap P _ _ f,
      familyPointClass_cubic, familyPointClass_cubic, ← bundleCoboundary_pullback,
      hc, bundleCoboundary_twist]
  let m := GroupScheme.multiplication a.abelian.toGrp (6 : ℤ)
  have hm : GroupScheme.IsIsogeny m :=
    GroupScheme.multiplicationIsogeny S a.abelian.toGrp a.abelian.smooth a.abelian.proper
      a.abelian.geometricallyConnected 6 (by decide)
  have := hm.effectiveEpi
  have : Epi m.hom.hom := Over.epi_of_epi_left _
  have hcomp (v : a.abelian ⟶ a.dualWitness.dual P) :
      m.hom.hom ≫ overHom v = overHom (6 • v) := by
    change (GroupScheme.multiplication a.abelian.toGrp (6 : ℤ)).hom.hom ≫ overHom v = _
    simp only [GroupScheme.multiplication_hom, GrpObj.zpow_comp, Category.id_comp,
      overHom, groupHom_nsmul_hom]
    rfl
  have heq : overHom a.polarization = overHom lam :=
    (cancel_epi m.hom.hom).mp ((hcomp _).trans (h6.trans (hcomp _).symm))
  change a.polarization = lam
  exact Additive.toMul.injective (Grp.hom_ext _ _ heq)

end Langlands.AbelianScheme.PolarizedFiniteLevel
