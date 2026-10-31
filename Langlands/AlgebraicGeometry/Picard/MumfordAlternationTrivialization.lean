import Langlands.AlgebraicGeometry.Modules.PullbackTransport
import Langlands.AlgebraicGeometry.Modules.TensorPowerDistributivity
import Langlands.AlgebraicGeometry.Modules.TensorCoherenceMaps
import Langlands.AlgebraicGeometry.Picard.MumfordFiniteWeilAlternationReduction
import Langlands.AlgebraicGeometry.Picard.MumfordUnit
import Langlands.AlgebraicGeometry.Picard.PoincareSquare
import Langlands.AlgebraicGeometry.Picard.DualKernelPullback
import Langlands.AlgebraicGeometry.Picard.FiniteWeilFunctorialityProof
import Langlands.AlgebraicGeometry.Picard.RelativeDualMultiplication
import Langlands.AbelianScheme.RelativeGlobalUnits

/-! # A trivialization of the Mumford family along `[n]` with equal kernel restrictions -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

section Core

variable {Z W Y X : Scheme.{u}}

/-- The abstract comparison argument. Let `α'` be the trivialization of `(p ≫ mx)^* C`
obtained from `Ψ` and `R2`. Its restrictions along the sections `e` and `xs` of `pr` agree
under the unit comparison, provided global functions on `Y` come from `X` along `pr` and
the listed equations hold. These equations say that `R1`, `Ψ` and `R2` are compatible with
the rigidifications. -/
theorem transport_eq_of_constancy (C : Z.Modules) (pr : Y ⟶ X) [IsIso pr.appTop]
    (p : Y ⟶ Y) (mx m1 d : Y ⟶ Z) (sn : Y ⟶ W) (e xs : X ⟶ Y) (ε : W ⟶ Z)
    (hfs mn sw : Z ⟶ Z) (xl u0 : X ⟶ W)
    (R1 : (Scheme.Modules.pullback ε).obj (SheafOfModules.unit Z.ringCatSheaf) ⟶
      (Scheme.Modules.pullback ε).obj C) [IsIso R1]
    (Ψ : (Scheme.Modules.pullback hfs).obj C ⟶ (Scheme.Modules.pullback mn).obj C)
    (τ : (Scheme.Modules.pullback (𝟙 Z)).obj C ⟶ (Scheme.Modules.pullback sw).obj C)
    [IsIso τ]
    (R2 : (Scheme.Modules.pullback m1).obj C ⟶
      (Scheme.Modules.pullback m1).obj (SheafOfModules.unit Z.ringCatSheaf))
    (hC : IsLocallyFreeRankOne ((Scheme.Modules.pullback (d ≫ hfs)).obj C))
    (hO : IsLocallyFreeRankOne ((Scheme.Modules.pullback (sn ≫ ε)).obj
      (SheafOfModules.unit Z.ringCatSheaf)))
    (he : e ≫ pr = 𝟙 X) (hxs : xs ≫ pr = 𝟙 X)
    (hmx1 : mx ≫ hfs = p ≫ mx) (hmx2 : mx ≫ mn = m1)
    (hxsp : xs ≫ p = e) (hemx : e ≫ mx = xl ≫ ε)
    (hem1 : e ≫ m1 = u0 ≫ ε) (hxsd : xs ≫ d = xs ≫ mx) (hed : e ≫ d = u0 ≫ ε)
    (hdsw : (d ≫ hfs) ≫ sw = d ≫ mn)
    (hx1 : (xl ≫ ε) ≫ hfs = xl ≫ ε) (hx2 : (xl ≫ ε) ≫ mn = u0 ≫ ε)
    (h01 : (u0 ≫ ε) ≫ hfs = u0 ≫ ε) (h02 : (u0 ≫ ε) ≫ mn = u0 ≫ ε)
    (hxsw : (xl ≫ ε) ≫ sw = xs ≫ m1) (h0sw : (u0 ≫ ε) ≫ sw = u0 ≫ ε)
    (hq : (sn ≫ ε) ≫ sw = m1) (hxsn : xs ≫ sn = xl) (hesn : e ≫ sn = u0)
    (F1x : transport xl rfl rfl R1 ≫ transport (xl ≫ ε) hx1 hx2 Ψ =
      unitTransfer (xl ≫ ε) (u0 ≫ ε) ≫ transport u0 rfl rfl R1)
    (F1u : transport u0 rfl rfl R1 ≫ transport (u0 ≫ ε) h01 h02 Ψ = transport u0 rfl rfl R1)
    (F2 : transport u0 rfl rfl R1 ≫ transport e hem1 hem1 R2 = 𝟙 _)
    (ha : e ≫ (p ≫ mx) = xl ≫ ε) (hb : xs ≫ (p ≫ mx) = xl ≫ ε) :
    transport e ha hem1 (transport mx hmx1 hmx2 Ψ ≫ R2) ≫
        unitTransfer (u0 ≫ ε) (xs ≫ m1) =
      transport xs hb rfl (transport mx hmx1 hmx2 Ψ ≫ R2) := by
  -- the two constants
  obtain ⟨c2, hc2⟩ := exists_transport_eq_smul pr hC
    (transport d rfl rfl Ψ) (transport (d ≫ hfs) (Category.comp_id _) hdsw τ)
  obtain ⟨c1, hc1⟩ := exists_transport_eq_smul pr hO
    (transport sn rfl rfl R1 ≫ transport (sn ≫ ε) (Category.comp_id _) hq τ ≫ R2)
    (unitTransfer (sn ≫ ε) m1)
  -- auxiliary equations
  have hxd1 : xs ≫ (d ≫ hfs) = xl ≫ ε := by
    rw [← Category.assoc, hxsd, Category.assoc, hmx1, ← Category.assoc, hxsp, hemx]
  have hxd2 : xs ≫ (d ≫ mn) = xs ≫ m1 := by
    rw [← Category.assoc, hxsd, Category.assoc, hmx2]
  have hed1 : e ≫ (d ≫ hfs) = u0 ≫ ε := by rw [← Category.assoc, hed, h01]
  have hed2 : e ≫ (d ≫ mn) = u0 ≫ ε := by rw [← Category.assoc, hed, h02]
  have hxm1 : (xs ≫ mx) ≫ hfs = xl ≫ ε := by rw [← hxsd, Category.assoc]; exact hxd1
  have hxm2 : (xs ≫ mx) ≫ mn = xs ≫ m1 := by rw [Category.assoc, hmx2]
  have hxq : xs ≫ (sn ≫ ε) = xl ≫ ε := by rw [← Category.assoc, hxsn]
  have heq : e ≫ (sn ≫ ε) = u0 ≫ ε := by rw [← Category.assoc, hesn]
  -- specializations of the constancy statements
  have C2x := hc2 xs hxs hxd1 hxd2
  rw [transport_transport_eq d xs hxsd _ _ _ _ hxm1 hxm2,
    transport_transport_eq (d ≫ hfs) xs hxd1 _ _ _ _ (Category.comp_id _) hxsw] at C2x
  have C2e := hc2 e he hed1 hed2
  rw [transport_transport_eq d e hed _ _ _ _ h01 h02,
    transport_transport_eq (d ≫ hfs) e hed1 _ _ _ _ (Category.comp_id _) h0sw] at C2e
  have C1x := hc1 xs hxs hxq rfl
  rw [transport_comp xs hxq hxq rfl, transport_comp xs hxq rfl rfl,
    transport_transport_eq sn xs hxsn _ _ _ _ rfl rfl,
    transport_transport_eq (sn ≫ ε) xs hxq _ _ _ _ (Category.comp_id _) hxsw,
    transport_unitTransfer] at C1x
  have C1e := hc1 e he heq hem1
  rw [transport_comp e heq heq hem1, transport_comp e heq hem1 hem1,
    transport_transport_eq sn e hesn _ _ _ _ rfl rfl,
    transport_transport_eq (sn ≫ ε) e heq _ _ _ _ (Category.comp_id _) h0sw,
    transport_unitTransfer, unitTransfer_self] at C1e
  -- the two restrictions of the trivialization
  rw [transport_comp e ha hem1 hem1, transport_transport_eq mx e hemx _ _ _ _ hx1 hx2,
    transport_comp xs hb rfl rfl, transport_transport_eq mx xs rfl _ _ _ _ hxm1 hxm2, C2x]
  -- the product of the constants acts trivially
  have hc : (c2 * c1) • 𝟙 ((Scheme.Modules.pullback (u0 ≫ ε)).obj
      (SheafOfModules.unit Z.ringCatSheaf)) = 𝟙 _ := by
    have h1 : transport u0 rfl rfl R1 =
        c2 • (transport u0 rfl rfl R1 ≫
          transport (u0 ≫ ε) (Category.comp_id _) h0sw τ) := by
      rw [← Linear.comp_smul, ← C2e, F1u]
    rw [mul_smul, ← C1e, ← Category.assoc, ← Linear.smul_comp, ← h1, F2]
  rw [← cancel_epi (transport xl rfl rfl R1)]
  simp only [Category.assoc]
  rw [reassoc_of% F1x, reassoc_of% F2, unitTransfer_comp, Linear.smul_comp,
    Linear.comp_smul, C1x, ← mul_smul]
  calc unitTransfer (xl ≫ ε) (xs ≫ m1) =
      unitTransfer (xl ≫ ε) (u0 ≫ ε) ≫ 𝟙 _ ≫ unitTransfer (u0 ≫ ε) (xs ≫ m1) := by simp
    _ = unitTransfer (xl ≫ ε) (u0 ≫ ε) ≫ ((c2 * c1) • 𝟙 _) ≫
        unitTransfer (u0 ≫ ε) (xs ≫ m1) := by rw [hc]
    _ = (c2 * c1) • unitTransfer (xl ≫ ε) (xs ≫ m1) := by
      rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, unitTransfer_comp]

end Core

section Geometry

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- The automorphism of `A ×_S A` exchanging the two factors. -/
def mumfordSwap : (relativeSpace A.X.hom).obj A.X ⟶ (relativeSpace A.X.hom).obj A.X :=
  pullback.lift (pullback.snd A.X.hom A.X.hom) (pullback.fst A.X.hom A.X.hom)
    pullback.condition.symm

@[reassoc (attr := simp)]
lemma mumfordSwap_fst :
    mumfordSwap A ≫ pullback.fst A.X.hom A.X.hom = pullback.snd A.X.hom A.X.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma mumfordSwap_snd :
    mumfordSwap A ≫ pullback.snd A.X.hom A.X.hom = pullback.fst A.X.hom A.X.hom :=
  pullback.lift_snd _ _ _

/-- Addition on `A ×_S A` is invariant under exchanging the factors. -/
lemma mumfordSwap_addition : mumfordSwap A ≫ mumfordAddition A = mumfordAddition A := by
  let s : mumfordProduct A ⟶ mumfordProduct A := Over.homMk (mumfordSwap A) (by
    change mumfordSwap A ≫ pullback.fst A.X.hom A.X.hom ≫ A.X.hom =
      pullback.fst A.X.hom A.X.hom ≫ A.X.hom
    rw [mumfordSwap_fst_assoc, ← pullback.condition])
  have h1 : s ≫ mumfordFirst A = mumfordSecond A := by
    apply Over.OverMorphism.ext
    exact mumfordSwap_fst A
  have h2 : s ≫ mumfordSecond A = mumfordFirst A := by
    apply Over.OverMorphism.ext
    exact mumfordSwap_snd A
  change (s ≫ (mumfordFirst A * mumfordSecond A)).left = _
  rw [MonObj.comp_mul, h1, h2, mul_comm]
  rfl

@[reassoc (attr := simp)]
lemma mumfordSection_fst :
    mumfordSection A ≫ pullback.fst A.X.hom A.X.hom = 𝟙 A.X.left :=
  relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) A.X

@[reassoc (attr := simp)]
lemma mumfordSection_snd :
    mumfordSection A ≫ pullback.snd A.X.hom A.X.hom = A.X.hom ≫ unitSection A :=
  relativeSection_snd A.X.hom (unitSection A) (unitSection_comp A) A.X

/-- The map `T ×_S A → A ×_S A`, `(t, b) ↦ (b, b)`. -/
def mumfordDiagonal (T : Over S) :
    (relativeSpace A.X.hom).obj T ⟶ (relativeSpace A.X.hom).obj A.X :=
  pullback.lift (pullback.snd T.hom A.X.hom) (pullback.snd T.hom A.X.hom) rfl

@[reassoc (attr := simp)]
lemma mumfordDiagonal_fst (T : Over S) :
    mumfordDiagonal A T ≫ pullback.fst A.X.hom A.X.hom = pullback.snd T.hom A.X.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma mumfordDiagonal_snd (T : Over S) :
    mumfordDiagonal A T ≫ pullback.snd A.X.hom A.X.hom = pullback.snd T.hom A.X.hom :=
  pullback.lift_snd _ _ _

lemma unitPoint_left_comp_unitSection (T : Over S) :
    (1 : T ⟶ A.X).left ≫ A.X.hom ≫ unitSection A = (1 : T ⟶ A.X).left := by
  rw [← Category.assoc, Over.w, unitPoint_left]

/-- The section `e_T` of `T ×_S A` followed by a change of parameter. -/
lemma relativeSection_map {T U : Over S} (a : T ⟶ U) :
    (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T ≫
        (relativeSpace A.X.hom).map a =
      a.left ≫ (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app U :=
  ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).naturality a).symm

lemma mumfordSection_homFamilySpaceMap (f : A ⟶ A) {X : Scheme.{u}} (v : X ⟶ A.X.left) :
    (v ≫ mumfordSection A) ≫ (homFamilySpaceMap f).app A.X = v ≫ mumfordSection A := by
  rw [Category.assoc, relativeSection_homFamilySpaceMap]

lemma mumfordSection_swap {X : Scheme.{u}} (v : X ⟶ A.X.left) :
    (v ≫ mumfordSection A) ≫ mumfordSwap A =
      pullback.lift (v ≫ A.X.hom ≫ unitSection A) v (by simp) := by
  apply pullback.hom_ext <;> simp

variable (n : ℕ) {T : Over S}
  (x : T ⟶ (GroupScheme.kernel (groupHom (multiplication A (n : ℤ)))).X)

lemma kernelPoint_multiplication :
    (x ≫ (GroupScheme.kernelι (groupHom (multiplication A (n : ℤ)))).hom.hom) ≫
      (groupHom (multiplication A (n : ℤ))).hom.hom = 1 :=
  (GroupScheme.kernelPointsEquiv (groupHom (multiplication A (n : ℤ))) T x).property

lemma kernelPoint_multiplication_left :
    (x ≫ (GroupScheme.kernelι (groupHom (multiplication A (n : ℤ)))).hom.hom).left ≫
      (groupHom (multiplication A (n : ℤ))).hom.hom.left = (1 : T ⟶ A.X).left := by
  rw [← Over.comp_left, kernelPoint_multiplication]

lemma unitPoint_multiplication_left :
    (1 : T ⟶ A.X).left ≫ (groupHom (multiplication A (n : ℤ))).hom.hom.left =
      (1 : T ⟶ A.X).left := by
  rw [unitPoint_left, Category.assoc]
  exact congrArg (T.hom ≫ ·) (unitSection_hom (multiplication A (n : ℤ)))

/-- The translate `e_T + x` of the unit section is the point `(id, x)`. -/
lemma kernelShearSection_eq :
    (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T ≫
        kernelShear (multiplication A (n : ℤ)) (𝟙 T) x =
      pullback.lift (𝟙 T.left)
        (x ≫ (GroupScheme.kernelι (groupHom (multiplication A (n : ℤ)))).hom.hom).left
        (by rw [Category.id_comp, Over.w]) := by
  rw [relativeSection_kernelShear]
  rfl

end Geometry

section Points

/-! The point equations used in `transport_eq_of_constancy`, in exactly the form in which that
theorem states them. -/

variable {S : Scheme.{u}} (A : AbelianScheme S) (n : ℕ) {T : Over S}
  (x : T ⟶ (GroupScheme.kernel (groupHom (multiplication A (n : ℤ)))).X)

lemma kernelShearSection_projection :
    ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T ≫
        kernelShear (multiplication A (n : ℤ)) (𝟙 T) x) ≫
      (relativeProjection A.X.hom).app T = 𝟙 T.left := by
  rw [kernelShearSection_eq]
  exact pullback.lift_fst _ _ _

lemma kernelShearSection_homFamilySpaceMap :
    ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T ≫
        kernelShear (multiplication A (n : ℤ)) (𝟙 T) x) ≫
      (homFamilySpaceMap (multiplication A (n : ℤ))).app T =
    (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T := by
  rw [Category.assoc, kernelShear_homFamilySpaceMap, CategoryTheory.Functor.map_id,
    Category.id_comp, relativeSection_homFamilySpaceMap]

lemma kernelPoint_map_homFamilySpaceMap :
    (relativeSpace A.X.hom).map
        (x ≫ (GroupScheme.kernelι (groupHom (multiplication A (n : ℤ)))).hom.hom) ≫
      (homFamilySpaceMap (multiplication A (n : ℤ))).app A.X =
    (homFamilySpaceMap (multiplication A (n : ℤ))).app T ≫
      (relativeSpace A.X.hom).map
        (x ≫ (GroupScheme.kernelι (groupHom (multiplication A (n : ℤ)))).hom.hom) :=
  (homFamilySpaceMap (multiplication A (n : ℤ))).naturality _

lemma kernelPoint_map_multiplication :
    (relativeSpace A.X.hom).map
        (x ≫ (GroupScheme.kernelι (groupHom (multiplication A (n : ℤ)))).hom.hom) ≫
      (relativeSpace A.X.hom).map (groupHom (multiplication A (n : ℤ))).hom.hom =
    (relativeSpace A.X.hom).map (1 : T ⟶ A.X) := by
  rw [← CategoryTheory.Functor.map_comp, kernelPoint_multiplication]

lemma kernelShearSection_diagonal :
    ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T ≫
        kernelShear (multiplication A (n : ℤ)) (𝟙 T) x) ≫ mumfordDiagonal A T =
    ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T ≫
        kernelShear (multiplication A (n : ℤ)) (𝟙 T) x) ≫
      (relativeSpace A.X.hom).map
        (x ≫ (GroupScheme.kernelι (groupHom (multiplication A (n : ℤ)))).hom.hom) := by
  rw [kernelShearSection_eq]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, mumfordDiagonal_fst, relativeSpace_map_fst,
      pullback.lift_snd, pullback.lift_fst_assoc]
    exact (Category.id_comp _).symm
  · rw [Category.assoc, Category.assoc, mumfordDiagonal_snd, relativeSpace_map_snd]

lemma kernelShearSection_snd :
    ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T ≫
        kernelShear (multiplication A (n : ℤ)) (𝟙 T) x) ≫ pullback.snd T.hom A.X.hom =
    (x ≫ (GroupScheme.kernelι (groupHom (multiplication A (n : ℤ)))).hom.hom).left := by
  rw [kernelShearSection_eq]
  exact pullback.lift_snd _ _ _

lemma kernelShearSection_map_homFamilySpaceMap :
    ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T ≫
        kernelShear (multiplication A (n : ℤ)) (𝟙 T) x) ≫
      ((homFamilySpaceMap (multiplication A (n : ℤ))).app T ≫
        (relativeSpace A.X.hom).map
          (x ≫ (GroupScheme.kernelι (groupHom (multiplication A (n : ℤ)))).hom.hom)) =
    (x ≫ (GroupScheme.kernelι (groupHom (multiplication A (n : ℤ)))).hom.hom).left ≫
      mumfordSection A := by
  rw [← Category.assoc, kernelShearSection_homFamilySpaceMap]
  exact relativeSection_map A _

lemma unitSection_map_homFamilySpaceMap :
    (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T ≫
      ((homFamilySpaceMap (multiplication A (n : ℤ))).app T ≫
        (relativeSpace A.X.hom).map
          (x ≫ (GroupScheme.kernelι (groupHom (multiplication A (n : ℤ)))).hom.hom)) =
    (x ≫ (GroupScheme.kernelι (groupHom (multiplication A (n : ℤ)))).hom.hom).left ≫
      mumfordSection A := by
  rw [← Category.assoc, relativeSection_homFamilySpaceMap]
  exact relativeSection_map A _

lemma kernelPoint_mumfordSection_multiplication :
    ((x ≫ (GroupScheme.kernelι (groupHom (multiplication A (n : ℤ)))).hom.hom).left ≫
        mumfordSection A) ≫
      (relativeSpace A.X.hom).map (groupHom (multiplication A (n : ℤ))).hom.hom =
    (1 : T ⟶ A.X).left ≫ mumfordSection A := by
  rw [Category.assoc, relativeSection_map A (groupHom (multiplication A (n : ℤ))).hom.hom,
    ← Category.assoc, kernelPoint_multiplication_left]

lemma kernelPoint_mumfordSection_swap :
    ((x ≫ (GroupScheme.kernelι (groupHom (multiplication A (n : ℤ)))).hom.hom).left ≫
        mumfordSection A) ≫ mumfordSwap A =
    ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T ≫
        kernelShear (multiplication A (n : ℤ)) (𝟙 T) x) ≫
      (relativeSpace A.X.hom).map (1 : T ⟶ A.X) := by
  rw [mumfordSection_swap, kernelShearSection_eq]
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc, relativeSpace_map_fst, pullback.lift_fst_assoc,
      unitPoint_left, ← Category.assoc, Over.w]
    exact (Category.id_comp _).symm
  · rw [pullback.lift_snd, Category.assoc, relativeSpace_map_snd, pullback.lift_snd]

omit x in
lemma unitPoint_mumfordSection_multiplication :
    ((1 : T ⟶ A.X).left ≫ mumfordSection A) ≫
      (relativeSpace A.X.hom).map (groupHom (multiplication A (n : ℤ))).hom.hom =
    (1 : T ⟶ A.X).left ≫ mumfordSection A := by
  rw [Category.assoc, relativeSection_map A (groupHom (multiplication A (n : ℤ))).hom.hom,
    ← Category.assoc, unitPoint_multiplication_left]

omit n x in
lemma unitPoint_mumfordSection_swap :
    ((1 : T ⟶ A.X).left ≫ mumfordSection A) ≫ mumfordSwap A =
      (1 : T ⟶ A.X).left ≫ mumfordSection A := by
  rw [mumfordSection_swap]
  apply pullback.hom_ext
  · simp only [pullback.lift_fst, Category.assoc, mumfordSection_fst, Category.comp_id]
    exact unitPoint_left_comp_unitSection A T
  · simp only [pullback.lift_snd, Category.assoc, mumfordSection_snd]
    exact (unitPoint_left_comp_unitSection A T).symm

omit n x in
lemma unitSection_mumfordDiagonal :
    (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T ≫
        mumfordDiagonal A T =
      (1 : T ⟶ A.X).left ≫ mumfordSection A := by
  apply pullback.hom_ext
  · simp only [Category.assoc, mumfordDiagonal_fst, mumfordSection_fst, Category.comp_id]
    rw [relativeSection_snd, unitPoint_left]
  · simp only [Category.assoc, mumfordDiagonal_snd, mumfordSection_snd]
    rw [unitPoint_left_comp_unitSection, relativeSection_snd, unitPoint_left]

omit n x in
lemma unitSection_snd :
    (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T ≫
        pullback.snd T.hom A.X.hom =
      (1 : T ⟶ A.X).left := by
  rw [relativeSection_snd, unitPoint_left]

omit x in
lemma mumfordDiagonal_homFamilySpaceMap_swap :
    (mumfordDiagonal A T ≫ (homFamilySpaceMap (multiplication A (n : ℤ))).app A.X) ≫
        mumfordSwap A =
      mumfordDiagonal A T ≫
        (relativeSpace A.X.hom).map (groupHom (multiplication A (n : ℤ))).hom.hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, mumfordSwap_fst, homFamilySpaceMap_snd, relativeSpace_map_fst,
      mumfordDiagonal_snd_assoc, mumfordDiagonal_fst_assoc]
  · simp

omit n x in
lemma mumfordSection_snd_swap :
    (pullback.snd T.hom A.X.hom ≫ mumfordSection A) ≫ mumfordSwap A =
      (relativeSpace A.X.hom).map (1 : T ⟶ A.X) := by
  rw [mumfordSection_swap]
  apply pullback.hom_ext
  · simp only [pullback.lift_fst, relativeSpace_map_fst, unitPoint_left]
    rw [← Category.assoc, ← pullback.condition, Category.assoc]
  · rw [pullback.lift_snd, relativeSpace_map_snd]

end Points

section Swap

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})

/-- For `Q = (add^* P ⊗ fst^* M) ⊗ snd^* M`, an isomorphism `Q ≅ sw^* Q` when `sw` fixes
`add` and exchanges `fst` and `snd`. -/
def swapTensorIso {Z W : Scheme.{u}} (sw : Z ⟶ Z) (add fst snd : Z ⟶ W)
    (hadd : sw ≫ add = add) (hfst : sw ≫ fst = snd) (hsnd : sw ≫ snd = fst)
    (P M : W.Modules) :
    tensorObj (tensorObj ((Scheme.Modules.pullback add).obj P)
        ((Scheme.Modules.pullback fst).obj M)) ((Scheme.Modules.pullback snd).obj M) ≅
      (Scheme.Modules.pullback sw).obj (tensorObj (tensorObj
        ((Scheme.Modules.pullback add).obj P) ((Scheme.Modules.pullback fst).obj M))
          ((Scheme.Modules.pullback snd).obj M)) :=
  letI := preservation sw
  tensorAssociator _ _ _ ≪≫ tensorMapIso (Iso.refl _) (tensorComm _ _) ≪≫
    (tensorAssociator _ _ _).symm ≪≫
    tensorMapIso (tensorMapIso (compIso sw add add hadd P).symm
      (compIso sw fst snd hfst M).symm) (compIso sw snd fst hsnd M).symm ≪≫
    (tensorMapIso ((asIso (pullbackTensorComparison sw)).app
      ((Scheme.Modules.pullback add).obj P, (Scheme.Modules.pullback fst).obj M))
        (Iso.refl _)).symm ≪≫
    ((asIso (pullbackTensorComparison sw)).app
      (tensorObj ((Scheme.Modules.pullback add).obj P) ((Scheme.Modules.pullback fst).obj M),
        (Scheme.Modules.pullback snd).obj M)).symm

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- The carrier `C` of the Mumford family satisfies `C ≅ sw^* C` for the exchange `sw` of the
two factors of `A ×_S A`. -/
def mumfordSwapCarrierIso (N : RigidifiedLineBundle (unitSection A)) (M : LineBundle A.X.left)
    (evaluation : tensorObj N.obj.carrier M.obj ≅ structureSheaf A.X.left) :
    (Scheme.Modules.pullback (𝟙 _)).obj
        (mumfordBundle A preservation N M evaluation).obj.carrier ≅
      (Scheme.Modules.pullback (mumfordSwap A)).obj
        (mumfordBundle A preservation N M evaluation).obj.carrier :=
  (Scheme.Modules.pullbackId _).app _ ≪≫
    swapTensorIso preservation (mumfordSwap A) (mumfordAddition A)
      (pullback.fst A.X.hom A.X.hom) (pullback.snd A.X.hom A.X.hom) (mumfordSwap_addition A)
      (mumfordSwap_fst A) (mumfordSwap_snd A) N.obj.carrier M.obj

end Swap

section Main

open Langlands.SchemeModule

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (square : MumfordBundlePicardZeroStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] (A : AbelianScheme S)
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (L : LineBundle A.X.left) (B : LineBundle S)
  (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅
    structureSheaf S)
  (M : LineBundle A.X.left)
  (evaluation : tensorObj (LineBundle.normalize preservation A.X.hom (unitSection A)
    (unitSection_comp A) L B evaluationB).obj.carrier M.obj ≅ structureSheaf A.X.left)

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry

/-- If the Mumford map `φ` underlies a homomorphism, the `[n]`-pullback of the Mumford family
is isomorphic, as a rigidified family, to its pullback along the parameter map `[n]`: both are
pullbacks of the Poincaré family along `[n] ≫ φ`. -/
lemma mumfordMultiplicationPullback_nonempty (lam : A ⟶ DA)
    (hlam : (groupHom lam).hom.hom =
      mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA)
    (n : ℕ) :
    Nonempty ((homFamilyPullback (multiplication A (n : ℤ)) A.X).obj
        (mumfordFamilyOfLineBundle preservation A L B evaluationB M evaluation) ≅
      (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
        (groupHom (multiplication A (n : ℤ))).hom.hom).obj
        (mumfordFamilyOfLineBundle preservation A L B evaluationB M evaluation)) := by
  have hcomm : mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation
        square hA ≫ dualSchemeMap homPicardZeroPullback (multiplication A (n : ℤ)) hA hA =
      (groupHom (multiplication A (n : ℤ))).hom.hom ≫
        mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, ← hlam]
    have h := congrArg hom (relativeDualAbelianSchemeMap_multiplication preservation
      composition unitCoherence associativity comparison symmetry stability hA MA evaluationA
      geometryA (n : ℤ))
    rw [dualAbelianSchemeMapFromEvaluation_hom] at h
    rw [h]
    exact congrArg hom (multiplication_comp_hom lam (n : ℤ)).symm
  obtain ⟨i⟩ := dualPointFamily_dualSchemeMap_nonempty stability hA hA
    (multiplication A (n : ℤ))
    (mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA)
  let e := mumfordSchemeMapOfLineBundlePullbackIso preservation A L B evaluationB M evaluation
    square hA
  exact ⟨(homFamilyPullback (multiplication A (n : ℤ)) A.X).mapIso e.symm ≪≫ i.symm ≪≫
    eqToIso (congrArg (dualPointFamily A hA) hcomm) ≪≫
    (dualPointFamilyPullbackIso A hA (groupHom (multiplication A (n : ℤ))).hom.hom
      (mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA)).symm ≪≫
    (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
      (groupHom (multiplication A (n : ℤ))).hom.hom).mapIso e⟩

set_option maxHeartbeats 2000000 in
/-- If the Mumford map underlies a homomorphism `lam`, then for every point `x` of `A[n]` the
pulled-back Mumford module has a trivialization of its `[n]`-pullback whose restrictions along
the unit section and along its translate by `x` agree. -/
theorem mumfordKernelPointTrivialization_of_hom (lam : A ⟶ DA)
    (hlam : (groupHom lam).hom.hom =
      mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA)
    (n : ℕ) {T : Over S}
    (x : T ⟶ (GroupScheme.kernel (groupHom (multiplication A (n : ℤ)))).X) :
    MumfordKernelPointTrivialization preservation A L B evaluationB M evaluation n x := by
  obtain ⟨Ψiso⟩ := mumfordMultiplicationPullback_nonempty preservation square composition
    unitCoherence associativity comparison symmetry stability A hA geometryA MA evaluationA
    L B evaluationB M evaluation lam hlam n
  have := universalGlobalFunctions A T
  let Λ := mumfordFamilyOfLineBundle preservation A L B evaluationB M evaluation
  let Ψ : (Scheme.Modules.pullback ((homFamilySpaceMap (multiplication A (n : ℤ))).app A.X)).obj
      Λ.obj.carrier ⟶ (Scheme.Modules.pullback ((relativeSpace A.X.hom).map
        (groupHom (multiplication A (n : ℤ))).hom.hom)).obj Λ.obj.carrier :=
    Ψiso.hom.hom.val
  have : IsIso Ψ := Iso.isIso_hom
    ((RigidifiedLineBundle.forgetToRigidified _ ⋙ RigidifiedModule.forget _).mapIso Ψiso)
  let Z0 := mumfordZeroParameterIso A preservation
    (LineBundle.normalize preservation A.X.hom (unitSection A) (unitSection_comp A) L B
      evaluationB) M evaluation T
  let Φ0 : (Scheme.Modules.pullback ((relativeSpace A.X.hom).map (1 : T ⟶ A.X))).obj
      Λ.obj.carrier ⟶ SheafOfModules.unit ((relativeSpace A.X.hom).obj T).ringCatSheaf :=
    Z0.hom.hom.val
  have : IsIso Φ0 := Iso.isIso_hom
    ((RigidifiedLineBundle.forgetToRigidified _ ⋙ RigidifiedModule.forget _).mapIso Z0)
  have comm₁ : mumfordSection A ≫ (homFamilySpaceMap (multiplication A (n : ℤ))).app A.X =
      𝟙 _ ≫ mumfordSection A := by
    rw [relativeSection_homFamilySpaceMap, Category.id_comp]
  have F1x := transport_sectionMap_comp_of_hom_comp Λ.obj comm₁
    (relativeSection_map A (groupHom (multiplication A (n : ℤ))).hom.hom) Ψ
    Ψiso.hom.hom.property
    (x ≫ (GroupScheme.kernelι (groupHom (multiplication A (n : ℤ)))).hom.hom).left
    (Category.comp_id _) (kernelPoint_multiplication_left A n x)
    (mumfordSection_homFamilySpaceMap A _ _) rfl
    (kernelPoint_mumfordSection_multiplication A n x) rfl
  have F1u := transport_sectionMap_comp_of_hom_comp Λ.obj comm₁
    (relativeSection_map A (groupHom (multiplication A (n : ℤ))).hom.hom) Ψ
    Ψiso.hom.hom.property (1 : T ⟶ A.X).left
    (Category.comp_id _) (unitPoint_multiplication_left A n (T := T))
    (mumfordSection_homFamilySpaceMap A _ _) rfl
    (unitPoint_mumfordSection_multiplication A n (T := T)) rfl
  rw [unitTransfer_self, Category.id_comp] at F1u
  have F2 := transport_sectionMap_comp_of_trivial Λ.obj (relativeSection_map A (1 : T ⟶ A.X))
    Φ0 Z0.hom.hom.property (relativeSection_map A (1 : T ⟶ A.X)) rfl
  have core := transport_eq_of_constancy Λ.obj.carrier ((relativeProjection A.X.hom).app T)
    ((homFamilySpaceMap (multiplication A (n : ℤ))).app T)
    ((relativeSpace A.X.hom).map
      (x ≫ (GroupScheme.kernelι (groupHom (multiplication A (n : ℤ)))).hom.hom))
    ((relativeSpace A.X.hom).map (1 : T ⟶ A.X)) (mumfordDiagonal A T)
    (pullback.snd T.hom A.X.hom) _ _ (mumfordSection A) _ _ (mumfordSwap A) _ _
    (sectionMap Λ.obj) Ψ (mumfordSwapCarrierIso preservation A _ M evaluation).hom
    (Φ0 ≫ (pullbackUnitIso _).inv) (Λ.property.pullback _)
    ((LineBundle.trivial _).property.pullback _)
    (relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) T)
    (kernelShearSection_projection A n x) (kernelPoint_map_homFamilySpaceMap A n x)
    (kernelPoint_map_multiplication A n x) (kernelShearSection_homFamilySpaceMap A n x)
    (relativeSection_map A _) (relativeSection_map A (1 : T ⟶ A.X))
    (kernelShearSection_diagonal A n x) (unitSection_mumfordDiagonal A)
    (mumfordDiagonal_homFamilySpaceMap_swap A n) (mumfordSection_homFamilySpaceMap A _ _)
    (kernelPoint_mumfordSection_multiplication A n x) (mumfordSection_homFamilySpaceMap A _ _)
    (unitPoint_mumfordSection_multiplication A n) (kernelPoint_mumfordSection_swap A n x)
    (unitPoint_mumfordSection_swap A) (mumfordSection_snd_swap A) (kernelShearSection_snd A n x)
    (unitSection_snd A) F1x F1u F2 (unitSection_map_homFamilySpaceMap A n x)
    (kernelShearSection_map_homFamilySpaceMap A n x)
  exact ⟨_, equalCompositeUnitAut_eq_refl_of_transport _ _ _ _ _ _ _ _ _ _ rfl core⟩

end Main

end Langlands.AbelianScheme
