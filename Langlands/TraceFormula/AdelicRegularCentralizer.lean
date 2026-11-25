import Langlands.BaseChange.RegularCentralizer
import Langlands.TraceFormula.GeneralLinearWeilAdelicTwistStatement
import Langlands.Global.AdelicGroupLocalPoints
import Langlands.Global.FiniteAdelicGL.LocalFactor

/-! # Commutativity of regular rational adelic centralizers -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.GroupScheme Langlands.JacquetLanglands Langlands.BaseChange
open AdelicGroupAutomorphism

universe u

private theorem commute_of_inv_mul_conj_eq {G : Type*} [Group G] {x y : G}
    (h : x⁻¹ * y * x = y) : Commute x y := by
  change x * y = y * x
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using
    (congrArg (fun z => x * z) h).symm

private theorem commute_of_commute_with_regular_map {F E : Type*} [Field F] [Field E] {n : ℕ}
    (f : F →+* E) {g₀ : GeneralLinear n F} (hg₀ : IsRegularSemisimple g₀)
    {x y : GeneralLinear n E}
    (hx : Commute x (Matrix.GeneralLinearGroup.map f g₀))
    (hy : Commute y (Matrix.GeneralLinearGroup.map f g₀)) : Commute x y := by
  let a := Matrix.GeneralLinearGroup.map f g₀
  have hreg : IsRegularSemisimple a := by
    change (g₀.val.map f).charpoly.Separable
    rw [Matrix.charpoly_map]
    exact hg₀.map
  have hmem (z : GeneralLinear n E) (hz : Commute z a) : z ∈ glCentralizer a := by
    rwa [glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (glCentralizer_mul_comm hreg ⟨x, hmem x hx⟩ ⟨y, hmem y hy⟩)

section Adelic

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

private def adelicGLAtPlace (v : Place K) :
    AdelicGL K n →* GeneralLinear n (placeCompletion K v) :=
  Matrix.GeneralLinearGroup.map (adeleProjection K v).toRingHom

/-- A regular semisimple rational matrix has commutative adelic centralizer. -/
theorem adelicGL_commute_of_regular_rational_centralizer
    {g₀ : RationalGL K n} (hg₀ : IsRegularSemisimple g₀) {x y : AdelicGL K n}
    (hx : Commute x (AdelicGL.rational K n g₀)) (hy : Commute y (AdelicGL.rational K n g₀)) :
    Commute x y := by
  have hAt (v : Place K) :
      adelicGLAtPlace K n v (x * y) = adelicGLAtPlace K n v (y * x) := by
    let e := adelicGLAtPlace K n v
    change e (x * y) = e (y * x)
    rw [map_mul, map_mul]
    have h₁ := hx.map e
    have h₂ := hy.map e
    rcases v with v | v
    · exact commute_of_commute_with_regular_map (algebraMap K v.Completion) hg₀ h₁ h₂
    · exact commute_of_commute_with_regular_map
        (algebraMap K (Langlands.Global.FiniteCompletion K v)) hg₀ h₁ h₂
  change x * y = y * x
  apply Units.ext
  ext i j
  apply Prod.ext
  · funext v
    exact congrArg (fun a : GeneralLinear n (placeCompletion K (.inl v)) => a.val i j)
      (hAt (.inl v))
  · ext1 v
    exact congrArg (fun a : GeneralLinear n (placeCompletion K (.inr v)) => a.val i j)
      (hAt (.inr v))

private theorem isRegularSemisimple_of_finite_adelic_projection (v : Langlands.Global.FinitePlace K)
    (g₀ : RationalGL K n)
    (hg₀ : IsRegularElliptic (FiniteAdelicGL.localProjection K n v
      (AdelicGL.finite K n (AdelicGL.rational K n g₀)))) : IsRegularSemisimple g₀ := by
  have h := hg₀.isRegularSemisimple
  change (g₀.val.map (algebraMap K (Langlands.Global.FiniteCompletion K v))).charpoly.Separable at h
  rw [Matrix.charpoly_map] at h
  exact (Polynomial.separable_map _).mp h

end Adelic

private local instance (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

private local instance (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option maxRecDepth 2000 in
/-- A rational ordinary class qualifying in the simple trace formula has
commutative centralizer in the actual norm-one group. -/
def GeneralLinearRegularCentralizerCommutativeStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ) (v : Langlands.Global.FinitePlace K),
    let H := normOneSubgroup K GLₙ
    ∀ (r : rationalNormOneSubgroup K GLₙ),
      IsRegularElliptic (FiniteAdelicGL.localProjection K n v
        (AdelicGL.finite K n (GeneralLinearGroupPoints.adelicHomeomorph K n
          ((r : H) : AdelicGroupPoints K GLₙ)))) →
      ∀ x y : twistedCentralizer (MonoidHom.id H) (r : H), x * y = y * x

set_option maxRecDepth 2200 in
set_option maxHeartbeats 2000000 in
theorem generalLinearRegularCentralizerCommutative :
    GeneralLinearRegularCentralizerCommutativeStatement.{u} := by
  intro K _ _ n v H r hreg x y
  let E := GeneralLinearGroupPoints.adelicHomeomorph K n
  let e : H →* AdelicGL K n := E.toMonoidHom.comp H.subtype
  have he : Function.Injective e := E.injective.comp Subtype.val_injective
  have hr : ((r : H) : AdelicGroupPoints K GLₙ) ∈ rationalSubgroup K GLₙ :=
    (rationalNormOneSubgroupInclusion K GLₙ r).property
  obtain ⟨q, hq⟩ := hr
  let g₀ := GeneralLinearGroupPoints.rationalEquiv K n q
  have hE : e (r : H) = AdelicGL.rational K n g₀ := by
    change E ((r : H) : AdelicGroupPoints K GLₙ) = _
    rw [← hq, GeneralLinearGroupPoints.adelicHomeomorph_rational]
  have hg₀ : IsRegularSemisimple g₀ := by
    change IsRegularElliptic (FiniteAdelicGL.localProjection K n v
      (AdelicGL.finite K n (e (r : H)))) at hreg
    rw [hE] at hreg
    exact isRegularSemisimple_of_finite_adelic_projection K n v g₀ hreg
  have hCent (z : twistedCentralizer (MonoidHom.id H) (r : H)) :
      Commute (e z.val) (AdelicGL.rational K n g₀) := by
    have hz : z.val⁻¹ * (r : H) * z.val = (r : H) := z.property
    rw [← hE]
    exact (commute_of_inv_mul_conj_eq hz).map e
  apply Subtype.ext
  apply he
  change e (x.val * y.val) = e (y.val * x.val)
  rw [map_mul, map_mul]
  exact adelicGL_commute_of_regular_rational_centralizer K n hg₀ (hCent x) (hCent y)

section CyclicNorm

variable {G : Type*} [Group G]

private def orderedAutomorphismNorm (f : MulAut G) (l : ℕ) (x : G) : G :=
  ((List.range l).map fun i => (f ^ i) x).prod

private theorem orderedAutomorphismNorm_succ (f : MulAut G) (l : ℕ) (x : G) :
    orderedAutomorphismNorm f (l + 1) x = orderedAutomorphismNorm f l x * (f ^ l) x := by
  simp [orderedAutomorphismNorm, List.range_succ]

private theorem orderedAutomorphismNorm_twistedConj (f : MulAut G) (l : ℕ) (x z : G) :
    orderedAutomorphismNorm f l (x⁻¹ * z * f x) =
      x⁻¹ * orderedAutomorphismNorm f l z * (f ^ l) x := by
  induction l with
  | zero => simp [orderedAutomorphismNorm]
  | succ l ih =>
    rw [orderedAutomorphismNorm_succ, orderedAutomorphismNorm_succ, ih,
      map_mul, map_mul, map_inv, ← MulAut.mul_apply, ← pow_succ]
    group

end CyclicNorm

set_option hygiene false in
local notation "Wₙ" => weilGroup K L GLₙ

set_option maxRecDepth 2700 in
/-- A rational twisted class qualifying in the twisted simple trace formula
has commutative centralizer in the actual norm-one group. -/
def GeneralLinearTwistedRegularCentralizerCommutativeStatement : Prop :=
  GeneralLinearWeilAdelicTwistStatement.{u} →
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (n : ℕ),
    let H := normOneSubgroup K Wₙ
    let θ := normOneAut K (unitGaloisAut K L GLₙ σ)
    let Φ : AdelicGroupPoints K Wₙ → AdelicGL L n := fun g =>
      GeneralLinearGroupPoints.adelicHomeomorph L n
        (AdelicGroupPoints.map L (AffineWeil.unitBaseChange K L GLₙ)
          (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of L))
          (GroupScheme.GeneralLinear.baseChangeIso (Fin n) (Spec.algebraMap K L)).hom
          (AdelicGaloisUnit.weilAdelicEquiv K L GLₙ g))
    let N : AdelicGroupPoints K Wₙ → AdelicGroupPoints K Wₙ := fun g =>
      ((List.range l).map fun k => adelicAut K (unitGaloisAut K L GLₙ (σ ^ k)) g).prod
    ∀ (w : Langlands.Global.FinitePlace L) (r : rationalNormOneSubgroup K Wₙ),
      IsRegularElliptic (FiniteAdelicGL.localProjection L n w
        (AdelicGL.finite L n (Φ (N ((r : H) : AdelicGroupPoints K Wₙ))))) →
      ∀ x y : twistedCentralizer θ (r : H), x * y = y * x

set_option maxRecDepth 3200 in
set_option maxHeartbeats 4300000 in
theorem generalLinearTwistedRegularCentralizerCommutative :
    GeneralLinearTwistedRegularCentralizerCommutativeStatement.{u} := by
  intro hWeil K _ _ L _ _ _ _ σ l hσ n H θ Φ N w r hreg x y
  let A := AdelicGroupPoints K Wₙ
  let q : A := (r : H)
  let α := unitGaloisAutHom K L GLₙ
  let f : MulAut A := (adelicAut K (α σ)).toMulEquiv
  obtain ⟨⟨E, hE⟩, hTwist, hRat⟩ := hWeil K L n
  have hEΦ : ⇑E = Φ := hE
  have hRat' : ∃ a : RationalGL L n, AdelicGL.rational L n a = E q := by
    rw [hEΦ]
    exact (hRat q).mp (rationalNormOneSubgroupInclusion K Wₙ r).property
  obtain ⟨a, ha⟩ := hRat'
  have hf (j : ℕ) (z : A) : (f ^ j) z = adelicAut K (α (σ ^ j)) z := by
    induction j with
    | zero => rw [pow_zero, MulAut.one_apply, pow_zero, map_one, adelicAut_one_apply]
    | succ j ih =>
      rw [pow_succ' f, MulAut.mul_apply, ih, pow_succ' σ, map_mul, adelicAut_mul_apply]
      rfl
  have hfL (z : A) : (f ^ l) z = z := by
    rw [hf, hσ.pow_eq_one, map_one, adelicAut_one_apply]
  have hN (z : A) : N z = orderedAutomorphismNorm f l z := by
    change ((List.range l).map fun j => adelicAut K (α (σ ^ j)) z).prod =
      ((List.range l).map fun j => (f ^ j) z).prod
    congr 1
    apply List.map_congr_left
    intro j _
    exact (hf j z).symm
  have hNorm : E (N q) = AdelicGL.rational L n (cyclicNorm σ l a) := by
    change E (((List.range l).map fun j => adelicAut K (α (σ ^ j)) q).prod) = _
    rw [map_list_prod, cyclicNorm, map_list_prod, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro j _
    change E (adelicAut K (unitGaloisAut K L GLₙ (σ ^ j)) q) =
      AdelicGL.rational L n (entrywiseAut (σ ^ j) n a)
    calc
      _ = Φ (adelicAut K (unitGaloisAut K L GLₙ (σ ^ j)) q) := congrFun hEΦ _
      _ = AdelicGLTransport.adelicEquiv n (σ ^ j).toRingEquiv (Φ q) := hTwist _ _
      _ = AdelicGLTransport.adelicEquiv n (σ ^ j).toRingEquiv (AdelicGL.rational L n a) := by
        rw [ha, hEΦ]
      _ = _ := AdelicGLTransport.adelicEquiv_rational n (σ ^ j).toRingEquiv a
  have hNormReg : IsRegularSemisimple (cyclicNorm σ l a) := by
    apply isRegularSemisimple_of_finite_adelic_projection L n w
    rw [← hNorm, hEΦ]
    exact hreg
  let e : H →* AdelicGL L n := E.toMonoidHom.comp H.subtype
  have he : Function.Injective e := E.injective.comp Subtype.val_injective
  have hCent (z : twistedCentralizer θ (r : H)) :
      Commute (e z.val) (AdelicGL.rational L n (cyclicNorm σ l a)) := by
    let b : A := z.val
    have hb : b⁻¹ * q * f b = q :=
      congrArg (fun p : H => (p : A)) z.property
    have hn := orderedAutomorphismNorm_twistedConj f l b q
    rw [hb, hfL] at hn
    have hComm : Commute b (N q) := by
      rw [hN]
      exact commute_of_inv_mul_conj_eq hn.symm
    have hImage := hComm.map E
    rw [hNorm] at hImage
    exact hImage
  apply Subtype.ext
  apply he
  change e (x.val * y.val) = e (y.val * x.val)
  rw [map_mul, map_mul]
  exact adelicGL_commute_of_regular_rational_centralizer L n hNormReg (hCent x) (hCent y)

/-- The commutativity hypotheses for both norm-one geometric expansions. -/
def AdelicRegularCentralizerStatement : Prop :=
  GeneralLinearRegularCentralizerCommutativeStatement.{u} ∧
    GeneralLinearTwistedRegularCentralizerCommutativeStatement.{u}

theorem adelicRegularCentralizer : AdelicRegularCentralizerStatement.{u} :=
  ⟨generalLinearRegularCentralizerCommutative, generalLinearTwistedRegularCentralizerCommutative⟩

end Langlands.TraceFormula
