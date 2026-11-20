import Langlands.GroupScheme.HomScheme.AdicTorsionRestriction
import Langlands.GroupScheme.Torus.DiagonalizableTorsionDensity
import Langlands.GroupScheme.Torus.RelativeTorusMultiplicativeType

/-! # Recovery of torus maps on unbounded torsion orders -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.AdicAffinePoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

open TorsionDetermination

variable {S : Scheme.{u}} {H : GroupScheme S} {Z : Scheme.{u}}

private def FactorsTorsion (P : ℕ → Prop) (j : Z ⟶ H.X.left) : Prop :=
  ∀ n : ℕ, P n → ∀ {T : Over S} (x : T ⟶ H.X), x ^ n = 1 → PointLifts j x

private theorem FactorsTorsion.baseChange (P : ℕ → Prop) (j : Z ⟶ H.X.left)
    (h : FactorsTorsion P j) {S' : Scheme.{u}} (b : S' ⟶ S) :
    FactorsTorsion P (baseChangeι b H j) := by
  intro n hn T x hx
  apply (lifts_baseChange_iff b H j x).mpr
  apply h n hn
  rw [← map_pow, hx, map_one]

private theorem FactorsTorsion.pullback (P : ℕ → Prop) (j : Z ⟶ H.X.left)
    (h : FactorsTorsion P j) {D : GroupScheme S} (a : D ⟶ H) :
    FactorsTorsion P (pullback.snd j a.hom.hom.left) := by
  intro n hn T x hx
  apply (lifts_pullback_iff a j x).mpr
  apply h n hn
  rw [← MonObj.pow_comp, hx, MonObj.one_comp]

private theorem factors_one_separates_free_lattice (R : CommRingCat.{u})
    (L : Type u) [Fintype L] (a : AddMonoidAlgebra R (L → ℤ)) (ha : a ≠ 0) :
    ∃ M : ℕ, ∀ n : ℕ, 1 ∣ n → M < n →
      AddMonoidAlgebra.mapDomain
        (QuotientAddGroup.mk' (TorsionDensity.multiples (L → ℤ) n)) a ≠ 0 := by
  obtain ⟨N, -, hN, hsep⟩ := TorsionDensity.exists_separating (L → ℤ)
  have hN' : N = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd hne
    obtain ⟨x, hx, hpx⟩ := hN p hp hpN
    apply hx
    funext l
    have hl : (p : ℤ) * x l = 0 := by
      simpa only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply] using congrFun hpx l
    exact (mul_eq_zero.mp hl).resolve_left (by exact_mod_cast hp.ne_zero)
  subst N
  exact hsep R a ha

set_option maxHeartbeats 900000 in
private theorem isIso_of_factorsTorsion_splitAffine (R : CommRingCat.{u})
    {H : GroupScheme (Spec R)} (hH : IsSplitTorus H) {Z : Scheme.{u}}
    (j : Z ⟶ H.X.left) [IsClosedImmersion j]
    (P : ℕ → Prop) (hP : ∀ M : ℕ, ∃ n, P n ∧ M < n) (h : FactorsTorsion P j) :
    IsIso j := by
  classical
  obtain ⟨L, hL, ⟨e⟩⟩ := hH
  let : Fintype L := Fintype.ofFinite L
  let d := Diagonalizable.splitIso R (AddEquiv.refl (L → ℤ)) ≪≫ e.symm
  let j' := pullback.snd j d.hom.hom.hom.left
  have : IsClosedImmersion j' := inferInstanceAs (IsClosedImmersion (pullback.snd _ _))
  have : IsIso j' := TorsionDensity.isIso_of_torsion_factors R
    (factors_one_separates_free_lattice R L) P
    (fun M => let ⟨n, hn, hMn⟩ := hP M; ⟨n, hn, one_dvd _, hMn⟩)
    j' (fun n hn _ x hx => FactorsTorsion.pullback P j h d.hom n hn x hx)
  exact isIso_of_lifts_id j (lifts_id_of_pullback_iso j d (lifts_id_of_isIso j'))

set_option maxHeartbeats 900000 in
private theorem isIso_of_factorsTorsion_split (hH : IsSplitTorus H) (j : Z ⟶ H.X.left)
    [IsClosedImmersion j] (P : ℕ → Prop) (hP : ∀ M : ℕ, ∃ n, P n ∧ M < n)
    (h : FactorsTorsion P j) : IsIso j := by
  let 𝒜 := S.affineOpenCover
  let 𝒰 := 𝒜.openCover.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
    (fun _ => ⟨inferInstance, inferInstance⟩)
  apply isIso_of_lifts_id
  apply lifts_id_of_cover H j 𝒰
  intro i
  have : IsIso (baseChangeι (𝒜.f i) H j) := isIso_of_factorsTorsion_splitAffine _
    (hH.baseChange (𝒜.f i)) _ P hP (FactorsTorsion.baseChange P j h (𝒜.f i))
  change PointLifts (baseChangeι (𝒜.f i) H j) _
  exact lifts_id_of_isIso _

set_option maxHeartbeats 1000000 in
/-- Torsion of unbounded orders is schematically dense in a relative torus,
in the form of detection of closed immersions by all torsion points. -/
theorem isIso_of_factorsTorsion_unbounded (hH : RelativeTorus.IsTorus H) (j : Z ⟶ H.X.left)
    [IsClosedImmersion j] (P : ℕ → Prop) (hP : ∀ M : ℕ, ∃ n, P n ∧ M < n)
    (h : ∀ (n : ℕ), P n → ∀ {T : Over S} (x : T ⟶ H.X), x ^ n = 1 → PointLifts j x) : IsIso j := by
  obtain ⟨𝒱, h𝒱⟩ := hH
  let 𝒰 := 𝒱.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation) (fun i => by
    have : Etale (𝒱.f i) := 𝒱.map_prop i
    exact ⟨inferInstance, inferInstance⟩)
  apply isIso_of_lifts_id
  apply lifts_id_of_cover H j 𝒰
  intro i
  have : IsIso (baseChangeι (𝒱.f i) H j) := isIso_of_factorsTorsion_split (h𝒱 i) _ P hP
    (FactorsTorsion.baseChange P j h (𝒱.f i))
  change PointLifts (baseChangeι (𝒱.f i) H j) _
  exact lifts_id_of_isIso _

/-- Equality of homomorphisms into a separated group is detected on any
unbounded set of actual torsion orders of a relative torus. -/
theorem hom_eq_of_torus_torsion_unbounded (hH : RelativeTorus.IsTorus H)
    [IsCommMonObj H.X] {G : GroupScheme S} [IsSeparated G.X.hom] (f g : H ⟶ G)
    (P : ℕ → Prop) (hP : ∀ M : ℕ, ∃ n, P n ∧ M < n)
    (h : ∀ n : ℕ, P n → torsionι H (n : ℤ) ≫ f = torsionι H (n : ℤ) ≫ g) : f = g := by
  let i := equalizer.ι f.hom.hom g.hom.hom
  have : IsClosedImmersion i.left := isClosedImmersion_equalizer_ι_left _ _
  have : IsIso i.left := isIso_of_factorsTorsion_unbounded hH i.left P hP (by
    intro n hn T x hx
    obtain ⟨y, hy, -⟩ := (existsUnique_torsion_lift_iff H (n : ℤ) T x).mpr (by simpa using hx)
    have he : x ≫ f.hom.hom = x ≫ g.hom.hom := by
      rw [← hy, Category.assoc, Category.assoc, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, h n hn]
    refine ⟨(equalizer.lift x he).left, ?_⟩
    change (equalizer.lift x he ≫ i).left = x.left
    exact congrArg (fun a : T ⟶ H.X => a.left) (equalizer.lift_ι _ _))
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_epi i.left).mp
  exact congrArg CommaMorphism.left (equalizer.condition f.hom.hom g.hom.hom)

namespace HomScheme.Adic.System

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [IsAdicComplete (maximalIdeal A) A]
  {H G : GroupScheme (Spec (CommRingCat.of A))} [IsCommMonObj H.X] [IsSeparated G.X.hom]

set_option maxHeartbeats 1200000 in
/-- A map algebraizes a formal relative torus Hom system if its torsion
restrictions agree on all powers of a single integer greater than one. -/
theorem restrict_eq_iff_torsionPowers (s : System (maximalIdeal A) H G)
    (hH : RelativeTorus.IsTorus H) (f : H ⟶ G) (q : ℕ) (hq : 1 < q) :
    System.restrict (maximalIdeal A) H G f = s ↔
      ∀ k : ℕ, torsionι H ((q ^ k : ℕ) : ℤ) ≫ f =
        s.torsionRestriction hH.isMultiplicativeType (q ^ k) (pow_pos (by omega) _) := by
  constructor
  · intro hf k
    exact (s.restrict_eq_iff_torsionRestriction hH.isMultiplicativeType f).mp hf (q ^ k) _
  · intro hf
    apply System.ext
    intro d
    let r := quotientMap (maximalIdeal A) d
    let B := baseChange r
    have : IsSeparated (B.obj G).X.hom := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
    change B.map f = s.hom d
    apply hom_eq_of_torus_torsion_unbounded (hH.baseChange r) _ _ (fun n => ∃ k, q ^ k = n)
    · intro M
      exact ⟨q ^ M, ⟨M, rfl⟩, Nat.lt_pow_self hq⟩
    · rintro n ⟨k, rfl⟩
      have he := congrArg (fun a => B.map a) (hf k)
      rw [Functor.map_comp, torsionRestriction_reduce] at he
      let e := torsionBaseChangeIso r H ((q ^ k : ℕ) : ℤ)
      have hc : e.hom ≫ torsionι (B.obj H) ((q ^ k : ℕ) : ℤ) =
          B.map (torsionι H ((q ^ k : ℕ) : ℤ)) := torsionBaseChangeIso_hom_ι r H _
      apply (cancel_epi e.hom).mp
      rw [← Category.assoc, hc, ← Category.assoc, hc]
      exact he

end HomScheme.Adic.System

namespace HomScheme.Adic

/-- Algebraization of a torus Hom system is tested on any one power tower. -/
def TorusTorsionTowerRecoveryStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (H G : GroupScheme (Spec (CommRingCat.of A))) [IsCommMonObj H.X] [IsSeparated G.X.hom]
    (hH : RelativeTorus.IsTorus H) (s : System (maximalIdeal A) H G)
    (f : H ⟶ G) (q : ℕ) (hq : 1 < q),
    System.restrict (maximalIdeal A) H G f = s ↔
      ∀ k : ℕ, torsionι H ((q ^ k : ℕ) : ℤ) ≫ f =
        s.torsionRestriction hH.isMultiplicativeType (q ^ k) (pow_pos (by omega) _)

theorem torusTorsionTowerRecovery : TorusTorsionTowerRecoveryStatement.{u} := by
  intro A _ _ _ _ H G _ _ hH s f q hq
  exact s.restrict_eq_iff_torsionPowers hH f q hq

end HomScheme.Adic

end Langlands.GroupScheme
