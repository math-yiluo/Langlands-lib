import Langlands.AbelianScheme.AbelianInertiaQuasiUnipotentStatement
import Langlands.AbelianScheme.Tate.GeometricTorsionRankProof
import Langlands.AbelianScheme.Tate.PrimeAdicCoordinates
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-! # Quasi-unipotence from power conjugacy at the finite Tate levels -/

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing
open Langlands.AlgebraicGeometry.FiniteEtale

namespace Langlands.AbelianScheme

universe u

namespace Tate.PrimeAdic

open GroupScheme.Tate.PrimeAdic.GeometricRank

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y))
  (A : AbelianScheme S) (ℓ : ℕ) [Fact ℓ.Prime]
  (hu : ∀ n : ℕ, IsUnit ((ℓ ^ n : ℕ) : Γ(S, ⊤)))

/-- Finite Tate monodromy as an endomorphism over the residue coefficient ring. -/
def levelMonodromyZMod (n : ℕ) (g : FundamentalGroup s hfin) :
    Module.End (ZMod (ℓ ^ n)) (Level A (Over.mk s) ℓ n) where
  toAddHom := (levelMonodromy s hfin torsionFiniteEtale A (ℓ ^ n)
    (pow_pos (Fact.out : ℓ.Prime).pos n) (hu n) g).toAddMonoidHom
  map_smul' := levelMonodromy_zmod_smul s hfin torsionFiniteEtale A (ℓ ^ n)
    (pow_pos (Fact.out : ℓ.Prime).pos n) (hu n) g

private theorem charpoly_monodromyMap_eq_of_level_conj
    {r : ℕ}
    [Module.Free ℤ_[ℓ] (Integral A (Over.mk s) ℓ)]
    [Module.Finite ℤ_[ℓ] (Integral A (Over.mk s) ℓ)]
    (hL : ∀ n : ℕ,
      Nonempty ((Fin r → ZMod (ℓ ^ n)) ≃ₗ[ZMod (ℓ ^ n)]
        Level A (Over.mk s) ℓ n) ∧
        Nat.card (Level A (Over.mk s) ℓ n) = (ℓ ^ n) ^ r)
    (g k : FundamentalGroup s hfin)
    (h : ∀ n : ℕ, ∃ e : Level A (Over.mk s) ℓ n ≃ₗ[ZMod (ℓ ^ n)]
      Level A (Over.mk s) ℓ n,
        e.conj (levelMonodromyZMod s hfin A ℓ hu n g) =
          levelMonodromyZMod s hfin A ℓ hu n k) :
    (monodromyMap s hfin torsionFiniteEtale A ℓ hu g).charpoly =
      (monodromyMap s hfin torsionFiniteEtale A ℓ hu k).charpoly := by
  classical
  obtain ⟨c, hc, hc'⟩ := exists_compatible_bases hL
  let e := LinearEquiv.ofBijective (coordinates hc')
    ⟨coordinates_injective hc hc', coordinates_surjective hc hc'⟩
  let eₙ (n : ℕ) := LinearEquiv.ofBijective (Fintype.linearCombination (ZMod (ℓ ^ n)) (c n))
    (hc n)
  let M (g : FundamentalGroup s hfin) :=
    LinearMap.toMatrixAlgEquiv' (e.symm.conj (monodromyMap s hfin torsionFiniteEtale A ℓ hu g))
  let Mₙ (n : ℕ) (g : FundamentalGroup s hfin) :=
    LinearMap.toMatrixAlgEquiv' ((eₙ n).symm.conj (levelMonodromyZMod s hfin A ℓ hu n g))
  have hcoord (n : ℕ) (v : Fin r → ℤ_[ℓ]) :
      evaluation A (Over.mk s) ℓ n (e v) = eₙ n (fun i => PadicInt.toZModPow n (v i)) :=
    evaluation_coordinates hc' n v
  have hreduce (n : ℕ) (g : FundamentalGroup s hfin) :
      (M g).map (PadicInt.toZModPow n) = Mₙ n g := by
    ext i j
    let v : Fin r → ℤ_[ℓ] := Pi.single j 1
    have hv : (fun i => PadicInt.toZModPow n (v i)) = Pi.single j 1 := by
      funext i
      by_cases h : i = j <;> simp [v, h]
    have heval := hcoord n (e.symm (monodromyMap s hfin torsionFiniteEtale A ℓ hu g (e v)))
    rw [LinearEquiv.apply_symm_apply, evaluation_monodromyMap, hcoord n v, hv] at heval
    change (levelMonodromyZMod s hfin A ℓ hu n g) (eₙ n (Pi.single j 1)) =
      eₙ n (fun i => PadicInt.toZModPow n
        (e.symm (monodromyMap s hfin torsionFiniteEtale A ℓ hu g (e v)) i)) at heval
    simpa only [M, Mₙ, Matrix.map_apply, LinearMap.toMatrixAlgEquiv'_apply,
      LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply, v] using
      (congrFun (congrArg (eₙ n).symm heval) i).symm
  have hchar (g : FundamentalGroup s hfin) :
      (M g).charpoly = (monodromyMap s hfin torsionFiniteEtale A ℓ hu g).charpoly := by
    rw [← Matrix.charpoly_toLin']
    change (Matrix.toLinAlgEquiv' (M g)).charpoly = _
    simp [M]
  let (n : ℕ) : Module.Free (ZMod (ℓ ^ n)) (Level A (Over.mk s) ℓ n) :=
    Module.Free.of_equiv (eₙ n)
  let (n : ℕ) : Module.Finite (ZMod (ℓ ^ n)) (Level A (Over.mk s) ℓ n) :=
    Module.Finite.equiv (eₙ n)
  have hcharₙ (n : ℕ) (g : FundamentalGroup s hfin) :
      (Mₙ n g).charpoly = (levelMonodromyZMod s hfin A ℓ hu n g).charpoly := by
    rw [← Matrix.charpoly_toLin']
    change (Matrix.toLinAlgEquiv' (Mₙ n g)).charpoly = _
    simp [Mₙ]
  rw [← hchar g, ← hchar k]
  apply Polynomial.ext
  intro i
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  obtain ⟨f, hf⟩ := h n
  have hpol : (Mₙ n g).charpoly = (Mₙ n k).charpoly := by
    rw [hcharₙ n g, hcharₙ n k, ← hf, LinearEquiv.charpoly_conj]
  have hmap := congrArg (fun f : Polynomial (ZMod (ℓ ^ n)) => f.coeff i) hpol
  rw [← hreduce n g, ← hreduce n k, Matrix.charpoly_map, Matrix.charpoly_map] at hmap
  simpa only [Polynomial.coeff_map] using hmap

end Tate.PrimeAdic

open Tate.PrimeAdic

/-- A fixed power \(q>1\) is realized by conjugation at every finite Tate level, after taking
a positive power of the given inertia element. -/
def AbelianInertiaTatePowerConjugacyStatement : Prop :=
  ∀ (W L : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [HenselianLocalRing W] [IsSepClosed (ResidueField W)]
    [Field L] [Algebra W L] [IsFractionRing W L]
    (A : AbelianScheme (Spec (.of L))) (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : W) →
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of L))
      (hu : ∀ n : ℕ, IsUnit ((ℓ ^ n : ℕ) : Γ(Spec (.of L), ⊤)))
      (g : FundamentalGroup s (geometricFiberFinite s)),
      ∃ a q : ℕ, 0 < a ∧ 1 < q ∧
        ∀ n : ℕ, ∃ e : Level A (Over.mk s) ℓ n ≃ₗ[ZMod (ℓ ^ n)] Level A (Over.mk s) ℓ n,
          e.conj (levelMonodromyZMod s (geometricFiberFinite s) A ℓ hu n (g ^ a)) =
            levelMonodromyZMod s (geometricFiberFinite s) A ℓ hu n (g ^ (a * q))

/-- Finite-level power conjugacy suffices for quasi-unipotence of the rational Tate action. -/
def AbelianInertiaQuasiUnipotentReductionStatement : Prop :=
  AbelianInertiaTatePowerConjugacyStatement.{u} → AbelianInertiaQuasiUnipotentStatement.{u}

open scoped TensorProduct

private theorem exists_pos_pow_sub_one_nilpotent_of_charpoly_pow
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : Module.End K V) (hT : IsUnit T) {q : ℕ} (hq : 1 < q)
    (hchar : T.charpoly = (T ^ q).charpoly) :
    ∃ m : ℕ, 0 < m ∧ IsNilpotent (T ^ m - 1) := by
  classical
  let E := AlgebraicClosure K
  let f := Module.End.baseChangeHom K E V
  let U := f T
  let P := spectrum E U
  have hf : Function.Injective f := LinearMap.baseChangeHom_injective K V E
  have hU : U.charpoly = (U ^ q).charpoly := by
    change (T.baseChange E).charpoly = (f T ^ q).charpoly
    rw [← map_pow]
    change (T.baseChange E).charpoly = ((T ^ q).baseChange E).charpoly
    rw [LinearMap.charpoly_baseChange, LinearMap.charpoly_baseChange, hchar]
  have hstep (x : P) : x.val ^ q ∈ P := by
    have hx := spectrum.pow_mem_pow U q x.property
    rwa [Module.End.mem_spectrum_iff_isRoot_charpoly, ← hU,
      ← Module.End.mem_spectrum_iff_isRoot_charpoly] at hx
  have hiter (j : ℕ) (x : P) : x.val ^ (q ^ j) ∈ P := by
    induction j with
    | zero => simp [x.property]
    | succ j ih => simpa only [pow_succ q, pow_mul] using hstep ⟨_, ih⟩
  let F (j : ℕ) (x : P) : P := ⟨x.val ^ (q ^ j), hiter j x⟩
  have : Finite P := (Module.End.finite_spectrum U).to_subtype
  obtain ⟨i, j, hij, hF⟩ := Finite.exists_ne_map_eq_of_infinite F
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm hF.symm (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm)
  have hlt' : q ^ i < q ^ j := Nat.pow_lt_pow_right hq hlt
  let m := q ^ j - q ^ i
  have hm : 0 < m := Nat.sub_pos_of_lt hlt'
  have hroot (x : P) : x.val ^ m = 1 := by
    have hpow : x.val ^ (q ^ i) = x.val ^ (q ^ j) :=
      congrArg Subtype.val (congrFun hF x)
    have hne : x.val ≠ 0 := by
      intro hx
      exact spectrum.zero_notMem E (hT.map f) (hx ▸ x.property)
    rw [← Nat.add_sub_of_le hlt'.le, pow_add] at hpow
    exact mul_left_cancel₀ (pow_ne_zero _ hne) (hpow.symm.trans (mul_one _).symm)
  let N := U ^ m - 1
  have hroots {x : E} (hx : x ∈ N.charpoly.roots) : x = 0 := by
    have he := (Module.End.hasEigenvalue_iff_isRoot_charpoly N x).mpr (Polynomial.isRoot_of_mem_roots hx)
    obtain ⟨v, hv⟩ := he.exists_hasEigenvector
    have hv' : (U ^ m) v = (x + 1) • v := by
      rw [add_smul, one_smul]
      exact sub_eq_iff_eq_add.mp hv.apply_eq_smul
    have hx' : x + 1 ∈ spectrum E (U ^ m) :=
      Module.End.hasEigenvalue_iff_mem_spectrum.mp
        (Module.End.hasEigenvalue_of_hasEigenvector
          ⟨Module.End.mem_eigenspace_iff.mpr hv', hv.2⟩)
    rw [spectrum.map_pow_of_pos U hm] at hx'
    obtain ⟨z, hz, hz'⟩ := hx'
    apply add_right_cancel (b := 1)
    simpa using hz'.symm.trans (hroot ⟨z, hz⟩)
  have hsplit := IsAlgClosed.splits N.charpoly
  have hnil : IsNilpotent N := by
    apply (LinearMap.isNilpotent_iff_charpoly N).mpr
    rw [hsplit.eq_prod_roots_of_monic N.charpoly_monic]
    calc
      (N.charpoly.roots.map fun x => Polynomial.X - Polynomial.C x).prod =
          (N.charpoly.roots.map fun _ => Polynomial.X).prod := by
            congr 1
            exact Multiset.map_congr rfl fun x hx => by simp [hroots hx]
      _ = Polynomial.X ^ Module.finrank E (E ⊗[K] V) := by
        rw [Multiset.map_const', Multiset.prod_replicate, hsplit.natDegree_eq_card_roots.symm,
          N.charpoly_natDegree]
  refine ⟨m, hm, (IsNilpotent.map_iff hf).mp ?_⟩
  simpa only [map_sub, map_pow, map_one] using hnil

/-- Compute the characteristic polynomials in compatible torsion bases and apply the
finite-spectrum argument to the rational Tate action. -/
theorem abelianInertiaQuasiUnipotent_of_powerConjugacy :
    AbelianInertiaQuasiUnipotentReductionStatement.{u} := by
  intro h W L _ _ _ _ _ _ _ _ A ℓ _ hℓ Ω _ _ s hu g
  classical
  obtain ⟨a, q, ha, hq, hconj⟩ := h W L A ℓ hℓ Ω s hu g
  have : ConnectedSpace A.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.X.hom
  obtain ⟨d, hd⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension _ _ A.X.hom
    inferInstance inferInstance
  have hL (n : ℕ) := Tate.geometricTorsionRank _ A d hd (ℓ ^ n)
    (pow_pos (Fact.out : ℓ.Prime).pos n) (hu n) Ω s
  let basis := (GroupScheme.Tate.PrimeAdic.GeometricRank.integral_linearEquiv hL).some
  have : Module.Free ℤ_[ℓ] (Integral A (Over.mk s) ℓ) := Module.Free.of_equiv basis
  have : Module.Finite ℤ_[ℓ] (Integral A (Over.mk s) ℓ) := Module.Finite.equiv basis
  have : FiniteDimensional ℚ_[ℓ] (Rational A (Over.mk s) ℓ) :=
    (GroupScheme.Tate.PrimeAdic.rational_finrank_of_linearEquiv basis).1
  have hchar := charpoly_monodromyMap_eq_of_level_conj s (geometricFiberFinite s) A ℓ hu
    hL (g ^ a) (g ^ (a * q)) hconj
  let ρ := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (rationalMonodromyRepresentation s (geometricFiberFinite s) torsionFiniteEtale A ℓ hu)
  have hbc (x : FundamentalGroup s (geometricFiberFinite s)) :
      (ρ x).charpoly =
        (monodromyMap s (geometricFiberFinite s) torsionFiniteEtale A ℓ hu x).charpoly.map
          (algebraMap ℤ_[ℓ] ℚ_[ℓ]) :=
    LinearMap.charpoly_baseChange (monodromyMap s (geometricFiberFinite s) torsionFiniteEtale
      A ℓ hu x) ℚ_[ℓ]
  have hrpow : (ρ (g ^ a)).charpoly = ((ρ (g ^ a)) ^ q).charpoly := by
    rw [← map_pow, ← pow_mul, hbc, hbc, hchar]
  obtain ⟨m, hm, hnil⟩ :=
    exists_pos_pow_sub_one_nilpotent_of_charpoly_pow (ρ (g ^ a))
      ((Group.isUnit (g ^ a)).map ρ) hq hrpow
  refine ⟨a * m, Nat.mul_pos ha hm, ?_⟩
  change IsNilpotent (ρ (g ^ (a * m)) - 1)
  rwa [pow_mul, map_pow]

end Langlands.AbelianScheme
