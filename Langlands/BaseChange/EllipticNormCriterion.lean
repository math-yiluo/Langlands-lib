import Langlands.BaseChange.EllipticNormCriterionStatement
import Langlands.BaseChange.CyclicAlgebraBaseChange
import Langlands.BaseChange.CharZeroTraceConductorPremises
import Langlands.BaseChange.RankOneSigmaLiftNorm
import Langlands.ClassFieldTheory.Local.Artin.FiniteArtinNormalization
import Langlands.Global.AdelicFunctoriality.NormReduction
import Mathlib.RingTheory.TensorProduct.Pi

/-! # The regular elliptic norm criterion -/

noncomputable section

namespace Langlands.BaseChange

open Langlands.JacquetLanglands
open scoped TensorProduct

universe u v

private theorem normUnitsRange_congr {K A B : Type*} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (e : A ≃ₐ[K] B) :
    (Units.map (Algebra.norm K : A →* K)).range =
      (Units.map (Algebra.norm K : B →* K)).range := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Units.map e.toMonoidHom x, Units.ext (Algebra.norm_eq_of_algEquiv e (x : A))⟩
  · rintro ⟨x, rfl⟩
    exact ⟨Units.map e.symm.toMonoidHom x, Units.ext (Algebra.norm_eq_of_algEquiv e.symm (x : B))⟩

private theorem normUnitsRange_pi {K A ι : Type*} [Field K] [CommRing A] [Algebra K A]
    [Module.Finite K A] [Fintype ι] (i₀ : ι) :
    (Units.map (Algebra.norm K : (ι → A) →* K)).range =
      (Units.map (Algebra.norm K : A →* K)).range := by
  classical
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨∏ i : ι, MulEquiv.piUnits x i, Units.ext ?_⟩
    change Algebra.norm K (↑(∏ i : ι, MulEquiv.piUnits x i) : A) =
      Algebra.norm K (x : ι → A)
    rw [show (↑(∏ i : ι, MulEquiv.piUnits x i) : A) =
        ∏ i : ι, (x : ι → A) i from map_prod (Units.coeHom A) _ _, map_prod,
      Global.AdelicFunctoriality.norm_pi K ι (fun _ => A)]
  · rintro ⟨x, rfl⟩
    let b : ι → Aˣ := fun i => if i = i₀ then x else 1
    refine ⟨MulEquiv.piUnits.symm b, Units.ext ?_⟩
    change Algebra.norm K (fun i => (b i : A)) = Algebra.norm K (x : A)
    rw [Global.AdelicFunctoriality.norm_pi K ι (fun _ => A)]
    simp only [b, apply_ite (fun y : Aˣ => Algebra.norm K (y : A)), Units.val_one,
      map_one, Fintype.prod_ite_eq']

/-- The product of all cyclic conjugates is the determinant norm also in the presence
of several field factors. -/
private theorem cyclicProduct_eq_norm {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    {σ : A ≃ₐ[K] A} {l : ℕ} (hσ : IsCyclicAlgebra σ l) (x : A) :
    ((List.range l).map fun i => (σ ^ i) x).prod = algebraMap K A (Algebra.norm K x) := by
  classical
  have hlist : ((List.range l).map fun i => (σ ^ i) x).prod =
      ∏ i ∈ Finset.range l, (σ ^ i) x := by
    have hrange : (List.finRange l).map (fun i : Fin l => (i : ℕ)) = List.range l := by simp
    rw [Finset.prod_range, Fin.prod_univ_def, ← hrange, List.map_map]
    rfl
  rw [hlist]
  let y := ∏ i ∈ Finset.range l, (σ ^ i) x
  change y = _
  have hy : σ y = y := by
    obtain ⟨k, hk : l = k + 1⟩ := Nat.exists_eq_succ_of_ne_zero hσ.pos.ne'
    have hone : σ ^ (k + 1) = 1 := by
      rw [← hk]
      exact hσ.pow_eq_one
    dsimp only [y]
    simp only [map_prod, ← AlgEquiv.mul_apply, ← pow_succ']
    rw [hk, Finset.prod_range_succ (fun i => (σ ^ (i + 1)) x),
      Finset.prod_range_succ' (fun i => (σ ^ i) x), hone, pow_zero]
  obtain ⟨a, ha⟩ := hσ.2.2.2.2 y hy
  obtain ⟨c⟩ := CyclicAlgebraStructure.exists_coordinates hσ
  let : c.m.asIdeal.IsMaximal := c.m.isMaximal
  let L := A ⧸ c.m.asIdeal
  let : Field L := Ideal.Quotient.field c.m.asIdeal
  let : Module.Finite K L := c.cyclic.1
  let q : A →ₐ[K] L := Ideal.Quotient.mkₐ K c.m.asIdeal
  have hwrap (j : ℕ) (z : A) : q ((σ ^ (c.r * j)) z) = (c.τ ^ j) (q z) := by
    induction j generalizing z with
    | zero => simp
    | succ j ih =>
      rw [Nat.mul_succ, pow_add, AlgEquiv.mul_apply, ih, pow_succ, AlgEquiv.mul_apply]
      exact congrArg (fun t => (c.τ ^ j) t) (c.wrap z)
  let e : Fin c.d × Fin c.r ≃ Fin l :=
    finProdFinEquiv.trans (finCongr ((Nat.mul_comm c.d c.r).trans c.degree_eq.symm))
  have hprod : q y = ∏ i : Fin c.r, algebraMap K L (Algebra.norm K (c.coords x i)) := by
    dsimp only [y]
    rw [map_prod, Finset.prod_range]
    calc
      _ = ∏ p : Fin c.d × Fin c.r, (c.τ ^ (p.1 : ℕ)) (c.coords x p.2) := by
        symm
        apply Fintype.prod_equiv e
        rintro ⟨j, i⟩
        change (c.τ ^ (j : ℕ)) (c.coords x i) = q ((σ ^ ((i : ℕ) + c.r * (j : ℕ))) x)
        rw [add_comm, pow_add, AlgEquiv.mul_apply, hwrap, c.coords_apply]
        rfl
      _ = _ := by
        rw [Fintype.prod_prod_type_right]
        apply Finset.prod_congr rfl
        intro i _
        rw [c.cyclic.norm_eq_prod_powers, Finset.prod_range]
  rw [← ha]
  congr 1
  apply (algebraMap K L).injective
  rw [← q.commutes, ha, hprod, ← map_prod,
    ← Global.AdelicFunctoriality.norm_pi K (Fin c.r) (fun _ => L), Algebra.norm_eq_of_algEquiv c.coords]

open ClassFieldTheory.Local.Artin in
/-- Restrict the local Artin symbol along a field quotient of the scalar extension.
Surjectivity of the quotient makes restriction to the original field factor injective. -/
private theorem norm_mem_iff_of_tensor_field
    {F P K L : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field P] [ValuativeRel P] [TopologicalSpace P]
    [IsNonarchimedeanLocalField P] [Field K] [Field L]
    [Algebra F P] [FiniteDimensional F P] [Algebra.IsSeparable F P]
    [Valuation.HasExtension (ValuativeRel.valuation F) (ValuativeRel.valuation P)]
    [Algebra F K] [FiniteDimensional F K] [IsAbelianGalois F K]
    [Algebra P L] [FiniteDimensional P L] [IsAbelianGalois P L]
    (q : P ⊗[F] K →ₐ[P] L) (hq : Function.Surjective q) (x : Pˣ) :
    x ∈ (Units.map (Algebra.norm P : L →* P)).range ↔
      Units.map (Algebra.norm F : P →* F) x ∈ (Units.map (Algebra.norm F : K →* F)).range := by
  let : Algebra F L := Algebra.compHom L (algebraMap F P)
  let : IsScalarTower F P L := IsScalarTower.of_algebraMap_eq' rfl
  let j : K →ₐ[F] L := (q.restrictScalars F).comp Algebra.TensorProduct.includeRight
  let : Algebra K L := j.toRingHom.toAlgebra
  let : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun a => (j.commutes a).symm
  let ρ : Gal(L/P) →* Gal(K/F) :=
    (AlgEquiv.restrictNormalHom K).comp (AlgEquiv.restrictScalarsHom F)
  have hρ : Function.Injective ρ := by
    intro s t hst
    have hcomp : s.toAlgHom.comp q = t.toAlgHom.comp q := by
      apply Algebra.TensorProduct.ext'
      intro a b
      change s (q (a ⊗ₜ b)) = t (q (a ⊗ₜ b))
      have ht : q (a ⊗ₜ b) = algebraMap P L a * algebraMap K L b := by
        calc
          _ = q (algebraMap P (P ⊗[F] K) a * (1 ⊗ₜ b)) := by
            congr 1
            change a ⊗ₜ b = (a ⊗ₜ 1) * (1 ⊗ₜ b)
            simp
          _ = _ := by rw [map_mul, q.commutes]; rfl
      rw [ht, map_mul, map_mul, s.commutes, t.commutes]
      congr 1
      change s.restrictScalars F (algebraMap K L b) = t.restrictScalars F (algebraMap K L b)
      rw [← (s.restrictScalars F).restrictNormal_commutes K b,
        ← (t.restrictScalars F).restrictNormal_commutes K b]
      exact congrArg (fun e : Gal(K/F) => algebraMap K L (e b)) hst
    ext z
    obtain ⟨a, rfl⟩ := hq z
    exact DFunLike.congr_fun hcomp a
  have hart := restrictNormalHom_arithmeticFiniteArtin_normUnits F P K L x
  change ρ (arithmeticFiniteArtin P L x) = _ at hart
  change x ∈ LocalClassField.normSubgroup P L ↔
    LocalClassField.normUnits F P x ∈ LocalClassField.normSubgroup F K
  rw [← arithmeticFiniteArtin_eq_one_iff P L, ← arithmeticFiniteArtin_eq_one_iff F K, ← hart,
    ← map_one ρ]
  exact hρ.eq_iff.symm

private theorem norm_mem_iff_of_scalarExtension {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
    (P : Type u) [Field P] [Algebra F P] [FiniteDimensional F P]
    {A : Type v} [CommRing A] [Algebra F A] {σ : A ≃ₐ[F] A} {l : ℕ}
    (hσ : IsCyclicAlgebra σ l) (x : Pˣ) :
    x ∈ (Units.map (Algebra.norm P : (P ⊗[F] A) →* P)).range ↔
      Units.map (Algebra.norm F : P →* F) x ∈ (Units.map (Algebra.norm F : A →* F)).range := by
  obtain ⟨c⟩ := CyclicAlgebraStructure.exists_coordinates hσ
  let : c.m.asIdeal.IsMaximal := c.m.isMaximal
  let K := A ⧸ c.m.asIdeal
  let : Field K := Ideal.Quotient.field c.m.asIdeal
  let : Module.Finite F K := c.cyclic.1
  let : IsAbelianGalois F K := c.cyclic.isAbelianGalois
  let : Algebra.FormallyEtale F K := c.cyclic.formallyEtale
  have hT := c.cyclic.scalarExtension P
  let : Module.Finite P (P ⊗[F] K) := hT.1
  obtain ⟨d⟩ := CyclicAlgebraStructure.exists_coordinates hT
  let : d.m.asIdeal.IsMaximal := d.m.isMaximal
  let L := (P ⊗[F] K) ⧸ d.m.asIdeal
  let : Field L := Ideal.Quotient.field d.m.asIdeal
  let : Module.Finite P L := d.cyclic.1
  let : IsAbelianGalois P L := d.cyclic.isAbelianGalois
  let e : (P ⊗[F] A) ≃ₐ[P] (Fin c.r → P ⊗[F] K) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : P ≃ₐ[P] P) c.coords).trans
      (Algebra.TensorProduct.piRight F P P (fun _ : Fin c.r => K))
  let i : Fin c.r := ⟨0, c.r_pos⟩
  let j : Fin d.r := ⟨0, d.r_pos⟩
  rw [normUnitsRange_congr (K := F) c.coords, normUnitsRange_pi (K := F) (A := K) i,
    normUnitsRange_congr e, normUnitsRange_pi (K := P) (A := P ⊗[F] K) i,
    normUnitsRange_congr d.coords, normUnitsRange_pi (K := P) (A := L) j]
  let := LocalField.FiniteExtension.normedField F P
  let := LocalField.FiniteExtension.valuativeRel F P
  let := LocalField.FiniteExtension.isLocalField F P
  let := ClassFieldTheory.Local.Artin.spectral_hasExtension F P
  exact norm_mem_iff_of_tensor_field (Ideal.Quotient.mkₐ P d.m.asIdeal)
    (Ideal.Quotient.mkₐ_surjective P _) x

private theorem determinant_eq_norm_root {F : Type u} [Field F] {n : ℕ}
    (γ : GeneralLinear n F) :
    Algebra.norm F (AdjoinRoot.root γ.val.charpoly) = (GeneralLinear.determinant γ : F) := by
  let A : Matrix (Fin n) (Fin n) F := γ.val
  let p := A.charpoly
  have hp : p.Monic := A.charpoly_monic
  change Algebra.norm F (AdjoinRoot.root p) = A.det
  rw [← AdjoinRoot.powerBasis_gen hp.ne_zero, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly,
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hp, Matrix.det_eq_sign_charpoly_coeff]
  simp [p]

/-- An elliptic regular matrix over a characteristic-zero local field is a cyclic
norm exactly when its determinant belongs to the scalar norm group. -/
theorem ellipticNormCriterion : EllipticNormCriterionStatement.{u, v} := by
  intro F _ _ _ _ _ E _ _ σ l n hσ γ hγ
  let p := γ.val.charpoly
  let : Fact (Irreducible p) := ⟨hγ.2⟩
  let P := AdjoinRoot p
  let : Field P := inferInstanceAs (Field (AdjoinRoot p))
  let : Module.Finite F P := γ.val.charpoly_monic.finite_adjoinRoot
  have hdet : Algebra.norm F (AdjoinRoot.root p) = (GeneralLinear.determinant γ : F) :=
    determinant_eq_norm_root γ
  have hne : AdjoinRoot.root p ≠ 0 := by
    intro h
    rw [h, Algebra.norm_zero] at hdet
    exact Units.ne_zero _ hdet.symm
  let x : Pˣ := Units.mk0 (AdjoinRoot.root p) hne
  have hx : Units.map (Algebra.norm F : P →* F) x = GeneralLinear.determinant γ := Units.ext hdet
  let : Algebra.FormallyEtale F E := hσ.formallyEtale
  have hT := hσ.scalarExtension P
  let : Nontrivial (P ⊗[F] E) :=
    Module.nontrivial_of_finrank_pos (R := P) (hT.2.1 ▸ hσ.pos)
  rw [isNorm_iff_charpolyTensor_product σ γ hσ hγ.1]
  change (∃ b : (P ⊗[F] E)ˣ,
    ((List.range l).map fun i => (tensorFactorAut P σ ^ i) (b : P ⊗[F] E)).prod =
      algebraMap P (P ⊗[F] E) (x : P)) ↔ _
  simp_rw [cyclicProduct_eq_norm hT]
  rw [← hx, ← norm_mem_iff_of_scalarExtension P hσ x]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, Units.ext ((algebraMap P (P ⊗[F] E)).injective hb)⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, congrArg (fun a : Pˣ => algebraMap P (P ⊗[F] E) (a : P)) hb⟩

end Langlands.BaseChange
