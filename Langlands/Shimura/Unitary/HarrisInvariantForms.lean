import Langlands.Shimura.EquivariantFormsFactor
import Langlands.Shimura.Unitary.HarrisPairPoints

/-!
# Harris's (4.8): `K_ℓ`-invariant forms at level `H(m)`

Harris 1999, §4, p.311: "The right-hand side of (4.7) is the sum of `M` copies of the group
`D_m(K_{ℓ,m} × C_p/H_p)` of `𝒪_m`-valued functions on `K_{ℓ,m} × C_p/H_p`. Via the duality
between functions and group rings, this is canonically isomorphic to
`Hom(𝒪_m[K_{ℓ,m} × C_p/H_p]^M, 𝒪_m)`, and thus the decomposition (4.6) yields a canonical
isomorphism (4.8) `𝒜_ℓ(GJ, 𝓛_m, H(m))^{K_ℓ} ⥲ Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)`."

For distinct primes `ℓ` and `p`, the published splitting `e : σ(A_f) ≃ₜ* σ(∏_{v ∣ ℓ p} ℚ_v) ×
σ(A_f^{ℓ p})` and `pairPointsEquiv` identify Harris's level `K_C = K^{ℓ,p} × K_ℓ × C_p`
(`splitLevel` of `pairLevel K_ℓ C_p` and `L`). Its components at `ℓ` and `p` and the embedding of
`C_p` form a `LevelFactorization` of `K_C` adapted to `K^{ℓ,p} × K_ℓ × H_p`
(`harrisLevelFactorization`). Under (4.5) every stabilizer of `K_C` has trivial components at
`ℓ` and `p` (`harrisLevelFactorization_stabilizer_le`), so the generic results of
`EquivariantFormsFactor` apply:

* `harrisFormsEquiv`: the forms of level `K^{ℓ,p} × K_ℓ × H_p` with coefficients a representation
  `V` of `K_ℓ` are `Hom_R(R[(C_p ⧸ H_p) × GJ(ℚ) \ GJ(A_f) / K_C], V)`;
* `harrisInvariantsEquiv`: Harris's (4.8). The invariants of `K_ℓ`, embedded by `ellLevelHom`, in
  the forms of level `H(m) = K^{ℓ,p} × K_ℓ(m) × H_p` are the same `Hom` module.

The double cosets are taken modulo `K_C`, so the number of copies is the number of double cosets
modulo `K_C`, not Harris's `M` of (4.6) (taken modulo `K^{ℓ,p} × K_ℓ × K_p`); see
`HarrisDividingLevelFree`.
-/

noncomputable section

open Langlands.Global Langlands.Shimura.EquivariantForms
open scoped NumberField

set_option autoImplicit false

universe v uR t

namespace Langlands.Shimura.DefiniteForms

/-- A subgroup is normal in itself. -/
instance subgroupOf_self_normal {G : Type*} [Group G] (H : Subgroup G) :
    (H.subgroupOf H).Normal := by
  rw [Subgroup.subgroupOf_self]
  infer_instance

section Components

variable {A : Type v} [Ring A] [Algebra ℚ A] {σ : AlgebraInvolution ℚ A} [Module.Finite ℚ A]
  {n : ℕ} {vℓ vp : {v : FinitePlace ℚ // (n : 𝓞 ℚ) ∈ v.asIdeal}}

/-- The component at `vℓ` of `pairLevel K_ℓ C_p`, with values in `K_ℓ`. -/
def pairLevelFst (Kℓ : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1)))
    (Cp : Subgroup (σ.Points (FiniteCompletion ℚ vp.1))) : pairLevel σ vℓ vp Kℓ Cp →* Kℓ :=
  ((σ.dividingLocalMap n vℓ).toMonoidHom.comp (pairLevel σ vℓ vp Kℓ Cp).subtype).codRestrict Kℓ
    fun u => u.2.1

/-- The component at `vp` of `pairLevel K_ℓ C_p`, with values in `C_p`. -/
def pairLevelSnd (Kℓ : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1)))
    (Cp : Subgroup (σ.Points (FiniteCompletion ℚ vp.1))) : pairLevel σ vℓ vp Kℓ Cp →* Cp :=
  ((σ.dividingLocalMap n vp).toMonoidHom.comp (pairLevel σ vℓ vp Kℓ Cp).subtype).codRestrict Cp
    fun u => u.2.2

@[simp]
theorem pairLevelFst_apply_coe {Kℓ : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1))}
    {Cp : Subgroup (σ.Points (FiniteCompletion ℚ vp.1))} (u : pairLevel σ vℓ vp Kℓ Cp) :
    (pairLevelFst Kℓ Cp u : σ.Points (FiniteCompletion ℚ vℓ.1)) = σ.dividingLocalMap n vℓ u :=
  rfl

@[simp]
theorem pairLevelSnd_apply_coe {Kℓ : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1))}
    {Cp : Subgroup (σ.Points (FiniteCompletion ℚ vp.1))} (u : pairLevel σ vℓ vp Kℓ Cp) :
    (pairLevelSnd Kℓ Cp u : σ.Points (FiniteCompletion ℚ vp.1)) = σ.dividingLocalMap n vp u :=
  rfl

variable (hn : n ≠ 0)

/-- The first component of the splitting of the embedded first factor. -/
theorem finiteAdelicPointsSplit_factorHom (u : σ.DividingPoints n) :
    σ.finiteAdelicPointsSplit n hn
        (CompactOpenLevel.factorHom (σ.finiteAdelicPointsSplit n hn) u) = (u, 1) := by
  rw [CompactOpenLevel.factorHom_apply, ContinuousMulEquiv.apply_symm_apply]

end Components

section Harris

variable {A : Type v} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A) [Module.Finite ℚ A]
  {ℓ p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hℓp : ℓ ≠ p)
  (vℓ : {v : FinitePlace ℚ // (ℓ : 𝓞 ℚ) ∈ v.asIdeal})
  (vp : {v : FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal})

/-- `σ(ℚ_ℓ)` inside `σ(∏_{v ∣ ℓ p} ℚ_v)`, with trivial component at `p`. -/
def pairInl : σ.Points (FiniteCompletion ℚ vℓ.1) →* σ.DividingPoints (ℓ * p) :=
  ((pairPointsEquiv σ hℓ hp hℓp vℓ vp).symm :
      σ.Points (FiniteCompletion ℚ vℓ.1) × σ.Points (FiniteCompletion ℚ vp.1) →*
        σ.DividingPoints (ℓ * p)).comp (MonoidHom.inl _ _)

/-- `σ(ℚ_p)` inside `σ(∏_{v ∣ ℓ p} ℚ_v)`, with trivial component at `ℓ`. -/
def pairInr : σ.Points (FiniteCompletion ℚ vp.1) →* σ.DividingPoints (ℓ * p) :=
  ((pairPointsEquiv σ hℓ hp hℓp vℓ vp).symm :
      σ.Points (FiniteCompletion ℚ vℓ.1) × σ.Points (FiniteCompletion ℚ vp.1) →*
        σ.DividingPoints (ℓ * p)).comp (MonoidHom.inr _ _)

theorem pairPointsEquiv_pairInl (a : σ.Points (FiniteCompletion ℚ vℓ.1)) :
    pairPointsEquiv σ hℓ hp hℓp vℓ vp (pairInl σ hℓ hp hℓp vℓ vp a) = (a, 1) :=
  (pairPointsEquiv σ hℓ hp hℓp vℓ vp).apply_symm_apply (a, 1)

theorem pairPointsEquiv_pairInr (c : σ.Points (FiniteCompletion ℚ vp.1)) :
    pairPointsEquiv σ hℓ hp hℓp vℓ vp (pairInr σ hℓ hp hℓp vℓ vp c) = (1, c) :=
  (pairPointsEquiv σ hℓ hp hℓp vℓ vp).apply_symm_apply (1, c)

theorem dividingLocalMap_ellPlace_pairInl (a : σ.Points (FiniteCompletion ℚ vℓ.1)) :
    σ.dividingLocalMap (ℓ * p) (ellPlace p vℓ) (pairInl σ hℓ hp hℓp vℓ vp a) = a := by
  have h := pairPointsEquiv_apply σ hℓ hp hℓp vℓ vp (pairInl σ hℓ hp hℓp vℓ vp a)
  rw [pairPointsEquiv_pairInl] at h
  exact (congrArg Prod.fst h).symm

theorem dividingLocalMap_primePlace_pairInl (a : σ.Points (FiniteCompletion ℚ vℓ.1)) :
    σ.dividingLocalMap (ℓ * p) (primePlace ℓ vp) (pairInl σ hℓ hp hℓp vℓ vp a) = 1 := by
  have h := pairPointsEquiv_apply σ hℓ hp hℓp vℓ vp (pairInl σ hℓ hp hℓp vℓ vp a)
  rw [pairPointsEquiv_pairInl] at h
  exact (congrArg Prod.snd h).symm

theorem dividingLocalMap_ellPlace_pairInr (c : σ.Points (FiniteCompletion ℚ vp.1)) :
    σ.dividingLocalMap (ℓ * p) (ellPlace p vℓ) (pairInr σ hℓ hp hℓp vℓ vp c) = 1 := by
  have h := pairPointsEquiv_apply σ hℓ hp hℓp vℓ vp (pairInr σ hℓ hp hℓp vℓ vp c)
  rw [pairPointsEquiv_pairInr] at h
  exact (congrArg Prod.fst h).symm

theorem dividingLocalMap_primePlace_pairInr (c : σ.Points (FiniteCompletion ℚ vp.1)) :
    σ.dividingLocalMap (ℓ * p) (primePlace ℓ vp) (pairInr σ hℓ hp hℓp vℓ vp c) = c := by
  have h := pairPointsEquiv_apply σ hℓ hp hℓp vℓ vp (pairInr σ hℓ hp hℓp vℓ vp c)
  rw [pairPointsEquiv_pairInr] at h
  exact (congrArg Prod.snd h).symm

variable (hn : ℓ * p ≠ 0) (Kℓ : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1)))
  {Cp Hp : Subgroup (σ.Points (FiniteCompletion ℚ vp.1))} (L : Subgroup (σ.PrimeToPoints (ℓ * p)))

/-- Harris's level factorization (1999, §4): `K_C = K^{ℓ,p} × K_ℓ × C_p` with its components at
`ℓ` and `p` and the embedding of `C_p` with trivial other components, adapted to
`K^{ℓ,p} × K_ℓ × H_p` for `H_p ≤ C_p`. -/
def harrisLevelFactorization (hHp : Hp ≤ Cp) :
    LevelFactorization
      (splitLevel σ (ℓ * p) hn (pairLevel σ (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Cp) L)
      (splitLevel σ (ℓ * p) hn (pairLevel σ (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Hp) L)
      Kℓ Cp (Hp.subgroupOf Cp) where
  le := splitLevel_mono (pairLevel_mono le_rfl hHp) le_rfl
  fst := (pairLevelFst (vℓ := ellPlace p vℓ) (vp := primePlace ℓ vp) Kℓ Cp).comp
    (splitLevelMap _ L)
  snd := (pairLevelSnd (vℓ := ellPlace p vℓ) (vp := primePlace ℓ vp) Kℓ Cp).comp
    (splitLevelMap _ L)
  inr := ((CompactOpenLevel.factorHom (σ.finiteAdelicPointsSplit (ℓ * p) hn)).comp
      ((pairInr σ hℓ hp hℓp vℓ vp).comp Cp.subtype)).codRestrict _ fun c =>
    factorHom_mem_splitLevel L (mem_pairLevel.2
      ⟨by
        change σ.dividingLocalMap (ℓ * p) (ellPlace p vℓ) (pairInr σ hℓ hp hℓp vℓ vp c) ∈ Kℓ
        rw [dividingLocalMap_ellPlace_pairInr]
        exact Kℓ.one_mem,
       by
        change σ.dividingLocalMap (ℓ * p) (primePlace ℓ vp) (pairInr σ hℓ hp hℓp vℓ vp c) ∈ Cp
        rw [dividingLocalMap_primePlace_pairInr]
        exact c.2⟩)
  fst_inr c := Subtype.ext <| by
    change σ.dividingLocalMap (ℓ * p) (ellPlace p vℓ) (σ.finiteAdelicPointsSplit (ℓ * p) hn
      (CompactOpenLevel.factorHom (σ.finiteAdelicPointsSplit (ℓ * p) hn)
        (pairInr σ hℓ hp hℓp vℓ vp c))).1 = 1
    rw [finiteAdelicPointsSplit_factorHom]
    exact dividingLocalMap_ellPlace_pairInr σ hℓ hp hℓp vℓ vp c
  snd_inr c := Subtype.ext <| by
    change σ.dividingLocalMap (ℓ * p) (primePlace ℓ vp) (σ.finiteAdelicPointsSplit (ℓ * p) hn
      (CompactOpenLevel.factorHom (σ.finiteAdelicPointsSplit (ℓ * p) hn)
        (pairInr σ hℓ hp hℓp vℓ vp c))).1 = c
    rw [finiteAdelicPointsSplit_factorHom]
    exact dividingLocalMap_primePlace_pairInr σ hℓ hp hℓp vℓ vp c
  mem_iff k := by
    rw [mem_splitLevel, mem_pairLevel, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.1.2, fun h => ⟨⟨k.2.1.1, h⟩, k.2.2⟩⟩

variable {σ hℓ hp hℓp vℓ vp hn Kℓ L}

@[simp]
theorem harrisLevelFactorization_fst_coe (hHp : Hp ≤ Cp)
    (k : splitLevel σ (ℓ * p) hn (pairLevel σ (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Cp) L) :
    ((harrisLevelFactorization σ hℓ hp hℓp vℓ vp hn Kℓ L hHp).fst k :
        σ.Points (FiniteCompletion ℚ vℓ.1)) =
      σ.dividingLocalMap (ℓ * p) (ellPlace p vℓ) (σ.finiteAdelicPointsSplit (ℓ * p) hn k).1 :=
  rfl

@[simp]
theorem harrisLevelFactorization_snd_coe (hHp : Hp ≤ Cp)
    (k : splitLevel σ (ℓ * p) hn (pairLevel σ (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Cp) L) :
    ((harrisLevelFactorization σ hℓ hp hℓp vℓ vp hn Kℓ L hHp).snd k :
        σ.Points (FiniteCompletion ℚ vp.1)) =
      σ.dividingLocalMap (ℓ * p) (primePlace ℓ vp) (σ.finiteAdelicPointsSplit (ℓ * p) hn k).1 :=
  rfl

theorem harrisLevelFactorization_inr_coe (hHp : Hp ≤ Cp) (c : Cp) :
    ((harrisLevelFactorization σ hℓ hp hℓp vℓ vp hn Kℓ L hHp).inr c : σ.FiniteAdelicPoints) =
      CompactOpenLevel.factorHom (σ.finiteAdelicPointsSplit (ℓ * p) hn)
        (pairInr σ hℓ hp hℓp vℓ vp c) :=
  rfl

/-- Under Harris's (4.5), every stabilizer of the level `K_C` has trivial components at `ℓ` and
`p`. -/
theorem harrisLevelFactorization_stabilizer_le
    (h : HarrisDividingLevelFree σ (ℓ * p) hn (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Cp L)
    (hHp : Hp ≤ Cp) (g : σ.FiniteAdelicPoints) :
    doubleCosetStabilizer σ.finiteAdelicDiagonal
        (splitLevel σ (ℓ * p) hn (pairLevel σ (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Cp) L) g ≤
      (harrisLevelFactorization σ hℓ hp hℓp vℓ vp hn Kℓ L hHp).fst.ker ⊓
        (harrisLevelFactorization σ hℓ hp hℓp vℓ vp hn Kℓ L hHp).snd.ker := by
  intro k hk
  have h1 : (σ.finiteAdelicPointsSplit (ℓ * p) hn k).1 = 1 :=
    Subgroup.mem_bot.1
      (Subgroup.mem_subgroupOf.1 (DividingLevelFree.doubleCosetStabilizer_le h le_rfl g hk)).1
  refine Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 ?_, MonoidHom.mem_ker.2 ?_⟩ <;>
  · ext
    simp [h1]

variable (σ hℓ hp hℓp vℓ vp hn Kℓ L) in
/-- The embedding `K_ℓ →* K^{ℓ,p} × K_ℓ × H_p` with trivial components away from `ℓ`. -/
def ellLevelHom (Hp : Subgroup (σ.Points (FiniteCompletion ℚ vp.1))) :
    Kℓ →* splitLevel σ (ℓ * p) hn (pairLevel σ (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Hp) L :=
  ((CompactOpenLevel.factorHom (σ.finiteAdelicPointsSplit (ℓ * p) hn)).comp
      ((pairInl σ hℓ hp hℓp vℓ vp).comp Kℓ.subtype)).codRestrict _ fun a =>
    factorHom_mem_splitLevel L (mem_pairLevel.2
      ⟨by
        change σ.dividingLocalMap (ℓ * p) (ellPlace p vℓ) (pairInl σ hℓ hp hℓp vℓ vp a) ∈ Kℓ
        rw [dividingLocalMap_ellPlace_pairInl]
        exact a.2,
       by
        change σ.dividingLocalMap (ℓ * p) (primePlace ℓ vp) (pairInl σ hℓ hp hℓp vℓ vp a) ∈ Hp
        rw [dividingLocalMap_primePlace_pairInl]
        exact Hp.one_mem⟩)

theorem ellLevelHom_coe (a : Kℓ) :
    (ellLevelHom σ hℓ hp hℓp vℓ vp hn Kℓ L Hp a : σ.FiniteAdelicPoints) =
      CompactOpenLevel.factorHom (σ.finiteAdelicPointsSplit (ℓ * p) hn)
        (pairInl σ hℓ hp hℓp vℓ vp a) :=
  rfl

/-- `K^{ℓ,p} × K_ℓ × H_p` is generated by `K_ℓ` and `H(m) = K^{ℓ,p} × K_ℓ(m) × H_p`: every `k` is
`j_ℓ(k_ℓ) · ((j_ℓ k_ℓ)⁻¹ k)` with the second factor in `H(m)`. -/
theorem exists_eq_ellLevelHom_mul {Kℓm : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1))}
    (k : splitLevel σ (ℓ * p) hn (pairLevel σ (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Hp) L) :
    ∃ a : Kℓ, ∃ m ∈ (splitLevel σ (ℓ * p) hn
        (pairLevel σ (ellPlace p vℓ) (primePlace ℓ vp) Kℓm Hp) L).subgroupOf
          (splitLevel σ (ℓ * p) hn (pairLevel σ (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Hp) L),
      k = ellLevelHom σ hℓ hp hℓp vℓ vp hn Kℓ L Hp a * m := by
  set e := σ.finiteAdelicPointsSplit (ℓ * p) hn
  let a : Kℓ := ⟨σ.dividingLocalMap (ℓ * p) (ellPlace p vℓ) (e k).1, k.2.1.1⟩
  refine ⟨a, (ellLevelHom σ hℓ hp hℓp vℓ vp hn Kℓ L Hp a)⁻¹ * k, ?_, by group⟩
  have he : e ((((ellLevelHom σ hℓ hp hℓp vℓ vp hn Kℓ L Hp a)⁻¹ * k :
      splitLevel σ (ℓ * p) hn (pairLevel σ (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Hp) L) :
        σ.FiniteAdelicPoints)) =
      ((pairInl σ hℓ hp hℓp vℓ vp a)⁻¹ * (e k).1, (e k).2) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, ellLevelHom_coe, map_mul, map_inv,
      finiteAdelicPointsSplit_factorHom]
    ext <;> simp
  rw [Subgroup.mem_subgroupOf, mem_splitLevel, he, mem_pairLevel]
  refine ⟨⟨?_, ?_⟩, k.2.2⟩
  · rw [map_mul, map_inv, dividingLocalMap_ellPlace_pairInl, inv_mul_cancel]
    exact Kℓm.one_mem
  · rw [map_mul, map_inv, dividingLocalMap_primePlace_pairInl, inv_one, one_mul]
    exact k.2.1.2

variable {R : Type uR} [CommRing R] {V : Type t} [AddCommGroup V] [Module R V]

section Forms

variable [(Hp.subgroupOf Cp).Normal]

/-- Harris's (4.8) at the level `K^{ℓ,p} × K_ℓ × H_p` (1999, p.311): under (4.5), the forms of level
`K^{ℓ,p} × K_ℓ × H_p` with coefficients a representation `ρ` of `K_ℓ` (through the component at
`ℓ`) are `Hom_R(R[(C_p ⧸ H_p) × GJ(ℚ) \ GJ(A_f) / K_C], V)`, with `K_C = K^{ℓ,p} × K_ℓ × C_p`. -/
def harrisFormsEquiv
    (h : HarrisDividingLevelFree σ (ℓ * p) hn (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Cp L)
    (hHp : Hp ≤ Cp) (ρ : Representation R Kℓ V) :
    forms σ.finiteAdelicDiagonal
        (splitLevel σ (ℓ * p) hn (pairLevel σ (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Hp) L)
        ((harrisLevelFactorization σ hℓ hp hℓp vℓ vp hn Kℓ L hHp).rep ρ) ≃ₗ[R]
      (((Cp ⧸ Hp.subgroupOf Cp) × DoubleCosets σ.finiteAdelicDiagonal
          (splitLevel σ (ℓ * p) hn (pairLevel σ (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Cp) L) →₀
            R) →ₗ[R] V) :=
  (harrisLevelFactorization σ hℓ hp hℓp vℓ vp hn Kℓ L hHp).factorFinsuppEquiv
    (harrisLevelFactorization_stabilizer_le h hHp)

/-- The linear map attached to a form `f` sends the basis vector of `([c], x)` to
`f (x.out * (j_p c)⁻¹)`, where `j_p c` is `c ∈ C_p` with trivial other components. -/
theorem harrisFormsEquiv_apply_single
    (h : HarrisDividingLevelFree σ (ℓ * p) hn (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Cp L)
    (hHp : Hp ≤ Cp) (ρ : Representation R Kℓ V)
    (f : forms σ.finiteAdelicDiagonal
      (splitLevel σ (ℓ * p) hn (pairLevel σ (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Hp) L)
      ((harrisLevelFactorization σ hℓ hp hℓp vℓ vp hn Kℓ L hHp).rep ρ)) (c : Cp)
    (x : DoubleCosets σ.finiteAdelicDiagonal
      (splitLevel σ (ℓ * p) hn (pairLevel σ (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Cp) L)) :
    harrisFormsEquiv h hHp ρ f (Finsupp.single ((c : Cp ⧸ Hp.subgroupOf Cp), x) 1) =
      f.1 (x.out * (CompactOpenLevel.factorHom (σ.finiteAdelicPointsSplit (ℓ * p) hn)
        (pairInr σ hℓ hp hℓp vℓ vp c))⁻¹) :=
  LevelFactorization.factorFinsuppEquiv_apply_single _ _ f c x

variable {Kℓm : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1))} [(Kℓm.subgroupOf Kℓ).Normal]

/-- Harris's (4.8) (1999, p.311): under (4.5), for `K_ℓ(m)` normal in `K_ℓ` and `H_p` normal in
`C_p`, the invariants of `K_ℓ` (embedded by `ellLevelHom`) for the level action on the forms of
level `H(m) = K^{ℓ,p} × K_ℓ(m) × H_p` with coefficients `ρ` are
`Hom_R(R[(C_p ⧸ H_p) × GJ(ℚ) \ GJ(A_f) / K_C], V)`, with `K_C = K^{ℓ,p} × K_ℓ × C_p`. The level
action is the published `levelAction` of `K^{ℓ,p} × K_ℓ × H_p`, `(k • f) g = ρ (k_ℓ) (f (g k))`. -/
def harrisInvariantsEquiv
    (h : HarrisDividingLevelFree σ (ℓ * p) hn (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Cp L)
    (hℓm : Kℓm ≤ Kℓ) (hHp : Hp ≤ Cp) (ρ : Representation R Kℓ V) :
    Representation.invariants
        ((levelAction σ.finiteAdelicDiagonal
          ((harrisLevelFactorization σ hℓ hp hℓp vℓ vp hn Kℓ L hHp).rep ρ)
          (splitLevel_mono (hn := hn) (pairLevel_mono hℓm le_rfl) (le_refl L))).comp
          (ellLevelHom σ hℓ hp hℓp vℓ vp hn Kℓ L Hp)) ≃ₗ[R]
      (((Cp ⧸ Hp.subgroupOf Cp) × DoubleCosets σ.finiteAdelicDiagonal
          (splitLevel σ (ℓ * p) hn (pairLevel σ (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Cp) L) →₀
            R) →ₗ[R] V) :=
  (LinearEquiv.ofEq _ _
      (invariants_comp_eq _ _ _ fun k => exists_eq_ellLevelHom_mul (Kℓm := Kℓm) k)).trans
    ((levelInvariantsEquiv _ _ _).trans (harrisFormsEquiv h hHp ρ))

end Forms

end Harris

end Langlands.Shimura.DefiniteForms
