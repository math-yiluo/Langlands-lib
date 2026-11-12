import Langlands.Shimura.Unitary.HarrisPairPoints

/-!
# Harris's (4.5) for sufficiently small levels

Harris 1999, §4, p.310: "We strengthen (3.6) by assuming that `K = K^{ℓ,p} × K_ℓ × K_p` and that
`K^{ℓ,p}` is sufficiently small so that (4.5) `K_ℓ × C_p` acts without fixed points on
`GJ(ℚ)\GJ(𝔸)/K_∞ · K^{ℓ,p}`."

This module proves (4.5) (`DividingLevelFree`) from two conditions:

* `RationalFiniteOrder σ K`: every rational point `γ` whose diagonal image lies in a conjugate
  `g K g⁻¹` of the level has finite order;
* `LevelTorsionFreeAt σ v (e⁻¹ (1 × L))` at a place `v` not dividing `n`: the elements of the
  away level `K^{ℓ,p}` whose component at `v` has finite order have trivial component at `v`.

The proof: if `g u` and `g` have the same class, then `γ g = g u a` with `γ` rational and `a` in
the away level. So `g⁻¹ γ g` lies in the level and `γ` has finite order. At `v` the factor `u` is
trivial, so the component of `a` at `v` has finite order and is trivial. Then `γ` is trivial at
`v`, hence `γ = 1`, and `u = a⁻¹` lies in both factors, so `u = 1`.
-/

noncomputable section

open Langlands.Global Langlands.Shimura.EquivariantForms
open scoped NumberField TensorProduct

set_option autoImplicit false

universe v

namespace Langlands.Shimura

namespace AlgebraInvolution

variable {A : Type v} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A)

/-- The diagonal map from the rational points to the points over a nontrivial `ℚ`-algebra is
injective. -/
theorem diagonalPoints_injective (S : Type*) [CommRing S] [Algebra ℚ S] [Nontrivial S] :
    Function.Injective (σ.diagonalPoints S) := by
  intro x y h
  have h1 : (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] S ⊗[ℚ] A) (x.1.1 : A) =
      Algebra.TensorProduct.includeRight (y.1.1 : A) :=
    congrArg (fun z : σ.Points S => ((z.1.1 : (S ⊗[ℚ] A)ˣ) : S ⊗[ℚ] A)) h
  have h2 : algebraMap ℚ S (x.1.2 : ℚ) = algebraMap ℚ S (y.1.2 : ℚ) :=
    congrArg (fun z : σ.Points S => ((z.1.2 : Sˣ) : S)) h
  exact Subtype.ext (Prod.ext
    (Units.ext (Algebra.TensorProduct.includeRight_injective (algebraMap ℚ S).injective h1))
    (Units.ext ((algebraMap ℚ S).injective h2)))

end AlgebraInvolution

namespace DefiniteForms

variable {A : Type v} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A) [Module.Finite ℚ A]

section PrimeTo

variable (n : ℕ)

/-- Evaluation of the prime-to-`n` finite adeles at a place not dividing `n`. -/
def primeToEvaluation (v : PrimeToFinitePlace n) :
    PrimeToFiniteAdeles n →ₐ[ℚ] FiniteCompletion ℚ v.1 where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The component at a place not dividing `n` of the prime-to-`n` points. -/
def primeToLocalMap (v : PrimeToFinitePlace n) :
    σ.PrimeToPoints n →* σ.Points (FiniteCompletion ℚ v.1) :=
  σ.pointsMap (primeToEvaluation n v)

variable {n} (hn : n ≠ 0)

/-- At a place not dividing `n`, the local component of a finite adelic point is the component
of its prime-to-`n` part. -/
theorem primeToLocalMap_finiteAdelicPointsSplit (v : PrimeToFinitePlace n)
    (g : σ.FiniteAdelicPoints) :
    primeToLocalMap σ n v (σ.finiteAdelicPointsSplit n hn g).2 = σ.finiteLocalMap v.1 g := by
  have h : (primeToEvaluation n v).comp (primeToFiniteRestriction n).toAlgHom =
      AlgebraInvolution.finiteEvaluation v.1 :=
    AlgHom.ext fun _ => rfl
  change σ.pointsMap _ (σ.finiteAdelicPointsSplit n hn g).2 = σ.pointsMap _ g
  rw [AlgebraInvolution.finiteAdelicPointsSplit_apply_snd, AlgebraInvolution.pointsMap_apply_apply]
  exact congrArg (fun f => σ.pointsMap f g) h

/-- The embedded factor at the places dividing `n` is trivial at every other place. -/
theorem finiteLocalMap_factorHom (v : PrimeToFinitePlace n) (u : σ.DividingPoints n) :
    σ.finiteLocalMap v.1 (CompactOpenLevel.factorHom (σ.finiteAdelicPointsSplit n hn) u) = 1 := by
  rw [← primeToLocalMap_finiteAdelicPointsSplit σ hn, CompactOpenLevel.factorHom_apply,
    ContinuousMulEquiv.apply_symm_apply, map_one]

end PrimeTo

/-- Harris's smallness away from `ℓ p` at one place `v`: an element of `K` whose component at `v`
has finite order has trivial component at `v`. -/
def LevelTorsionFreeAt (v : FinitePlace ℚ) (K : Subgroup σ.FiniteAdelicPoints) : Prop :=
  ∀ k ∈ K, IsOfFinOrder (σ.finiteLocalMap v k) → σ.finiteLocalMap v k = 1

/-- A rational point whose diagonal image lies in a conjugate `g K g⁻¹` of the level `K` has
finite order. For a definite group and a compact open `K` this is the finiteness of `GJ(ℚ) ∩ g K
g⁻¹`; here it is a hypothesis. -/
def RationalFiniteOrder (K : Subgroup σ.FiniteAdelicPoints) : Prop :=
  ∀ (g : σ.FiniteAdelicPoints) (γ : σ.similitudes),
    g⁻¹ * σ.finiteAdelicDiagonal γ * g ∈ K → IsOfFinOrder γ

variable {σ}

theorem LevelTorsionFreeAt.mono {v : FinitePlace ℚ} {K K' : Subgroup σ.FiniteAdelicPoints}
    (h : LevelTorsionFreeAt σ v K) (hK : K' ≤ K) : LevelTorsionFreeAt σ v K' :=
  fun k hk => h k (hK hk)

omit [Module.Finite ℚ A] in
theorem RationalFiniteOrder.mono {K K' : Subgroup σ.FiniteAdelicPoints}
    (h : RationalFiniteOrder σ K) (hK : K' ≤ K) : RationalFiniteOrder σ K' :=
  fun g γ hγ => h g γ (hK hγ)

variable {n : ℕ} {hn : n ≠ 0}

/-- Harris's (4.5) for a sufficiently small level: if rational points in conjugates of
`e⁻¹ (U × L)` have finite order and `e⁻¹ (1 × L)` is torsion-free at a place `v` not dividing `n`,
then `U` acts without fixed points on `GJ(ℚ) \ GJ(A_f) / e⁻¹ (1 × L)`. -/
theorem DividingLevelFree.of_levelTorsionFreeAt {U : Subgroup (σ.DividingPoints n)}
    {L : Subgroup (σ.PrimeToPoints n)} (hfin : RationalFiniteOrder σ (splitLevel σ n hn U L))
    (v : PrimeToFinitePlace n) (htf : LevelTorsionFreeAt σ v.1 (splitLevel σ n hn ⊥ L)) :
    DividingLevelFree σ n hn U L := by
  intro g u h
  set e := σ.finiteAdelicPointsSplit n hn
  set f := CompactOpenLevel.factorHom e (u : σ.DividingPoints n)
  obtain ⟨x, ⟨γ, rfl⟩, k, hk, hg⟩ := DoubleCoset.eq.1 h
  -- `g = γ (g f) k`, so `g⁻¹ γ g = k⁻¹ f⁻¹`.
  have hdg : σ.finiteAdelicDiagonal γ * g = g * k⁻¹ * f⁻¹ := by
    calc σ.finiteAdelicDiagonal γ * g
        = σ.finiteAdelicDiagonal γ * (g * f) * k * k⁻¹ * f⁻¹ := by group
      _ = g * k⁻¹ * f⁻¹ := by rw [← hg]
  have hconj : g⁻¹ * σ.finiteAdelicDiagonal γ * g = k⁻¹ * f⁻¹ := by
    rw [mul_assoc, hdg]
    group
  have hf : f ∈ splitLevel σ n hn U L := factorHom_mem_splitLevel L u.2
  have hkU : k ∈ splitLevel σ n hn U L := splitLevel_mono bot_le le_rfl hk
  have hγfin : IsOfFinOrder γ :=
    hfin g γ (hconj ▸ (splitLevel σ n hn U L).mul_mem
      ((splitLevel σ n hn U L).inv_mem hkU) ((splitLevel σ n hn U L).inv_mem hf))
  have hfv : σ.finiteLocalMap v.1 f = 1 := finiteLocalMap_factorHom σ hn v u
  have hloc : σ.finiteLocalMap v.1 (g⁻¹ * σ.finiteAdelicDiagonal γ * g) =
      (σ.finiteLocalMap v.1 k)⁻¹ := by
    rw [hconj, map_mul, map_inv, map_inv, hfv, inv_one, mul_one]
  have hkfin : IsOfFinOrder (σ.finiteLocalMap v.1 k) := by
    have h1 : IsOfFinOrder (g⁻¹ * σ.finiteAdelicDiagonal γ * g) := by
      have := ((MulAut.conj g⁻¹).toMonoidHom.comp σ.finiteAdelicDiagonal).isOfFinOrder hγfin
      simpa [MulAut.conj_apply] using this
    have h2 := (σ.finiteLocalMap v.1).toMonoidHom.isOfFinOrder h1
    change IsOfFinOrder (σ.finiteLocalMap v.1 _) at h2
    rw [hloc] at h2
    exact isOfFinOrder_inv_iff.1 h2
  have hk1 : σ.finiteLocalMap v.1 k = 1 := htf k hk hkfin
  have hγ1 : γ = 1 := by
    apply σ.diagonalPoints_injective (FiniteCompletion ℚ v.1)
    rw [map_one, ← AlgebraInvolution.finiteLocalMap_diagonal]
    have h1 : σ.finiteLocalMap v.1 (g⁻¹ * σ.finiteAdelicDiagonal γ * g) = 1 := by
      rw [hloc, hk1, inv_one]
    rw [map_mul, map_mul, map_inv] at h1
    calc σ.finiteLocalMap v.1 (σ.finiteAdelicDiagonal γ)
        = σ.finiteLocalMap v.1 g * ((σ.finiteLocalMap v.1 g)⁻¹ *
            σ.finiteLocalMap v.1 (σ.finiteAdelicDiagonal γ) * σ.finiteLocalMap v.1 g) *
              (σ.finiteLocalMap v.1 g)⁻¹ := by group
      _ = 1 := by rw [h1]; group
  subst hγ1
  -- Now `g = g f k`, so `f = k⁻¹`.
  have hfk : f = k⁻¹ := by
    rw [map_one, one_mul, mul_assoc, left_eq_mul] at hg
    exact eq_inv_of_mul_eq_one_left hg
  have h1 : (e k).1 = 1 := Subgroup.mem_bot.1 hk.1
  have := congrArg (fun y => (e y).1) hfk
  simp only [f, CompactOpenLevel.factorHom_apply, ContinuousMulEquiv.apply_symm_apply, map_inv,
    Prod.fst_inv, h1, inv_one] at this
  exact this

/-- Harris's (4.5) for a sufficiently small `K^{ℓ,p}` (1999, p.310): if rational points in
conjugates of `K^{ℓ,p} × K_ℓ × C_p` have finite order and `K^{ℓ,p}` is torsion-free at a place `v`
over a prime other than `ℓ` and `p`, then `K_ℓ × C_p` acts without fixed points on
`GJ(ℚ) \ GJ(A_f) / K^{ℓ,p}`. -/
theorem HarrisDividingLevelFree.of_levelTorsionFreeAt {ℓ p : ℕ} (hn : ℓ * p ≠ 0)
    (vℓ : {v : FinitePlace ℚ // ((ℓ * p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal})
    (vp : {v : FinitePlace ℚ // ((ℓ * p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal})
    {Kℓ : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1))}
    {Cp : Subgroup (σ.Points (FiniteCompletion ℚ vp.1))} {L : Subgroup (σ.PrimeToPoints (ℓ * p))}
    (hfin : RationalFiniteOrder σ (splitLevel σ (ℓ * p) hn (pairLevel σ vℓ vp Kℓ Cp) L))
    (v : FinitePlace ℚ) (hvℓ : (ℓ : 𝓞 ℚ) ∉ v.asIdeal) (hvp : (p : 𝓞 ℚ) ∉ v.asIdeal)
    (htf : LevelTorsionFreeAt σ v (splitLevel σ (ℓ * p) hn ⊥ L)) :
    HarrisDividingLevelFree σ (ℓ * p) hn vℓ vp Kℓ Cp L :=
  DividingLevelFree.of_levelTorsionFreeAt hfin
    ⟨v, fun h => ((natCast_mul_mem_asIdeal_iff v).1 h).elim hvℓ hvp⟩ htf

end DefiniteForms

end Langlands.Shimura
