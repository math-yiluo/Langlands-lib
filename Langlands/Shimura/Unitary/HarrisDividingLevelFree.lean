import Langlands.Shimura.DefiniteFormsDoubleCoset
import Langlands.Shimura.SplitLevelTower
import Langlands.Shimura.Unitary.PointsSplit

/-!
# Harris's hypothesis (4.5) and the restriction to double cosets (4.7)

Harris 1999, §4, p.310: "We strengthen (3.6) by assuming that `K = K^{ℓ,p} × K_ℓ × K_p` and that
`K^{ℓ,p}` is sufficiently small so that (4.5) `K_ℓ × C_p` acts without fixed points on
`GJ(ℚ)\GJ(𝔸)/K_∞ · K^{ℓ,p}`." p.311: "hypothesis (4.5) implies that restriction to the double
cosets in (4.6) defines an isomorphism
(4.7) `𝒜_ℓ(GJ, 𝒪_m, H(m)) ⥲ [D_m(K_ℓ × C_p)^M]^{K_ℓ(m) × H_p}`."

Through the published splitting `e : σ(A_f) ≃ₜ* σ(∏_{v ∣ n} ℚ_v) × σ(A_f^n)`, a subgroup `U` of the
first factor acts by right translation on `GJ(ℚ) \ GJ(A_f) / L` for a subgroup `L` of the second
factor, since the two factors commute. `DividingLevelFree σ n hn U L` says that this action has
no fixed points. It forces all stabilizers of the level `e⁻¹ (U × L)` into `e⁻¹ (1 × L)`; hence
Harris's (3.6) (`DividingLevelFree.localLevelFree`) and a restriction isomorphism of the form
(4.7) for every level `e⁻¹ (U' × L)` with `U'` normal in `U` (`DividingLevelFree.splitLevelEquiv`).
Harris's case is `n = ℓ p`, `U = K_ℓ × C_p` (`pairLevel`) and `U' = K_ℓ(m) × H_p`.

Harris's (4.6) takes double cosets modulo `K = K^{ℓ,p} × K_ℓ × K_p`, while (4.7) uses
`K_ℓ × C_p` with the number `M` of these double cosets. For `K_p < C_p` the two do not match.
`HarrisDividingLevelFree.restrictionEquiv` takes double cosets modulo
`K_C = K^{ℓ,p} × K_ℓ × C_p` with factor `K_ℓ × C_p`; `HarrisDividingLevelFree.restrictionEquivOfLe`
takes them modulo Harris's `K` with factor `K_ℓ × K_p`.
-/

noncomputable section

open Langlands.Global Langlands.Shimura.EquivariantForms
open scoped NumberField

set_option autoImplicit false

universe v uR

namespace Langlands.Shimura.DefiniteForms

variable {A : Type v} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A) [Module.Finite ℚ A]
  (n : ℕ) (hn : n ≠ 0)

section Split

/-- The level `e⁻¹ (U × L)` of `σ(A_f)`, for subgroups `U` of `σ(∏_{v ∣ n} ℚ_v)` and `L` of
`σ(A_f^n)`, through the published splitting `e = finiteAdelicPointsSplit`. -/
def splitLevel (U : Subgroup (σ.DividingPoints n)) (L : Subgroup (σ.PrimeToPoints n)) :
    Subgroup σ.FiniteAdelicPoints :=
  (U.prod L).comap (σ.finiteAdelicPointsSplit n hn).toMonoidHom

variable {σ n hn}

theorem mem_splitLevel {U : Subgroup (σ.DividingPoints n)} {L : Subgroup (σ.PrimeToPoints n)}
    {g : σ.FiniteAdelicPoints} :
    g ∈ splitLevel σ n hn U L ↔
      (σ.finiteAdelicPointsSplit n hn g).1 ∈ U ∧ (σ.finiteAdelicPointsSplit n hn g).2 ∈ L :=
  Iff.rfl

theorem splitLevel_mono {U U' : Subgroup (σ.DividingPoints n)}
    {L L' : Subgroup (σ.PrimeToPoints n)} (hU : U' ≤ U) (hL : L' ≤ L) :
    splitLevel σ n hn U' L' ≤ splitLevel σ n hn U L :=
  fun _ hg => ⟨hU hg.1, hL hg.2⟩

/-- The first factor, embedded in `σ(A_f)` with trivial prime-to-`n` component, lies in
`e⁻¹ (U × L)` on `U`. -/
theorem factorHom_mem_splitLevel {U : Subgroup (σ.DividingPoints n)}
    (L : Subgroup (σ.PrimeToPoints n)) {u : σ.DividingPoints n} (hu : u ∈ U) :
    CompactOpenLevel.factorHom (σ.finiteAdelicPointsSplit n hn) u ∈ splitLevel σ n hn U L := by
  rw [mem_splitLevel, CompactOpenLevel.factorHom_apply, ContinuousMulEquiv.apply_symm_apply]
  exact ⟨hu, L.one_mem⟩

/-- `e⁻¹ (1 × L)` is `L` embedded in `σ(A_f)` with trivial component at the places dividing
`n`. -/
theorem mem_splitLevel_bot {L : Subgroup (σ.PrimeToPoints n)} {g : σ.FiniteAdelicPoints} :
    g ∈ splitLevel σ n hn ⊥ L ↔
      ∃ a ∈ L, CompactOpenLevel.awayHom (σ.finiteAdelicPointsSplit n hn) a = g := by
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ := mem_splitLevel.1 hg
    refine ⟨_, h2, ?_⟩
    have h := CompactOpenLevel.factorHom_mul_awayHom (σ.finiteAdelicPointsSplit n hn) g
    rwa [Subgroup.mem_bot.mp h1, map_one, one_mul] at h
  · rintro ⟨a, ha, rfl⟩
    rw [mem_splitLevel, CompactOpenLevel.awayHom_apply, ContinuousMulEquiv.apply_symm_apply]
    exact ⟨Subgroup.one_mem _, ha⟩

/-- Right translation by the first factor descends to `GJ(ℚ) \ GJ(A_f) / e⁻¹ (1 × L)`, since the
two factors commute. -/
theorem mk_mul_factorHom_eq {L : Subgroup (σ.PrimeToPoints n)} {g g' : σ.FiniteAdelicPoints}
    (h : DoubleCoset.mk σ.finiteAdelicDiagonal.range (splitLevel σ n hn ⊥ L) g =
      DoubleCoset.mk σ.finiteAdelicDiagonal.range (splitLevel σ n hn ⊥ L) g')
    (u : σ.DividingPoints n) :
    DoubleCoset.mk σ.finiteAdelicDiagonal.range (splitLevel σ n hn ⊥ L)
        (g * CompactOpenLevel.factorHom (σ.finiteAdelicPointsSplit n hn) u) =
      DoubleCoset.mk σ.finiteAdelicDiagonal.range (splitLevel σ n hn ⊥ L)
        (g' * CompactOpenLevel.factorHom (σ.finiteAdelicPointsSplit n hn) u) := by
  obtain ⟨γ, hγ, k, hk, rfl⟩ := DoubleCoset.eq.1 h
  obtain ⟨a, -, rfl⟩ := mem_splitLevel_bot.1 hk
  refine DoubleCoset.eq.2 ⟨γ, hγ, _, hk, ?_⟩
  rw [mul_assoc (γ * g), (CompactOpenLevel.factorHom_commute_awayHom _ u a).symm.eq, mul_assoc,
    mul_assoc, mul_assoc]

variable (σ n hn) in
/-- Harris's (4.5) (1999, p.310): the subgroup `U` of `σ(∏_{v ∣ n} ℚ_v)` acts without fixed
points on `GJ(ℚ) \ GJ(A_f) / L` for a subgroup `L` of `σ(A_f^n)`. That is, for `g` in `σ(A_f)`
and `u ∈ U`, if `g u` and `g` have the same class in `GJ(ℚ) \ GJ(A_f) / e⁻¹ (1 × L)` then
`u = 1`; here `u` is embedded with trivial prime-to-`n` component. -/
def DividingLevelFree (U : Subgroup (σ.DividingPoints n)) (L : Subgroup (σ.PrimeToPoints n)) :
    Prop :=
  ∀ (g : σ.FiniteAdelicPoints) (u : U),
    DoubleCoset.mk σ.finiteAdelicDiagonal.range (splitLevel σ n hn ⊥ L)
        (g * CompactOpenLevel.factorHom (σ.finiteAdelicPointsSplit n hn) u) =
      DoubleCoset.mk σ.finiteAdelicDiagonal.range (splitLevel σ n hn ⊥ L) g →
    (u : σ.DividingPoints n) = 1

namespace DividingLevelFree

variable {U : Subgroup (σ.DividingPoints n)} {L : Subgroup (σ.PrimeToPoints n)}

/-- (4.5) passes to smaller `U` and smaller `L`. -/
theorem mono (h : DividingLevelFree σ n hn U L) {U' : Subgroup (σ.DividingPoints n)}
    {L' : Subgroup (σ.PrimeToPoints n)} (hU : U' ≤ U) (hL : L' ≤ L) :
    DividingLevelFree σ n hn U' L' := by
  intro g u he
  obtain ⟨γ, hγ, k, hk, hg⟩ := DoubleCoset.eq.1 he
  exact h g ⟨u, hU u.2⟩ (DoubleCoset.eq.2 ⟨γ, hγ, k, splitLevel_mono le_rfl hL hk, hg⟩)

/-- Under (4.5), every stabilizer `Δ_g` of the level `e⁻¹ (U' × L)`, `U' ≤ U`, lies in
`e⁻¹ (1 × L)`. -/
theorem doubleCosetStabilizer_le (h : DividingLevelFree σ n hn U L)
    {U' : Subgroup (σ.DividingPoints n)} (hU : U' ≤ U) (g : σ.FiniteAdelicPoints) :
    doubleCosetStabilizer σ.finiteAdelicDiagonal (splitLevel σ n hn U' L) g ≤
      (splitLevel σ n hn ⊥ L).subgroupOf (splitLevel σ n hn U' L) := by
  rintro k ⟨γ, hγ⟩
  set e := σ.finiteAdelicPointsSplit n hn
  have hk : CompactOpenLevel.factorHom e (e k).1 * CompactOpenLevel.awayHom e (e k).2 =
      (k : σ.FiniteAdelicPoints) :=
    CompactOpenLevel.factorHom_mul_awayHom e k
  have hu : (e k).1 ∈ U := hU k.2.1
  have h1 : (e k).1 = 1 := by
    refine h g ⟨_, hu⟩ (DoubleCoset.eq.2 ⟨σ.finiteAdelicDiagonal γ⁻¹, ⟨γ⁻¹, rfl⟩,
      CompactOpenLevel.awayHom e (e k).2, mem_splitLevel_bot.2 ⟨_, k.2.2, rfl⟩, ?_⟩)
    change g = σ.finiteAdelicDiagonal γ⁻¹ * (g * CompactOpenLevel.factorHom e (e k).1) *
      CompactOpenLevel.awayHom e (e k).2
    rw [mul_assoc _ (g * _), mul_assoc g, hk, ← hγ, map_inv, inv_mul_cancel_left]
  exact Subgroup.mem_subgroupOf.2 ⟨Subgroup.mem_bot.2 h1, k.2.2⟩

/-- (4.5) holds exactly when every stabilizer `Δ_g` of `e⁻¹ (U × L)` lies in `e⁻¹ (1 × L)`. -/
theorem iff_doubleCosetStabilizer_le :
    DividingLevelFree σ n hn U L ↔
      ∀ g : σ.FiniteAdelicPoints,
        doubleCosetStabilizer σ.finiteAdelicDiagonal (splitLevel σ n hn U L) g ≤
          (splitLevel σ n hn ⊥ L).subgroupOf (splitLevel σ n hn U L) := by
  refine ⟨fun h => h.doubleCosetStabilizer_le le_rfl, fun hΔ g u he => ?_⟩
  have hfree := (doubleCosetStabilizer_le_iff σ.finiteAdelicDiagonal
    (splitLevel_mono bot_le le_rfl)).1 hΔ g
    ⟨_, factorHom_mem_splitLevel L u.2⟩ he
  have h1 : (σ.finiteAdelicPointsSplit n hn
      (CompactOpenLevel.factorHom (σ.finiteAdelicPointsSplit n hn) u)).1 ∈
        (⊥ : Subgroup (σ.DividingPoints n)) :=
    (mem_splitLevel.1 (Subgroup.mem_subgroupOf.1 hfree)).1
  rwa [CompactOpenLevel.factorHom_apply, ContinuousMulEquiv.apply_symm_apply,
    Subgroup.mem_bot] at h1

/-- Harris's remark that (4.5) strengthens (3.6): under (4.5), the level `K = e⁻¹ (U' × L)`,
`U' ≤ U`, satisfies the published `LocalLevelFree` (Harris's (3.6)) at every place dividing
`n`. -/
theorem localLevelFree (h : DividingLevelFree σ n hn U L) {U' : Subgroup (σ.DividingPoints n)}
    (hU : U' ≤ U) (v : {v : FinitePlace ℚ // (n : 𝓞 ℚ) ∈ v.asIdeal}) :
    LocalLevelFree σ v.1 (splitLevel σ n hn U' L) := by
  rw [localLevelFree_iff]
  intro g k hk
  have h1 := (mem_splitLevel.1 (Subgroup.mem_subgroupOf.1 (h.doubleCosetStabilizer_le hU g hk))).1
  refine Subgroup.mem_subgroupOf.2 ⟨k.2, ?_⟩
  change σ.finiteLocalMap v.1 k = 1
  rw [← σ.dividingLocalMap_finiteAdelicPointsSplit n hn v, Subgroup.mem_bot.1 h1, map_one]

end DividingLevelFree

section Quotient

variable (U : Subgroup (σ.DividingPoints n)) (L : Subgroup (σ.PrimeToPoints n))

/-- The component map `k ↦ (e k).1` from `e⁻¹ (U × L)` onto `U`. -/
def splitLevelMap : splitLevel σ n hn U L →* U where
  toFun k := ⟨(σ.finiteAdelicPointsSplit n hn k).1, k.2.1⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

@[simp]
theorem splitLevelMap_apply_coe (k : splitLevel σ n hn U L) :
    (splitLevelMap U L k : σ.DividingPoints n) = (σ.finiteAdelicPointsSplit n hn k).1 :=
  rfl

theorem splitLevelMap_surjective : Function.Surjective (splitLevelMap (hn := hn) U L) := by
  intro u
  refine ⟨⟨_, factorHom_mem_splitLevel L u.2⟩, Subtype.ext ?_⟩
  simp [CompactOpenLevel.factorHom_apply]

variable {U} (U' : Subgroup (σ.DividingPoints n))

/-- For `U' ≤ U`, `e⁻¹ (U' × L)` is, inside `e⁻¹ (U × L)`, the inverse image of `U'`. -/
theorem splitLevel_subgroupOf :
    (splitLevel σ n hn U' L).subgroupOf (splitLevel σ n hn U L) =
      (U'.subgroupOf U).comap (splitLevelMap U L) := by
  ext k
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, splitLevelMap_apply_coe]
  exact ⟨fun hk => hk.1, fun hk => ⟨hk, k.2.2⟩⟩

variable [(U'.subgroupOf U).Normal]

instance splitLevel_subgroupOf_normal :
    ((splitLevel σ n hn U' L).subgroupOf (splitLevel σ n hn U L)).Normal := by
  rw [splitLevel_subgroupOf]
  infer_instance

/-- The bijection `e⁻¹ (U × L) ⧸ e⁻¹ (U' × L) ≃ U ⧸ U'`, `[k] ↦ [(e k).1]`. -/
def splitLevelQuotientEquiv :
    splitLevel σ n hn U L ⧸ (splitLevel σ n hn U' L).subgroupOf (splitLevel σ n hn U L) ≃*
      U ⧸ U'.subgroupOf U :=
  (QuotientGroup.quotientMulEquivOfEq (by
      rw [splitLevel_subgroupOf]
      ext k
      simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff])).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      ((QuotientGroup.mk' (U'.subgroupOf U)).comp (splitLevelMap U L))
      ((QuotientGroup.mk'_surjective _).comp (splitLevelMap_surjective U L)))

@[simp]
theorem splitLevelQuotientEquiv_mk (k : splitLevel σ n hn U L) :
    splitLevelQuotientEquiv L U'
        (k : splitLevel σ n hn U L ⧸ (splitLevel σ n hn U' L).subgroupOf (splitLevel σ n hn U L)) =
      (splitLevelMap U L k : U ⧸ U'.subgroupOf U) :=
  rfl

variable {R : Type uR} [CommRing R]

omit [(U'.subgroupOf U).Normal] in
/-- Under (4.5), every stabilizer `Δ_g` of `e⁻¹ (U × L)` lies in `e⁻¹ (U' × L)`. -/
theorem DividingLevelFree.doubleCosetStabilizer_le_splitLevel (h : DividingLevelFree σ n hn U L)
    (g : σ.FiniteAdelicPoints) :
    doubleCosetStabilizer σ.finiteAdelicDiagonal (splitLevel σ n hn U L) g ≤
      (splitLevel σ n hn U' L).subgroupOf (splitLevel σ n hn U L) :=
  (h.doubleCosetStabilizer_le le_rfl g).trans fun _ hk =>
    Subgroup.mem_subgroupOf.2 (splitLevel_mono bot_le le_rfl (Subgroup.mem_subgroupOf.1 hk))

/-- Restriction to double cosets in the form of Harris's (4.7) (1999, p.311) under (4.5), for the
level `K = e⁻¹ (U × L)` and its normal subgroup `N = e⁻¹ (U' × L)`: the level action of `K` (right
translation) on the forms of level `N` with trivial coefficients `R` is the representation of
`U` on the functions `U ⧸ U' → (GJ(ℚ) \ GJ(A_f) / K → R)`, restricted to `K` along
`splitLevelMap`. It is the published `levelDoubleCosetEquiv`, with the stabilizer hypothesis from
`DividingLevelFree.doubleCosetStabilizer_le`, followed by `splitLevelQuotientEquiv`. -/
def DividingLevelFree.splitLevelEquiv
    (h : DividingLevelFree σ n hn U L) (hU' : U' ≤ U) :
    Representation.Equiv
      (levelAction σ.finiteAdelicDiagonal
        (Representation.trivial R (splitLevel σ n hn U L) R)
        (splitLevel_mono (hn := hn) hU' (le_refl L)))
      ((Langlands.Induction.functionRepresentation
        (Representation.trivial R U
          (DoubleCosets σ.finiteAdelicDiagonal (splitLevel σ n hn U L) → R))
        (U ⧸ U'.subgroupOf U)).comp (splitLevelMap U L)) :=
  (levelDoubleCosetEquiv σ.finiteAdelicDiagonal (splitLevel_mono (hn := hn) hU' (le_refl L))
    (h.doubleCosetStabilizer_le_splitLevel L U')).trans
    (Langlands.Induction.functionRepresentationCongr _ _ (splitLevelMap U L) (fun _ => rfl)
      (splitLevelQuotientEquiv L U').toEquiv fun k q => by
        induction q using QuotientGroup.induction_on with
        | H k' =>
          change splitLevelQuotientEquiv (hn := hn) L U'
            ((k * k' : splitLevel σ n hn U L) : splitLevel σ n hn U L ⧸
              (splitLevel σ n hn U' L).subgroupOf (splitLevel σ n hn U L)) = _
          rw [splitLevelQuotientEquiv_mk, map_mul]
          rfl)

theorem DividingLevelFree.splitLevelEquiv_apply_mk
    (h : DividingLevelFree σ n hn U L) (hU' : U' ≤ U)
    (f : forms σ.finiteAdelicDiagonal (splitLevel σ n hn U' L)
      ((Representation.trivial R (splitLevel σ n hn U L) R).comp
        (Subgroup.inclusion (splitLevel_mono (hn := hn) hU' (le_refl L)))))
    (k : splitLevel σ n hn U L) (x : DoubleCosets σ.finiteAdelicDiagonal (splitLevel σ n hn U L)) :
    h.splitLevelEquiv L U' hU' f (splitLevelMap U L k : U ⧸ U'.subgroupOf U) x =
      f.1 (x.out * (k : σ.FiniteAdelicPoints)⁻¹) := by
  have hk : (splitLevelQuotientEquiv (hn := hn) L U').symm
      (splitLevelMap U L k : U ⧸ U'.subgroupOf U) =
        (k : splitLevel σ n hn U L ⧸
          (splitLevel σ n hn U' L).subgroupOf (splitLevel σ n hn U L)) := by
    rw [MulEquiv.symm_apply_eq, splitLevelQuotientEquiv_mk]
  change levelDoubleCosetEquiv σ.finiteAdelicDiagonal (splitLevel_mono (hn := hn) hU' (le_refl L))
    (h.doubleCosetStabilizer_le_splitLevel L U') f
      ((splitLevelQuotientEquiv (hn := hn) L U').symm
        (splitLevelMap U L k : U ⧸ U'.subgroupOf U)) x = _
  rw [hk]
  rfl

end Quotient

end Split

section Harris

variable {σ n hn}

/-- A place dividing `d` divides every multiple `n` of `d`; for instance a place over `ℓ` or `p`
divides `n = ℓ p`. -/
abbrev dividingPlaceOfDvd {d : ℕ} (v : {v : FinitePlace ℚ // (d : 𝓞 ℚ) ∈ v.asIdeal}) (hd : d ∣ n) :
    {v : FinitePlace ℚ // (n : 𝓞 ℚ) ∈ v.asIdeal} :=
  ⟨v.1, by
    obtain ⟨c, hc⟩ := hd
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ v.2⟩

variable (σ) (vℓ vp : {v : FinitePlace ℚ // (n : 𝓞 ℚ) ∈ v.asIdeal})

/-- Harris's `K_ℓ × C_p` as a subgroup of `σ(∏_{v ∣ n} ℚ_v)`: the points whose components at the
places `vℓ` and `vp` lie in `K_ℓ` and `C_p`. -/
def pairLevel (Kℓ : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1)))
    (Cp : Subgroup (σ.Points (FiniteCompletion ℚ vp.1))) : Subgroup (σ.DividingPoints n) :=
  Kℓ.comap (σ.dividingLocalMap n vℓ).toMonoidHom ⊓ Cp.comap (σ.dividingLocalMap n vp).toMonoidHom

variable {σ vℓ vp}

theorem mem_pairLevel {Kℓ : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1))}
    {Cp : Subgroup (σ.Points (FiniteCompletion ℚ vp.1))} {u : σ.DividingPoints n} :
    u ∈ pairLevel σ vℓ vp Kℓ Cp ↔ σ.dividingLocalMap n vℓ u ∈ Kℓ ∧ σ.dividingLocalMap n vp u ∈ Cp :=
  Iff.rfl

theorem pairLevel_mono {Kℓ Kℓ' : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1))}
    {Cp Cp' : Subgroup (σ.Points (FiniteCompletion ℚ vp.1))} (hℓ : Kℓ' ≤ Kℓ) (hp : Cp' ≤ Cp) :
    pairLevel σ vℓ vp Kℓ' Cp' ≤ pairLevel σ vℓ vp Kℓ Cp :=
  fun _ hu => ⟨hℓ hu.1, hp hu.2⟩

/-- For `K_ℓ(m)` normal in `K_ℓ` and `H_p` normal in `C_p`, `K_ℓ(m) × H_p` is normal in
`K_ℓ × C_p`. -/
instance pairLevel_subgroupOf_normal {Kℓ Kℓm : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1))}
    {Cp Hp : Subgroup (σ.Points (FiniteCompletion ℚ vp.1))} [hℓ : (Kℓm.subgroupOf Kℓ).Normal]
    [hp : (Hp.subgroupOf Cp).Normal] :
    ((pairLevel σ vℓ vp Kℓm Hp).subgroupOf (pairLevel σ vℓ vp Kℓ Cp)).Normal where
  conj_mem x hx u := by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨hxℓ, hxp⟩ := hx
    refine ⟨?_, ?_⟩
    · have := hℓ.conj_mem ⟨σ.dividingLocalMap n vℓ x, x.2.1⟩ (Subgroup.mem_subgroupOf.2 hxℓ)
        ⟨σ.dividingLocalMap n vℓ u, u.2.1⟩
      simpa [Subgroup.mem_subgroupOf] using this
    · have := hp.conj_mem ⟨σ.dividingLocalMap n vp x, x.2.2⟩ (Subgroup.mem_subgroupOf.2 hxp)
        ⟨σ.dividingLocalMap n vp u, u.2.2⟩
      simpa [Subgroup.mem_subgroupOf] using this

variable (σ n hn vℓ vp)

/-- Harris's (4.5) (1999, p.310): `K_ℓ × C_p` acts without fixed points on
`GJ(ℚ) \ GJ(A_f) / K^{ℓ,p}`, for a level `K^{ℓ,p}` of `σ(A_f^n)`. -/
abbrev HarrisDividingLevelFree (Kℓ : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1)))
    (Cp : Subgroup (σ.Points (FiniteCompletion ℚ vp.1))) (L : Subgroup (σ.PrimeToPoints n)) :
    Prop :=
  DividingLevelFree σ n hn (pairLevel σ vℓ vp Kℓ Cp) L

variable {σ n hn vℓ vp}

/-- Harris (1999, p.310): (4.5) strengthens (3.6). If `K_ℓ × C_p` acts without fixed points on
`GJ(ℚ) \ GJ(A_f) / K^{ℓ,p}` and `K_p ≤ C_p`, then `K = K^{ℓ,p} × K_ℓ × K_p` satisfies (3.6) at
`ℓ`. -/
theorem HarrisDividingLevelFree.localLevelFree
    {Kℓ : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1))}
    {Cp Kp : Subgroup (σ.Points (FiniteCompletion ℚ vp.1))} {L : Subgroup (σ.PrimeToPoints n)}
    (h : HarrisDividingLevelFree σ n hn vℓ vp Kℓ Cp L) (hKp : Kp ≤ Cp) :
    LocalLevelFree σ vℓ.1 (splitLevel σ n hn (pairLevel σ vℓ vp Kℓ Kp) L) :=
  DividingLevelFree.localLevelFree h (pairLevel_mono le_rfl hKp) vℓ

variable {R : Type uR} [CommRing R]

/-- The `C_p`-level form of Harris's (4.7) (1999, p.311) under (4.5): for `K_ℓ(m)` normal in `K_ℓ`
and `H_p` normal in `C_p`, the level action of `K_C = K^{ℓ,p} × K_ℓ × C_p` on the forms of level
`H(m) = K^{ℓ,p} × K_ℓ(m) × H_p` with trivial coefficients `R` is the representation of
`K_ℓ × C_p` on the functions `(K_ℓ × C_p) ⧸ (K_ℓ(m) × H_p) → (GJ(ℚ) \ GJ(A_f) / K_C → R)`.
The double cosets are taken modulo `K_C`, not modulo Harris's `K = K^{ℓ,p} × K_ℓ × K_p` of (4.6);
the two agree when `K_p = C_p`. `restrictionEquivOfLe` is the form indexed by the double cosets
of (4.6). -/
def HarrisDividingLevelFree.restrictionEquiv
    {Kℓ Kℓm : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1))}
    {Cp Hp : Subgroup (σ.Points (FiniteCompletion ℚ vp.1))} {L : Subgroup (σ.PrimeToPoints n)}
    [(Kℓm.subgroupOf Kℓ).Normal] [(Hp.subgroupOf Cp).Normal]
    (h : HarrisDividingLevelFree σ n hn vℓ vp Kℓ Cp L) (hℓ : Kℓm ≤ Kℓ) (hp : Hp ≤ Cp) :
    Representation.Equiv
      (levelAction σ.finiteAdelicDiagonal
        (Representation.trivial R (splitLevel σ n hn (pairLevel σ vℓ vp Kℓ Cp) L) R)
        (splitLevel_mono (hn := hn) (pairLevel_mono hℓ hp) (le_refl L)))
      ((Langlands.Induction.functionRepresentation
        (Representation.trivial R (pairLevel σ vℓ vp Kℓ Cp)
          (DoubleCosets σ.finiteAdelicDiagonal
            (splitLevel σ n hn (pairLevel σ vℓ vp Kℓ Cp) L) → R))
        (pairLevel σ vℓ vp Kℓ Cp ⧸
          (pairLevel σ vℓ vp Kℓm Hp).subgroupOf (pairLevel σ vℓ vp Kℓ Cp))).comp
        (splitLevelMap (pairLevel σ vℓ vp Kℓ Cp) L)) :=
  DividingLevelFree.splitLevelEquiv L (pairLevel σ vℓ vp Kℓm Hp) h (pairLevel_mono hℓ hp)

/-- Harris's `H_p`, normal in `C_p` and contained in `K_p ≤ C_p`, is normal in `K_p`. -/
theorem subgroupOf_normal_of_le {G : Type*} [Group G] {C K H : Subgroup G}
    [(H.subgroupOf C).Normal] (hK : K ≤ C) (hH : H ≤ K) : (H.subgroupOf K).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    (hK.trans (Subgroup.le_normalizer_of_normal_subgroupOf (hH.trans hK)))

/-- Harris's (4.7) indexed by the double cosets of (4.6) (1999, pp.310-311) under (4.5): for
`K_p ≤ C_p`, `H_p ≤ K_p`, `K_ℓ(m)` normal in `K_ℓ` and `H_p` normal in `K_p` (for instance by
`subgroupOf_normal_of_le`, from `H_p` normal in `C_p`), the level action of Harris's
`K = K^{ℓ,p} × K_ℓ × K_p` on the forms of level `H(m) = K^{ℓ,p} × K_ℓ(m) × H_p` with trivial
coefficients `R` is the representation of `K_ℓ × K_p` on the functions
`(K_ℓ × K_p) ⧸ (K_ℓ(m) × H_p) → (GJ(ℚ) \ GJ(A_f) / K → R)`. The factor is `K_ℓ × K_p`, not the
printed `K_ℓ × C_p` of (4.7); Harris's proof of Proposition 4.10 writes `𝒪_m[K_p/H_p]^M`. -/
def HarrisDividingLevelFree.restrictionEquivOfLe
    {Kℓ Kℓm : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1))}
    {Cp Kp Hp : Subgroup (σ.Points (FiniteCompletion ℚ vp.1))} {L : Subgroup (σ.PrimeToPoints n)}
    [(Kℓm.subgroupOf Kℓ).Normal] [(Hp.subgroupOf Kp).Normal]
    (h : HarrisDividingLevelFree σ n hn vℓ vp Kℓ Cp L) (hℓ : Kℓm ≤ Kℓ) (hKp : Kp ≤ Cp)
    (hp : Hp ≤ Kp) :
    Representation.Equiv
      (levelAction σ.finiteAdelicDiagonal
        (Representation.trivial R (splitLevel σ n hn (pairLevel σ vℓ vp Kℓ Kp) L) R)
        (splitLevel_mono (hn := hn) (pairLevel_mono hℓ hp) (le_refl L)))
      ((Langlands.Induction.functionRepresentation
        (Representation.trivial R (pairLevel σ vℓ vp Kℓ Kp)
          (DoubleCosets σ.finiteAdelicDiagonal
            (splitLevel σ n hn (pairLevel σ vℓ vp Kℓ Kp) L) → R))
        (pairLevel σ vℓ vp Kℓ Kp ⧸
          (pairLevel σ vℓ vp Kℓm Hp).subgroupOf (pairLevel σ vℓ vp Kℓ Kp))).comp
        (splitLevelMap (pairLevel σ vℓ vp Kℓ Kp) L)) :=
  HarrisDividingLevelFree.restrictionEquiv
    (DividingLevelFree.mono h (pairLevel_mono le_rfl hKp) le_rfl) hℓ hp

end Harris

end Langlands.Shimura.DefiniteForms
