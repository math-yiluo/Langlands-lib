import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.Artin
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Induced
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Multiplicative
import Langlands.GaloisCohomology.Field.Modules
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Reduction of the Euler characteristic formula to modules induced from cyclic quotients

Let `G` be a profinite group, `Q ⊆ G` an open normal subgroup and `ℓ` a prime. A finite `𝔽_ℓ[G/Q]`-module
`ρ` gives a smooth `G`-module `infl Q ρ`. A function `χ` of finite smooth `G`-modules with values in
`ℚ_{>0}` that is multiplicative on short exact sequences of modules killed by `ℓ` (`MultKilled`) gives,
for every prime `p`, an additive function `ρ ↦ v_p(χ(infl Q ρ))` on finite `𝔽_ℓ[G/Q]`-modules
(`valFun`). By Artin's induction theorem for additive functions
(`Local.AdditiveFunction.toFun_eq_zero_of_forall_isCyclic`), `χ(infl Q ρ) = 1` as soon as
`χ = 1` on the modules induced from the cyclic subgroups of `G/Q` (`eq_one_of_forall_isCyclic`).

For `G = G_S` of a number field `K`, `Q` the subgroup fixing a finite Galois extension `L ⊆ K_S` and
`χ` the Euler characteristic ratio `globalEulerRatio`, the cyclic subgroups of `Gal(L/K)` are the
groups `Gal(L/L')` with `L/L'` cyclic, and the induced modules are `Ind_{G_S(L')}^{G_S} M`
(`coindResIsoFunRep`). So the formula for a module `M` killed by `ℓ` on which `G_S(L)` acts trivially
follows from the formula for the modules `Ind_{G_S(L')}^{G_S} M`, `L/L'` cyclic
(`globalEulerRatio_eq_one_of_cyclic`). This is the first reduction step of Tate's proof.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  GaloisGroupUnramifiedOutside

universe u

noncomputable section

section Infl

variable {G : Type u} [Group G] [TopologicalSpace G] (Q : OpenSubgroup G) [(Q : Subgroup G).Normal]
  {l : ℕ} {X : Type u} [AddCommGroup X] [Module (ZMod l) X]

/-- The action of `G` through `G/Q` on an `𝔽_ℓ[G/Q]`-module, as additive endomorphisms. -/
def inflHom (ρ : Representation (ZMod l) (G ⧸ (Q : Subgroup G)) X) : G →* AddMonoid.End X where
  toFun g := (ρ (QuotientGroup.mk g)).toAddMonoidHom
  map_one' := by ext x; simp only [QuotientGroup.mk_one, map_one]; rfl
  map_mul' g h := by ext x; simp only [QuotientGroup.mk_mul, map_mul]; rfl

/-- An `𝔽_ℓ[G/Q]`-module as a `G`-module (with coefficients in `ℤ`). -/
abbrev infl (ρ : Representation (ZMod l) (G ⧸ (Q : Subgroup G)) X) : Rep.{u} (ULift.{u} ℤ) G :=
  Rep.of (intRep.{u} (inflHom Q ρ))

theorem infl_apply (ρ : Representation (ZMod l) (G ⧸ (Q : Subgroup G)) X) (g : G) (x : X) :
    (infl Q ρ).ρ g x = ρ (QuotientGroup.mk g) x :=
  rfl

theorem finite_infl [Finite X] (ρ : Representation (ZMod l) (G ⧸ (Q : Subgroup G)) X) :
    Finite (infl Q ρ) :=
  ‹Finite X›

theorem isSmoothRep_infl [IsTopologicalGroup G] (ρ : Representation (ZMod l) (G ⧸ (Q : Subgroup G)) X) :
    IsSmoothRep (infl Q ρ) :=
  IsSmoothRep.of_isOpen_stabilizer _ fun a => Subgroup.isOpen_mono (H₁ := (Q : Subgroup G))
    (fun q hq => by
      change (infl Q ρ).ρ q a = a
      rw [infl_apply, (QuotientGroup.eq_one_iff q).2 hq, map_one]
      rfl) Q.isOpen

end Infl

theorem rat_eq_one_of_padicValRat {q : ℚ} (hq : 0 < q) (h : ∀ p : ℕ, p.Prime → padicValRat p q = 0) :
    q = 1 := by
  have hval : ∀ p : ℕ, p.Prime → padicValNat p q.num.natAbs = padicValNat p q.den := by
    intro p hp
    have := h p hp
    simp only [padicValRat, padicValInt] at this
    omega
  have hn0 : q.num.natAbs ≠ 0 := by
    have := Rat.num_pos.2 hq
    omega
  have hnum : ∀ p : ℕ, p.Prime → ¬ p ∣ q.num.natAbs := by
    intro p hp hd
    have := Fact.mk hp
    have h1 := one_le_padicValNat_of_dvd hn0 hd
    have hd' : p ∣ q.den := by
      by_contra hnd
      rw [hval p hp, padicValNat.eq_zero_of_not_dvd hnd] at h1
      omega
    exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hd hd' q.reduced
  have hden : ∀ p : ℕ, p.Prime → ¬ p ∣ q.den := by
    intro p hp hd
    have := Fact.mk hp
    have h1 := one_le_padicValNat_of_dvd q.den_nz hd
    have hd' : p ∣ q.num.natAbs := by
      by_contra hnd
      rw [← hval p hp, padicValNat.eq_zero_of_not_dvd hnd] at h1
      omega
    exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hd' hd q.reduced
  have h1 : q.num.natAbs = 1 := Nat.eq_one_iff_not_exists_prime_dvd.2 hnum
  have h2 : q.den = 1 := Nat.eq_one_iff_not_exists_prime_dvd.2 hden
  have h3 : q.num = 1 := by
    have := Rat.num_pos.2 hq
    omega
  exact Rat.ext h3 h2

section Artin

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Q : OpenSubgroup G)
  [(Q : Subgroup G).Normal] (l : ℕ) [Fact l.Prime]
  (χ : (A : Rep.{u} (ULift.{u} ℤ) G) → [IsSmoothRep A] → ℚ)

/-- `χ` is multiplicative on short exact sequences of finite modules killed by `ℓ`. -/
def MultKilled : Prop :=
  ∀ (T : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)) [IsSmoothRep T.X₁] [IsSmoothRep T.X₂]
    [IsSmoothRep T.X₃] [Finite T.X₂], T.ShortExact → (∀ m : T.X₂, l • m = 0) →
      χ T.X₂ = χ T.X₁ * χ T.X₃

/-- `χ` is positive on finite modules killed by `ℓ`. -/
def PosKilled : Prop :=
  ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep A] [Finite A], (∀ m : A, l • m = 0) → 0 < χ A

variable {l χ}

attribute [local instance] isSmoothRep_infl finite_infl

theorem nsmul_eq_zero_of_zmod {X : Type*} [AddCommGroup X] [Module (ZMod l) X] (x : X) :
    l • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod l), ZMod.natCast_self, zero_smul]

/-- `ρ ↦ v_p(χ(infl Q ρ))`, an additive function on finite `𝔽_ℓ[G/Q]`-modules. -/
def valFun (hmult : MultKilled l χ) (hpos : PosKilled l χ) (p : ℕ) [Fact p.Prime] :
    Local.AdditiveFunction.{u} l (G ⧸ (Q : Subgroup G)) where
  toFun X _ _ _ ρ := padicValRat p (χ (infl Q ρ))
  additive := by
    intro X₁ X₂ X₃ _ _ _ _ _ _ _ _ _ ρ₁ ρ₂ ρ₃ f g hf hg hinj hfg hs
    let F : infl Q ρ₁ ⟶ infl Q ρ₂ := Rep.ofHom ⟨uliftIntLinearMap f.toAddMonoidHom,
      fun γ => LinearMap.ext fun x => hf.isIntertwining (QuotientGroup.mk γ) x⟩
    let Gm : infl Q ρ₂ ⟶ infl Q ρ₃ := Rep.ofHom ⟨uliftIntLinearMap g.toAddMonoidHom,
      fun γ => LinearMap.ext fun x => hg.isIntertwining (QuotientGroup.mk γ) x⟩
    have hzero : F ≫ Gm = 0 := by
      ext x
      exact (hfg (f x)).2 ⟨x, rfl⟩
    let T := ShortComplex.mk F Gm hzero
    have hT : T.ShortExact :=
      ClassFieldTheory.Global.repShortExact_of_values T hinj (fun y hy => (hfg y).1 hy) hs
    have hm : χ (infl Q ρ₂) = χ (infl Q ρ₁) * χ (infl Q ρ₃) :=
      @hmult T (isSmoothRep_infl Q ρ₁) (isSmoothRep_infl Q ρ₂) (isSmoothRep_infl Q ρ₃)
        (finite_infl Q ρ₂) hT (fun m => nsmul_eq_zero_of_zmod (l := l) (X := X₂) m)
    have h1 := hpos (infl Q ρ₁) (fun m => nsmul_eq_zero_of_zmod (l := l) (X := X₁) m)
    have h3 := hpos (infl Q ρ₃) (fun m => nsmul_eq_zero_of_zmod (l := l) (X := X₃) m)
    change padicValRat p (χ (infl Q ρ₂)) = padicValRat p (χ (infl Q ρ₁)) +
      padicValRat p (χ (infl Q ρ₃))
    rw [hm]
    exact padicValRat.mul h1.ne' h3.ne'

/-- **Reduction to cyclic subgroups.** If `χ = 1` on the modules induced from the cyclic subgroups of
`G/Q`, then `χ(infl Q ρ) = 1`. -/
theorem eq_one_of_forall_isCyclic (hmult : MultKilled l χ) (hpos : PosKilled l χ)
    [Finite (G ⧸ (Q : Subgroup G))] {X : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X]
    (ρ : Representation (ZMod l) (G ⧸ (Q : Subgroup G)) X)
    (h : ∀ D : Subgroup (G ⧸ (Q : Subgroup G)), IsCyclic D →
      χ (infl Q (funRep ((G ⧸ (Q : Subgroup G)) ⧸ D) ρ)) = 1) :
    χ (infl Q ρ) = 1 := by
  apply rat_eq_one_of_padicValRat (hpos _ (fun m => nsmul_eq_zero_of_zmod (l := l) (X := X) m))
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  exact (valFun Q hmult hpos p).toFun_eq_zero_of_forall_isCyclic ρ (fun D hD => by
    change padicValRat p (χ (infl Q _)) = 0
    rw [h D hD]
    exact padicValRat.one)

end Artin

section Quotient

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Q : OpenSubgroup G)
  [(Q : Subgroup G).Normal]

/-- The action of `G` on an additive group, as additive endomorphisms. -/
def addAct (M : Rep.{u} (ULift.{u} ℤ) G) : G →* AddMonoid.End M where
  toFun g := (M.ρ g).toAddMonoidHom
  map_one' := by ext x; simp only [map_one]; rfl
  map_mul' g h := by ext x; simp only [map_mul]; rfl

/-- A `ℤ`-linear action on an `𝔽_ℓ`-vector space is `𝔽_ℓ`-linear. -/
def zmodRepOfAddAct (n : ℕ) {V : Type u} [AddCommGroup V] [Module (ZMod n) V]
    (φ : G →* AddMonoid.End V) : Representation (ZMod n) G V where
  toFun g := (φ g).toZModLinearMap n
  map_one' := by ext x; simp only [map_one]; rfl
  map_mul' g h := by ext x; simp only [map_mul]; rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem nonempty_iso_of_addEquiv (A B : Rep.{u} (ULift.{u} ℤ) G) (e : A ≃+ B)
    (h : ∀ (g : G) (x : A), e (A.ρ g x) = B.ρ g (e x)) : Nonempty (A ≅ B) :=
  ⟨Rep.mkIso (Representation.Equiv.mk (LinearEquiv.ofBijective
    ((uliftIntLinearEquivAddHom A B).symm e.toAddMonoidHom) e.bijective)
      fun g => LinearMap.ext fun x => h g x)⟩

omit [IsTopologicalGroup G] in
/-- A `𝔽_ℓ`-module on which `Q` acts trivially is the inflation of an `𝔽_ℓ[G/Q]`-module. -/
theorem exists_iso_infl_of_module {l : ℕ} (M : Rep.{u} (ULift.{u} ℤ) G) [Module (ZMod l) M]
    (htriv : ∀ g ∈ (Q : Subgroup G), M.ρ g = 1) :
    ∃ ρ : Representation (ZMod l) (G ⧸ (Q : Subgroup G)) M,
      (∀ (g : G) (m : M), ρ (QuotientGroup.mk g) m = M.ρ g m) ∧ Nonempty (M ≅ infl Q ρ) := by
  have hker : (Q : Subgroup G) ≤ (zmodRepOfAddAct l (addAct M)).ker := fun g hg => by
    rw [MonoidHom.mem_ker]
    refine LinearMap.ext fun x => ?_
    change (M.ρ g) x = x
    rw [htriv g hg]
    rfl
  exact ⟨QuotientGroup.lift _ (zmodRepOfAddAct l (addAct M)) hker, fun g m => rfl,
    nonempty_iso_of_addEquiv M (infl Q _) (AddEquiv.refl M) (fun _ _ => rfl)⟩

omit [IsTopologicalGroup G] in
/-- A module killed by `ℓ` on which `Q` acts trivially is the inflation of an `𝔽_ℓ[G/Q]`-module. -/
theorem exists_iso_infl {l : ℕ} (M : Rep.{u} (ULift.{u} ℤ) G) (hl : ∀ m : M, l • m = 0)
    (htriv : ∀ g ∈ (Q : Subgroup G), M.ρ g = 1) :
    ∃ (_ : Module (ZMod l) M) (ρ : Representation (ZMod l) (G ⧸ (Q : Subgroup G)) M),
      (∀ (g : G) (m : M), ρ (QuotientGroup.mk g) m = M.ρ g m) ∧ Nonempty (M ≅ infl Q ρ) := by
  let inst : Module (ZMod l) M := AddCommGroup.zmodModule hl
  exact ⟨inst, exists_iso_infl_of_module Q M htriv⟩

end Quotient

section Induced

variable {k G : Type u} [CommRing k] [Group G] (W : Subgroup G) (A : Rep.{u} k G)

theorem coindRes_apply_mul' (f : Rep.coind W.subtype (Rep.res W.subtype A)) (w : W) (y : G) :
    f.1 ((w : G) * y) = A.ρ (w : G) (f.1 y) :=
  f.2 w y

/-- An element of `Ind_W^G Res_W A` as a function on `G/W`: `gW ↦ g f(g⁻¹)`. -/
def coindResToFun (f : Rep.coind W.subtype (Rep.res W.subtype A)) : G ⧸ W → A :=
  fun c => Quotient.liftOn' c (fun y => A.ρ y (f.1 y⁻¹)) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab
    have h1 : b⁻¹ = ((⟨a⁻¹ * b, hab⟩⁻¹ : W) : G) * a⁻¹ := by simp
    rw [h1, coindRes_apply_mul', ← Module.End.mul_apply, ← map_mul]
    congr 2
    simp

@[simp]
theorem coindResToFun_mk (f : Rep.coind W.subtype (Rep.res W.subtype A)) (y : G) :
    coindResToFun W A f (QuotientGroup.mk y) = A.ρ y (f.1 y⁻¹) :=
  rfl

theorem funToCoindRes_mem (F : G ⧸ W → A) :
    (fun y : G => A.ρ y (F (QuotientGroup.mk y⁻¹))) ∈
      Representation.coindV W.subtype (Rep.res W.subtype A).ρ := by
  intro w y
  have hq : (QuotientGroup.mk ((W.subtype w * y)⁻¹) : G ⧸ W) = QuotientGroup.mk y⁻¹ := by
    rw [QuotientGroup.eq]
    simp
  change A.ρ (W.subtype w * y) (F (QuotientGroup.mk ((W.subtype w * y)⁻¹))) =
    A.ρ (w : G) (A.ρ y (F (QuotientGroup.mk y⁻¹)))
  rw [hq, map_mul, Module.End.mul_apply]
  rfl

/-- `Ind_W^G Res_W A ≅ (G/W → A)` with `(g F)(y) = g F(g⁻¹ y)`. -/
def coindResEquivFunRep :
    (Rep.coind W.subtype (Rep.res W.subtype A)).ρ.Equiv (funRep (G ⧸ W) A.ρ) where
  toFun := coindResToFun W A
  map_add' f f' := funext fun c => by
    induction c using QuotientGroup.induction_on with
    | H y => simp [coindResToFun_mk]
  map_smul' r f := funext fun c => by
    induction c using QuotientGroup.induction_on with
    | H y => simp [coindResToFun_mk]
  invFun F := ⟨fun y => A.ρ y (F (QuotientGroup.mk y⁻¹)), funToCoindRes_mem W A F⟩
  left_inv f := by
    apply Subtype.ext
    funext y
    change A.ρ y (A.ρ y⁻¹ (f.1 y⁻¹⁻¹)) = f.1 y
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, inv_inv, Module.End.one_apply]
  right_inv F := funext fun c => by
    induction c using QuotientGroup.induction_on with
    | H y =>
      change A.ρ y (A.ρ y⁻¹ (F (QuotientGroup.mk y⁻¹⁻¹))) = F (QuotientGroup.mk y)
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, inv_inv, Module.End.one_apply]
  isIntertwining' g := by
    refine LinearMap.ext fun f => funext fun c => ?_
    induction c using QuotientGroup.induction_on with
    | H y =>
      change A.ρ y (f.1 (y⁻¹ * g)) = A.ρ g (A.ρ (g⁻¹ * y) (f.1 (g⁻¹ * y)⁻¹))
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left, mul_inv_rev, inv_inv]

end Induced

section CosetEquiv

variable {G Γ : Type*} [Group G] [Group Γ] (π : G →* Γ) (hπ : Function.Surjective π)
  (D : Subgroup Γ) (W : Subgroup G) (hW : W = D.comap π)

/-- `G/W ≃ Γ/D` for `W` the preimage of `D` under a surjection `π : G → Γ`. -/
def cosetEquiv : G ⧸ W ≃ Γ ⧸ D :=
  (Subgroup.quotientEquivOfEq hW).trans (Equiv.ofBijective (Quotient.map' π fun a b h => by
      rw [QuotientGroup.leftRel_apply] at h ⊢
      simpa [Subgroup.mem_comap] using h) (by
    constructor
    · intro x y h
      induction x using QuotientGroup.induction_on with
      | H a =>
        induction y using QuotientGroup.induction_on with
        | H b =>
          have h' : (QuotientGroup.mk (π a) : Γ ⧸ D) = QuotientGroup.mk (π b) := h
          rw [QuotientGroup.eq] at h'
          rw [QuotientGroup.eq, Subgroup.mem_comap]
          simpa using h'
    · intro c
      induction c using QuotientGroup.induction_on with
      | H γ =>
        obtain ⟨g, rfl⟩ := hπ γ
        exact ⟨QuotientGroup.mk g, rfl⟩))

theorem cosetEquiv_mk (g : G) :
    cosetEquiv π hπ D W hW (QuotientGroup.mk g) = QuotientGroup.mk (π g) := rfl

theorem cosetEquiv_smul (g : G) (x : G ⧸ W) :
    cosetEquiv π hπ D W hW (g • x) = π g • cosetEquiv π hπ D W hW x := by
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [MulAction.Quotient.smul_mk, cosetEquiv_mk, cosetEquiv_mk, MulAction.Quotient.smul_mk,
      smul_eq_mul, smul_eq_mul, map_mul]

theorem cosetEquiv_symm_smul (g : G) (y : Γ ⧸ D) :
    (cosetEquiv π hπ D W hW).symm (π g • y) = g • (cosetEquiv π hπ D W hW).symm y := by
  apply (cosetEquiv π hπ D W hW).injective
  rw [cosetEquiv_smul, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end CosetEquiv

section InducedInfl

-- The `ULift ℤ`-module structure of a representation is its own instance `Rep.hV2`, not the one
-- induced from its `ℤ`-module structure.
attribute [-instance] ULift.module

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Q : OpenSubgroup G)
  [(Q : Subgroup G).Normal] {l : ℕ}

omit [IsTopologicalGroup G] in
/-- The module induced from the preimage `W` of a subgroup `D` of `G/Q` is the inflation of the
module induced from `D`. -/
theorem nonempty_coind_iso_infl_funRep (M : Rep.{u} (ULift.{u} ℤ) G) [Module (ZMod l) M]
    (ρ : Representation (ZMod l) (G ⧸ (Q : Subgroup G)) M)
    (hρ : ∀ (g : G) (m : M), ρ (QuotientGroup.mk g) m = M.ρ g m)
    (D : Subgroup (G ⧸ (Q : Subgroup G))) (W : Subgroup G) (hW : W = D.comap (QuotientGroup.mk' _)) :
    Nonempty (Rep.coind W.subtype (Rep.res W.subtype M) ≅
      infl Q (funRep ((G ⧸ (Q : Subgroup G)) ⧸ D) ρ)) := by
  have hπ : Function.Surjective (QuotientGroup.mk' (Q : Subgroup G)) := QuotientGroup.mk'_surjective _
  let E := cosetEquiv _ hπ D W hW
  refine ⟨(Rep.mkIso (coindResEquivFunRep W M)).trans
    (Classical.choice (nonempty_iso_of_addEquiv _ _
      { toFun := fun F y => F (E.symm y)
        invFun := fun F x => F (E x)
        left_inv := fun F => by funext x; simp
        right_inv := fun F => by funext y; simp
        map_add' := fun F F' => rfl } fun g F => ?_))⟩
  funext y
  change M.ρ g (F (g⁻¹ • E.symm y)) = ρ (QuotientGroup.mk g) (F (E.symm
    ((QuotientGroup.mk g : G ⧸ (Q : Subgroup G))⁻¹ • y)))
  rw [hρ]
  congr 2
  exact (cosetEquiv_symm_smul _ hπ D W hW g⁻¹ y).symm

end InducedInfl

section GS

-- A separable closure of a number field is Galois over it; found first, before the search for
-- other ways to prove `IsGalois`.
attribute [local instance 2000] IsSepClosure.isGalois

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] (ι : PlaceEmbeddings K Ω)

/-- The ratio is multiplicative on short exact sequences of modules killed by `ℓ`. -/
theorem multKilled_globalEulerRatio {ℓ : ℕ}
    [hℓ : Fact ℓ.Prime] (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    MultKilled ℓ (fun (A : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S))
      [IsSmoothRep A] => globalEulerRatio ι A) := by
  intro T _ _ _ _ hT hl
  exact globalEulerRatio_shortExact ι hT
    (mem_of_natCard_mem_of_nsmul hℓ.out hS (r := 1) fun m => by rw [pow_one]; exact hl m)

/-- The ratio is positive on modules killed by `ℓ`. -/
theorem posKilled_globalEulerRatio {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    PosKilled ℓ (fun (A : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S))
      [IsSmoothRep A] => globalEulerRatio ι A) := by
  intro A _ _ hA
  exact globalEulerRatio_pos ι A
    (mem_of_natCard_mem_of_nsmul hℓ.out hS (r := 1) fun m => by rw [pow_one]; exact hA m)

omit [Finite S] in
/-- The open subgroup of `G_S` attached to a subgroup `D` of `G_S/G_S(L)`: the subgroup fixing a field
`L' ⊆ L`, with `Gal(L/L') ≅ D`. -/
theorem exists_fixingOpenSubgroup_eq_comap (L : IntermediateField K Ω) [NumberField L]
    (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)
    [(GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal]
    (D : Subgroup (GaloisGroupUnramifiedOutside K Ω S ⧸
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))))
    (hD : IsCyclic D) :
    ∃ (L' : IntermediateField K Ω) (_ : NumberField L')
      (hL' : ∀ x : L', algebraMap L' Ω x ∈ maximalUnramifiedOutside K Ω S),
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL' : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) =
          D.comap (QuotientGroup.mk' _) ∧
        (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) ≤
          GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL' ∧
        IsCyclic ((GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL' : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) ⧸
          (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subgroupOf
            (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL' : Subgroup (GaloisGroupUnramifiedOutside K Ω S))) := by
  set U := (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
  have hUD : U ≤ D.comap (QuotientGroup.mk' U) := fun u hu => by
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff u).2 hu]
    exact D.one_mem
  let V : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S) :=
    ⟨D.comap (QuotientGroup.mk' U), Subgroup.isOpen_mono hUD (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL).isOpen⟩
  obtain ⟨L', hL'f, hL', hV⟩ := exists_fixingOpenSubgroup_eq (S := S) V
  have hW : (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL' : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) =
      D.comap (QuotientGroup.mk' U) := by
    rw [hV]
  refine ⟨L', hL'f, hL', hW, fun u hu => (Subgroup.ext_iff.1 hW u).2 (hUD hu), ?_⟩
  let φ : (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL' : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) →* D :=
    ((QuotientGroup.mk' U).comp
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL' : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype).codRestrict D
      (fun w => (Subgroup.ext_iff.1 hW w).1 w.2)
  have hsurj : Function.Surjective φ := by
    rintro ⟨d, hd⟩
    obtain ⟨g, hgd⟩ := QuotientGroup.mk_surjective d
    have hg : g ∈ (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL' : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) :=
      (Subgroup.ext_iff.1 hW g).2 (by
        change QuotientGroup.mk g ∈ D
        rw [hgd]
        exact hd)
    exact ⟨⟨g, hg⟩, Subtype.ext hgd⟩
  have hk : φ.ker = U.subgroupOf
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL' : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).2 h)
  let e := (QuotientGroup.quotientMulEquivOfEq hk).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

attribute [local instance] isSmoothRep_infl finite_infl

/-- **Reduction to cyclic quotients.** Let `L ⊆ K_S` be finite Galois over `K` and `M` a finite module
killed by a prime `ℓ` (with the places above `ℓ` in `S`) on which `G_S(L)` acts trivially. If the
formula holds for the modules induced from `G_S(L')` for the fields `K ⊆ L' ⊆ L` with `L/L'` cyclic,
it holds for `M`. -/
theorem globalEulerRatio_eq_one_of_cyclic {ℓ : ℕ}
    [Fact ℓ.Prime] (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (L : IntermediateField K Ω) [NumberField L]
    (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)
    [(GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal]
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, ℓ • m = 0)
    (htriv : ∀ g ∈ (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)),
      M.ρ g = 1)
    (hcyc : ∀ (L' : IntermediateField K Ω) [NumberField L']
      (hL' : ∀ x : L', algebraMap L' Ω x ∈ maximalUnramifiedOutside K Ω S),
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) ≤
        GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL' →
      IsCyclic ((GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL' : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) ⧸
        (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subgroupOf
          (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL' : Subgroup (GaloisGroupUnramifiedOutside K Ω S))) →
      globalEulerRatio ι (Rep.coind (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL' :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL' :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M)) = 1) :
    globalEulerRatio ι M = 1 := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have : Finite (GaloisGroupUnramifiedOutside K Ω S ⧸
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))) :=
    Subgroup.finite_quotient_of_finiteIndex
  obtain ⟨inst, ρ, hρ, ⟨e⟩⟩ := exists_iso_infl (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL) M hM htriv
  rw [globalEulerRatio_eq_of_iso ι M e]
  refine eq_one_of_forall_isCyclic (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL) (multKilled_globalEulerRatio ι hS)
    (posKilled_globalEulerRatio ι hS) ρ fun D hD => ?_
  obtain ⟨L', hL'f, hL', hW, hle, hcycW⟩ := exists_fixingOpenSubgroup_eq_comap L hL D hD
  obtain ⟨e'⟩ := nonempty_coind_iso_infl_funRep (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL) M ρ hρ D _ hW
  rw [← globalEulerRatio_eq_of_iso ι _ e']
  exact hcyc L' hL' hle hcycW

end GS

end

end Langlands.GaloisCohomology
