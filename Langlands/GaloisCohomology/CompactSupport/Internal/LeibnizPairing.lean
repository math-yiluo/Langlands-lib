import Langlands.GaloisCohomology.CompactSupport.Basic
import Langlands.Cohomology.Profinite.Cup.Pairing
import Langlands.Cohomology.Profinite.Cup.Functoriality

/-!
# Leibniz pairings of complexes and the cup product of cochains (internal)

A `LeibnizPairing M N P` of `ℕ`-indexed complexes of `k`-modules is a family of bilinear maps
`Mʳ × Nˢ → Pⁿ` (`r + s = n`) satisfying `d(x·y) = dx·y + (-1)ʳ x·dy`. It induces a pairing of
cycles and a bilinear pairing `Hʳ(M) × Hˢ(N) → Hⁿ(P)`; for pairings compatible with two short
exact sequences of complexes the connecting maps satisfy `δx·y + (-1)ʳ x·δy = 0`
(`LeibnizPairing.homology_δ_add_homology_δ`). The cup product of locally constant cochains along
`μ : A ⊗ B ⟶ C` is a Leibniz pairing (`cupLeibniz`) inducing the foundations' `cupPairing`; products
of Leibniz pairings are Leibniz pairings of the product complexes, and `localRes` is compatible with
cup products. These are the building blocks of the cup products with compact support.
-/

namespace Langlands.GaloisCohomology

open Langlands Langlands.ProfiniteCohomology

universe u

-- from CompactSupportCohomology/Pairing.lean
section Pairing

open CategoryTheory Limits


variable {k : Type u} [CommRing k]

section Elements

variable (K : CochainComplex (ModuleCat.{u} k) ℕ)

theorem iCycles_hom_injective (n : ℕ) : Function.Injective (K.iCycles n).hom :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

theorem homologyπ_hom_surjective (n : ℕ) : Function.Surjective (K.homologyπ n).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

theorem iCycles_toCycles_hom_apply (i n : ℕ) (a : K.X i) :
    (K.iCycles n).hom ((K.toCycles i n).hom a) = (K.d i n).hom a :=
  hom_apply_hom_apply_of_comp_eq (K.toCycles_i i n) a

theorem homologyπ_toCycles_hom_apply (i n : ℕ) (a : K.X i) :
    (K.homologyπ n).hom ((K.toCycles i n).hom a) = 0 :=
  hom_apply_hom_apply_of_comp_eq (K.toCycles_comp_homologyπ i n) a

/-- A linear map out of `Hʳ(K)` defined on cycles, killing boundaries. -/
noncomputable def descHomologyNat {r : ℕ} {T : Type u} [AddCommGroup T] [Module k T]
    (L : K.cycles r →ₗ[k] T) (hL : ∀ i, i + 1 = r → ∀ a, L ((K.toCycles i r).hom a) = 0) :
    K.homology r →ₗ[k] T :=
  ((K.homologyIsCokernel _ r rfl).desc (CokernelCofork.ofπ (ModuleCat.ofHom L) (by
    by_cases hr : (ComplexShape.up ℕ).Rel ((ComplexShape.up ℕ).prev r) r
    · exact ModuleCat.hom_ext (LinearMap.ext fun a => hL _ hr a)
    · rw [K.toCycles_eq_zero hr]
      exact zero_comp))).hom

theorem descHomologyNat_homologyπ {r : ℕ} {T : Type u} [AddCommGroup T] [Module k T]
    (L : K.cycles r →ₗ[k] T) (hL : ∀ i, i + 1 = r → ∀ a, L ((K.toCycles i r).hom a) = 0)
    (x : K.cycles r) : descHomologyNat K L hL ((K.homologyπ r).hom x) = L x :=
  ConcreteCategory.congr_hom (Cofork.IsColimit.π_desc (K.homologyIsCokernel _ r rfl)) x

end Elements

/-- A pairing of `ℕ`-indexed complexes `M ⊗ N → P` given degreewise by bilinear maps `Mʳ × Nˢ →
Pⁿ` (`r + s = n`) satisfying the Leibniz rule `d(x·y) = dx·y + (-1)ʳ x·dy`. -/
structure LeibnizPairing (M N P : CochainComplex (ModuleCat.{u} k) ℕ) where
  /-- The bilinear map `Mʳ × Nˢ → Pⁿ` for `r + s = n`. -/
  μ : ∀ {r s n : ℕ}, r + s = n → M.X r →ₗ[k] N.X s →ₗ[k] P.X n
  /-- The Leibniz rule `d(x·y) = dx·y + (-1)ʳ x·dy`. -/
  leibniz : ∀ {r s n : ℕ} (h : r + s = n) (x : M.X r) (y : N.X s),
    (P.d n (n + 1)).hom (μ h x y) =
      μ (by omega) ((M.d r (r + 1)).hom x) y + (-1 : k) ^ r • μ (by omega) x ((N.d s (s + 1)).hom y)

namespace LeibnizPairing

variable {M N P : CochainComplex (ModuleCat.{u} k) ℕ} (μ : LeibnizPairing M N P)

theorem d_μ_cycles {r s n : ℕ} (h : r + s = n) (x : M.cycles r) (y : N.cycles s) :
    (P.d n (n + 1)).hom (μ.μ h ((M.iCycles r).hom x) ((N.iCycles s).hom y)) = 0 := by
  rw [μ.leibniz, iCycles_d_apply, iCycles_d_apply, map_zero, LinearMap.zero_apply, map_zero,
    smul_zero, add_zero]

/-- The product of two cycles, as a cycle. -/
noncomputable def cyclesProduct {r s n : ℕ} (h : r + s = n) (x : M.cycles r) (y : N.cycles s) :
    P.cycles n :=
  P.cyclesMk (μ.μ h ((M.iCycles r).hom x) ((N.iCycles s).hom y)) (n + 1) (by simp)
    (μ.d_μ_cycles h x y)

theorem iCycles_cyclesProduct {r s n : ℕ} (h : r + s = n) (x : M.cycles r) (y : N.cycles s) :
    (P.iCycles n).hom (μ.cyclesProduct h x y) = μ.μ h ((M.iCycles r).hom x) ((N.iCycles s).hom y) :=
  P.i_cyclesMk _ _ _ _

/-- The product of cycles, as a bilinear map. -/
noncomputable def cycles {r s n : ℕ} (h : r + s = n) :
    M.cycles r →ₗ[k] N.cycles s →ₗ[k] P.cycles n :=
  LinearMap.mk₂ k (μ.cyclesProduct h)
    (fun x x' y => iCycles_hom_injective P n (by simp [iCycles_cyclesProduct]))
    (fun c x y => iCycles_hom_injective P n (by simp [iCycles_cyclesProduct]))
    (fun x y y' => iCycles_hom_injective P n (by simp [iCycles_cyclesProduct]))
    (fun c x y => iCycles_hom_injective P n (by simp [iCycles_cyclesProduct]))

@[simp]
theorem iCycles_cycles {r s n : ℕ} (h : r + s = n) (x : M.cycles r) (y : N.cycles s) :
    (P.iCycles n).hom (μ.cycles h x y) = μ.μ h ((M.iCycles r).hom x) ((N.iCycles s).hom y) :=
  μ.iCycles_cyclesProduct h x y

theorem cycles_toCycles_left {r s n i m : ℕ} (h : r + s = n) (hi : i + 1 = r) (hm : i + s = m)
    (hmn : m + 1 = n) (a : M.X i) (y : N.cycles s) :
    μ.cycles h ((M.toCycles i r).hom a) y =
      (P.toCycles m n).hom (μ.μ hm a ((N.iCycles s).hom y)) := by
  subst hi hmn
  apply iCycles_hom_injective P
  rw [iCycles_cycles, iCycles_toCycles_hom_apply, iCycles_toCycles_hom_apply, μ.leibniz hm,
    iCycles_d_apply, map_zero, smul_zero, add_zero]

theorem cycles_toCycles_right {r s n j m : ℕ} (h : r + s = n) (hj : j + 1 = s) (hm : r + j = m)
    (hmn : m + 1 = n) (x : M.cycles r) (b : N.X j) :
    μ.cycles h x ((N.toCycles j s).hom b) =
      (-1 : k) ^ r • (P.toCycles m n).hom (μ.μ hm ((M.iCycles r).hom x) b) := by
  subst hj hmn
  apply iCycles_hom_injective P
  rw [iCycles_cycles, map_smul, iCycles_toCycles_hom_apply, iCycles_toCycles_hom_apply,
    μ.leibniz hm, iCycles_d_apply, map_zero, LinearMap.zero_apply, zero_add, smul_smul,
    ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

/-- The product of cycles, followed by the class map, as a bilinear map on cycles. -/
noncomputable def homologyPairing {r s n : ℕ} (h : r + s = n) :
    N.homology s →ₗ[k] M.cycles r →ₗ[k] P.homology n :=
  descHomologyNat N ((μ.cycles h).compr₂ (P.homologyπ n).hom).flip fun j hj b => by
    ext x
    change (P.homologyπ n).hom (μ.cycles h x ((N.toCycles j s).hom b)) = 0
    rw [μ.cycles_toCycles_right h hj rfl (by omega), map_smul, homologyπ_toCycles_hom_apply,
      smul_zero]

theorem homologyPairing_homology_class {r s n : ℕ} (h : r + s = n) (x : M.cycles r) (y : N.cycles s) :
    μ.homologyPairing h ((N.homologyπ s).hom y) x = (P.homologyπ n).hom (μ.cycles h x y) := by
  rw [homologyPairing, descHomologyNat_homologyπ]
  rfl

/-- The pairing induced in homology, `Hʳ(M) × Hˢ(N) → Hⁿ(P)`. -/
noncomputable def homology {r s n : ℕ} (h : r + s = n) :
    M.homology r →ₗ[k] N.homology s →ₗ[k] P.homology n :=
  descHomologyNat M (μ.homologyPairing h).flip fun i hi a => by
    ext z
    obtain ⟨y, rfl⟩ := homologyπ_hom_surjective N s z
    change μ.homologyPairing h ((N.homologyπ s).hom y) ((M.toCycles i r).hom a) = 0
    rw [homologyPairing_homology_class, μ.cycles_toCycles_left h hi rfl (by omega),
      homologyπ_toCycles_hom_apply]

@[simp]
theorem homology_homologyπ {r s n : ℕ} (h : r + s = n) (x : M.cycles r) (y : N.cycles s) :
    μ.homology h ((M.homologyπ r).hom x) ((N.homologyπ s).hom y) =
      (P.homologyπ n).hom (μ.cycles h x y) := by
  rw [homology, descHomologyNat_homologyπ, LinearMap.flip_apply, homologyPairing_homology_class]

end LeibnizPairing

section TwoSequences

variable {SM SN : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ)}
  {P : CochainComplex (ModuleCat.{u} k) ℕ}

theorem δ_homologyπ_of_lift (hS : SM.ShortExact) (r : ℕ) (x₃ : SM.X₃.cycles r)
    (x₂ : SM.X₂.X r) (hx₂ : (SM.g.f r).hom x₂ = (SM.X₃.iCycles r).hom x₃)
    (x₁ : SM.X₁.cycles (r + 1))
    (hx₁ : (SM.f.f (r + 1)).hom ((SM.X₁.iCycles (r + 1)).hom x₁) = (SM.X₂.d r (r + 1)).hom x₂) :
    hS.δ r (r + 1) rfl ((SM.X₃.homologyπ r).hom x₃) = (SM.X₁.homologyπ (r + 1)).hom x₁ := by
  have hx₃ : (SM.X₃.d r (r + 1)).hom ((SM.X₃.iCycles r).hom x₃) = 0 :=
    iCycles_d_apply _ r (r + 1) x₃
  have key := hS.δ_apply r (r + 1) rfl ((SM.X₃.iCycles r).hom x₃) hx₃ x₂ hx₂
    ((SM.X₁.iCycles (r + 1)).hom x₁) hx₁ (r + 1 + 1) (by simp)
  have e3 : SM.X₃.cyclesMk ((SM.X₃.iCycles r).hom x₃) (r + 1)
      ((ComplexShape.up ℕ).next_eq' rfl) hx₃ = x₃ :=
    iCycles_hom_injective _ r (SM.X₃.i_cyclesMk _ _ _ _)
  have e1 : SM.X₁.cyclesMk ((SM.X₁.iCycles (r + 1)).hom x₁) (r + 1 + 1) (by simp)
      (hS.d_eq_zero_of_f_eq_d_apply r (r + 1) x₂ ((SM.X₁.iCycles (r + 1)).hom x₁) hx₁
        (r + 1 + 1)) = x₁ :=
    iCycles_hom_injective _ (r + 1) (SM.X₁.i_cyclesMk _ _ _ _)
  rw [← e3, ← e1]
  exact key

theorem exists_cycles_f_eq_d (hS : SM.ShortExact) (r : ℕ) (x₃ : SM.X₃.cycles r)
    (x₂ : SM.X₂.X r) (hx₂ : (SM.g.f r).hom x₂ = (SM.X₃.iCycles r).hom x₃) :
    ∃ x₁ : SM.X₁.cycles (r + 1),
      (SM.f.f (r + 1)).hom ((SM.X₁.iCycles (r + 1)).hom x₁) = (SM.X₂.d r (r + 1)).hom x₂ := by
  have hn := (HomologicalComplex.shortExact_iff_degreewise_shortExact SM).1 hS (r + 1)
  have e := hn.exact
  rw [ShortComplex.moduleCat_exact_iff] at e
  obtain ⟨y, hy⟩ := e ((SM.X₂.d r (r + 1)).hom x₂) (by
    change (SM.g.f (r + 1)).hom ((SM.X₂.d r (r + 1)).hom x₂) = 0
    rw [← hom_apply_hom_apply_eq_of_comp_eq (SM.g.comm r (r + 1)) x₂, hx₂, iCycles_d_apply])
  have hy' : (SM.X₁.d (r + 1) (r + 1 + 1)).hom y = 0 :=
    hS.d_eq_zero_of_f_eq_d_apply r (r + 1) x₂ y hy (r + 1 + 1)
  obtain ⟨x₁, hx₁⟩ := exists_iCycles_eq (K := SM.X₁) y (by rw [CochainComplex.next]; exact hy')
  exact ⟨x₁, by rw [hx₁]; exact hy⟩

variable (μ : LeibnizPairing SM.X₂ SN.X₂ P) (μ₁ : LeibnizPairing SM.X₁ SN.X₃ P)
  (μ₃ : LeibnizPairing SM.X₃ SN.X₁ P)

/-- For pairings `μ₁, μ₂, μ₃` compatible with two short exact sequences of complexes, `δx·y +
(-1)ʳ x·δy = 0` in homology. -/
theorem LeibnizPairing.homology_δ_add_homology_δ
    (h₁₂ : ∀ {r s n : ℕ} (h : r + s = n) (x : SM.X₁.X r) (y : SN.X₂.X s),
      μ.μ h ((SM.f.f r).hom x) y = μ₁.μ h x ((SN.g.f s).hom y))
    (h₂₃ : ∀ {r s n : ℕ} (h : r + s = n) (x : SM.X₂.X r) (y : SN.X₁.X s),
      μ.μ h x ((SN.f.f s).hom y) = μ₃.μ h ((SM.g.f r).hom x) y)
    (hSM : SM.ShortExact) (hSN : SN.ShortExact) {r s n : ℕ} (h₁ : r + 1 + s = n + 1)
    (h₃ : r + (s + 1) = n + 1) (x : SM.X₃.homology r) (y : SN.X₃.homology s) :
    μ₁.homology h₁ (hSM.δ r (r + 1) rfl x) y +
      (-1 : k) ^ r • μ₃.homology h₃ x (hSN.δ s (s + 1) rfl y) = 0 := by
  obtain ⟨x₃, rfl⟩ := homologyπ_hom_surjective _ r x
  obtain ⟨y₃, rfl⟩ := homologyπ_hom_surjective _ s y
  have hSMr := (HomologicalComplex.shortExact_iff_degreewise_shortExact SM).1 hSM r
  have hSNs := (HomologicalComplex.shortExact_iff_degreewise_shortExact SN).1 hSN s
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ : SM.X₂.X r, (SM.g.f r).hom x₂ = (SM.X₃.iCycles r).hom x₃ :=
    (ModuleCat.epi_iff_surjective _).1 hSMr.epi_g _
  obtain ⟨y₂, hy₂⟩ : ∃ y₂ : SN.X₂.X s, (SN.g.f s).hom y₂ = (SN.X₃.iCycles s).hom y₃ :=
    (ModuleCat.epi_iff_surjective _).1 hSNs.epi_g _
  obtain ⟨x₁, hx₁⟩ := exists_cycles_f_eq_d hSM r x₃ x₂ hx₂
  obtain ⟨y₁, hy₁⟩ := exists_cycles_f_eq_d hSN s y₃ y₂ hy₂
  rw [δ_homologyπ_of_lift hSM r x₃ x₂ hx₂ x₁ hx₁, δ_homologyπ_of_lift hSN s y₃ y₂ hy₂ y₁ hy₁,
    μ₁.homology_homologyπ, μ₃.homology_homologyπ, ← map_smul, ← map_add]
  have hn : n = r + s := by omega
  subst hn
  have e : μ₁.cycles h₁ x₁ y₃ + (-1 : k) ^ r • μ₃.cycles h₃ x₃ y₁ =
      (P.toCycles (r + s) (r + s + 1)).hom (μ.μ rfl x₂ y₂) := by
    apply iCycles_hom_injective P
    rw [map_add, map_smul, LeibnizPairing.iCycles_cycles, LeibnizPairing.iCycles_cycles,
      iCycles_toCycles_hom_apply, μ.leibniz, ← hx₁, ← hy₁, h₁₂, h₂₃, hx₂, hy₂]
  rw [e, homologyπ_toCycles_hom_apply]

end TwoSequences

end Pairing

-- from CompactSupportCohomology/CupLeibniz.lean
section CupLeibniz

open CategoryTheory Limits MonoidalCategory groupCohomology


section Global

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A B C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] [IsSmoothRep C]

/-- The cup product of locally constant cochains along `μ : A ⊗ B ⟶ C`, as a bilinear map. -/
noncomputable def cupPairingCochains (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n) :
    (cochains A).X r →ₗ[k] (cochains B).X s →ₗ[k] (cochains C).X n :=
  (cupLocallyConstant h).compr₂ ((coeffCochainsMap μ).f n).hom

theorem cochainOf_cupPairingCochains (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n)
    (x : (cochains A).X r) (y : (cochains B).X s) :
    cochainOf C (cupPairingCochains μ h x y) =
      fun σ => μ.hom (cupCochain h (cochainOf A x) (cochainOf B y) σ) :=
  rfl

/-- The Leibniz rule for the cup product of locally constant cochains. -/
theorem d_cupLocallyConstant {r s n : ℕ} (h : r + s = n) (x : (cochains A).X r)
    (y : (cochains B).X s) :
    ((cochains (A ⊗ B)).d n (n + 1)).hom (cupLocallyConstant h x y) =
      cupLocallyConstant (by omega) (((cochains A).d r (r + 1)).hom x) y +
        (-1 : k) ^ r • cupLocallyConstant (by omega) x (((cochains B).d s (s + 1)).hom y) := by
  apply cochainOf_injective
  rw [cochainOf_add, cochainOf_smul]
  exact (cochainOf_d _).trans ((d_cupCochain h _ _).trans (by
    rw [← cochainOf_d, ← cochainOf_d]
    rfl))

/-- The cup product of locally constant cochains along `μ : A ⊗ B ⟶ C` as a Leibniz pairing. -/
noncomputable def cupLeibniz (μ : A ⊗ B ⟶ C) :
    LeibnizPairing (cochains A) (cochains B) (cochains C) where
  μ h := cupPairingCochains μ h
  leibniz {r s n} h x y := by
    change ((cochains C).d n (n + 1)).hom
        (((coeffCochainsMap μ).f n).hom (cupLocallyConstant h x y)) =
      ((coeffCochainsMap μ).f (n + 1)).hom
          (cupLocallyConstant (by omega) (((cochains A).d r (r + 1)).hom x) y) +
        (-1 : k) ^ r • ((coeffCochainsMap μ).f (n + 1)).hom
          (cupLocallyConstant (by omega) x (((cochains B).d s (s + 1)).hom y))
    rw [hom_apply_hom_apply_eq_of_comp_eq ((coeffCochainsMap μ).comm n (n + 1)),
      d_cupLocallyConstant, map_add, map_smul]

/-- The pairing in homology of `cupLeibniz μ` is the foundations' `cupPairing μ`. -/
theorem cupLeibniz_homology (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n) (x : cohomology A r)
    (y : cohomology B s) : (cupLeibniz μ).homology h x y = cupPairing μ h x y := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective _ r x
  obtain ⟨y, rfl⟩ := homologyπ_hom_surjective _ s y
  refine ((cupLeibniz μ).homology_homologyπ h x y).trans ?_
  refine Eq.trans ?_ (cupPairing_cohomologyπ μ h x y).symm
  congr 1
  apply iCycles_hom_injective
  rw [LeibnizPairing.iCycles_cycles, iCycles_cyclesMap_apply]
  exact congrArg ((coeffCochainsMap μ).f n).hom (cocycleι_cupCocycles h x y).symm

end Global

namespace LeibnizPairing

variable {k : Type u} [CommRing k] {ι : Type u} {K N P : ι → CochainComplex (ModuleCat.{u} k) ℕ}
  (μs : ∀ v, LeibnizPairing (K v) (N v) (P v))

/-- The product of a family of Leibniz pairings, as a Leibniz pairing of the product complexes. -/
noncomputable def pi : LeibnizPairing (piComplex K) (piComplex N) (piComplex P) where
  μ {r s n} h := LinearMap.mk₂ k
    (fun (x : ∀ v, (K v).X r) (y : ∀ v, (N v).X s) =>
      (show (piComplex P).X n from fun v => (μs v).μ h (x v) (y v)))
    (fun x x' y => funext fun v => LinearMap.map_add₂ _ _ _ _)
    (fun c x y => funext fun v => LinearMap.map_smul₂ _ _ _ _)
    (fun x y y' => funext fun v => map_add _ _ _)
    (fun c x y => funext fun v => map_smul _ _ _)
  leibniz {r s n} h x y := funext fun v => by
    rw [piComplex_d_hom_apply]
    change ((P v).d n (n + 1)).hom ((μs v).μ h (x v) (y v)) =
      (μs v).μ (by omega) (((piComplex K).d r (r + 1)).hom x v) (y v) +
        (-1 : k) ^ r • (μs v).μ (by omega) (x v) (((piComplex N).d s (s + 1)).hom y v)
    rw [piComplex_d_hom_apply, piComplex_d_hom_apply]
    exact (μs v).leibniz h (x v) (y v)

theorem pi_μ_apply {r s n : ℕ} (h : r + s = n) (x : (piComplex K).X r) (y : (piComplex N).X s)
    (v : ι) : (pi μs).μ h x y v = (μs v).μ h (x v) (y v) :=
  rfl

/-- The homology pairing of a product of Leibniz pairings is computed factorwise. -/
theorem piHomologyIso_hom_pi_homology {r s n : ℕ} (h : r + s = n)
    (x : (piComplex K).homology r) (y : (piComplex N).homology s) (v : ι) :
    (piHomologyIso P n).hom.hom ((pi μs).homology h x y) v =
      (μs v).homology h ((piHomologyIso K r).hom.hom x v) ((piHomologyIso N s).hom.hom y v) := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective _ r x
  obtain ⟨y, rfl⟩ := homologyπ_hom_surjective _ s y
  rw [piHomologyIso_hom_apply, piHomologyIso_hom_apply, piHomologyIso_hom_apply,
    homology_homologyπ, homologyMap_homologyπ_apply, homologyMap_homologyπ_apply,
    homologyMap_homologyπ_apply, homology_homologyπ]
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cyclesMap_apply, iCycles_cycles, iCycles_cycles, iCycles_cyclesMap_apply,
    iCycles_cyclesMap_apply]
  rfl

end LeibnizPairing

section Local

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {A B C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] [IsSmoothRep C]
  {Aᵥ Bᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsSmoothRep (Aᵥ v)] [∀ v, IsSmoothRep (Bᵥ v)]
  [∀ v, IsSmoothRep (Cᵥ v)] {a : ∀ v, Rep.res (φ v : H v →* G) A ⟶ Aᵥ v}
  {b : ∀ v, Rep.res (φ v : H v →* G) B ⟶ Bᵥ v} {c : ∀ v, Rep.res (φ v : H v →* G) C ⟶ Cᵥ v}

/-- `localRes` is compatible with cup products when the local pairings are compatible with the
global one. -/
theorem localRes_cupPairingCochains (μ : A ⊗ B ⟶ C) (μᵥ : ∀ v, Aᵥ v ⊗ Bᵥ v ⟶ Cᵥ v)
    (hμ : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map μ ≫ c v =
      resTensorHom (φ v : H v →* G) (a v) (b v) ≫ μᵥ v)
    {r s n : ℕ} (h : r + s = n) (x : (cochains A).X r) (z : (cochains B).X s) :
    ((localRes φ C Cᵥ c).f n).hom (cupPairingCochains μ h x z) =
      (LeibnizPairing.pi fun v => cupLeibniz (μᵥ v)).μ h (((localRes φ A Aᵥ a).f r).hom x)
        (((localRes φ B Bᵥ b).f s).hom z) := by
  funext v
  apply cochainOf_injective
  funext σ
  change (c v).hom (μ.hom (cupCochain h (cochainOf A x) (cochainOf B z) (⇑(φ v : H v →* G) ∘ σ))) =
    (μᵥ v).hom (cupCochain h (fun τ => (a v).hom (cochainOf A x (⇑(φ v : H v →* G) ∘ τ)))
      (fun τ => (b v).hom (cochainOf B z (⇑(φ v : H v →* G) ∘ τ))) σ)
  rw [cupCochain_apply, cupCochain_apply, ← Rep.hom_comm_apply, partialProd_comp_monoidHom]
  exact congrArg (fun F : Rep.res (φ v : H v →* G) (A ⊗ B) ⟶ Cᵥ v => F.hom
    ((cochainOf A x fun i => (⇑(φ v : H v →* G) ∘ σ) ⟨i, by omega⟩) ⊗ₜ[k]
      B.ρ ((φ v : H v →* G) (Fin.partialProd σ ⟨r, by omega⟩))
        (cochainOf B z fun j => (⇑(φ v : H v →* G) ∘ σ) ⟨r + j, by omega⟩) :
      (A ⊗ B : Rep k G))) (hμ v)

end Local

end CupLeibniz

end Langlands.GaloisCohomology
