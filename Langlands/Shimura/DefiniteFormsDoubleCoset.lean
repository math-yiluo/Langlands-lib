import Langlands.Shimura.DefiniteForms
import Langlands.Shimura.EquivariantFormsDoubleCoset

/-!
# Harris's forms of definite similitude groups restricted to double cosets

Let `σ` be an involution of a finite-dimensional `ℚ`-algebra with finite adelic points
`σ.FiniteAdelicPoints` (Harris's `GJ(𝔸^f)`), `ℓ` a finite place of `ℚ`, and `K` a subgroup of
the finite adelic points. This file applies the generic restriction to double cosets of
`Langlands.Shimura.EquivariantFormsDoubleCoset` to Harris, *Galois properties of cohomological
automorphic forms on GL(n)*, 1999, (3.6)-(3.10), with `GJ(ℚ)` embedded diagonally by
`σ.finiteAdelicDiagonal`.

Harris assumes `K = K^ℓ × K_ℓ`. Without this product decomposition we take for `K^ℓ` the
elements of `K` with trivial `ℓ`-component and for `K_ℓ` the image of `K` under the
`ℓ`-component map `σ.finiteLocalMap ℓ`; for a product these are Harris's subgroups.

## Main definitions

* `primeToLevel σ ℓ K`, `localLevel σ ℓ K`, `localLevelMap σ ℓ K`: the subgroups `K^ℓ` of `K`
  and `K_ℓ` of the `ℓ`-adic points, and the surjection `K → K_ℓ`, `k ↦ k_ℓ`.
* `LocalLevelFree σ ℓ K`: Harris's hypothesis (3.6), that `K_ℓ` acts without fixed points on
  `GJ(ℚ)\GJ(𝔸^f)/K^ℓ`; `localLevelFree_iff` restates it as the stabilizer condition of
  `EquivariantFormsDoubleCoset`.
* `ellModuleForms σ ℓ K ρ`: Harris's `𝒜_ℓ(GJ, 𝓛, K)` (3.7) for a representation `ρ` of `K_ℓ`;
  `ellAdicForms_eq_ellModuleForms` recovers the published `ellAdicForms`, and
  `ellModuleForms_trivial` the generic `forms` with trivial coefficients.
* `ellModuleFormsEquiv σ ℓ h`: under (3.6), restriction to the double cosets
  `GJ(ℚ)\GJ(𝔸^f)/K` identifies `𝒜_ℓ(GJ, 𝓛, K)` with the functions on the double cosets with
  values in `𝓛`.
* `congruenceLevel σ ℓ K H`: Harris's `K(n)`, the elements of `K` whose `ℓ`-component lies in a
  normal subgroup `H` (Harris's `K_ℓ(n)`) of `K_ℓ`.
* `congruenceLevelEquiv σ ℓ H h`: Harris's (3.10), under (3.6): the forms of level `K(n)` with
  trivial coefficients, with `K` acting by right translation, are the functions on
  `K_ℓ ⧸ K_ℓ(n)` with values in the functions on the double cosets `GJ(ℚ)\GJ(𝔸^f)/K`.
* `Langlands.Induction.functionRepresentationCongr`: transport of function representations along
  an equivariant bijection, used for `K ⧸ K(n) ≃ K_ℓ ⧸ K_ℓ(n)`.
-/

noncomputable section

namespace Langlands.Induction

universe uR uW uG uG' uX uY

variable {R : Type uR} [CommRing R] {W : Type uW} [AddCommGroup W] [Module R W]
  {G : Type uG} {G' : Type uG'} [Group G] [Group G']

/-- Transport of function representations: for a homomorphism `f : G →* G'`, representations
`σ` of `G` and `σ'` of `G'` on `W` with `σ g = σ' (f g)`, and a bijection `e : X ≃ Y` with
`e (g • x) = f g • e x`, composition with `e.symm` is an equivalence from the representation of
`G` on `X → W` to the representation of `G'` on `Y → W` restricted to `G` along `f`. -/
def functionRepresentationCongr (σ : Representation R G W) (σ' : Representation R G' W)
    (f : G →* G') (hσ : ∀ g, σ g = σ' (f g)) {X : Type uX} {Y : Type uY} [MulAction G X]
    [MulAction G' Y] (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = f g • e x) :
    Representation.Equiv (functionRepresentation σ X) ((functionRepresentation σ' Y).comp f) :=
  Representation.Equiv.mk (LinearEquiv.funCongrLeft R W e.symm) fun g => by
    refine LinearMap.ext fun F => funext fun y => ?_
    have hy : e.symm ((f g)⁻¹ • y) = g⁻¹ • e.symm y := by
      rw [Equiv.symm_apply_eq, he, map_inv, Equiv.apply_symm_apply]
    change σ g (F (g⁻¹ • e.symm y)) = σ' (f g) (F (e.symm ((f g)⁻¹ • y)))
    rw [hy, hσ]

@[simp]
lemma functionRepresentationCongr_apply (σ : Representation R G W) (σ' : Representation R G' W)
    (f : G →* G') (hσ : ∀ g, σ g = σ' (f g)) {X : Type uX} {Y : Type uY} [MulAction G X]
    [MulAction G' Y] (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = f g • e x) (F : X → W)
    (y : Y) : functionRepresentationCongr σ σ' f hσ e he F y = F (e.symm y) :=
  rfl

end Langlands.Induction

namespace Langlands.Shimura.DefiniteForms

open Langlands.Global Langlands.Shimura.EquivariantForms
open scoped TensorProduct

universe u v w t uR

variable {A : Type v} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A) [Module.Finite ℚ A]
  (ℓ : FinitePlace ℚ)

section Levels

variable (K : Subgroup σ.FiniteAdelicPoints)

/-- Harris's `K^ℓ = K ∩ GJ^ℓ`: the elements of `K` with trivial `ℓ`-component. -/
def primeToLevel : Subgroup σ.FiniteAdelicPoints :=
  K ⊓ (σ.finiteLocalMap ℓ).toMonoidHom.ker

/-- The image of `K` under the `ℓ`-component map; for `K = K^ℓ × K_ℓ` this is Harris's
`K_ℓ = K ∩ GJ_ℓ`, viewed in the `ℓ`-adic points. -/
def localLevel : Subgroup (σ.Points (FiniteCompletion ℚ ℓ)) :=
  K.map (σ.finiteLocalMap ℓ).toMonoidHom

/-- The `ℓ`-component map `k ↦ k_ℓ` from `K` onto `K_ℓ`. -/
def localLevelMap : K →* localLevel σ ℓ K :=
  (σ.finiteLocalMap ℓ).toMonoidHom.subgroupMap K

@[simp]
lemma localLevelMap_apply_coe (k : K) :
    (localLevelMap σ ℓ K k : σ.Points (FiniteCompletion ℚ ℓ)) = σ.finiteLocalMap ℓ k :=
  rfl

lemma localLevelMap_surjective : Function.Surjective (localLevelMap σ ℓ K) :=
  MonoidHom.subgroupMap_surjective _ _

variable {σ ℓ K} in
lemma mem_primeToLevel {g : σ.FiniteAdelicPoints} :
    g ∈ primeToLevel σ ℓ K ↔ g ∈ K ∧ σ.finiteLocalMap ℓ g = 1 :=
  Iff.rfl

lemma primeToLevel_le : primeToLevel σ ℓ K ≤ K :=
  inf_le_left

variable {σ ℓ K} in
lemma mem_primeToLevel_subgroupOf {k : K} :
    k ∈ (primeToLevel σ ℓ K).subgroupOf K ↔ σ.finiteLocalMap ℓ k = 1 :=
  Subgroup.mem_subgroupOf.trans (mem_primeToLevel.trans (and_iff_right k.2))

/-- `K^ℓ` is the kernel of `K → K_ℓ`. -/
lemma primeToLevel_subgroupOf : (primeToLevel σ ℓ K).subgroupOf K = (localLevelMap σ ℓ K).ker := by
  ext k
  rw [mem_primeToLevel_subgroupOf, MonoidHom.mem_ker, ← Subtype.coe_inj]
  rfl

instance : ((primeToLevel σ ℓ K).subgroupOf K).Normal := by
  rw [primeToLevel_subgroupOf]
  infer_instance

/-- Harris's hypothesis (1999, (3.6)) that `K_ℓ` acts without fixed points on
`GJ(ℚ)\GJ(𝔸^f)/K^ℓ`: right translation by `k ∈ K` fixes the class of some `g` only if `k` has
trivial `ℓ`-component. -/
def LocalLevelFree : Prop :=
  ∀ (g : σ.FiniteAdelicPoints) (k : K),
    DoubleCoset.mk σ.finiteAdelicDiagonal.range (primeToLevel σ ℓ K) (g * k) =
        DoubleCoset.mk σ.finiteAdelicDiagonal.range (primeToLevel σ ℓ K) g →
      σ.finiteLocalMap ℓ k = 1

/-- Harris's (3.6) is the condition that every stabilizer `Δ_g` lies in `K^ℓ`. -/
lemma localLevelFree_iff :
    LocalLevelFree σ ℓ K ↔
      ∀ g : σ.FiniteAdelicPoints,
        doubleCosetStabilizer σ.finiteAdelicDiagonal K g ≤ (primeToLevel σ ℓ K).subgroupOf K := by
  rw [doubleCosetStabilizer_le_iff σ.finiteAdelicDiagonal (primeToLevel_le σ ℓ K)]
  simp only [mem_primeToLevel_subgroupOf]
  rfl

end Levels

section Module

variable (K : Subgroup σ.FiniteAdelicPoints) {R : Type uR} [CommRing R] {V : Type t}
  [AddCommGroup V] [Module R V] (ρ : Representation R (localLevel σ ℓ K) V)

/-- Harris's `𝒜_ℓ(GJ, 𝓛, K)` (1999, (3.7)) for a representation `ρ` of `K_ℓ` on an
`R`-module `𝓛`: the functions `f : GJ(𝔸^f) → 𝓛` with `f (γ g) = f g` for rational `γ` and
`f (g k) = ρ(k_ℓ)⁻¹ (f g)` for `k ∈ K`; the generic `forms` for `ρ` composed with
`k ↦ k_ℓ`. -/
abbrev ellModuleForms : Submodule R (σ.FiniteAdelicPoints → V) :=
  forms σ.finiteAdelicDiagonal K (ρ.comp (localLevelMap σ ℓ K))

/-- With trivial coefficients `R`, `𝒜_ℓ(GJ, R, K)` is the generic `forms` for the trivial
representation of `K`. -/
lemma ellModuleForms_trivial :
    ellModuleForms σ ℓ K (Representation.trivial R (localLevel σ ℓ K) R) =
      forms σ.finiteAdelicDiagonal K (Representation.trivial R K R) :=
  rfl

/-- On `K^ℓ`, the representation `ρ` composed with `k ↦ k_ℓ` is trivial. -/
lemma comp_localLevelMap_eq_one {k : K} (hk : k ∈ (primeToLevel σ ℓ K).subgroupOf K) :
    ρ.comp (localLevelMap σ ℓ K) k = 1 := by
  rw [primeToLevel_subgroupOf, MonoidHom.mem_ker] at hk
  rw [MonoidHom.comp_apply, hk, map_one]

variable {σ ℓ K} in
/-- Under (3.6), every vector is invariant under the stabilizers `Δ_g`. -/
lemma invariants_eq_top (h : LocalLevelFree σ ℓ K) (g : σ.FiniteAdelicPoints) :
    Representation.invariants
        ((ρ.comp (localLevelMap σ ℓ K)).comp
          (doubleCosetStabilizer σ.finiteAdelicDiagonal K g).subtype) = ⊤ := by
  refine eq_top_iff.2 fun v _ => (Representation.mem_invariants _ v).2 fun k => ?_
  change ρ.comp (localLevelMap σ ℓ K) k v = v
  rw [comp_localLevelMap_eq_one σ ℓ K ρ ((localLevelFree_iff σ ℓ K).1 h g k.2)]
  rfl

variable {K ρ} in
/-- Under Harris's (3.6), restriction to the representatives of the double cosets
`GJ(ℚ)\GJ(𝔸^f)/K` identifies `𝒜_ℓ(GJ, 𝓛, K)` with the functions on the double cosets with values
in `𝓛`, `f ↦ (x ↦ f x.out)`: the stabilizers lie in `K^ℓ`, which acts trivially on `𝓛`. -/
def ellModuleFormsEquiv (h : LocalLevelFree σ ℓ K) :
    ellModuleForms σ ℓ K ρ ≃ₗ[R] (DoubleCosets σ.finiteAdelicDiagonal K → V) :=
  (doubleCosetEquiv σ.finiteAdelicDiagonal K (ρ.comp (localLevelMap σ ℓ K))).trans
    (LinearEquiv.piCongrRight fun x =>
      (LinearEquiv.ofEq _ _ (invariants_eq_top ρ h x.out)).trans Submodule.topEquiv)

@[simp]
lemma ellModuleFormsEquiv_apply (h : LocalLevelFree σ ℓ K) (f : ellModuleForms σ ℓ K ρ)
    (x : DoubleCosets σ.finiteAdelicDiagonal K) :
    ellModuleFormsEquiv σ ℓ h f x = f.1 x.out :=
  rfl

end Module

section Adic

variable {L : Type u} [Field L] [Algebra ℚ L] {W : Type w} [AddCommGroup W] [Module L W]
  (ρ : (σ.baseChange L).AlgebraicRepresentation W) {S : Type u} [CommRing S] [Algebra ℚ S]
  [Algebra L S] (φ : FiniteCompletion ℚ ℓ →ₐ[ℚ] S) (K : Subgroup σ.FiniteAdelicPoints)

/-- Harris's `ρ` on `W(S)` restricted to `K_ℓ`: the action `k_ℓ ↦ ρ(k_ℓ)` of the `ℓ`-adic points
through `φ : ℚ_ℓ → S`, restricted to `K_ℓ`. -/
def localRep : Representation S (localLevel σ ℓ K) (S ⊗[L] W) :=
  (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (ρ.actVia φ)).comp
    (localLevel σ ℓ K).subtype

/-- The published `𝒜_ℓ(GJ, ρ, K)(S)` (3.3) is `𝒜_ℓ(GJ, 𝓛, K)` (3.7) for `𝓛 = W(S)` with the
action of `K_ℓ` by `ρ`. -/
lemma ellAdicForms_eq_ellModuleForms :
    ellAdicForms σ ρ ℓ φ K = ellModuleForms σ ℓ K (localRep σ ℓ ρ φ K) :=
  rfl

variable {K} in
/-- Under Harris's (3.6), restriction to the representatives of the double cosets identifies
`𝒜_ℓ(GJ, ρ, K)(S)` with the functions on the double cosets with values in `W(S)`. -/
def ellAdicFormsEquiv (h : LocalLevelFree σ ℓ K) :
    ellAdicForms σ ρ ℓ φ K ≃ₗ[S] (DoubleCosets σ.finiteAdelicDiagonal K → S ⊗[L] W) :=
  ellModuleFormsEquiv σ ℓ (ρ := localRep σ ℓ ρ φ K) h

@[simp]
lemma ellAdicFormsEquiv_apply (h : LocalLevelFree σ ℓ K) (f : ellAdicForms σ ρ ℓ φ K)
    (x : DoubleCosets σ.finiteAdelicDiagonal K) :
    ellAdicFormsEquiv σ ℓ ρ φ h f x = f.1 x.out :=
  rfl

end Adic

section Congruence

variable (K : Subgroup σ.FiniteAdelicPoints) (H : Subgroup (localLevel σ ℓ K))

/-- Harris's `K(n) = K_ℓ(n) × K^ℓ`: the elements of `K` whose `ℓ`-component lies in the
subgroup `H` (Harris's normal subgroup `K_ℓ(n)`) of `K_ℓ`. -/
def congruenceLevel : Subgroup σ.FiniteAdelicPoints :=
  K ⊓ (H.map (localLevel σ ℓ K).subtype).comap (σ.finiteLocalMap ℓ).toMonoidHom

lemma congruenceLevel_le : congruenceLevel σ ℓ K H ≤ K :=
  inf_le_left

/-- `K(n)` is the preimage of `K_ℓ(n)` under `K → K_ℓ`. -/
lemma congruenceLevel_subgroupOf :
    (congruenceLevel σ ℓ K H).subgroupOf K = H.comap (localLevelMap σ ℓ K) := by
  ext k
  simp only [Subgroup.mem_subgroupOf, congruenceLevel, Subgroup.mem_inf, Subgroup.mem_comap,
    Subgroup.mem_map, Subgroup.coe_subtype, k.2, true_and]
  constructor
  · rintro ⟨y, hy, he⟩
    have : y = localLevelMap σ ℓ K k := Subtype.ext he
    exact this ▸ hy
  · intro hk
    exact ⟨_, hk, rfl⟩

lemma primeToLevel_le_congruenceLevel : primeToLevel σ ℓ K ≤ congruenceLevel σ ℓ K H := by
  rintro g ⟨hK, hg⟩
  refine ⟨hK, ⟨1, H.one_mem, ?_⟩⟩
  exact hg.symm

/-- Under Harris's (3.6), the stabilizers `Δ_g` lie in `K(n)`. -/
lemma doubleCosetStabilizer_le_congruenceLevel {K : Subgroup σ.FiniteAdelicPoints}
    (h : LocalLevelFree σ ℓ K) (H : Subgroup (localLevel σ ℓ K)) (g : σ.FiniteAdelicPoints) :
    doubleCosetStabilizer σ.finiteAdelicDiagonal K g ≤
      (congruenceLevel σ ℓ K H).subgroupOf K :=
  ((localLevelFree_iff σ ℓ K).1 h g).trans fun _ hk =>
    Subgroup.mem_subgroupOf.2 (primeToLevel_le_congruenceLevel σ ℓ K H hk)

variable [H.Normal]

instance : ((congruenceLevel σ ℓ K H).subgroupOf K).Normal := by
  rw [congruenceLevel_subgroupOf]
  infer_instance

/-- The bijection `K ⧸ K(n) ≃ K_ℓ ⧸ K_ℓ(n)`, `[k] ↦ [k_ℓ]`. -/
def congruenceQuotientEquiv :
    K ⧸ (congruenceLevel σ ℓ K H).subgroupOf K ≃* localLevel σ ℓ K ⧸ H :=
  (QuotientGroup.quotientMulEquivOfEq (by
      rw [congruenceLevel_subgroupOf]
      ext k
      simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff])).trans
    (QuotientGroup.quotientKerEquivOfSurjective ((QuotientGroup.mk' H).comp (localLevelMap σ ℓ K))
      ((QuotientGroup.mk'_surjective H).comp (localLevelMap_surjective σ ℓ K)))

@[simp]
lemma congruenceQuotientEquiv_mk (k : K) :
    congruenceQuotientEquiv σ ℓ K H (k : K ⧸ (congruenceLevel σ ℓ K H).subgroupOf K) =
      (localLevelMap σ ℓ K k : localLevel σ ℓ K ⧸ H) :=
  rfl

variable {R : Type uR} [CommRing R]

omit [H.Normal] in
/-- The forms of level `K(n)` with trivial coefficients on which `levelAction` acts are
Harris's `𝒜_ℓ(GJ, R, K(n))`. -/
lemma levelForms_eq_ellModuleForms :
    forms σ.finiteAdelicDiagonal (congruenceLevel σ ℓ K H)
        ((Representation.trivial R K R).comp (Subgroup.inclusion (congruenceLevel_le σ ℓ K H))) =
      ellModuleForms σ ℓ (congruenceLevel σ ℓ K H)
        (Representation.trivial R (localLevel σ ℓ (congruenceLevel σ ℓ K H)) R) :=
  rfl

variable {K} in
/-- Harris's restriction to double cosets (1999, (3.10)), under the hypothesis (3.6): the forms
of level `K(n)` with trivial coefficients `R`, with `K` acting by right translation
(`levelAction`), are the functions on `K_ℓ ⧸ K_ℓ(n)` with values in the functions on the double
cosets `GJ(ℚ)\GJ(𝔸^f)/K`, with `K` acting through `k ↦ k_ℓ` by left translation of the argument.
A form `f` goes to `[k_ℓ] ↦ x ↦ f (x.out * k⁻¹)`. -/
def congruenceLevelEquiv (h : LocalLevelFree σ ℓ K) :
    Representation.Equiv
      (levelAction σ.finiteAdelicDiagonal (Representation.trivial R K R)
        (congruenceLevel_le σ ℓ K H))
      ((Langlands.Induction.functionRepresentation
        (Representation.trivial R (localLevel σ ℓ K)
          (DoubleCosets σ.finiteAdelicDiagonal K → R)) (localLevel σ ℓ K ⧸ H)).comp
        (localLevelMap σ ℓ K)) :=
  (levelDoubleCosetEquiv σ.finiteAdelicDiagonal (congruenceLevel_le σ ℓ K H)
    (doubleCosetStabilizer_le_congruenceLevel σ ℓ h H)).trans
    (Langlands.Induction.functionRepresentationCongr _ _ (localLevelMap σ ℓ K) (fun _ => rfl)
      (congruenceQuotientEquiv σ ℓ K H).toEquiv fun k q => by
        induction q using QuotientGroup.induction_on with
        | H k' =>
          change congruenceQuotientEquiv σ ℓ K H ((k * k' : K) : K ⧸ _) = _
          rw [congruenceQuotientEquiv_mk, map_mul]
          rfl)

lemma congruenceLevelEquiv_apply_mk (h : LocalLevelFree σ ℓ K)
    (f : forms σ.finiteAdelicDiagonal (congruenceLevel σ ℓ K H)
      ((Representation.trivial R K R).comp (Subgroup.inclusion (congruenceLevel_le σ ℓ K H))))
    (k : K) (x : DoubleCosets σ.finiteAdelicDiagonal K) :
    congruenceLevelEquiv σ ℓ H h f (localLevelMap σ ℓ K k : localLevel σ ℓ K ⧸ H) x =
      f.1 (x.out * (k : σ.FiniteAdelicPoints)⁻¹) := by
  have hk : (congruenceQuotientEquiv σ ℓ K H).symm
      (localLevelMap σ ℓ K k : localLevel σ ℓ K ⧸ H) = (k : K ⧸ _) := by
    rw [MulEquiv.symm_apply_eq, congruenceQuotientEquiv_mk]
  change levelDoubleCosetEquiv σ.finiteAdelicDiagonal (congruenceLevel_le σ ℓ K H)
    (doubleCosetStabilizer_le_congruenceLevel σ ℓ h H) f
      ((congruenceQuotientEquiv σ ℓ K H).symm (localLevelMap σ ℓ K k : localLevel σ ℓ K ⧸ H)) x = _
  rw [hk]
  rfl

end Congruence

end Langlands.Shimura.DefiniteForms
