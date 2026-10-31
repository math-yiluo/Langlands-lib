import Langlands.Representation.Jacquet.Localization
import Langlands.Representation.Jacquet.PositiveCharacter
import Langlands.Representation.Category.Twist

/-!
# Transitivity of character localization, with supplied twists

For subgroups `U M W H` of `G` with `W ≤ M`, `H ≤ M`, `M` normalizing `U` and `H`
normalizing `W`, localizing at `(U, θ)`, then at the actual copy of `(W, η)` inside `M`,
and restricting to the actual copy of `H`, is the localization at `(U ⊔ W, Θ)` for any
character `Θ` restricting to `θ` and `η`. On classes the comparison is `[[v]] ↦ [v]`.
Supplied twists by `α` on `M` (trivial on `W`) and `β` on `H` give the twist by
`α|_H * β`; no Haar modulus is identified with `α` or `β` here.
-/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.Jacquet.Localization

universe uR uG uV uW uN

variable {G : Type uG} [Group G]

section Join

/-- A subgroup of `U ⊔ W` containing the actual inclusions of `U` and `W` is everything. -/
theorem sup_eq_top_of_inclusion_mem {U W : Subgroup G} (S : Subgroup ↥(U ⊔ W))
    (hU : ∀ u : U, Subgroup.inclusion (le_sup_left : U ≤ U ⊔ W) u ∈ S)
    (hW : ∀ w : W, Subgroup.inclusion (le_sup_right : W ≤ U ⊔ W) w ∈ S) : S = ⊤ := by
  have hle : U ⊔ W ≤ S.map (U ⊔ W).subtype :=
    sup_le (fun u hu => ⟨_, hU ⟨u, hu⟩, rfl⟩) (fun w hw => ⟨_, hW ⟨w, hw⟩, rfl⟩)
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨y, hy, hyx⟩ := hle x.2
  rwa [show y = x from Subtype.ext hyx] at hy

/-- Homomorphisms on `U ⊔ W` that agree along both actual inclusions are equal. -/
theorem sup_hom_ext {N : Type uN} [Group N] {U W : Subgroup G} {f g : ↥(U ⊔ W) →* N}
    (hU : f.comp (Subgroup.inclusion (le_sup_left : U ≤ U ⊔ W)) =
      g.comp (Subgroup.inclusion (le_sup_left : U ≤ U ⊔ W)))
    (hW : f.comp (Subgroup.inclusion (le_sup_right : W ≤ U ⊔ W)) =
      g.comp (Subgroup.inclusion (le_sup_right : W ≤ U ⊔ W))) :
    f = g := by
  have h := sup_eq_top_of_inclusion_mem (MonoidHom.eqLocus f g)
    (fun u => DFunLike.congr_fun hU u) (fun w => DFunLike.congr_fun hW w)
  refine MonoidHom.ext fun x => ?_
  have hx : x ∈ MonoidHom.eqLocus f g := by
    rw [h]
    exact Subgroup.mem_top x
  exact hx

variable {R : Type uR} [CommRing R] {V : Type uV} {X : Type uW}
variable [AddCommGroup V] [Module R V] [AddCommGroup X] [Module R X]

/-- A linear map that is covariant along `U` and along `W` is covariant along `U ⊔ W`,
for a character `Θ` of the join. -/
theorem covariant_sup (ρ : Representation R G V) {U W : Subgroup G}
    (Θ : ↥(U ⊔ W) →* Rˣ) (F : V →ₗ[R] X)
    (hU : ∀ (u : U) (v : V),
      F (ρ u v) = (Θ (Subgroup.inclusion (le_sup_left : U ≤ U ⊔ W) u) : R) • F v)
    (hW : ∀ (w : W) (v : V),
      F (ρ w v) = (Θ (Subgroup.inclusion (le_sup_right : W ≤ U ⊔ W) w) : R) • F v)
    (x : ↥(U ⊔ W)) (v : V) : F (ρ x v) = (Θ x : R) • F v := by
  let S : Subgroup ↥(U ⊔ W) :=
    { carrier := {x | ∀ v, F (ρ x v) = (Θ x : R) • F v}
      mul_mem' := by
        intro a b ha hb v
        change F (ρ ((a : G) * (b : G)) v) = (Θ (a * b) : R) • F v
        rw [map_mul ρ, Module.End.mul_apply, ha, hb, smul_smul, map_mul Θ, Units.val_mul]
      one_mem' := by
        intro v
        change F (ρ (1 : G) v) = (Θ 1 : R) • F v
        simp
      inv_mem' := by
        intro a ha v
        have h := ha (ρ ((a⁻¹ : ↥(U ⊔ W)) : G) v)
        have e : ρ (a : G) (ρ ((a⁻¹ : ↥(U ⊔ W)) : G) v) = v := by
          rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul, mul_inv_cancel,
            OneMemClass.coe_one, map_one, Module.End.one_apply]
        rw [e] at h
        change F (ρ ((a⁻¹ : ↥(U ⊔ W)) : G) v) = (Θ a⁻¹ : R) • F v
        rw [map_inv Θ, h, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          one_smul] }
  have hS : S = ⊤ := sup_eq_top_of_inclusion_mem S hU hW
  have hx : x ∈ S := by
    rw [hS]
    exact Subgroup.mem_top x
  exact hx v

end Join

/-- Concrete subgroup and character data for a localization tower: `W ≤ M`, `H ≤ M`,
`M` normalizes `U`, `H` normalizes `W`, invariant characters `θ` and `η`, and a
character `Θ` of `U ⊔ W` restricting along the actual inclusions to `θ` and `η`. -/
structure TowerDatum (R : Type uR) (G : Type uG) [CommRing R] [Group G] where
  /-- Bundle the data; named so that `mk` keeps referring to the quotient map. -/
  ofData ::
  /-- The first localizing subgroup. -/
  U : Subgroup G
  /-- The subgroup acting on the first quotient. -/
  M : Subgroup G
  /-- The second localizing subgroup. -/
  W : Subgroup G
  /-- The final acting subgroup. -/
  H : Subgroup G
  W_le_M : W ≤ M
  H_le_M : H ≤ M
  M_le_normalizer : M ≤ Subgroup.normalizer U
  H_le_normalizer : H ≤ Subgroup.normalizer W
  /-- The character of the first localization. -/
  θ : U →* Rˣ
  /-- The character of the second localization. -/
  η : W →* Rˣ
  θ_invariant : IsInvariant U M M_le_normalizer θ
  η_invariant : IsInvariant W H H_le_normalizer η
  /-- The combined character of the join. -/
  Θ : ↥(U ⊔ W) →* Rˣ
  Θ_comp_left : Θ.comp (Subgroup.inclusion (le_sup_left : U ≤ U ⊔ W)) = θ
  Θ_comp_right : Θ.comp (Subgroup.inclusion (le_sup_right : W ≤ U ⊔ W)) = η

namespace TowerDatum

section General

variable {R : Type uR} [CommRing R] (D : TowerDatum R G)

theorem Θ_inclusion_left (u : D.U) :
    D.Θ (Subgroup.inclusion (le_sup_left : D.U ≤ D.U ⊔ D.W) u) = D.θ u :=
  DFunLike.congr_fun D.Θ_comp_left u

theorem Θ_inclusion_right (w : D.W) :
    D.Θ (Subgroup.inclusion (le_sup_right : D.W ≤ D.U ⊔ D.W) w) = D.η w :=
  DFunLike.congr_fun D.Θ_comp_right w

/-- The combined character is determined by `θ` and `η`. -/
theorem Θ_unique (Θ' : ↥(D.U ⊔ D.W) →* Rˣ)
    (hl : Θ'.comp (Subgroup.inclusion (le_sup_left : D.U ≤ D.U ⊔ D.W)) = D.θ)
    (hr : Θ'.comp (Subgroup.inclusion (le_sup_right : D.W ≤ D.U ⊔ D.W)) = D.η) :
    Θ' = D.Θ :=
  sup_hom_ext (hl.trans D.Θ_comp_left.symm) (hr.trans D.Θ_comp_right.symm)

/-- `H` normalizes the join `U ⊔ W`. -/
theorem H_le_normalizer_sup : D.H ≤ Subgroup.normalizer (D.U ⊔ D.W : Subgroup G) :=
  fun _ hh => Subgroup.inf_normalizer_le_normalizer_sup D.U D.W
    ⟨D.M_le_normalizer (D.H_le_M hh), D.H_le_normalizer hh⟩

/-- `Θ` is invariant under conjugation by `H`. -/
theorem Θ_invariant : IsInvariant (D.U ⊔ D.W) D.H D.H_le_normalizer_sup D.Θ := by
  intro h x
  let c : ↥(D.U ⊔ D.W) →* ↥(D.U ⊔ D.W) :=
    { toFun := conjugate (D.U ⊔ D.W) D.H D.H_le_normalizer_sup h
      map_one' := Subtype.ext (by
        change (h : G) * 1 * (h : G)⁻¹ = 1
        group)
      map_mul' := fun a b => Subtype.ext (by
        change (h : G) * ((a : G) * (b : G)) * (h : G)⁻¹ =
          ((h : G) * a * (h : G)⁻¹) * ((h : G) * b * (h : G)⁻¹)
        group) }
  have hc : D.Θ.comp c = D.Θ := by
    apply sup_hom_ext
    · refine MonoidHom.ext fun u => ?_
      change D.Θ (Subgroup.inclusion (le_sup_left : D.U ≤ D.U ⊔ D.W)
          (conjugate D.U D.M D.M_le_normalizer ⟨h, D.H_le_M h.2⟩ u)) =
        D.Θ (Subgroup.inclusion (le_sup_left : D.U ≤ D.U ⊔ D.W) u)
      rw [Θ_inclusion_left, Θ_inclusion_left, D.θ_invariant]
    · refine MonoidHom.ext fun w => ?_
      change D.Θ (Subgroup.inclusion (le_sup_right : D.W ≤ D.U ⊔ D.W)
          (conjugate D.W D.H D.H_le_normalizer h w)) =
        D.Θ (Subgroup.inclusion (le_sup_right : D.W ≤ D.U ⊔ D.W) w)
      rw [Θ_inclusion_right, Θ_inclusion_right, D.η_invariant]
  exact DFunLike.congr_fun hc x

/-! ## Actual copies inside `M` -/

/-- The actual copy of `W` inside `M`. -/
abbrev innerSubgroup : Subgroup D.M := D.W.subgroupOf D.M

/-- The actual copy of `H` inside `M`. -/
abbrev actingSubgroup : Subgroup D.M := D.H.subgroupOf D.M

/-- `η` transported along the canonical isomorphism `W.subgroupOf M ≃* W`. -/
def innerCharacter : D.innerSubgroup →* Rˣ :=
  D.η.comp (Subgroup.subgroupOfEquivOfLe D.W_le_M).toMonoidHom

@[simp]
theorem innerCharacter_apply (w : D.innerSubgroup) :
    D.innerCharacter w = D.η ⟨((w : D.M) : G), w.2⟩ := rfl

/-- The canonical isomorphism `H ≃* H.subgroupOf M`, as a homomorphism. -/
def toActing : D.H →* D.actingSubgroup :=
  (Subgroup.subgroupOfEquivOfLe D.H_le_M).symm.toMonoidHom

@[simp]
theorem coe_coe_toActing (h : D.H) : (((D.toActing h : D.M)) : G) = h := rfl

/-- The copy of `H` normalizes the copy of `W` inside `M`. -/
theorem acting_le_normalizer :
    D.actingSubgroup ≤ Subgroup.normalizer (D.innerSubgroup : Set D.M) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro n
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact (Subgroup.mem_normalizer_iff.mp
    (D.H_le_normalizer (Subgroup.mem_subgroupOf.mp hh))) (n : G)

/-- The transported character is invariant under the copy of `H`. -/
theorem innerCharacter_invariant :
    IsInvariant D.innerSubgroup D.actingSubgroup D.acting_le_normalizer D.innerCharacter := by
  intro m w
  exact D.η_invariant ⟨((m : D.M) : G), m.2⟩ ⟨((w : D.M) : G), w.2⟩

/-! ## The algebraic tower equivalence -/

variable {V : Type uV} {X : Type uW} {Y : Type uN}
variable [AddCommGroup V] [Module R V] [AddCommGroup X] [Module R X]
variable [AddCommGroup Y] [Module R Y]

/-- The first localization at `(U, θ)`, with its descended `M` action. -/
abbrev firstAction (ρ : Representation R G V) : Representation R D.M (Coinvariants ρ D.U D.θ) :=
  action ρ D.U D.θ D.M D.M_le_normalizer D.θ_invariant

/-- The carrier of the iterated localization. -/
abbrev IteratedCoinvariants (ρ : Representation R G V) :=
  Coinvariants (D.firstAction ρ) D.innerSubgroup D.innerCharacter

/-- The iterated class map `v ↦ [[v]]`. -/
def iteratedMk (ρ : Representation R G V) : V →ₗ[R] D.IteratedCoinvariants ρ :=
  mk (D.firstAction ρ) D.innerSubgroup D.innerCharacter ∘ₗ mk ρ D.U D.θ

theorem iteratedMk_apply (ρ : Representation R G V) (v : V) :
    D.iteratedMk ρ v =
      mk (D.firstAction ρ) D.innerSubgroup D.innerCharacter (mk ρ D.U D.θ v) := rfl

/-- The iterated localization, with the descended action restricted to `H`. -/
def iteratedAction (ρ : Representation R G V) :
    Representation R D.H (D.IteratedCoinvariants ρ) :=
  (action (D.firstAction ρ) D.innerSubgroup D.innerCharacter D.actingSubgroup
    D.acting_le_normalizer D.innerCharacter_invariant).comp D.toActing

@[simp]
theorem iteratedAction_iteratedMk (ρ : Representation R G V) (h : D.H) (v : V) :
    D.iteratedAction ρ h (D.iteratedMk ρ v) = D.iteratedMk ρ (ρ h v) := rfl

/-- The direct localization at `(U ⊔ W, Θ)`, with its descended `H` action. -/
abbrev directAction (ρ : Representation R G V) :
    Representation R D.H (Coinvariants ρ (D.U ⊔ D.W) D.Θ) :=
  action ρ (D.U ⊔ D.W) D.Θ D.H D.H_le_normalizer_sup D.Θ_invariant

/-- The comparison `[v] ↦ [v]` from the first quotient to the direct quotient. -/
def firstToDirect (ρ : Representation R G V) :
    Coinvariants ρ D.U D.θ →ₗ[R] Coinvariants ρ (D.U ⊔ D.W) D.Θ :=
  lift ρ D.U D.θ (mk ρ (D.U ⊔ D.W) D.Θ) fun u v => by
    rw [← D.Θ_inclusion_left u]
    exact mk_apply_subgroup ρ (D.U ⊔ D.W) D.Θ
      (Subgroup.inclusion (le_sup_left : D.U ≤ D.U ⊔ D.W) u) v

@[simp]
theorem firstToDirect_mk (ρ : Representation R G V) (v : V) :
    D.firstToDirect ρ (mk ρ D.U D.θ v) = mk ρ (D.U ⊔ D.W) D.Θ v := rfl

theorem firstToDirect_inner (ρ : Representation R G V) (w : D.innerSubgroup) (v : V) :
    D.firstToDirect ρ (mk ρ D.U D.θ (ρ ((w : D.M) : G) v)) =
      (D.innerCharacter w : R) • D.firstToDirect ρ (mk ρ D.U D.θ v) := by
  rw [D.innerCharacter_apply, ← D.Θ_inclusion_right]
  exact mk_apply_subgroup ρ (D.U ⊔ D.W) D.Θ
    (Subgroup.inclusion (le_sup_right : D.W ≤ D.U ⊔ D.W) ⟨((w : D.M) : G), w.2⟩) v

/-- The forward map `[[v]] ↦ [v]`. -/
def forward (ρ : Representation R G V) :
    D.IteratedCoinvariants ρ →ₗ[R] Coinvariants ρ (D.U ⊔ D.W) D.Θ :=
  lift (D.firstAction ρ) D.innerSubgroup D.innerCharacter (D.firstToDirect ρ) fun w x => by
    obtain ⟨v, rfl⟩ := mk_surjective ρ D.U D.θ x
    exact D.firstToDirect_inner ρ w v

/-- The iterated class map is `Θ`-covariant along the whole join `U ⊔ W`. -/
theorem iteratedMk_covariant (ρ : Representation R G V) (x : ↥(D.U ⊔ D.W)) (v : V) :
    D.iteratedMk ρ (ρ x v) = (D.Θ x : R) • D.iteratedMk ρ v := by
  refine covariant_sup ρ D.Θ (D.iteratedMk ρ) (fun u v => ?_) (fun w v => ?_) x v
  · rw [D.Θ_inclusion_left]
    change mk (D.firstAction ρ) D.innerSubgroup D.innerCharacter (mk ρ D.U D.θ (ρ u v)) =
      (D.θ u : R) • mk (D.firstAction ρ) D.innerSubgroup D.innerCharacter (mk ρ D.U D.θ v)
    rw [mk_apply_subgroup, map_smul]
  · rw [D.Θ_inclusion_right]
    exact mk_apply_subgroup (D.firstAction ρ) D.innerSubgroup D.innerCharacter
      ((Subgroup.subgroupOfEquivOfLe D.W_le_M).symm w) (mk ρ D.U D.θ v)

/-- The backward map `[v] ↦ [[v]]`. -/
def backward (ρ : Representation R G V) :
    Coinvariants ρ (D.U ⊔ D.W) D.Θ →ₗ[R] D.IteratedCoinvariants ρ :=
  lift ρ (D.U ⊔ D.W) D.Θ (D.iteratedMk ρ) (D.iteratedMk_covariant ρ)

/-- The `H`-equivariant tower equivalence, `[[v]] ↦ [v]`. -/
def equiv (ρ : Representation R G V) : (D.iteratedAction ρ).Equiv (D.directAction ρ) :=
  Representation.Equiv.mk
    (LinearEquiv.ofLinearMap (D.forward ρ) (D.backward ρ)
      (hom_ext (LinearMap.ext fun _ => rfl))
      (hom_ext (hom_ext (LinearMap.ext fun _ => rfl))))
    (fun _ => hom_ext (hom_ext (LinearMap.ext fun _ => rfl)))

@[simp]
theorem equiv_mk_mk (ρ : Representation R G V) (v : V) :
    D.equiv ρ (mk (D.firstAction ρ) D.innerSubgroup D.innerCharacter (mk ρ D.U D.θ v)) =
      mk ρ (D.U ⊔ D.W) D.Θ v := rfl

@[simp]
theorem equiv_iteratedMk (ρ : Representation R G V) (v : V) :
    D.equiv ρ (D.iteratedMk ρ v) = mk ρ (D.U ⊔ D.W) D.Θ v := rfl

@[simp]
theorem equiv_symm_mk (ρ : Representation R G V) (v : V) :
    (D.equiv ρ).symm (mk ρ (D.U ⊔ D.W) D.Θ v) = D.iteratedMk ρ v := rfl

/-- Equivariance for every `h : H`. -/
theorem equiv_equivariant (ρ : Representation R G V) (h : D.H)
    (x : D.IteratedCoinvariants ρ) :
    D.equiv ρ (D.iteratedAction ρ h x) = D.directAction ρ h (D.equiv ρ x) :=
  (D.equiv ρ).toIntertwiningMap.isIntertwining _ _ h x

/-- An intertwiner of representations of the copy of `H`, restricted along `H → H'`. -/
def actingMap {τ : Representation R D.actingSubgroup X}
    {ς : Representation R D.actingSubgroup Y} (f : τ.IntertwiningMap ς) :
    Representation.IntertwiningMap (τ.comp D.toActing) (ς.comp D.toActing) where
  toLinearMap := f.toLinearMap
  isIntertwining' h := f.isIntertwining' (D.toActing h)

/-- The iterated localization of an ambient intertwiner, from the published induced maps. -/
def iteratedMap {ρ : Representation R G V} {σ : Representation R G X}
    (f : ρ.IntertwiningMap σ) : (D.iteratedAction ρ).IntertwiningMap (D.iteratedAction σ) :=
  D.actingMap (map D.innerSubgroup D.innerCharacter D.actingSubgroup
    D.acting_le_normalizer D.innerCharacter_invariant
    (map D.U D.θ D.M D.M_le_normalizer D.θ_invariant f))

@[simp]
theorem iteratedMap_iteratedMk {ρ : Representation R G V} {σ : Representation R G X}
    (f : ρ.IntertwiningMap σ) (v : V) :
    D.iteratedMap f (D.iteratedMk ρ v) = D.iteratedMk σ (f v) := rfl

/-- The direct induced map at `(U ⊔ W, Θ)`. -/
abbrev directMap {ρ : Representation R G V} {σ : Representation R G X}
    (f : ρ.IntertwiningMap σ) : (D.directAction ρ).IntertwiningMap (D.directAction σ) :=
  map (D.U ⊔ D.W) D.Θ D.H D.H_le_normalizer_sup D.Θ_invariant f

/-- Naturality for every ambient intertwiner. -/
theorem equiv_natural {ρ : Representation R G V} {σ : Representation R G X}
    (f : ρ.IntertwiningMap σ) :
    (D.directMap f).comp (D.equiv ρ).toIntertwiningMap =
      (D.equiv σ).toIntertwiningMap.comp (D.iteratedMap f) := by
  apply Representation.IntertwiningMap.ext
  exact hom_ext (hom_ext (LinearMap.ext fun _ => rfl))

/-! ## The smooth natural isomorphism -/

section Smooth

variable [TopologicalSpace G]

/-- The subgroup-copy transport `H → H.subgroupOf M` is continuous for the induced
topologies. -/
theorem continuous_toActing : Continuous D.toActing := by
  change Continuous fun h : D.H =>
    (⟨⟨(h : G), D.H_le_M h.2⟩, h.2⟩ : D.actingSubgroup)
  exact (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Restriction of smooth representations along the copy `H → H.subgroupOf M`. -/
def actingFunctor :
    SmoothRep.{uR, uG, uV} R D.actingSubgroup ⥤ SmoothRep.{uR, uG, uV} R D.H where
  obj A := SmoothRep.of (A.representation.comp D.toActing)
    (isSmooth_comp D.toActing D.continuous_toActing A.isSmooth)
  map f := SmoothRep.ofHom (D.actingMap (SmoothRep.hom f))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Localize at `(U, θ)`, then at the copy of `(W, η)`, then restrict to `H`. -/
def iteratedSmoothFunctor : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uR, uG, uV} R D.H :=
  smoothFunctor D.U D.θ D.M D.M_le_normalizer D.θ_invariant ⋙
    smoothFunctor D.innerSubgroup D.innerCharacter D.actingSubgroup
      D.acting_le_normalizer D.innerCharacter_invariant ⋙
    D.actingFunctor

/-- Localize directly at `(U ⊔ W, Θ)`, with the descended `H` action. -/
abbrev directSmoothFunctor : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uR, uG, uV} R D.H :=
  smoothFunctor (D.U ⊔ D.W) D.Θ D.H D.H_le_normalizer_sup D.Θ_invariant

/-- The natural isomorphism of smooth localization functors. -/
def smoothIso :
    (D.iteratedSmoothFunctor : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uR, uG, uV} R D.H) ≅
      D.directSmoothFunctor :=
  NatIso.ofComponents (fun A => SmoothRep.mkIso (D.equiv A.representation)) fun f => by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    exact (D.equiv_natural (SmoothRep.hom f)).symm

@[simp]
theorem smoothIso_hom_app_mk_mk (A : SmoothRep.{uR, uG, uV} R G) (v : A) :
    SmoothRep.hom (D.smoothIso.hom.app A)
        (mk (D.firstAction A.representation) D.innerSubgroup D.innerCharacter
          (mk A.representation D.U D.θ v)) =
      mk A.representation (D.U ⊔ D.W) D.Θ v := rfl

@[simp]
theorem smoothIso_inv_app_mk (A : SmoothRep.{uR, uG, uV} R G) (v : A) :
    SmoothRep.hom (D.smoothIso.inv.app A) (mk A.representation (D.U ⊔ D.W) D.Θ v) =
      mk (D.firstAction A.representation) D.innerSubgroup D.innerCharacter
        (mk A.representation D.U D.θ v) := rfl

end Smooth

/-! ## Supplied twists -/

section Twist

variable (α : D.M →* Rˣ) (hα : ∀ w : D.innerSubgroup, α w = 1) (β : D.H →* Rˣ)

/-- The character `α|_H * β` of `H`. -/
def restrictedProduct : D.H →* Rˣ := α.comp (Subgroup.inclusion D.H_le_M) * β

@[simp]
theorem restrictedProduct_apply (h : D.H) :
    (D.restrictedProduct α β h : R) = (α (Subgroup.inclusion D.H_le_M h) : R) * (β h : R) :=
  rfl

/-- The first quotient with its `M` action twisted by `α`. -/
abbrev twistedFirstAction (ρ : Representation R G V) :
    Representation R D.M (Coinvariants ρ D.U D.θ) :=
  twist α (D.firstAction ρ)

/-- The carrier of the twisted iterated localization. -/
abbrev TwistedIteratedCoinvariants (ρ : Representation R G V) :=
  Coinvariants (D.twistedFirstAction α ρ) D.innerSubgroup D.innerCharacter

/-- The twisted iterated class map `v ↦ [[v]]`. -/
def twistedIteratedMk (ρ : Representation R G V) : V →ₗ[R] D.TwistedIteratedCoinvariants α ρ :=
  mk (D.twistedFirstAction α ρ) D.innerSubgroup D.innerCharacter ∘ₗ mk ρ D.U D.θ

/-- Twist by `α` before the second quotient, restrict to `H`, then twist by `β`. -/
def twistedIteratedAction (ρ : Representation R G V) :
    Representation R D.H (D.TwistedIteratedCoinvariants α ρ) :=
  twist β ((action (D.twistedFirstAction α ρ) D.innerSubgroup D.innerCharacter
    D.actingSubgroup D.acting_le_normalizer D.innerCharacter_invariant).comp D.toActing)

theorem twistedIteratedAction_twistedIteratedMk (ρ : Representation R G V) (h : D.H)
    (v : V) :
    D.twistedIteratedAction α β ρ h (D.twistedIteratedMk α ρ v) =
      (β h : R) • (α (Subgroup.inclusion D.H_le_M h) : R) •
        D.twistedIteratedMk α ρ (ρ h v) := by
  change (β h : R) • mk (D.twistedFirstAction α ρ) D.innerSubgroup D.innerCharacter
      ((α (Subgroup.inclusion D.H_le_M h) : R) • mk ρ D.U D.θ (ρ h v)) = _
  rw [map_smul]
  rfl

/-- The twisted forward map `[[v]] ↦ [v]`. -/
def twistedForward (ρ : Representation R G V) :
    D.TwistedIteratedCoinvariants α ρ →ₗ[R] Coinvariants ρ (D.U ⊔ D.W) D.Θ :=
  lift (D.twistedFirstAction α ρ) D.innerSubgroup D.innerCharacter (D.firstToDirect ρ)
    fun w x => by
      obtain ⟨v, rfl⟩ := mk_surjective ρ D.U D.θ x
      change D.firstToDirect ρ ((α w : R) • mk ρ D.U D.θ (ρ ((w : D.M) : G) v)) = _
      rw [hα w, Units.val_one, one_smul]
      exact D.firstToDirect_inner ρ w v

include hα in
theorem twistedIteratedMk_covariant (ρ : Representation R G V) (x : ↥(D.U ⊔ D.W))
    (v : V) :
    D.twistedIteratedMk α ρ (ρ x v) = (D.Θ x : R) • D.twistedIteratedMk α ρ v := by
  refine covariant_sup ρ D.Θ (D.twistedIteratedMk α ρ) (fun u v => ?_) (fun w v => ?_) x v
  · rw [D.Θ_inclusion_left]
    change mk (D.twistedFirstAction α ρ) D.innerSubgroup D.innerCharacter
        (mk ρ D.U D.θ (ρ u v)) =
      (D.θ u : R) • mk (D.twistedFirstAction α ρ) D.innerSubgroup D.innerCharacter
        (mk ρ D.U D.θ v)
    rw [mk_apply_subgroup, map_smul]
  · rw [D.Θ_inclusion_right]
    have h := mk_apply_subgroup (D.twistedFirstAction α ρ) D.innerSubgroup D.innerCharacter
      ((Subgroup.subgroupOfEquivOfLe D.W_le_M).symm w) (mk ρ D.U D.θ v)
    change mk (D.twistedFirstAction α ρ) D.innerSubgroup D.innerCharacter
        ((α (((Subgroup.subgroupOfEquivOfLe D.W_le_M).symm w : D.innerSubgroup) : D.M) : R) •
          mk ρ D.U D.θ (ρ (w : G) v)) =
      (D.η w : R) • mk (D.twistedFirstAction α ρ) D.innerSubgroup D.innerCharacter
        (mk ρ D.U D.θ v) at h
    rw [hα, Units.val_one, one_smul] at h
    exact h

/-- The twisted backward map `[v] ↦ [[v]]`. -/
def twistedBackward (ρ : Representation R G V) :
    Coinvariants ρ (D.U ⊔ D.W) D.Θ →ₗ[R] D.TwistedIteratedCoinvariants α ρ :=
  lift ρ (D.U ⊔ D.W) D.Θ (D.twistedIteratedMk α ρ) (D.twistedIteratedMk_covariant α hα ρ)

/-- The twisted tower equivalence onto the direct localization twisted by a character
`γ` equal to `α|_H * β`. -/
def twistedEquivOfEq (γ : D.H →* Rˣ) (hγ : D.restrictedProduct α β = γ)
    (ρ : Representation R G V) :
    (D.twistedIteratedAction α β ρ).Equiv (twist γ (D.directAction ρ)) :=
  Representation.Equiv.mk
    (LinearEquiv.ofLinearMap (D.twistedForward α hα ρ) (D.twistedBackward α hα ρ)
      (hom_ext (LinearMap.ext fun _ => rfl))
      (hom_ext (hom_ext (LinearMap.ext fun _ => rfl))))
    (fun h => hom_ext (hom_ext (LinearMap.ext fun v => by
      subst hγ
      change D.twistedForward α hα ρ
          (D.twistedIteratedAction α β ρ h (D.twistedIteratedMk α ρ v)) =
        (D.restrictedProduct α β h : R) • mk ρ (D.U ⊔ D.W) D.Θ (ρ h v)
      rw [twistedIteratedAction_twistedIteratedMk, map_smul, map_smul,
        restrictedProduct_apply, smul_smul, mul_comm (β h : R)]
      rfl)))

/-- The twisted tower equivalence onto the direct localization twisted by `α|_H * β`. -/
abbrev twistedEquiv (ρ : Representation R G V) :
    (D.twistedIteratedAction α β ρ).Equiv
      (twist (D.restrictedProduct α β) (D.directAction ρ)) :=
  D.twistedEquivOfEq α hα β (D.restrictedProduct α β) rfl ρ

@[simp]
theorem twistedEquivOfEq_mk_mk (γ : D.H →* Rˣ) (hγ : D.restrictedProduct α β = γ)
    (ρ : Representation R G V) (v : V) :
    D.twistedEquivOfEq α hα β γ hγ ρ
        (mk (D.twistedFirstAction α ρ) D.innerSubgroup D.innerCharacter (mk ρ D.U D.θ v)) =
      mk ρ (D.U ⊔ D.W) D.Θ v := rfl

@[simp]
theorem twistedEquivOfEq_symm_mk (γ : D.H →* Rˣ) (hγ : D.restrictedProduct α β = γ)
    (ρ : Representation R G V) (v : V) :
    (D.twistedEquivOfEq α hα β γ hγ ρ).symm (mk ρ (D.U ⊔ D.W) D.Θ v) =
      mk (D.twistedFirstAction α ρ) D.innerSubgroup D.innerCharacter (mk ρ D.U D.θ v) := rfl

/-- The action on the single class is exactly `α(h) β(h) • [ρ(h) v]`. -/
theorem twist_directAction_mk (γ : D.H →* Rˣ) (hγ : D.restrictedProduct α β = γ)
    (ρ : Representation R G V) (h : D.H) (v : V) :
    twist γ (D.directAction ρ) h (mk ρ (D.U ⊔ D.W) D.Θ v) =
      ((α (Subgroup.inclusion D.H_le_M h) : R) * (β h : R)) •
        mk ρ (D.U ⊔ D.W) D.Θ (ρ h v) := by
  subst hγ
  rfl

/-- Equivariance of the twisted equivalence for every `h : H`. -/
theorem twistedEquivOfEq_equivariant (γ : D.H →* Rˣ) (hγ : D.restrictedProduct α β = γ)
    (ρ : Representation R G V) (h : D.H) (x : D.TwistedIteratedCoinvariants α ρ) :
    D.twistedEquivOfEq α hα β γ hγ ρ (D.twistedIteratedAction α β ρ h x) =
      twist γ (D.directAction ρ) h (D.twistedEquivOfEq α hα β γ hγ ρ x) :=
  (D.twistedEquivOfEq α hα β γ hγ ρ).toIntertwiningMap.isIntertwining _ _ h x

/-- The twisted iterated localization of an ambient intertwiner. -/
def twistedIteratedMap {ρ : Representation R G V} {σ : Representation R G X}
    (f : ρ.IntertwiningMap σ) :
    (D.twistedIteratedAction α β ρ).IntertwiningMap (D.twistedIteratedAction α β σ) :=
  twistIntertwining β (D.actingMap (map D.innerSubgroup D.innerCharacter D.actingSubgroup
    D.acting_le_normalizer D.innerCharacter_invariant
    (twistIntertwining α (map D.U D.θ D.M D.M_le_normalizer D.θ_invariant f))))

/-- Naturality of the twisted equivalence for every ambient intertwiner. -/
theorem twistedEquivOfEq_natural (γ : D.H →* Rˣ) (hγ : D.restrictedProduct α β = γ)
    {ρ : Representation R G V} {σ : Representation R G X} (f : ρ.IntertwiningMap σ) :
    (twistIntertwining γ (D.directMap f)).comp
        (D.twistedEquivOfEq α hα β γ hγ ρ).toIntertwiningMap =
      (D.twistedEquivOfEq α hα β γ hγ σ).toIntertwiningMap.comp
        (D.twistedIteratedMap α β f) := by
  apply Representation.IntertwiningMap.ext
  exact hom_ext (hom_ext (LinearMap.ext fun _ => rfl))

section Smooth

variable [TopologicalSpace G]

/-- Localize at `(U, θ)`, twist by `α`, localize at the copy of `(W, η)`, restrict to
`H` and twist by `β`. -/
def twistedIteratedSmoothFunctor (hαo : IsOpen (α.ker : Set D.M))
    (hβo : IsOpen (β.ker : Set D.H)) :
    SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uR, uG, uV} R D.H :=
  smoothFunctor D.U D.θ D.M D.M_le_normalizer D.θ_invariant ⋙
    SmoothRep.twistFunctor α hαo ⋙
    smoothFunctor D.innerSubgroup D.innerCharacter D.actingSubgroup
      D.acting_le_normalizer D.innerCharacter_invariant ⋙
    D.actingFunctor ⋙
    SmoothRep.twistFunctor β hβo

/-- The twisted smooth natural isomorphism, onto the direct localization twisted by a
character `γ` equal to `α|_H * β`. -/
def twistedSmoothIsoOfEq (hαo : IsOpen (α.ker : Set D.M)) (hβo : IsOpen (β.ker : Set D.H))
    (γ : D.H →* Rˣ) (hγ : D.restrictedProduct α β = γ) (hγo : IsOpen (γ.ker : Set D.H)) :
    (D.twistedIteratedSmoothFunctor α β hαo hβo :
        SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uR, uG, uV} R D.H) ≅
      D.directSmoothFunctor ⋙ SmoothRep.twistFunctor γ hγo :=
  NatIso.ofComponents
    (fun A => SmoothRep.mkIso (D.twistedEquivOfEq α hα β γ hγ A.representation)) fun f => by
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      exact (D.twistedEquivOfEq_natural α hα β γ hγ (SmoothRep.hom f)).symm

@[simp]
theorem twistedSmoothIsoOfEq_hom_app_mk_mk (hαo : IsOpen (α.ker : Set D.M))
    (hβo : IsOpen (β.ker : Set D.H)) (γ : D.H →* Rˣ) (hγ : D.restrictedProduct α β = γ)
    (hγo : IsOpen (γ.ker : Set D.H)) (A : SmoothRep.{uR, uG, uV} R G) (v : A) :
    SmoothRep.hom ((D.twistedSmoothIsoOfEq α hα β hαo hβo γ hγ hγo).hom.app A)
        (mk (D.twistedFirstAction α A.representation) D.innerSubgroup D.innerCharacter
          (mk A.representation D.U D.θ v)) =
      mk A.representation (D.U ⊔ D.W) D.Θ v := rfl

@[simp]
theorem twistedSmoothIsoOfEq_inv_app_mk (hαo : IsOpen (α.ker : Set D.M))
    (hβo : IsOpen (β.ker : Set D.H)) (γ : D.H →* Rˣ) (hγ : D.restrictedProduct α β = γ)
    (hγo : IsOpen (γ.ker : Set D.H)) (A : SmoothRep.{uR, uG, uV} R G) (v : A) :
    SmoothRep.hom ((D.twistedSmoothIsoOfEq α hα β hαo hβo γ hγ hγo).inv.app A)
        (mk A.representation (D.U ⊔ D.W) D.Θ v) =
      mk (D.twistedFirstAction α A.representation) D.innerSubgroup D.innerCharacter
        (mk A.representation D.U D.θ v) := rfl

/-- The twisted smooth natural isomorphism onto the direct localization twisted by
`α|_H * β`. -/
abbrev twistedSmoothIso (hαo : IsOpen (α.ker : Set D.M)) (hβo : IsOpen (β.ker : Set D.H))
    (hγo : IsOpen ((D.restrictedProduct α β).ker : Set D.H)) :
    (D.twistedIteratedSmoothFunctor α β hαo hβo :
        SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uR, uG, uV} R D.H) ≅
      D.directSmoothFunctor ⋙ SmoothRep.twistFunctor (D.restrictedProduct α β) hγo :=
  D.twistedSmoothIsoOfEq α hα β hαo hβo (D.restrictedProduct α β) rfl hγo

end Smooth

end Twist

/-! ## Open kernels -/

section OpenKernel

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The product of the restriction of an open-kernel character of `M` and an open-kernel
character of `H` has open kernel. -/
theorem isOpen_ker_restrict_mul {N : Type uN} [CommGroup N] (χ : D.M →* N) (ψ : D.H →* N)
    (hχ : IsOpen (χ.ker : Set D.M)) (hψ : IsOpen (ψ.ker : Set D.H)) :
    IsOpen ((χ.comp (Subgroup.inclusion D.H_le_M) * ψ).ker : Set D.H) := by
  have hcont : Continuous (Subgroup.inclusion D.H_le_M) :=
    continuous_subtype_val.subtype_mk _
  have h1 : IsOpen ((χ.comp (Subgroup.inclusion D.H_le_M)).ker : Set D.H) := by
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact hχ.preimage hcont
  apply Subgroup.isOpen_mono (H₁ := (χ.comp (Subgroup.inclusion D.H_le_M)).ker ⊓ ψ.ker)
  · intro h hh
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hh
    rw [MonoidHom.mem_ker, MonoidHom.mul_apply, hh.1, hh.2, mul_one]
  · exact h1.inter hψ

end OpenKernel

end General

/-! ## Supplied positive characters -/

section Positive

variable (D : TowerDatum ℂ G) (δ₁ : D.M →* ℝ≥0ˣ) (δ₂ : D.H →* ℝ≥0ˣ)

/-- The product of the two inverse-half twists on `H` is the inverse-half twist of the
product character. -/
theorem restrictedProduct_inverseHalfCharacter :
    D.restrictedProduct (inverseHalfCharacter δ₁) (inverseHalfCharacter δ₂) =
      inverseHalfCharacter (δ₁.comp (Subgroup.inclusion D.H_le_M) * δ₂) := by
  refine MonoidHom.ext fun h => Units.ext ?_
  simp [restrictedProduct, inverseHalfCharacter_apply, mul_comm]

/-- `inverseHalfCharacter δ₁` is trivial on the copy of `W` when `δ₁` is. -/
theorem inverseHalfCharacter_inner (hδ₁ : ∀ w : D.innerSubgroup, δ₁ w = 1)
    (w : D.innerSubgroup) : inverseHalfCharacter δ₁ w = 1 :=
  (inverseHalfCharacter_eq_one δ₁ w).2 (hδ₁ w)

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The normalized tower isomorphism for supplied positive characters `δ₁` of `M`
(trivial on the copy of `W`) and `δ₂` of `H`, both with open kernels. -/
def normalizedSmoothIso (hδ₁ : ∀ w : D.innerSubgroup, δ₁ w = 1)
    (hδ₁o : IsOpen (δ₁.ker : Set D.M)) (hδ₂o : IsOpen (δ₂.ker : Set D.H)) :
    (D.twistedIteratedSmoothFunctor (inverseHalfCharacter δ₁)
        (inverseHalfCharacter δ₂) (isOpen_ker_inverseHalfCharacter δ₁ hδ₁o)
        (isOpen_ker_inverseHalfCharacter δ₂ hδ₂o) :
        SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uG, uV} ℂ D.H) ≅
      D.directSmoothFunctor ⋙ SmoothRep.twistFunctor
        (inverseHalfCharacter (δ₁.comp (Subgroup.inclusion D.H_le_M) * δ₂))
        (isOpen_ker_inverseHalfCharacter _ (D.isOpen_ker_restrict_mul δ₁ δ₂ hδ₁o hδ₂o)) :=
  D.twistedSmoothIsoOfEq (inverseHalfCharacter δ₁) (D.inverseHalfCharacter_inner δ₁ hδ₁)
    (inverseHalfCharacter δ₂) _ _ _ (D.restrictedProduct_inverseHalfCharacter δ₁ δ₂) _

end Positive

end TowerDatum

end Langlands.Jacquet.Localization
