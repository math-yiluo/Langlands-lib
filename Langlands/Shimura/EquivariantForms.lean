import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Invariants
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Langlands.Representation.Category.SmoothPartAdjunction

/-!
# Equivariant functions on double cosets

Let `ι : Γ →* G` be a group homomorphism, `K` a subgroup of `G` and `ρ` an `R`-linear
representation of `K` on `V`. This file studies the `R`-module `forms ι K ρ` of functions
`f : G → V` with `f (ι γ * g) = f g` and `f (g * k) = ρ k⁻¹ (f g)` for `γ : Γ`, `g : G`,
`k : K`. It is a generic algebraic form of the functional equations defining Harris's spaces
of `ℓ`-adic automorphic forms on a totally definite group (Harris, *Galois properties of
cohomological automorphic forms on GL(n)*, 1999, (3.3) and (3.7)); no group, level or
coefficient system of Harris is specialized here.

## Main definitions

* `forms ι K ρ`: the module of such functions.
* `formsEquivInvariants ι K ρ`: `f ↦ (h ↦ f h⁻¹)` identifies `forms ι K ρ` with the
  `Γ`-invariants of Mathlib's coinduced representation `Representation.coind K.subtype ρ`
  restricted along `ι`.
* `formsFunctor R ι K : Rep R K ⥤ ModuleCat R`, naturally isomorphic (`formsFunctorIso`) to
  coinduction, restriction along `ι` and invariants; it preserves limits.
* `rightTranslation ι K ρ ψ hψ`: right translation by a group `H` mapping to `G` by `ψ` with
  image commuting with `K`; `formsRepFunctor` and, for topological `H`, the smooth vectors
  `smoothFormsFunctor`.
* `levelAction ι ρ hle`: for `K' ≤ K` with `K'` normal in `K`, the action
  `(k • f) g = ρ k (f (g * k))` of `K` on forms of level `K'`; it is trivial on `K'`, descends
  to `K ⧸ K'` (`levelQuotientAction`), and its invariants are the forms of level `K`
  (`levelInvariantsEquiv`).
-/

noncomputable section

namespace Langlands.Shimura.EquivariantForms

open CategoryTheory CategoryTheory.Limits

universe t uR uΓ uG uH

variable {R : Type uR} [CommRing R] {Γ : Type uΓ} {G : Type uG} [Group Γ] [Group G]

section Forms

variable (ι : Γ →* G) (K : Subgroup G) {V : Type t} [AddCommGroup V] [Module R V]
  (ρ : Representation R K V)

/-- The `R`-module of functions `f : G → V` that are invariant under left translation by
`ι Γ` and satisfy `f (g * k) = ρ k⁻¹ (f g)` for `k : K`: the functional equations of
Harris's `𝒜_ℓ(GJ, 𝓛, K)` (1999, (3.3) and (3.7)) for an arbitrary group, level and
representation. -/
def forms : Submodule R (G → V) where
  carrier := {f | (∀ (γ : Γ) (g : G), f (ι γ * g) = f g) ∧
    ∀ (g : G) (k : K), f (g * k) = ρ k⁻¹ (f g)}
  add_mem' {f₁ f₂} hf₁ hf₂ := ⟨fun γ g => by simp [hf₁.1 γ g, hf₂.1 γ g],
    fun g k => by simp [hf₁.2 g k, hf₂.2 g k]⟩
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => by simp⟩
  smul_mem' r f hf := ⟨fun γ g => by simp [hf.1 γ g], fun g k => by simp [hf.2 g k]⟩

variable {ι K ρ} in
lemma mem_forms {f : G → V} :
    f ∈ forms ι K ρ ↔ (∀ (γ : Γ) (g : G), f (ι γ * g) = f g) ∧
      ∀ (g : G) (k : K), f (g * k) = ρ k⁻¹ (f g) :=
  Iff.rfl

/-- Forms are the `Γ`-invariants of the coinduction of `ρ` from `K` to `G`, restricted to `Γ`
along `ι`. Mathlib's `coind` consists of functions `f'` with `f' (k * h) = ρ k (f' h)` and has
`G` acting by right translation; the equivalence sends `f` to `h ↦ f h⁻¹`. -/
def formsEquivInvariants :
    forms ι K ρ ≃ₗ[R] Representation.invariants ((Representation.coind K.subtype ρ).comp ι) where
  toFun f := ⟨⟨fun h => f.1 h⁻¹, fun k h => by
      have := f.2.2 h⁻¹ k⁻¹
      simp only [inv_inv, Subgroup.coe_inv] at this
      simpa [mul_inv_rev] using this⟩, fun γ => by
      ext h
      change f.1 (h * ι γ)⁻¹ = f.1 h⁻¹
      rw [mul_inv_rev, ← map_inv]
      exact f.2.1 γ⁻¹ h⁻¹⟩
  invFun x := ⟨fun g => x.1.1 g⁻¹, fun γ g => by
      have := congrArg (fun y => y.1 g⁻¹) (x.2 γ⁻¹)
      change x.1.1 (g⁻¹ * ι γ⁻¹) = x.1.1 g⁻¹ at this
      change x.1.1 (ι γ * g)⁻¹ = x.1.1 g⁻¹
      rw [mul_inv_rev, ← map_inv]
      exact this, fun g k => by
      have := x.1.2 k⁻¹ g⁻¹
      simpa [mul_inv_rev] using this⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by ext g; simp
  right_inv x := by ext g; simp

end Forms

section Functor

variable (R) (ι : Γ →* G) (K : Subgroup G)

variable {ι K} in
/-- Postcomposition with an intertwining map `φ` sends forms for `ρ` to forms for `σ`. -/
def formsMap {V W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    {ρ : Representation R K V} {σ : Representation R K W} (φ : ρ.IntertwiningMap σ) :
    forms ι K ρ →ₗ[R] forms ι K σ :=
  (φ.toLinearMap.compLeft G).restrict fun f hf =>
    ⟨fun γ g => by simp [hf.1 γ g], fun g k => by simp [hf.2 g k, φ.isIntertwining]⟩

variable {ι K} in
@[simp]
lemma formsMap_apply_coe {V W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W]
    [Module R W] {ρ : Representation R K V} {σ : Representation R K W}
    (φ : ρ.IntertwiningMap σ) (f : forms ι K ρ) (g : G) :
    (formsMap R φ f).1 g = φ (f.1 g) :=
  rfl

/-- Forms as a functor from representations of `K` to `R`-modules, acting on morphisms by
postcomposition. -/
def formsFunctor : Rep.{t} R K ⥤ ModuleCat.{max uG t} R where
  obj A := ModuleCat.of R (forms ι K A.ρ)
  map f := ModuleCat.ofHom (formsMap R f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor of forms is naturally isomorphic to coinduction from `K` to `G`, restriction
along `ι` and `Γ`-invariants, with components `formsEquivInvariants`. -/
def formsFunctorIso :
    formsFunctor.{t} R ι K ≅
      Rep.coindFunctor R K.subtype ⋙ Rep.resFunctor ι ⋙ Rep.invariantsFunctor R Γ :=
  NatIso.ofComponents (fun A => (formsEquivInvariants ι K A.ρ).toModuleIso) fun _ => rfl

/-- The functor of forms preserves limits, being isomorphic to a composite of right adjoints
and limit-preserving functors. The carrier universe of the representations is `max uG t`, so
that source and target carriers lie in one universe. -/
instance : PreservesLimits (formsFunctor.{max uG t} R ι K) :=
  preservesLimits_of_natIso (formsFunctorIso.{max uG t} R ι K).symm

end Functor

section Translation

variable (ι : Γ →* G) (K : Subgroup G) {V : Type t} [AddCommGroup V] [Module R V]
  (ρ : Representation R K V) {H : Type uH} [Group H] (ψ : H →* G)
  (hψ : ∀ (h : H) (k : K), ψ h * k = k * ψ h)

/-- Right translation `(h • f) g = f (g * ψ h)` by a group `H` whose image under `ψ` commutes
elementwise with `K`. -/
def rightTranslation : Representation R H (forms ι K ρ) where
  toFun h := (LinearMap.funLeft R V (· * ψ h)).restrict fun f hf =>
    ⟨fun γ g => by simp [mul_assoc, hf.1 γ (g * ψ h)], fun g k => by
      simp only [LinearMap.funLeft_apply]
      rw [mul_assoc, ← hψ h k, ← mul_assoc]
      exact hf.2 (g * ψ h) k⟩
  map_one' := by ext; simp
  map_mul' a b := by
    ext f g
    change f.1 (g * ψ (a * b)) = f.1 (g * ψ a * ψ b)
    rw [map_mul, mul_assoc]

@[simp]
lemma rightTranslation_apply_coe (h : H) (f : forms ι K ρ) (g : G) :
    (rightTranslation ι K ρ ψ hψ h f).1 g = f.1 (g * ψ h) :=
  rfl

variable (R) in
/-- Forms with right translation, as a functor to representations of `H`. -/
def formsRepFunctor : Rep.{t} R K ⥤ Rep.{max uG t} R H where
  obj A := Rep.of (rightTranslation ι K A.ρ ψ hψ)
  map f := Rep.ofHom ⟨formsMap R f.hom, fun _ => rfl⟩
  map_id _ := rfl
  map_comp _ _ := rfl

variable (R) in
/-- For a topological group `H`, the smooth vectors (those fixed by an open subgroup) of forms
under right translation, as a functor to smooth representations of `H`. -/
abbrev smoothFormsFunctor [TopologicalSpace H] [IsTopologicalGroup H] :
    Rep.{t} R K ⥤ SmoothRep.{uR, uH, max uG t} R H :=
  formsRepFunctor R ι K ψ hψ ⋙ SmoothRep.smoothPartFunctor.{uR, uH, max uG t} R H

end Translation

section LevelChange

variable (ι : Γ →* G) {K K' : Subgroup G} {V : Type t} [AddCommGroup V] [Module R V]
  (ρ : Representation R K V) (hle : K' ≤ K) [(K'.subgroupOf K).Normal]

/-- For `K' ≤ K` with `K'` normal in `K`, the action `(k • f) g = ρ k (f (g * k))` of `K` on
the forms of level `K'` for the restriction of `ρ`. -/
def levelAction : Representation R K (forms ι K' (ρ.comp (Subgroup.inclusion hle))) where
  toFun k := ((ρ k).compLeft G ∘ₗ LinearMap.funLeft R V (· * k)).restrict fun f hf =>
    ⟨fun γ g => by simp [mul_assoc, hf.1 γ (g * k)], fun g k' => by
      have hm : k⁻¹ * Subgroup.inclusion hle k' * k ∈ K'.subgroupOf K := by
        simpa using (inferInstance : (K'.subgroupOf K).Normal).conj_mem _
          (by simp [Subgroup.mem_subgroupOf]) k⁻¹
      let m : K' := ⟨(k : G)⁻¹ * k' * k, by simpa [Subgroup.mem_subgroupOf] using hm⟩
      have hg : g * k' * k = g * k * m := by simp [m, mul_assoc]
      change ρ k (f (g * k' * k)) = ρ (Subgroup.inclusion hle k'⁻¹) (ρ k (f (g * k)))
      rw [hg, hf.2 (g * k) m]
      change ρ k (ρ (Subgroup.inclusion hle m⁻¹) _) = _
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      ext
      simp [m, mul_assoc]⟩
  map_one' := by ext; simp
  map_mul' a b := by
    ext f g
    change ρ (a * b) (f.1 (g * ↑(a * b))) = ρ a (ρ b (f.1 (g * ↑a * ↑b)))
    rw [map_mul, Subgroup.coe_mul, mul_assoc]
    rfl

@[simp]
lemma levelAction_apply_coe (k : K) (f : forms ι K' (ρ.comp (Subgroup.inclusion hle)))
    (g : G) : (levelAction ι ρ hle k f).1 g = ρ k (f.1 (g * k)) :=
  rfl

/-- The level action is trivial on `K'`. -/
instance : Representation.IsTrivial
    ((levelAction ι ρ hle).comp (K'.subgroupOf K).subtype) where
  out k := by
    ext f g
    have hk : (k : K).1 ∈ K' := Subgroup.mem_subgroupOf.1 k.2
    change ρ k (f.1 (g * (k : K))) = f.1 g
    rw [show g * ((k : K) : G) = g * ((⟨_, hk⟩ : K') : G) from rfl, f.2.2 g ⟨_, hk⟩]
    change ρ k (ρ (Subgroup.inclusion hle ⟨_, hk⟩⁻¹) _) = _
    rw [← Module.End.mul_apply, ← map_mul]
    rw [show (k : K) * Subgroup.inclusion hle ⟨_, hk⟩⁻¹ = 1 by ext; simp]
    simp

/-- The level action descends to the quotient `K ⧸ K'`. -/
def levelQuotientAction :
    Representation R (K ⧸ K'.subgroupOf K) (forms ι K' (ρ.comp (Subgroup.inclusion hle))) :=
  (levelAction ι ρ hle).ofQuotient (K'.subgroupOf K)

/-- The invariants of the level action are the forms of level `K`; the underlying function is
unchanged in both directions. -/
def levelInvariantsEquiv : (levelAction ι ρ hle).invariants ≃ₗ[R] forms ι K ρ where
  toFun F := ⟨F.1.1, F.1.2.1, fun g k => by
      have := congrArg (fun f => ρ k⁻¹ (f.1 g)) (F.2 k)
      simpa [← Module.End.mul_apply, ← map_mul] using this⟩
  invFun f := ⟨⟨f.1, f.2.1, fun g k' => f.2.2 g (Subgroup.inclusion hle k')⟩, fun k => by
      ext g
      change ρ k (f.1 (g * k)) = f.1 g
      rw [f.2.2 g k, ← Module.End.mul_apply, ← map_mul]
      simp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

end LevelChange

end Langlands.Shimura.EquivariantForms
