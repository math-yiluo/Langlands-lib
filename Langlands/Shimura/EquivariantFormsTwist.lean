import Langlands.Shimura.EquivariantFormsHecke

/-!
# Twisted equivariant functions and functions on double-quotient level spaces

For a representation `ρ` of the whole group `G`, the forms `forms ι K (ρ|K)` of
`Langlands.Shimura.EquivariantForms` (functions with `f (ι γ * g) = f g` and
`f (g * k) = ρ k⁻¹ (f g)`) are compared with the twisted forms: functions with
`f (ι γ * g) = ρ (ι γ) (f g)` and `f (g * k) = f g`. These are generic algebraic forms of the
functional equations of Harris's spaces `𝒜_ℓ(GJ, ρ, K)` and `𝒜_f(GJ, ρ, K)` (Harris,
*Galois properties of cohomological automorphic forms on GL(n)*, 1999, (3.3) and (3.2)).
For trivial coefficients, forms are identified with functions on the double-quotient level
spaces `Langlands.Shimura.LevelSpace` with a one-point `X`.

## Main definitions

* `twistedForms ι K ρ`: the module of twisted forms.
* `twistEquiv ι K ρ`: `F ↦ (g ↦ ρ g (F g))`, a linear equivalence from `forms ι K (ρ|K)` to
  `twistedForms ι K ρ`.
* `twistedTranslate ι ρ g hg`: right translation `f ↦ (x ↦ f (x * g))` of twisted forms from
  level `L` to level `K` when `g⁻¹ K g ⊆ L`; `twistedLevelPresheaf R ι ρ` on compact open
  levels, and `levelPresheafTwistIso`, identifying it with `levelPresheaf R ι ρ`.
* `levelSpaceFunctions R ι X V`: the functions on `Γ \ (X × G) / K` with values in `V`, as a
  presheaf on compact open levels by pullback along `LevelSpace.translate`.
* `levelSpaceEquiv ι K ρ`, for a trivial representation `ρ`: forms are the functions on the
  level space `Γ \ (Unit × G) / K`; `levelPresheafTrivialIso` makes this natural in the level.
-/

noncomputable section

namespace Langlands.Shimura.EquivariantForms

open CategoryTheory

universe t uR uΓ uG uX

variable {R : Type uR} [CommRing R] {Γ : Type uΓ} {G : Type uG} [Group Γ] [Group G]

section Twist

variable (ι : Γ →* G) (K : Subgroup G) {V : Type t} [AddCommGroup V] [Module R V]
  (ρ : Representation R G V)

/-- The `R`-module of functions `f : G → V` with `f (ι γ * g) = ρ (ι γ) (f g)` for `γ : Γ` and
`f (g * k) = f g` for `k : K`: the functional equations of Harris's `𝒜_f(GJ, ρ, K)`
(1999, (3.2)) for an arbitrary group, level and representation. -/
def twistedForms : Submodule R (G → V) where
  carrier := {f | (∀ (γ : Γ) (g : G), f (ι γ * g) = ρ (ι γ) (f g)) ∧
    ∀ (g : G) (k : K), f (g * k) = f g}
  add_mem' {f₁ f₂} hf₁ hf₂ := ⟨fun γ g => by simp [hf₁.1 γ g, hf₂.1 γ g],
    fun g k => by simp [hf₁.2 g k, hf₂.2 g k]⟩
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ => rfl⟩
  smul_mem' r f hf := ⟨fun γ g => by simp [hf.1 γ g], fun g k => by simp [hf.2 g k]⟩

variable {ι K ρ} in
lemma mem_twistedForms {f : G → V} :
    f ∈ twistedForms ι K ρ ↔ (∀ (γ : Γ) (g : G), f (ι γ * g) = ρ (ι γ) (f g)) ∧
      ∀ (g : G) (k : K), f (g * k) = f g :=
  Iff.rfl

/-- The twist `F ↦ (g ↦ ρ g (F g))` from forms for the restriction of `ρ` to `K` to twisted
forms, with inverse `f ↦ (g ↦ ρ g⁻¹ (f g))`. -/
def twistEquiv : forms ι K (ρ.comp K.subtype) ≃ₗ[R] twistedForms ι K ρ where
  toFun F := ⟨fun g => ρ g (F.1 g), fun γ g => by
      change ρ (ι γ * g) (F.1 (ι γ * g)) = ρ (ι γ) (ρ g (F.1 g))
      rw [F.2.1 γ g, map_mul, Module.End.mul_apply], fun g k => by
      change ρ (g * k) (F.1 (g * k)) = ρ g (F.1 g)
      rw [F.2.2 g k]
      change ρ (g * k) (ρ ((k⁻¹ : K) : G) (F.1 g)) = ρ g (F.1 g)
      rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, mul_inv_cancel_right]⟩
  invFun f := ⟨fun g => ρ g⁻¹ (f.1 g), fun γ g => by
      change ρ (ι γ * g)⁻¹ (f.1 (ι γ * g)) = ρ g⁻¹ (f.1 g)
      rw [f.2.1 γ g, ← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right],
      fun g k => by
      change ρ (g * k)⁻¹ (f.1 (g * k)) = ρ ((k⁻¹ : K) : G) (ρ g⁻¹ (f.1 g))
      rw [f.2.2 g k, ← Module.End.mul_apply, ← map_mul, mul_inv_rev, Subgroup.coe_inv]⟩
  map_add' F₁ F₂ := by
    ext g
    simp
  map_smul' r F := by
    ext g
    simp
  left_inv F := by
    ext g
    change ρ g⁻¹ (ρ g (F.1 g)) = F.1 g
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  right_inv f := by
    ext g
    change ρ g (ρ g⁻¹ (f.1 g)) = f.1 g
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

@[simp]
lemma twistEquiv_apply_coe (F : forms ι K (ρ.comp K.subtype)) (g : G) :
    (twistEquiv ι K ρ F).1 g = ρ g (F.1 g) :=
  rfl

@[simp]
lemma twistEquiv_symm_apply_coe (f : twistedForms ι K ρ) (g : G) :
    ((twistEquiv ι K ρ).symm f).1 g = ρ g⁻¹ (f.1 g) :=
  rfl

end Twist

section TwistedTranslate

variable (ι : Γ →* G) {K L : Subgroup G} {V : Type t} [AddCommGroup V] [Module R V]
  (ρ : Representation R G V)

/-- Right translation `f ↦ (x ↦ f (x * g))` of twisted forms from level `L` to level `K`, for
`g : G` with `g⁻¹ * k * g ∈ L` for all `k ∈ K`. -/
def twistedTranslate (g : G) (hg : ∀ k ∈ K, g⁻¹ * k * g ∈ L) :
    twistedForms ι L ρ →ₗ[R] twistedForms ι K ρ :=
  (LinearMap.funLeft R V (· * g)).restrict fun f hf =>
    ⟨fun γ x => by simp [mul_assoc, hf.1 γ (x * g)], fun x k => by
      have hx : x * k * g = x * g * ((⟨g⁻¹ * k * g, hg k k.2⟩ : L) : G) := by
        simp [mul_assoc]
      change f (x * k * g) = f (x * g)
      rw [hx, hf.2]⟩

@[simp]
lemma twistedTranslate_apply_coe (g : G) (hg : ∀ k ∈ K, g⁻¹ * k * g ∈ L)
    (f : twistedForms ι L ρ) (x : G) :
    (twistedTranslate ι ρ g hg f).1 x = f.1 (x * g) :=
  rfl

end TwistedTranslate

section TwistedLevelPresheaf

variable [TopologicalSpace G] (R) (ι : Γ →* G) {V : Type t} [AddCommGroup V] [Module R V]
  (ρ : Representation R G V)

/-- Under the twist, `levelTransport` along a level arrow `a` (with intertwiner
`ρ a.element`) becomes right translation by `a.element`. -/
lemma twistEquiv_levelTransport {K L : CompactOpenLevel G} (a : K ⟶ L)
    (F : forms ι L.subgroup (ρ.comp L.subgroup.subtype)) :
    twistEquiv ι K.subgroup ρ (levelTransport R ι ρ a F) =
      twistedTranslate ι ρ a.element a.respects (twistEquiv ι L.subgroup ρ F) := by
  ext x
  simp [map_mul, Module.End.mul_apply]

/-- The twisted forms of all compact open levels, as a presheaf on the category of levels with
right translation `twistedTranslate` on arrows. -/
def twistedLevelPresheaf : (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat.{max uG t} R where
  obj K := ModuleCat.of R (twistedForms ι K.unop.subgroup ρ)
  map a := ModuleCat.ofHom (twistedTranslate ι ρ a.unop.element a.unop.respects)
  map_id K := by
    ext f x
    simp
  map_comp a b := by
    ext f x
    simp [mul_assoc]

@[simp]
lemma twistedLevelPresheaf_map_apply_coe {K L : (CompactOpenLevel G)ᵒᵖ} (a : K ⟶ L)
    (f : (twistedLevelPresheaf R ι ρ).obj K) (x : G) :
    (((twistedLevelPresheaf R ι ρ).map a).hom f).1 x = f.1 (x * a.unop.element) :=
  rfl

/-- The presheaf of forms is isomorphic to the presheaf of twisted forms, with components
`twistEquiv`. -/
def levelPresheafTwistIso : levelPresheaf R ι ρ ≅ twistedLevelPresheaf R ι ρ :=
  NatIso.ofComponents (fun K => (twistEquiv ι K.unop.subgroup ρ).toModuleIso) fun a => by
    ext F : 2
    exact twistEquiv_levelTransport R ι ρ a.unop F

end TwistedLevelPresheaf

section TwistedHecke

variable [TopologicalSpace G] [IsTopologicalGroup G] (R) (ι : Γ →* G) {V : Type t}
  [AddCommGroup V] [Module R V] (ρ : Representation R G V)

/-- Under the twist, the Hecke operator `[K g L]` has the untwisted formula
`x ↦ ∑ f (x * k * g)`, summed over representatives `k` of `K ⧸ (K ∩ g L g⁻¹)`. -/
lemma twistEquiv_heckeOperator (K L : CompactOpenLevel G) (g : G)
    [Fintype (K.subgroup ⧸ (CompactOpenLevel.heckeLevel K L g).subgroup.subgroupOf K.subgroup)]
    (F : forms ι L.subgroup (ρ.comp L.subgroup.subtype)) (x : G) :
    (twistEquiv ι K.subgroup ρ (heckeOperator R ι ρ K L g F)).1 x =
      ∑ q : K.subgroup ⧸ (CompactOpenLevel.heckeLevel K L g).subgroup.subgroupOf K.subgroup,
        (twistEquiv ι L.subgroup ρ F).1 (x * q.out * g) := by
  rw [twistEquiv_apply_coe, heckeOperator_apply_coe, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [twistEquiv_apply_coe, ← Module.End.mul_apply, ← map_mul, mul_assoc x]

end TwistedHecke

section LevelSpaceFunctions

variable (R) (ι : Γ →* G) (X : Type uX) [MulAction Γ X] (V : Type t) [AddCommGroup V]
  [Module R V]

/-- The `V`-valued functions on the double-quotient level spaces `Γ \ (X × G) / K` of compact
open levels `K`, as a presheaf on the category of levels by pullback along
`LevelSpace.translate`. -/
def levelSpaceFunctions [TopologicalSpace G] :
    (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat.{max uG uX t} R where
  obj K := ModuleCat.of R (LevelSpace (X := X) ι K.unop.subgroup → V)
  map a := ModuleCat.ofHom
    (LinearMap.funLeft R V (LevelSpace.translate a.unop.element a.unop.respects))
  map_id K := by
    ext φ q
    exact congrArg φ (LevelSpace.translate_one K.unop.subgroup q)
  map_comp a b := by
    ext φ q
    exact congrArg φ (LevelSpace.translate_comp b.unop.element a.unop.element
      b.unop.respects a.unop.respects q).symm

@[simp]
lemma levelSpaceFunctions_map_apply [TopologicalSpace G] {K L : (CompactOpenLevel G)ᵒᵖ}
    (a : K ⟶ L) (φ : (levelSpaceFunctions R ι X V).obj K) (q : LevelSpace (X := X) ι L.unop.subgroup) :
    ((levelSpaceFunctions R ι X V).map a).hom φ q =
      φ (LevelSpace.translate a.unop.element a.unop.respects q) :=
  rfl

/-- The maps of `levelSpaceFunctions` are pullback along the maps of the tower of level spaces
`LevelSpace.tower`. -/
lemma levelSpaceFunctions_map_apply_tower [TopologicalSpace G] [ContinuousMul G]
    [TopologicalSpace X] {K L : (CompactOpenLevel G)ᵒᵖ} (a : K ⟶ L)
    (φ : (levelSpaceFunctions R ι X V).obj K) (q : LevelSpace (X := X) ι L.unop.subgroup) :
    ((levelSpaceFunctions R ι X V).map a).hom φ q =
      φ ((LevelSpace.tower (X := X) (ι := ι)).map a.unop q) :=
  rfl

end LevelSpaceFunctions

section LevelSpace

/-- The restriction of a trivial representation is trivial. -/
instance {H : Type*} [Group H] {V : Type*} [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) [ρ.IsTrivial] (f : H →* G) : Representation.IsTrivial (ρ.comp f) where
  out h := Representation.isTrivial_def ρ (f h)

variable (ι : Γ →* G) (K : Subgroup G) {V : Type t} [AddCommGroup V] [Module R V]
  (ρ : Representation R K V) [ρ.IsTrivial]

/-- For a trivial representation `ρ`, a form is constant on the double cosets `ι Γ * g * K`,
so it is a function on the level space `Γ \ (Unit × G) / K`; the inverse evaluates a function
at the classes of the points `((), g)`. -/
def levelSpaceEquiv : forms ι K ρ ≃ₗ[R] (LevelSpace (X := Unit) ι K → V) where
  toFun f q := Quotient.liftOn q (fun x => f.1 x.2) fun x y ⟨γ, k, hk, _, hy⟩ => by
    rw [hy, f.2.2 _ ⟨k, hk⟩, f.2.1, Representation.isTrivial_def, LinearMap.id_apply]
  invFun φ := ⟨fun g => φ (LevelSpace.mk K ((), g)), fun γ g =>
      congrArg φ ((LevelSpace.mk_eq_mk K ((), g) ((), ι γ * g)).2
        ⟨γ, 1, K.one_mem, rfl, by simp⟩).symm, fun g k => by
      rw [Representation.isTrivial_def, LinearMap.id_apply]
      exact congrArg φ ((LevelSpace.mk_eq_mk K ((), g) ((), g * k)).2
        ⟨1, k, k.2, rfl, by simp⟩).symm⟩
  map_add' f₁ f₂ := by
    funext q
    induction q using Quotient.inductionOn with
    | h x => rfl
  map_smul' r f := by
    funext q
    induction q using Quotient.inductionOn with
    | h x => rfl
  left_inv f := rfl
  right_inv φ := by
    funext q
    induction q using Quotient.inductionOn with
    | h x => rfl

@[simp]
lemma levelSpaceEquiv_mk (f : forms ι K ρ) (g : G) :
    levelSpaceEquiv ι K ρ f (LevelSpace.mk K ((), g)) = f.1 g :=
  rfl

@[simp]
lemma levelSpaceEquiv_symm_apply_coe (φ : LevelSpace (X := Unit) ι K → V) (g : G) :
    ((levelSpaceEquiv ι K ρ).symm φ).1 g = φ (LevelSpace.mk K ((), g)) :=
  rfl

end LevelSpace

section LevelSpacePresheaf

variable [TopologicalSpace G] (R) (ι : Γ →* G) {V : Type t} [AddCommGroup V] [Module R V]
  (ρ : Representation R G V) [ρ.IsTrivial]

/-- For a trivial representation `ρ` of `G`, `levelTransport` along a level arrow `a` is
pullback of functions on level spaces along `LevelSpace.translate`. -/
lemma levelSpaceEquiv_levelTransport {K L : CompactOpenLevel G} (a : K ⟶ L)
    (F : forms ι L.subgroup (ρ.comp L.subgroup.subtype)) :
    levelSpaceEquiv ι K.subgroup _ (levelTransport R ι ρ a F) =
      levelSpaceEquiv ι L.subgroup _ F ∘ LevelSpace.translate a.element a.respects := by
  funext q
  induction q using Quotient.inductionOn with
  | h x =>
    change ρ a.element (F.1 (x.2 * a.element)) = F.1 (x.2 * a.element)
    rw [Representation.isTrivial_def, LinearMap.id_apply]

/-- For a trivial representation `ρ` of `G`, the presheaf of forms is isomorphic to the
presheaf of `V`-valued functions on the level spaces `Γ \ (Unit × G) / K`, with components
`levelSpaceEquiv`. -/
def levelPresheafTrivialIso : levelPresheaf R ι ρ ≅ levelSpaceFunctions R ι Unit V :=
  NatIso.ofComponents (fun K => (levelSpaceEquiv ι K.unop.subgroup _).toModuleIso) fun a => by
    ext F : 2
    exact levelSpaceEquiv_levelTransport R ι ρ a.unop F

end LevelSpacePresheaf

end Langlands.Shimura.EquivariantForms
