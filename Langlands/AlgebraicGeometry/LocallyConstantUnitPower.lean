import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Gluing locally constant families of global sections of a scheme -/

noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.LocallyConstantUnitPower

variable {X Y : Scheme.{u}}

/-- Two global sections with the same germs at every point are equal. -/
lemma ext_germ {s t : Γ(X, ⊤)}
    (h : ∀ x : X, X.presheaf.germ ⊤ x trivial s = X.presheaf.germ ⊤ x trivial t) : s = t :=
  TopCat.Presheaf.section_ext X.sheaf ⊤ s t (fun x _ => h x)

/-- A locally constant family of global sections has a global section with the prescribed
germ at every point. -/
lemma exists_germ_eq (g : LocallyConstant X Γ(X, ⊤)) :
    ∃ s : Γ(X, ⊤), ∀ x : X,
      X.presheaf.germ ⊤ x trivial s = X.presheaf.germ ⊤ x trivial (g x) := by
  let U : Γ(X, ⊤) → X.Opens := fun r => ⟨g ⁻¹' {r}, g.isLocallyConstant.isOpen_fiber r⟩
  let sf : ∀ r, Γ(X, U r) := fun r => X.presheaf.map (homOfLE le_top).op r
  obtain ⟨s, hs, -⟩ : ∃! s : Γ(X, ⊤), ∀ r, X.presheaf.map (homOfLE le_top).op s = sf r :=
    X.sheaf.existsUnique_gluing' U ⊤ (fun r => homOfLE le_top)
    (fun x _ => Opens.mem_iSup.2 ⟨g x, rfl⟩) sf (by
      intro r r'
      apply TopCat.Presheaf.section_ext X.sheaf
      intro x hx
      have hr : g x = r := hx.1
      have hr' : g x = r' := hx.2
      subst hr hr'
      rfl)
  refine ⟨s, fun x => ?_⟩
  have hx : x ∈ U (g x) := Set.mem_preimage.2 (Set.mem_singleton (g x))
  have h : X.presheaf.germ (U (g x)) x hx (X.presheaf.map (homOfLE le_top).op s) =
      X.presheaf.germ (U (g x)) x hx (X.presheaf.map (homOfLE le_top).op (g x)) :=
    congrArg (X.presheaf.germ (U (g x)) x hx) (hs (g x))
  rwa [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h

/-- The global section glued from a locally constant family of global sections. -/
def glue (g : LocallyConstant X Γ(X, ⊤)) : Γ(X, ⊤) :=
  (exists_germ_eq g).choose

lemma germ_glue (g : LocallyConstant X Γ(X, ⊤)) (x : X) :
    X.presheaf.germ ⊤ x trivial (glue g) = X.presheaf.germ ⊤ x trivial (g x) :=
  (exists_germ_eq g).choose_spec x

/-- The glued section is characterized by its germs. -/
lemma eq_glue_iff {g : LocallyConstant X Γ(X, ⊤)} {s : Γ(X, ⊤)} :
    s = glue g ↔ ∀ x : X,
      X.presheaf.germ ⊤ x trivial s = X.presheaf.germ ⊤ x trivial (g x) := by
  constructor
  · rintro rfl
    exact germ_glue g
  · intro h
    exact ext_germ fun x => (h x).trans (germ_glue g x).symm

/-- The germ of a pulled-back global section along a scheme morphism. -/
lemma germ_appTop (b : Y ⟶ X) (s : Γ(X, ⊤)) (y : Y) :
    Y.presheaf.germ ⊤ y trivial (b.appTop s) =
      b.stalkMap y (X.presheaf.germ ⊤ (b y) trivial s) :=
  (Scheme.Hom.germ_stalkMap_apply b ⊤ y trivial s).symm

/-- Stalk maps of open subscheme inclusions are injective. -/
lemma stalkMap_ι_injective (U : X.Opens) (x : U.toScheme) :
    Function.Injective (U.ι.stalkMap x) := by
  exact (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap x)).1

/-- Global sections that agree on an open neighbourhood of every point are equal. -/
lemma ext_of_cover {s t : Γ(X, ⊤)}
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ U.ι.appTop s = U.ι.appTop t) : s = t := by
  refine ext_germ fun x => ?_
  obtain ⟨U, hx, hU⟩ := h x
  apply stalkMap_ι_injective U ⟨x, hx⟩
  have h₁ := germ_appTop U.ι s ⟨x, hx⟩
  have h₂ := germ_appTop U.ι t ⟨x, hx⟩
  rw [hU] at h₁
  exact h₁.symm.trans h₂

/-- Gluing is natural for pullback along scheme morphisms. -/
lemma appTop_glue (b : Y ⟶ X) (g : LocallyConstant X Γ(X, ⊤)) :
    b.appTop (glue g) = glue ((g.map b.appTop).comap b.base.hom) := by
  refine eq_glue_iff.2 fun y => ?_
  rw [germ_appTop, germ_glue, ← germ_appTop]
  rfl

/-- Gluing a constant family returns its value. -/
@[simp] lemma glue_const (s : Γ(X, ⊤)) : glue (LocallyConstant.const X s) = s :=
  (eq_glue_iff.2 fun _ => rfl).symm

/-- The units of global sections glued from a locally constant family of units. -/
def glueUnits : LocallyConstant X Γ(X, ⊤)ˣ →* Γ(X, ⊤)ˣ where
  toFun g :=
    { val := glue (g.map Units.val)
      inv := glue (g.map fun u => ((u⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)))
      val_inv := ext_germ fun x => by
        rw [map_mul, germ_glue, germ_glue, ← map_mul]
        simp
      inv_val := ext_germ fun x => by
        rw [map_mul, germ_glue, germ_glue, ← map_mul]
        simp }
  map_one' := Units.ext <| ext_germ fun x => by
    rw [germ_glue]
    simp
  map_mul' g h := Units.ext <| ext_germ fun x => by
    simp only [Units.val_mul, map_mul, germ_glue, LocallyConstant.map_apply,
      LocallyConstant.coe_mul, Function.comp_apply, Pi.mul_apply]

@[simp] lemma glueUnits_val (g : LocallyConstant X Γ(X, ⊤)ˣ) :
    (glueUnits g : Γ(X, ⊤)) = glue (g.map Units.val) := rfl

lemma germ_glueUnits (g : LocallyConstant X Γ(X, ⊤)ˣ) (x : X) :
    X.presheaf.germ ⊤ x trivial (glueUnits g : Γ(X, ⊤)) =
      X.presheaf.germ ⊤ x trivial (g x : Γ(X, ⊤)) :=
  germ_glue _ x

/-- Glued units are characterized by their germs. -/
lemma eq_glueUnits_iff {g : LocallyConstant X Γ(X, ⊤)ˣ} {u : Γ(X, ⊤)ˣ} :
    u = glueUnits g ↔ ∀ x : X,
      X.presheaf.germ ⊤ x trivial (u : Γ(X, ⊤)) = X.presheaf.germ ⊤ x trivial (g x : Γ(X, ⊤)) := by
  rw [Units.ext_iff, glueUnits_val, eq_glue_iff]
  rfl

@[simp] lemma glueUnits_const (u : Γ(X, ⊤)ˣ) : glueUnits (LocallyConstant.const X u) = u :=
  (eq_glueUnits_iff.2 fun _ => rfl).symm

/-- Gluing units is natural for pullback along scheme morphisms. -/
lemma map_glueUnits (b : Y ⟶ X) (g : LocallyConstant X Γ(X, ⊤)ˣ) :
    Units.map b.appTop.hom.toMonoidHom (glueUnits g) =
      glueUnits ((g.map (Units.map b.appTop.hom.toMonoidHom)).comap b.base.hom) := by
  refine eq_glueUnits_iff.2 fun y => ?_
  change Y.presheaf.germ ⊤ y trivial (b.appTop (glueUnits g : Γ(X, ⊤))) =
    Y.presheaf.germ ⊤ y trivial (b.appTop (g (b y) : Γ(X, ⊤)))
  rw [germ_appTop, germ_glueUnits, ← germ_appTop]

/-- A unit agreeing near every point with the corresponding value of a locally constant
family of units is the glued unit. -/
lemma eq_glueUnits_of_cover {g : LocallyConstant X Γ(X, ⊤)ˣ} {u : Γ(X, ⊤)ˣ}
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Units.map U.ι.appTop.hom.toMonoidHom u = Units.map U.ι.appTop.hom.toMonoidHom (g x)) :
    u = glueUnits g := by
  refine eq_glueUnits_iff.2 fun x => ?_
  obtain ⟨U, hx, hU⟩ := h x
  apply stalkMap_ι_injective U ⟨x, hx⟩
  have h₁ := germ_appTop U.ι (u : Γ(X, ⊤)) ⟨x, hx⟩
  have h₂ := germ_appTop U.ι (g x : Γ(X, ⊤)) ⟨x, hx⟩
  have h₃ := congrArg Units.val hU
  simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe] at h₃
  rw [h₃] at h₁
  exact h₁.symm.trans h₂

/-- Units of global sections agreeing on an open neighbourhood of every point are equal. -/
lemma units_ext_of_cover {u v : Γ(X, ⊤)ˣ}
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Units.map U.ι.appTop.hom.toMonoidHom u = Units.map U.ι.appTop.hom.toMonoidHom v) :
    u = v :=
  (eq_glueUnits_of_cover (g := LocallyConstant.const X v) h).trans (glueUnits_const v)


/-! ### Locally constant powers of a character -/

variable {M : Type*} [AddCommGroup M]

/-- The locally constant power of `t` along `f`: the unit of `Γ(X, ⊤)` that equals
`t (ofAdd m)` on the clopen fibre `f ⁻¹' {m}`, for every `m : M`. -/
def lcPow (t : Multiplicative M →* Γ(X, ⊤)ˣ) (f : LocallyConstant X M) : Γ(X, ⊤)ˣ :=
  glueUnits (f.map fun m => t (Multiplicative.ofAdd m))

/-- The germ of `lcPow t f` at `x` is the germ of `t (ofAdd (f x))`. -/
lemma germ_lcPow (t : Multiplicative M →* Γ(X, ⊤)ˣ) (f : LocallyConstant X M) (x : X) :
    X.presheaf.germ ⊤ x trivial (lcPow t f : Γ(X, ⊤)) =
      X.presheaf.germ ⊤ x trivial (t (Multiplicative.ofAdd (f x)) : Γ(X, ⊤)) :=
  germ_glueUnits _ x

/-- `lcPow t f` is the unique unit whose germ at every `x` is the germ of `t (ofAdd (f x))`. -/
lemma eq_lcPow_iff {t : Multiplicative M →* Γ(X, ⊤)ˣ} {f : LocallyConstant X M}
    {u : Γ(X, ⊤)ˣ} :
    u = lcPow t f ↔ ∀ x : X, X.presheaf.germ ⊤ x trivial (u : Γ(X, ⊤)) =
      X.presheaf.germ ⊤ x trivial (t (Multiplicative.ofAdd (f x)) : Γ(X, ⊤)) :=
  eq_glueUnits_iff

/-- A unit that agrees, on an open neighbourhood `U` of every point `x`, with
`t (ofAdd (f x))` is `lcPow t f`. -/
lemma eq_lcPow_of_cover {t : Multiplicative M →* Γ(X, ⊤)ˣ} {f : LocallyConstant X M}
    {u : Γ(X, ⊤)ˣ}
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Units.map U.ι.appTop.hom.toMonoidHom u =
        Units.map U.ι.appTop.hom.toMonoidHom (t (Multiplicative.ofAdd (f x)))) :
    u = lcPow t f :=
  eq_glueUnits_of_cover h

/-- `lcPow` of a constant function is the value of `t`. -/
@[simp] lemma lcPow_const (t : Multiplicative M →* Γ(X, ⊤)ˣ) (m : M) :
    lcPow t (LocallyConstant.const X m) = t (Multiplicative.ofAdd m) :=
  (eq_lcPow_iff.2 fun _ => rfl).symm

/-- `lcPow` is additive in the locally constant function. -/
lemma lcPow_add (t : Multiplicative M →* Γ(X, ⊤)ˣ) (f g : LocallyConstant X M) :
    lcPow t (f + g) = lcPow t f * lcPow t g := by
  refine (eq_lcPow_iff.2 fun x => ?_).symm
  rw [Units.val_mul, map_mul, germ_lcPow, germ_lcPow, ← map_mul, ← Units.val_mul, ← map_mul]
  rfl

@[simp] lemma lcPow_zero (t : Multiplicative M →* Γ(X, ⊤)ˣ) :
    lcPow t (0 : LocallyConstant X M) = 1 := by
  refine (eq_lcPow_iff.2 fun x => ?_).symm
  simp

/-- `lcPow` is multiplicative in the character. -/
lemma lcPow_mul (t t' : Multiplicative M →* Γ(X, ⊤)ˣ) (f : LocallyConstant X M) :
    lcPow (t * t') f = lcPow t f * lcPow t' f := by
  refine (eq_lcPow_iff.2 fun x => ?_).symm
  rw [Units.val_mul, map_mul, germ_lcPow, germ_lcPow, ← map_mul, ← Units.val_mul]
  rfl

@[simp] lemma lcPow_one (f : LocallyConstant X M) :
    lcPow (1 : Multiplicative M →* Γ(X, ⊤)ˣ) f = 1 := by
  refine (eq_lcPow_iff.2 fun x => ?_).symm
  rfl

/-- `lcPow` is natural for pullback along scheme morphisms. -/
lemma lcPow_naturality (b : Y ⟶ X) (t : Multiplicative M →* Γ(X, ⊤)ˣ)
    (f : LocallyConstant X M) :
    Units.map b.appTop.hom.toMonoidHom (lcPow t f) =
      lcPow ((Units.map b.appTop.hom.toMonoidHom).comp t) (f.comap b.base.hom) := by
  refine eq_lcPow_iff.2 fun y => ?_
  change Y.presheaf.germ ⊤ y trivial (b.appTop (lcPow t f : Γ(X, ⊤))) =
    Y.presheaf.germ ⊤ y trivial (b.appTop (t (Multiplicative.ofAdd (f (b y))) : Γ(X, ⊤)))
  rw [germ_appTop, germ_lcPow, ← germ_appTop]

/-- On an open subscheme where `f` is constantly `m`, `lcPow t f` restricts to
`t (ofAdd m)`. -/
lemma map_ι_lcPow_of_eqOn (t : Multiplicative M →* Γ(X, ⊤)ˣ) (f : LocallyConstant X M)
    (U : X.Opens) (m : M) (hf : ∀ x ∈ U, f x = m) :
    Units.map U.ι.appTop.hom.toMonoidHom (lcPow t f) =
      Units.map U.ι.appTop.hom.toMonoidHom (t (Multiplicative.ofAdd m)) := by
  have hc : f.comap U.ι.base.hom = LocallyConstant.const U.toScheme m := by
    ext x
    exact hf x.1 x.2
  rw [lcPow_naturality, hc, lcPow_const]
  rfl

end Langlands.AlgebraicGeometry.LocallyConstantUnitPower
