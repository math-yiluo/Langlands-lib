import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleProof

/-! # Gauge classification of line bundles glued from unit cocycles

For a family of opens `T` and unit cocycles `g`, `h` on the pairwise overlaps, the glued
sheaves `glued g` and `glued h` are isomorphic exactly when there are units `a i` on `T i`
with `h i j = a i * g i j * (a j)⁻¹` on `T i ⊓ T j`. The isomorphism built from `a` multiplies
the `i`-th component by `a i` and sends the local generator `genSec g i` to
`a i • genSec h i`. Conversely, every morphism `glued g ⟶ glued h` is of this form, with
coefficients read off on the local generators.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.CocycleGluing

variable {X : Scheme.{u}} {ι : Type u} {T : ι → X.Opens}

/-- A morphism of sheaves of modules commutes with restriction of sections. -/
lemma app_presheaf_map {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (hVU : V ≤ U)
    (m : Γ(M, U)) :
    φ.app V (M.presheaf.map (homOfLE hVU).op m) = N.presheaf.map (homOfLE hVU).op (φ.app U m) :=
  NatTrans.naturality_apply φ.mapPresheaf (homOfLE hVU).op m

section Fam

/-- Componentwise multiplication of a family by functions `a i` on `T i`. -/
def gaugeFam (a : ∀ i : ι, Γ(X, T i)) {U : X.Opens} (b : Fam T U) : Fam T U :=
  fun i ↦ X.presheaf.map (homOfLE (inf_le_right : U ⊓ T i ≤ T i)).op (a i) * b i

lemma gaugeFam_apply (a : ∀ i : ι, Γ(X, T i)) {U : X.Opens} (b : Fam T U) (i : ι) :
    gaugeFam a b i = X.presheaf.map (homOfLE (inf_le_right : U ⊓ T i ≤ T i)).op (a i) * b i :=
  rfl

lemma gaugeFam_add (a : ∀ i : ι, Γ(X, T i)) {U : X.Opens} (b c : Fam T U) :
    gaugeFam a (b + c) = gaugeFam a b + gaugeFam a c :=
  funext fun i ↦ mul_add _ (b i) (c i)

lemma gaugeFam_smul (a : ∀ i : ι, Γ(X, T i)) {U : X.Opens} (r : Γ(X, U)) (b : Fam T U) :
    gaugeFam a (r • b) = r • gaugeFam a b :=
  funext fun i ↦ mul_left_comm _ _ (b i)

lemma famRes_gaugeFam (a : ∀ i : ι, Γ(X, T i)) {U V : X.Opens} (hVU : V ≤ U) (b : Fam T U) :
    famRes T hVU (gaugeFam a b) = gaugeFam a (famRes T hVU b) := by
  funext i
  rw [famRes_apply, gaugeFam_apply, gaugeFam_apply, famRes_apply, map_mul, res_res]

end Fam

section Gauge

variable (g h : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ)

/-- Functions `a i` on `T i` intertwine the cocycles `g` and `h`:
`a i * g i j = h i j * a j` on `T i ⊓ T j`. -/
def IsGaugeFamily (a : ∀ i : ι, Γ(X, T i)) : Prop :=
  ∀ i j : ι,
    X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (a i) *
        (g i j : Γ(X, T i ⊓ T j)) =
      (h i j : Γ(X, T i ⊓ T j)) *
        X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (a j)

/-- Units `a i` on `T i` form a gauge from `g` to `h`:
`h i j = a i * g i j * (a j)⁻¹` on `T i ⊓ T j`. -/
def IsGauge (a : ∀ i : ι, (Γ(X, T i))ˣ) : Prop :=
  ∀ i j : ι,
    (h i j : Γ(X, T i ⊓ T j)) =
      X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (a i : Γ(X, T i)) *
          (g i j : Γ(X, T i ⊓ T j)) *
        X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op
          (((a j)⁻¹ : (Γ(X, T j))ˣ) : Γ(X, T j))

/-- A unit gauge is the same as an intertwining family of units. -/
lemma isGauge_iff (a : ∀ i : ι, (Γ(X, T i))ˣ) :
    IsGauge g h a ↔ IsGaugeFamily g h (fun i ↦ (a i : Γ(X, T i))) := by
  constructor
  · intro ha i j
    symm
    rw [ha i j, mul_assoc (_ * _), ← map_mul, Units.inv_mul, map_one, mul_one]
  · intro ha i j
    rw [ha i j, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]

variable {g h}

/-- Inverting an intertwining family of units intertwines the cocycles the other way. -/
lemma IsGaugeFamily.inv {a : ∀ i : ι, (Γ(X, T i))ˣ}
    (ha : IsGaugeFamily g h (fun i ↦ (a i : Γ(X, T i)))) :
    IsGaugeFamily h g (fun i ↦ (((a i)⁻¹ : (Γ(X, T i))ˣ) : Γ(X, T i))) := by
  intro i j
  have e1 := ha i j
  have e2 : X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op
        (((a i)⁻¹ : (Γ(X, T i))ˣ) : Γ(X, T i)) *
      X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (a i : Γ(X, T i)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have e3 : X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (a j : Γ(X, T j)) *
      X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op
        (((a j)⁻¹ : (Γ(X, T j))ˣ) : Γ(X, T j)) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  dsimp only at e1 ⊢
  linear_combination
    (-(X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op
        (((a i)⁻¹ : (Γ(X, T i))ˣ) : Γ(X, T i)) *
      X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op
        (((a j)⁻¹ : (Γ(X, T j))ˣ) : Γ(X, T j)))) * e1 +
    ((g i j : Γ(X, T i ⊓ T j)) * X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op
        (((a j)⁻¹ : (Γ(X, T j))ˣ) : Γ(X, T j))) * e2 -
    (X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op
        (((a i)⁻¹ : (Γ(X, T i))ˣ) : Γ(X, T i)) * (h i j : Γ(X, T i ⊓ T j))) * e3

/-- The inverse of a unit gauge from `g` to `h` is a unit gauge from `h` to `g`. -/
lemma IsGauge.inv {a : ∀ i : ι, (Γ(X, T i))ˣ} (ha : IsGauge g h a) :
    IsGauge h g (fun i ↦ (a i)⁻¹) :=
  (isGauge_iff h g _).mpr ((isGauge_iff g h a).mp ha).inv

/-- Multiplication by an intertwining family preserves the cocycle relation. -/
lemma compat_gaugeFam {a : ∀ i : ι, Γ(X, T i)} (ha : IsGaugeFamily g h a) {U : X.Opens}
    {b : Fam T U} (hb : Compat g b) : Compat h (gaugeFam a b) := fun i j V hi hj ↦ by
  have hV : V ≤ T i ⊓ T j := le_inf (hi.trans inf_le_right) (hj.trans inf_le_right)
  have key := congrArg (fun z ↦ X.presheaf.map (homOfLE hV).op z) (ha i j)
  simp only [map_mul, res_res] at key
  rw [gaugeFam_apply, gaugeFam_apply, map_mul, map_mul, res_res, res_res, hb i j V hi hj]
  linear_combination X.presheaf.map (homOfLE hj).op (b j) * key

/-- The morphism of glued sheaves multiplying the `i`-th component by `a i`. -/
noncomputable def gaugeHom (a : ∀ i : ι, Γ(X, T i)) (ha : IsGaugeFamily g h a) :
    glued g ⟶ glued h where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := fun m ↦ mk h (gaugeFam a (m.1 : Fam T U.unop))
            (compat_gaugeFam ha (compat_of_mem g m))
          map_add' := fun m m' ↦ Subtype.ext (gaugeFam_add a m.1 m'.1)
          map_smul' := fun r m ↦ Subtype.ext (gaugeFam_smul a r m.1) }
      naturality := by
        intro U V f
        ext m
        apply Subtype.ext
        exact (famRes_gaugeFam a (leOfHom f.unop) m.1).symm }

/-- Component formula: the `i`-th component is multiplied by `a i`. -/
lemma comp_gaugeHom_app (a : ∀ i : ι, Γ(X, T i)) (ha : IsGaugeFamily g h a) {U : X.Opens}
    (m : Γ(glued g, U)) (i : ι) :
    comp h ((gaugeHom a ha).app U m) i =
      X.presheaf.map (homOfLE (inf_le_right : U ⊓ T i ≤ T i)).op (a i) * comp g m i :=
  rfl

/-- On local generators, the gauge morphism multiplies by `a i`. -/
lemma gaugeHom_app_genSec (hg : IsCocycle g) (hh : IsCocycle h) (a : ∀ i : ι, Γ(X, T i))
    (ha : IsGaugeFamily g h a) (i : ι) {V : X.Opens} (hV : V ≤ T i) :
    (gaugeHom a ha).app V (genSec g hg i hV) =
      X.presheaf.map (homOfLE hV).op (a i) • genSec h hh i hV := by
  refine eq_of_comp h fun j ↦ ?_
  rw [comp_gaugeHom_app]
  change _ * gen g i hV j = X.presheaf.map (homOfLE (inf_le_left : V ⊓ T j ≤ V)).op
    (X.presheaf.map (homOfLE hV).op (a i)) * gen h i hV j
  have hle : V ⊓ T j ≤ T j ⊓ T i := le_inf inf_le_right (inf_le_left.trans hV)
  have key := congrArg (fun z ↦ X.presheaf.map (homOfLE hle).op z) (ha j i)
  simp only [map_mul, res_res] at key
  rw [gen_apply, gen_apply, res_res]
  linear_combination key

/-- Gauge morphisms whose coefficients multiply to one compose to the identity. -/
lemma gaugeHom_comp_gaugeHom {a a' : ∀ i : ι, Γ(X, T i)} (ha : IsGaugeFamily g h a)
    (ha' : IsGaugeFamily h g a') (h1 : ∀ i, a i * a' i = 1) :
    gaugeHom a ha ≫ gaugeHom a' ha' = 𝟙 (glued g) := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext m
  refine eq_of_comp g fun i ↦ ?_
  change X.presheaf.map (homOfLE (inf_le_right : U ⊓ T i ≤ T i)).op (a' i) *
      (X.presheaf.map (homOfLE (inf_le_right : U ⊓ T i ≤ T i)).op (a i) * comp g m i) =
    comp g m i
  rw [← mul_assoc, ← map_mul, mul_comm (a' i), h1 i, map_one, one_mul]

/-- The isomorphism of glued line bundles defined by a unit gauge `a` from `g` to `h`.
It multiplies the `i`-th component by `a i`. -/
noncomputable def gaugeIso (a : ∀ i : ι, (Γ(X, T i))ˣ) (ha : IsGauge g h a) :
    glued g ≅ glued h where
  hom := gaugeHom (fun i ↦ (a i : Γ(X, T i))) ((isGauge_iff g h a).mp ha)
  inv := gaugeHom (fun i ↦ (((a i)⁻¹ : (Γ(X, T i))ˣ) : Γ(X, T i)))
    ((isGauge_iff g h a).mp ha).inv
  hom_inv_id := gaugeHom_comp_gaugeHom _ _ fun i ↦ Units.mul_inv (a i)
  inv_hom_id := gaugeHom_comp_gaugeHom _ _ fun i ↦ Units.inv_mul (a i)

/-- Component formula for the gauge isomorphism. -/
lemma comp_gaugeIso_hom_app (a : ∀ i : ι, (Γ(X, T i))ˣ) (ha : IsGauge g h a) {U : X.Opens}
    (m : Γ(glued g, U)) (i : ι) :
    comp h ((gaugeIso a ha).hom.app U m) i =
      X.presheaf.map (homOfLE (inf_le_right : U ⊓ T i ≤ T i)).op (a i : Γ(X, T i)) *
        comp g m i :=
  rfl

/-- The gauge isomorphism sends the local generator `genSec g i` to `a i • genSec h i`. -/
lemma gaugeIso_hom_app_genSec (hg : IsCocycle g) (hh : IsCocycle h) (a : ∀ i : ι, (Γ(X, T i))ˣ)
    (ha : IsGauge g h a) (i : ι) {V : X.Opens} (hV : V ≤ T i) :
    (gaugeIso a ha).hom.app V (genSec g hg i hV) =
      X.presheaf.map (homOfLE hV).op (a i : Γ(X, T i)) • genSec h hh i hV :=
  gaugeHom_app_genSec hg hh _ ((isGauge_iff g h a).mp ha) i hV

end Gauge

section Converse

variable {g h k : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ}

/-- Over an open inside `T i ⊓ T j`, the local generator for `j` is `g i j` times the local
generator for `i`. -/
lemma genSec_eq_smul_genSec (hg : IsCocycle g) {i j : ι} {V : X.Opens} (hi : V ≤ T i)
    (hj : V ≤ T j) :
    genSec g hg j hj = X.presheaf.map (homOfLE (le_inf hi hj)).op (g i j : Γ(X, T i ⊓ T j)) •
      genSec g hg i hi := by
  refine eq_of_comp g fun k ↦ ?_
  change gen g j hj k = X.presheaf.map (homOfLE (inf_le_left : V ⊓ T k ≤ V)).op
    (X.presheaf.map (homOfLE (le_inf hi hj)).op (g i j : Γ(X, T i ⊓ T j))) * gen g i hi k
  rw [gen_apply, gen_apply, res_res, mul_comm]
  exact (cocycle_res g hg k i j _ _ _).symm

/-- Two sections over `U` have the same `i`-th component if their restrictions to `U ⊓ T i`
agree. -/
lemma comp_eq_of_map_eq {U : X.Opens} {m m' : Γ(glued g, U)} {i : ι}
    (H : (glued g).presheaf.map (homOfLE (inf_le_left : U ⊓ T i ≤ U)).op m =
      (glued g).presheaf.map (homOfLE (inf_le_left : U ⊓ T i ≤ U)).op m') :
    comp g m i = comp g m' i := by
  have h1 := congrArg (fun z ↦ comp g z i) H
  change X.presheaf.map (homOfLE (inf_le_inf_right (T i) (inf_le_left : U ⊓ T i ≤ U))).op
      (comp g m i) =
    X.presheaf.map (homOfLE (inf_le_inf_right (T i) (inf_le_left : U ⊓ T i ≤ U))).op
      (comp g m' i) at h1
  have h2 := congrArg (fun z ↦ X.presheaf.map
    (homOfLE (le_inf le_rfl inf_le_right : U ⊓ T i ≤ U ⊓ T i ⊓ T i)).op z) h1
  simp only [res_res, res_self] at h2
  exact h2

/-- Morphisms out of a glued line bundle are determined by their values on the local
generators. -/
lemma hom_ext_genSec (hg : IsCocycle g) {φ ψ : glued g ⟶ glued h}
    (H : ∀ (i : ι) {V : X.Opens} (hV : V ≤ T i),
      φ.app V (genSec g hg i hV) = ψ.app V (genSec g hg i hV)) :
    φ = ψ := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext m
  refine eq_of_comp h fun i ↦ comp_eq_of_map_eq ?_
  obtain ⟨r, hr⟩ := (smul_genSec_bijective g hg i (inf_le_right : U ⊓ T i ≤ T i)).2
    ((glued g).presheaf.map (homOfLE (inf_le_left : U ⊓ T i ≤ U)).op m)
  rw [← app_presheaf_map, ← app_presheaf_map, ← hr, Scheme.Modules.Hom.app_smul,
    Scheme.Modules.Hom.app_smul, H i]

variable (hg : IsCocycle g) (hh : IsCocycle h) (hk : IsCocycle k)

/-- The coefficient of a morphism of glued line bundles on `T i`: the unique `c` with
`φ (genSec g i) = c • genSec h i` over `T i`. -/
noncomputable def coeff (φ : glued g ⟶ glued h) (i : ι) : Γ(X, T i) :=
  (Equiv.ofBijective _ (smul_genSec_bijective h hh i le_rfl)).symm
    (φ.app (T i) (genSec g hg i le_rfl))

lemma app_genSec_top (φ : glued g ⟶ glued h) (i : ι) :
    φ.app (T i) (genSec g hg i le_rfl) = coeff hg hh φ i • genSec h hh i le_rfl :=
  ((Equiv.ofBijective _ (smul_genSec_bijective h hh i le_rfl)).apply_symm_apply _).symm

lemma coeff_eq_of (φ : glued g ⟶ glued h) (i : ι) (c : Γ(X, T i))
    (hc : φ.app (T i) (genSec g hg i le_rfl) = c • genSec h hh i le_rfl) :
    coeff hg hh φ i = c :=
  (smul_genSec_bijective h hh i le_rfl).1 ((app_genSec_top hg hh φ i).symm.trans hc)

/-- On every local generator, a morphism multiplies by its coefficient. -/
lemma app_genSec (φ : glued g ⟶ glued h) (i : ι) {V : X.Opens} (hV : V ≤ T i) :
    φ.app V (genSec g hg i hV) =
      X.presheaf.map (homOfLE hV).op (coeff hg hh φ i) • genSec h hh i hV := by
  have hn := app_presheaf_map φ hV (genSec g hg i le_rfl)
  rw [map_genSec g hg i hV le_rfl, app_genSec_top hg hh φ i, Scheme.Modules.map_smul,
    map_genSec h hh i hV le_rfl] at hn
  exact hn

/-- The coefficients of a morphism intertwine the cocycles. -/
lemma isGaugeFamily_coeff (φ : glued g ⟶ glued h) : IsGaugeFamily g h (coeff hg hh φ) := by
  intro i j
  have hi : T i ⊓ T j ≤ T i := inf_le_left
  have hj : T i ⊓ T j ≤ T j := inf_le_right
  have e1 := app_genSec hg hh φ j hj
  rw [genSec_eq_smul_genSec hg hi hj, genSec_eq_smul_genSec hh hi hj,
    Scheme.Modules.Hom.app_smul, app_genSec hg hh φ i hi, smul_smul, smul_smul] at e1
  have e2 := (smul_genSec_bijective h hh i hi).1 e1
  simp only [res_self] at e2
  linear_combination e2

/-- Every morphism of glued line bundles is the gauge morphism of its coefficients. -/
lemma eq_gaugeHom (φ : glued g ⟶ glued h) :
    φ = gaugeHom (coeff hg hh φ) (isGaugeFamily_coeff hg hh φ) :=
  hom_ext_genSec hg fun i _ hV ↦ by rw [app_genSec hg hh φ i hV, gaugeHom_app_genSec hg hh]

/-- Component formula for an arbitrary morphism of glued line bundles. -/
lemma comp_app_eq (φ : glued g ⟶ glued h) {U : X.Opens} (m : Γ(glued g, U)) (i : ι) :
    comp h (φ.app U m) i =
      X.presheaf.map (homOfLE (inf_le_right : U ⊓ T i ≤ T i)).op (coeff hg hh φ i) *
        comp g m i :=
  congrArg (fun ψ : glued g ⟶ glued h ↦ comp h (ψ.app U m) i) (eq_gaugeHom hg hh φ)

lemma coeff_gaugeHom (a : ∀ i : ι, Γ(X, T i)) (ha : IsGaugeFamily g h a) :
    coeff hg hh (gaugeHom a ha) = a :=
  funext fun i ↦ coeff_eq_of hg hh _ i _ (by rw [gaugeHom_app_genSec hg hh, res_self])

lemma coeff_comp (φ : glued g ⟶ glued h) (ψ : glued h ⟶ glued k) (i : ι) :
    coeff hg hk (φ ≫ ψ) i = coeff hg hh φ i * coeff hh hk ψ i := by
  refine coeff_eq_of hg hk _ i _ ?_
  change ψ.app (T i) (φ.app (T i) (genSec g hg i le_rfl)) = _
  rw [app_genSec_top hg hh φ i, Scheme.Modules.Hom.app_smul, app_genSec_top hh hk ψ i,
    smul_smul]

lemma coeff_id (i : ι) : coeff hg hg (𝟙 (glued g)) i = 1 :=
  coeff_eq_of hg hg _ i _ (one_smul _ _).symm

/-- The units on `T i` defined by an isomorphism of glued line bundles. -/
noncomputable def isoUnits (e : glued g ≅ glued h) (i : ι) : (Γ(X, T i))ˣ where
  val := coeff hg hh e.hom i
  inv := coeff hh hg e.inv i
  val_inv := by rw [← coeff_comp hg hh hg, e.hom_inv_id, coeff_id]
  inv_val := by rw [← coeff_comp hh hg hh, e.inv_hom_id, coeff_id]

lemma isoUnits_val (e : glued g ≅ glued h) (i : ι) :
    (isoUnits hg hh e i : Γ(X, T i)) = coeff hg hh e.hom i :=
  rfl

/-- The units of an isomorphism form a unit gauge between the cocycles. -/
lemma isGauge_isoUnits (e : glued g ≅ glued h) : IsGauge g h (isoUnits hg hh e) :=
  (isGauge_iff g h _).mpr (isGaugeFamily_coeff hg hh e.hom)

/-- An isomorphism sends `genSec g i` to `a i • genSec h i`, where `a = isoUnits e`. -/
lemma iso_hom_app_genSec (e : glued g ≅ glued h) (i : ι) {V : X.Opens} (hV : V ≤ T i) :
    e.hom.app V (genSec g hg i hV) =
      X.presheaf.map (homOfLE hV).op (isoUnits hg hh e i : Γ(X, T i)) • genSec h hh i hV :=
  app_genSec hg hh e.hom i hV

/-- Every isomorphism of glued line bundles is the gauge isomorphism of its units. -/
lemma iso_eq_gaugeIso (e : glued g ≅ glued h) :
    e = gaugeIso (isoUnits hg hh e) (isGauge_isoUnits hg hh e) :=
  Iso.ext (eq_gaugeHom hg hh e.hom)

lemma isoUnits_gaugeIso (a : ∀ i : ι, (Γ(X, T i))ˣ) (ha : IsGauge g h a) :
    isoUnits hg hh (gaugeIso a ha) = a :=
  funext fun i ↦ Units.ext (congrFun (coeff_gaugeHom hg hh _ ((isGauge_iff g h a).mp ha)) i)

include hg hh in
/-- Gauge classification: the line bundles glued from unit cocycles `g` and `h` are isomorphic
if and only if there are units `a i` on `T i` with `h i j = a i * g i j * (a j)⁻¹`. -/
theorem nonempty_iso_glued_iff :
    Nonempty (glued g ≅ glued h) ↔ ∃ a : ∀ i : ι, (Γ(X, T i))ˣ, IsGauge g h a :=
  ⟨fun ⟨e⟩ ↦ ⟨isoUnits hg hh e, isGauge_isoUnits hg hh e⟩, fun ⟨a, ha⟩ ↦ ⟨gaugeIso a ha⟩⟩

end Converse

end Langlands.AlgebraicGeometry.Picard.CocycleGluing
