import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescent.Submodule
import Langlands.Algebra.UnitCocycleLocalUnitsStatement
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Local unit cocycle sections over affine opens -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct

namespace Langlands.Scheme.UnitCocycleDescent

variable {X Y : Scheme.{u}} (p : X ⟶ Y)
  (c : ∀ (U : Scheme.{u}) (a b : U ⟶ X), a ≫ p = b ≫ p → Γ(U, ⊤)ˣ)

/-- The unit `c U a b h` only depends on the morphisms `a` and `b`. -/
lemma c_congr {U : Scheme.{u}} {a a' b b' : U ⟶ X} (ha : a = a') (hb : b = b')
    (h : a ≫ p = b ≫ p) (h' : a' ≫ p = b' ≫ p) : c U a b h = c U a' b' h' := by
  subst ha hb
  rfl

/-- Naturality of the family `c` under precomposition. -/
def IsNatural : Prop :=
  ∀ (U V : Scheme.{u}) (q : V ⟶ U) (a b : U ⟶ X) (h : a ≫ p = b ≫ p)
    (h' : (q ≫ a) ≫ p = (q ≫ b) ≫ p),
    c V (q ≫ a) (q ≫ b) h' = Units.map q.appTop.hom.toMonoidHom (c U a b h)

/-- Multiplicativity of the family `c` along triples. -/
def IsMultiplicative : Prop :=
  ∀ (U : Scheme.{u}) (a b d : U ⟶ X) (h : a ≫ p = b ≫ p) (h' : b ≫ p = d ≫ p)
    (h'' : a ≫ p = d ≫ p), c U a b h * c U b d h' = c U a d h''

variable {p c}

/-- For a natural family `c`, the cocycle condition only needs to be checked on pairs of maps
sending the whole source into `p ⁻¹ᵁ W`. -/
lemma IsCocycleSection.of_top (hnat : IsNatural p c) {W : Y.Opens} {σ : Γ(X, p ⁻¹ᵁ W)}
    (hσ : ∀ (U : Scheme.{u}) (a b : U ⟶ X) (h : a ≫ p = b ≫ p)
      (ha : ⊤ ≤ a ⁻¹ᵁ p ⁻¹ᵁ W) (hb : ⊤ ≤ b ⁻¹ᵁ p ⁻¹ᵁ W),
      (c U a b h).1 * a.appLE (p ⁻¹ᵁ W) ⊤ ha σ = b.appLE (p ⁻¹ᵁ W) ⊤ hb σ) :
    IsCocycleSection p c W σ := by
  intro U a b h V ha hb
  have h' : (V.ι ≫ a) ≫ p = (V.ι ≫ b) ≫ p := by simp only [Category.assoc, h]
  have key := hσ V (V.ι ≫ a) (V.ι ≫ b) h' (fun x _ ↦ ha x.2) (fun x _ ↦ hb x.2)
  rw [hnat U V V.ι a b h h', Units.coe_map] at key
  apply ι_appLE_injective V
  rw [map_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.map_appLE]
  convert key using 2
  rw [appTop_eq_appLE]
  rfl

section Affine

variable (p c) {W : Y.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen (p ⁻¹ᵁ W))
  [Algebra Γ(Y, W) Γ(X, p ⁻¹ᵁ W)]

lemma fromSpec_comp (halg : algebraMap Γ(Y, W) Γ(X, p ⁻¹ᵁ W) = (p.app W).hom) :
    hW'.fromSpec ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, W) Γ(X, p ⁻¹ᵁ W))) ≫ hW.fromSpec := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec p hW hW' le_rfl, Scheme.Hom.appLE_eq_app, halg]
  rfl

/-- The morphism `Spec T ⟶ X` through `p ⁻¹ᵁ W` attached to an algebra map
`Γ(X, p ⁻¹ᵁ W) → T` over `Γ(Y, W)`. -/
noncomputable def specPoint {T : Type u} [CommRing T] [Algebra Γ(Y, W) T]
    (g : Γ(X, p ⁻¹ᵁ W) →ₐ[Γ(Y, W)] T) : Spec (.of T) ⟶ X :=
  Spec.map (CommRingCat.ofHom g.toRingHom) ≫ hW'.fromSpec

variable {T T' : Type u} [CommRing T] [Algebra Γ(Y, W) T] [CommRing T'] [Algebra Γ(Y, W) T']

lemma specPoint_comp (halg : algebraMap Γ(Y, W) Γ(X, p ⁻¹ᵁ W) = (p.app W).hom)
    (g : Γ(X, p ⁻¹ᵁ W) →ₐ[Γ(Y, W)] T) :
    specPoint p hW' g ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, W) T)) ≫ hW.fromSpec := by
  have hg : g.toRingHom.comp (algebraMap Γ(Y, W) Γ(X, p ⁻¹ᵁ W)) = algebraMap Γ(Y, W) T :=
    RingHom.ext g.commutes
  rw [specPoint, Category.assoc, fromSpec_comp p hW hW' halg, ← Spec.map_comp_assoc,
    ← CommRingCat.ofHom_comp]
  exact congrArg (fun f : Γ(Y, W) →+* T ↦ Spec.map (CommRingCat.ofHom f) ≫ hW.fromSpec) hg

lemma specPoint_map (f : T →ₐ[Γ(Y, W)] T') (g : Γ(X, p ⁻¹ᵁ W) →ₐ[Γ(Y, W)] T) :
    specPoint p hW' (f.comp g) = Spec.map (CommRingCat.ofHom f.toRingHom) ≫ specPoint p hW' g := by
  simp only [specPoint]
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  rfl

lemma le_preimage_specPoint (g : Γ(X, p ⁻¹ᵁ W) →ₐ[Γ(Y, W)] T) :
    ⊤ ≤ specPoint p hW' g ⁻¹ᵁ p ⁻¹ᵁ W := by
  intro x _
  change hW'.fromSpec _ ∈ p ⁻¹ᵁ W
  rw [← SetLike.mem_coe, ← hW'.range_fromSpec]
  exact ⟨_, rfl⟩

lemma specPoint_appLE (g : Γ(X, p ⁻¹ᵁ W) →ₐ[Γ(Y, W)] T) (e : ⊤ ≤ specPoint p hW' g ⁻¹ᵁ p ⁻¹ᵁ W)
    (m : Γ(X, p ⁻¹ᵁ W)) :
    (specPoint p hW' g).appLE (p ⁻¹ᵁ W) ⊤ e m = (Scheme.ΓSpecIso (.of T)).inv (g m) := by
  have : (specPoint p hW' g).appLE (p ⁻¹ᵁ W) ⊤ e =
      CommRingCat.ofHom g.toRingHom ≫ (Scheme.ΓSpecIso (.of T)).inv := by
    have key : ∀ e' : ⊤ ≤ (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ hW'.fromSpec) ⁻¹ᵁ p ⁻¹ᵁ W,
        (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ hW'.fromSpec).appLE (p ⁻¹ᵁ W) ⊤ e' =
          CommRingCat.ofHom g.toRingHom ≫ (Scheme.ΓSpecIso (.of T)).inv := by
      intro e'
      have h1 : hW'.fromSpec.appLE (p ⁻¹ᵁ W) ⊤ hW'.fromSpec_preimage_self.ge =
          (Scheme.ΓSpecIso Γ(X, p ⁻¹ᵁ W)).inv := by
        rw [Scheme.Hom.appLE, hW'.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
        convert Category.comp_id _
        convert (Spec Γ(X, p ⁻¹ᵁ W)).presheaf.map_id _
      rw [← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom g.toRingHom)) hW'.fromSpec
        (p ⁻¹ᵁ W) ⊤ ⊤ hW'.fromSpec_preimage_self.ge (Scheme.Hom.preimage_top _).ge,
        ← appTop_eq_appLE, Scheme.ΓSpecIso_inv_naturality, h1]
      rfl
    exact key e
  rw [this]
  rfl

lemma comp_specPoint_appLE {U : Scheme.{u}} (q : U ⟶ Spec (.of T))
    (k : Γ(X, p ⁻¹ᵁ W) →ₐ[Γ(Y, W)] T) (e : ⊤ ≤ (q ≫ specPoint p hW' k) ⁻¹ᵁ p ⁻¹ᵁ W)
    (m : Γ(X, p ⁻¹ᵁ W)) :
    (q ≫ specPoint p hW' k).appLE (p ⁻¹ᵁ W) ⊤ e m =
      q.appTop ((Scheme.ΓSpecIso (.of T)).inv (k m)) := by
  rw [← specPoint_appLE p hW' k (le_preimage_specPoint p hW' k), appTop_eq_appLE,
    ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

/-- The unit of `T` obtained from `c` on the pair of points of `X` attached to two algebra maps
`Γ(X, p ⁻¹ᵁ W) → T`. -/
noncomputable def cAlg (halg : algebraMap Γ(Y, W) Γ(X, p ⁻¹ᵁ W) = (p.app W).hom)
    (g₁ g₂ : Γ(X, p ⁻¹ᵁ W) →ₐ[Γ(Y, W)] T) : Tˣ :=
  Units.map (Scheme.ΓSpecIso (.of T)).hom.hom.toMonoidHom
    (c _ (specPoint p hW' g₁) (specPoint p hW' g₂)
      ((specPoint_comp p hW hW' halg g₁).trans (specPoint_comp p hW hW' halg g₂).symm))

variable {p c} (halg : algebraMap Γ(Y, W) Γ(X, p ⁻¹ᵁ W) = (p.app W).hom)

lemma cAlg_map (hnat : IsNatural p c) (f : T →ₐ[Γ(Y, W)] T')
    (g₁ g₂ : Γ(X, p ⁻¹ᵁ W) →ₐ[Γ(Y, W)] T) :
    Units.map f.toRingHom.toMonoidHom (cAlg p c hW hW' halg g₁ g₂) =
      cAlg p c hW hW' halg (f.comp g₁) (f.comp g₂) := by
  have h' : (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ specPoint p hW' g₁) ≫ p =
      (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ specPoint p hW' g₂) ≫ p := by
    rw [Category.assoc, Category.assoc, specPoint_comp p hW hW' halg,
      specPoint_comp p hW hW' halg]
  rw [cAlg, cAlg, c_congr p c (specPoint_map p hW' f g₁) (specPoint_map p hW' f g₂) _ h',
    hnat _ _ _ _ _ _ h']
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality]
  rfl

lemma cAlg_mul (hmul : IsMultiplicative p c) (g₁ g₂ g₃ : Γ(X, p ⁻¹ᵁ W) →ₐ[Γ(Y, W)] T) :
    cAlg p c hW hW' halg g₁ g₂ * cAlg p c hW hW' halg g₂ g₃ = cAlg p c hW hW' halg g₁ g₃ := by
  rw [cAlg, cAlg, cAlg, ← map_mul, hmul]

lemma cAlg_eq_mul (hmul : IsMultiplicative p c) (g₁ g₂ g₃ : Γ(X, p ⁻¹ᵁ W) →ₐ[Γ(Y, W)] T) :
    cAlg p c hW hW' halg g₁ g₃ = cAlg p c hW hW' halg g₂ g₃ * cAlg p c hW hW' halg g₁ g₂ := by
  rw [mul_comm, cAlg_mul hW hW' halg hmul]

variable (p c) in
/-- The unit of `Γ(X, p ⁻¹ᵁ W) ⊗ Γ(X, p ⁻¹ᵁ W)` induced by `c` on the two projections. -/
noncomputable def cocycleUnit : (Γ(X, p ⁻¹ᵁ W) ⊗[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W))ˣ :=
  cAlg p c hW hW' halg Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeRight

lemma cocycleUnit_cocycle (hnat : IsNatural p c) (hmul : IsMultiplicative p c) :
    Algebra.TensorProduct.map (AlgHom.id Γ(Y, W) Γ(X, p ⁻¹ᵁ W))
        (Algebra.TensorProduct.includeRight :
          Γ(X, p ⁻¹ᵁ W) →ₐ[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W) ⊗[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W))
        (cocycleUnit p c hW hW' halg).1 =
      (Algebra.TensorProduct.includeRight :
        Γ(X, p ⁻¹ᵁ W) ⊗[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W) →ₐ[Γ(Y, W)]
          Γ(X, p ⁻¹ᵁ W) ⊗[Γ(Y, W)] (Γ(X, p ⁻¹ᵁ W) ⊗[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W)))
          (cocycleUnit p c hW hW' halg).1 *
        Algebra.TensorProduct.map (AlgHom.id Γ(Y, W) Γ(X, p ⁻¹ᵁ W))
          (Algebra.TensorProduct.includeLeft :
            Γ(X, p ⁻¹ᵁ W) →ₐ[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W) ⊗[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W))
          (cocycleUnit p c hW hW' halg).1 := by
  have e (f : Γ(X, p ⁻¹ᵁ W) ⊗[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W) →ₐ[Γ(Y, W)]
      Γ(X, p ⁻¹ᵁ W) ⊗[Γ(Y, W)] (Γ(X, p ⁻¹ᵁ W) ⊗[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W))) :
      f (cocycleUnit p c hW hW' halg).1 = (cAlg p c hW hW' halg
        (f.comp Algebra.TensorProduct.includeLeft) (f.comp Algebra.TensorProduct.includeRight)).1 := by
    rw [← cAlg_map hW hW' halg hnat]
    rfl
  rw [e, e, e, ← Units.val_mul]
  congr 1
  simp only [Algebra.TensorProduct.map_comp_includeLeft,
    Algebra.TensorProduct.map_comp_includeRight, AlgHom.comp_id]
  exact cAlg_eq_mul hW hW' halg hmul _ _ _

/-- The cocycle condition along a pair of maps factoring through the two projections
`Spec (Γ(X, p ⁻¹ᵁ W) ⊗ Γ(X, p ⁻¹ᵁ W)) ⟶ X`, for `m` with `u * (m ⊗ 1) = 1 ⊗ m`. -/
lemma mul_appLE_eq_of_factor (hnat : IsNatural p c) (m : Γ(X, p ⁻¹ᵁ W))
    (hm : (cocycleUnit p c hW hW' halg).1 * (m ⊗ₜ[Γ(Y, W)] (1 : Γ(X, p ⁻¹ᵁ W))) =
      (1 : Γ(X, p ⁻¹ᵁ W)) ⊗ₜ[Γ(Y, W)] m)
    {U : Scheme.{u}} (a b : U ⟶ X) (h : a ≫ p = b ≫ p) (ha : ⊤ ≤ a ⁻¹ᵁ p ⁻¹ᵁ W)
    (hb : ⊤ ≤ b ⁻¹ᵁ p ⁻¹ᵁ W)
    (g : U ⟶ Spec (.of (Γ(X, p ⁻¹ᵁ W) ⊗[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W))))
    (hga : g ≫ specPoint p hW' (Algebra.TensorProduct.includeLeft :
      Γ(X, p ⁻¹ᵁ W) →ₐ[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W) ⊗[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W)) = a)
    (hgb : g ≫ specPoint p hW' (Algebra.TensorProduct.includeRight :
      Γ(X, p ⁻¹ᵁ W) →ₐ[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W) ⊗[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W)) = b) :
    (c U a b h).1 * a.appLE (p ⁻¹ᵁ W) ⊤ ha m = b.appLE (p ⁻¹ᵁ W) ⊤ hb m := by
  subst hga hgb
  have hsp : specPoint p hW' (Algebra.TensorProduct.includeLeft :
        Γ(X, p ⁻¹ᵁ W) →ₐ[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W) ⊗[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W)) ≫ p =
      specPoint p hW' (Algebra.TensorProduct.includeRight :
        Γ(X, p ⁻¹ᵁ W) →ₐ[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W) ⊗[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W)) ≫ p :=
    (specPoint_comp p hW hW' halg _).trans (specPoint_comp p hW hW' halg _).symm
  have hc₀ : (c _ _ _ hsp).1 = (Scheme.ΓSpecIso _).inv (cocycleUnit p c hW hW' halg).1 := by
    rw [cocycleUnit, cAlg, Units.coe_map]
    exact (Iso.hom_inv_id_apply _ _).symm
  rw [hnat _ _ g _ _ hsp h, Units.coe_map, comp_specPoint_appLE, comp_specPoint_appLE]
  change g.appTop (c _ _ _ hsp).1 * g.appTop _ = _
  rw [hc₀]
  refine (map_mul g.appTop.hom _ _).symm.trans (congrArg g.appTop.hom ?_)
  refine (map_mul (Scheme.ΓSpecIso _).inv.hom _ _).symm.trans ?_
  exact congrArg (Scheme.ΓSpecIso _).inv.hom hm

/-- If `u * (m ⊗ 1) = 1 ⊗ m` for the unit `u` induced by `c`, then `m` is a cocycle
section over `W`. -/
lemma isCocycleSection_of_mul_eq (hnat : IsNatural p c) (m : Γ(X, p ⁻¹ᵁ W))
    (hm : (cocycleUnit p c hW hW' halg).1 * (m ⊗ₜ[Γ(Y, W)] (1 : Γ(X, p ⁻¹ᵁ W))) =
      (1 : Γ(X, p ⁻¹ᵁ W)) ⊗ₜ[Γ(Y, W)] m) :
    IsCocycleSection p c W m := by
  refine IsCocycleSection.of_top hnat fun U a b h ha hb ↦ ?_
  have hra : Set.range a ⊆ Set.range hW'.fromSpec := by
    rw [hW'.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    exact ha (Set.mem_univ x)
  have hrb : Set.range b ⊆ Set.range hW'.fromSpec := by
    rw [hW'.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    exact hb (Set.mem_univ x)
  have e : IsOpenImmersion.lift hW'.fromSpec a hra ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, W) Γ(X, p ⁻¹ᵁ W))) =
      IsOpenImmersion.lift hW'.fromSpec b hrb ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, W) Γ(X, p ⁻¹ᵁ W))) := by
    rw [← cancel_mono hW.fromSpec, Category.assoc, Category.assoc, ← fromSpec_comp p hW hW' halg,
      IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac_assoc, h]
  refine mul_appLE_eq_of_factor hW hW' halg hnat m hm a b h ha hb
    (pullback.lift _ _ e ≫ (pullbackSpecIso Γ(Y, W) Γ(X, p ⁻¹ᵁ W) Γ(X, p ⁻¹ᵁ W)).hom) ?_ ?_
  · have hL : CommRingCat.ofHom (Algebra.TensorProduct.includeLeft :
        Γ(X, p ⁻¹ᵁ W) →ₐ[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W) ⊗[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W)).toRingHom =
        CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom := rfl
    rw [specPoint, hL, Category.assoc, pullbackSpecIso_hom_fst_assoc, pullback.lift_fst_assoc,
      IsOpenImmersion.lift_fac]
  · have hR : CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        Γ(X, p ⁻¹ᵁ W) →ₐ[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W) ⊗[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W)).toRingHom =
        CommRingCat.ofHom (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
          Γ(X, p ⁻¹ᵁ W) →ₐ[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W) ⊗[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W))) := rfl
    rw [specPoint, hR, Category.assoc, pullbackSpecIso_hom_snd_assoc, pullback.lift_snd_assoc,
      IsOpenImmersion.lift_fac]

end Affine

variable (p) in
/-- Over an affine open with affine preimage, pullback of functions along a flat surjection is
faithfully flat. -/
lemma faithfullyFlat_app [Flat p] [Surjective p] {W : Y.Opens} (hW : IsAffineOpen W)
    (hW' : IsAffineOpen (p ⁻¹ᵁ W)) : (p.app W).hom.FaithfullyFlat := by
  have : IsAffine W.toScheme := hW
  have : IsAffine (p ⁻¹ᵁ W).toScheme := hW'
  have : Surjective (p ∣_ W) := IsZariskiLocalAtTarget.restrict ‹Surjective p› W
  have h₁ : (p ∣_ W).appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (p ∣_ W)).mp ⟨inferInstance, inferInstance⟩
  have e : p.app W = (W.ι.appLE W ⊤ W.ι_preimage_self.ge ≫ (p ∣_ W).appTop) ≫
      inv ((p ⁻¹ᵁ W).ι.appLE (p ⁻¹ᵁ W) ⊤ (p ⁻¹ᵁ W).ι_preimage_self.ge) := by
    rw [← app_comp_ι_appLE, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp]
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _
    (RingHom.FaithfullyFlat.stableUnderComposition _ _
      (.of_bijective (ConcreteCategory.bijective_of_isIso _)) h₁)
    (.of_bijective (ConcreteCategory.bijective_of_isIso _))

/-- For an affine, flat, surjective `p` and a natural multiplicative family `c`, every point of
`Y` has an open neighbourhood `W` carrying a cocycle section over `W` that is a unit on
`p ⁻¹ᵁ W`. -/
theorem exists_unit_cocycleSection (hA : Langlands.Algebra.UnitCocycleLocalUnitsStatement.{u})
    [IsAffineHom p] [Flat p] [Surjective p] (hnat : IsNatural p c) (hmul : IsMultiplicative p c)
    (y : Y) :
    ∃ (W : Y.Opens) (σ : Γ(X, p ⁻¹ᵁ W)), y ∈ W ∧ IsCocycleSection p c W σ ∧ IsUnit σ := by
  obtain ⟨W, hW, hyW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : Y.Opens) from trivial)
  have hW' : IsAffineOpen (p ⁻¹ᵁ W) := hW.preimage p
  let : Algebra Γ(Y, W) Γ(X, p ⁻¹ᵁ W) := (p.app W).hom.toAlgebra
  have : Module.FaithfullyFlat Γ(Y, W) Γ(X, p ⁻¹ᵁ W) := faithfullyFlat_app p hW hW'
  have halg : algebraMap Γ(Y, W) Γ(X, p ⁻¹ᵁ W) = (p.app W).hom := rfl
  have hspan := hA Γ(Y, W) Γ(X, p ⁻¹ᵁ W) (cocycleUnit p c hW hW' halg).1
    (cocycleUnit p c hW hW' halg)⁻¹.1 (cocycleUnit p c hW hW' halg).mul_inv
    (cocycleUnit_cocycle hW hW' halg hnat hmul)
  obtain ⟨⟨r, hr₀⟩, hyr⟩ :=
    TopologicalSpace.Opens.mem_iSup.mp (hW.self_le_iSup_basicOpen_iff.mpr hspan hyW)
  change y ∈ Y.basicOpen r at hyr
  obtain ⟨m, m', hm, -, hr⟩ := hr₀
  have hle : Y.basicOpen r ≤ W := Y.basicOpen_le r
  refine ⟨Y.basicOpen r, X.presheaf.map (homOfLE (p.preimage_mono hle)).op m, hyr,
    (isCocycleSection_of_mul_eq hW hW' halg hnat m hm).map hle, ?_⟩
  have hres : X.presheaf.map (homOfLE (p.preimage_mono hle)).op (p.app W r) =
      p.app (Y.basicOpen r) (Y.presheaf.map (homOfLE hle).op r) := by
    have := congrArg (fun f ↦ f r) (p.naturality (homOfLE hle).op)
    simp only [CommRingCat.comp_apply] at this
    exact this.symm
  have hunit : IsUnit (X.presheaf.map (homOfLE (p.preimage_mono hle)).op (m * m')) := by
    rw [← hr]
    change IsUnit (X.presheaf.map _ (p.app W r))
    rw [hres]
    exact (Y.toRingedSpace.isUnit_res_basicOpen r).map (p.app (Y.basicOpen r)).hom
  rw [map_mul] at hunit
  exact isUnit_of_mul_isUnit_left hunit

end Langlands.Scheme.UnitCocycleDescent
