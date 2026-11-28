import Langlands.AlgebraicGeometry.FiniteEtale.Definitions
import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Kummer covers of a punctured spectrum after a finite étale base change -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

namespace Langlands.AlgebraicGeometry.FiniteEtale.KummerCover

/-- Composition of spectra of ring homomorphisms. -/
theorem specMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C)
    (g : A →+* B) : Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom g) =
      Spec.map (CommRingCat.ofHom (f.comp g)) := by
  rw [← Spec.map_comp]
  rfl

/-- Powers of an `n`-th root of unity are `n`-th roots of unity. -/
theorem pow_pow_eq_one {M : Type*} [Monoid M] {ζ : M} {n : ℕ} (hζn : ζ ^ n = 1) (c : ℕ) :
    (ζ ^ c) ^ n = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, hζn, one_pow]

variable {R : Type u} [CommRing R] (t : R) (R' : Type u) [CommRing R'] [Algebra R R']

/-- The localization `R'[1/t]` of `R'` at the image of `t`. -/
abbrev Loc := Localization.Away (algebraMap R R' t)

/-- The ring homomorphism `R[1/t] → R'[1/t]`. -/
def locHom : Localization.Away t →+* Loc t R' :=
  IsLocalization.Away.map _ _ (algebraMap R R') t

/-- `R → R[1/t] → R'[1/t]` is `R → R' → R'[1/t]`. -/
theorem locHom_comp : (locHom t R').comp (algebraMap R (Localization.Away t)) =
    (algebraMap R' (Loc t R')).comp (algebraMap R R') := by
  unfold locHom IsLocalization.Away.map
  exact IsLocalization.map_comp _

/-- The image of `t` in `R'[1/t]`, a unit. -/
abbrev tt : Loc t R' := algebraMap R' (Loc t R') (algebraMap R R' t)

theorem isUnit_tt : IsUnit (tt t R') := IsLocalization.Away.algebraMap_isUnit _

/-- The Kummer polynomial `X ^ n - t` over `R'[1/t]`. -/
abbrev kummerPoly (n : ℕ) : (Loc t R')[X] := X ^ n - C (tt t R')

/-- The Kummer algebra `R'[1/t][X]/(X ^ n - t)`. -/
abbrev Kum (n : ℕ) := AdjoinRoot (kummerPoly t R' n)

/-- The morphism `Spec R'[1/t] ⟶ Spec R[1/t]`. -/
abbrev projU : Spec (.of (Loc t R')) ⟶ Spec (.of (Localization.Away t)) :=
  Spec.map (CommRingCat.ofHom (locHom t R'))

/-- The morphism `Spec R'[1/t][X]/(X ^ n - t) ⟶ Spec R'[1/t]`. -/
abbrev projX (n : ℕ) : Spec (.of (Kum t R' n)) ⟶ Spec (.of (Loc t R')) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Loc t R') (Kum t R' n)))

/-- `Spec R'[1/t] → Spec R[1/t] → Spec R` is `Spec R'[1/t] → Spec R' → Spec R`. -/
theorem projU_comp : projU t R' ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t))) =
    Spec.map (CommRingCat.ofHom (algebraMap R' (Loc t R'))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
  rw [specMap_comp, specMap_comp, locHom_comp]

theorem isFinite_projU [Module.Finite R R'] : IsFinite (projU t R') := by
  rw [IsFinite.SpecMap_iff]
  exact RingHom.localization_away_map_finite R R' _ _ (algebraMap R R') t
    (RingHom.finite_algebraMap.mpr inferInstance)

theorem etale_projU [Algebra.Etale R R'] : Etale (projU t R') := by
  have h₁ : Etale (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  have : Etale (projU t R' ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t)))) := by
    rw [projU_comp]
    infer_instance
  exact Etale.of_comp _ (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t))))

theorem isFinite_projX (n : ℕ) (hn0 : n ≠ 0) : IsFinite (projX t R' n) := by
  rw [IsFinite.SpecMap_iff]
  have := (monic_X_pow_sub_C (tt t R') hn0).finite_adjoinRoot
  exact RingHom.finite_algebraMap.mpr this

theorem etale_projX (n : ℕ) (hn0 : n ≠ 0) (hn : IsUnit (n : R)) : Etale (projX t R' n) := by
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  have hn' : IsUnit (n : Loc t R') := by
    simpa only [map_natCast] using hn.map (algebraMap R (Loc t R'))
  exact RingHom.etale_algebraMap.mpr (AdjoinRoot.etale_X_pow_sub_C hn0 hn' (isUnit_tt t R'))

theorem root_pow (n : ℕ) : AdjoinRoot.root (kummerPoly t R' n) ^ n =
    AdjoinRoot.of (kummerPoly t R' n) (tt t R') := by
  have h := AdjoinRoot.eval₂_root (kummerPoly t R' n)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  exact sub_eq_zero.mp h

/-- The ring endomorphism of the Kummer algebra that is the identity on `R'[1/t]` and
multiplies the root by an element `u` of `R'` with `u ^ n = 1`. For `n ≠ 0` it is an
automorphism, with inverse `kappa (u ^ (n - 1))` by `kappa_comp_kappa`. -/
def kappa {n : ℕ} (u : R') (hu : u ^ n = 1) : Kum t R' n →+* Kum t R' n :=
  AdjoinRoot.lift (AdjoinRoot.of _)
    (AdjoinRoot.of _ (algebraMap R' (Loc t R') u) * AdjoinRoot.root _) (by
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, mul_pow, ← map_pow, ← map_pow, hu, map_one, map_one,
        one_mul, root_pow, sub_self])

theorem kappa_comp_of {n : ℕ} (u : R') (hu : u ^ n = 1) :
    (kappa t R' u hu).comp (AdjoinRoot.of _) = AdjoinRoot.of _ :=
  AdjoinRoot.lift_comp_of _

theorem kappa_root {n : ℕ} (u : R') (hu : u ^ n = 1) :
    kappa t R' u hu (AdjoinRoot.root _) =
      AdjoinRoot.of _ (algebraMap R' (Loc t R') u) * AdjoinRoot.root _ :=
  AdjoinRoot.lift_root _

/-- Composition of the root-scaling maps multiplies the roots of unity. -/
theorem kappa_comp_kappa {n : ℕ} (u v : R') (hu : u ^ n = 1) (hv : v ^ n = 1) :
    (kappa t R' u hu).comp (kappa t R' v hv) =
      kappa t R' (u * v) (by rw [mul_pow, hu, hv, one_mul]) := by
  apply AdjoinRoot.ringHom_ext
  · rw [RingHom.comp_assoc, kappa_comp_of, kappa_comp_of, kappa_comp_of]
  · rw [RingHom.comp_apply, kappa_root, kappa_root, map_mul, kappa_root,
      ← RingHom.comp_apply (kappa t R' u hu) (AdjoinRoot.of _), kappa_comp_of, map_mul, map_mul]
    ring

variable {t R'} in
/-- The endomorphism of `R'[1/t]` induced by an `R`-algebra endomorphism `α` of `R'`. -/
def locEnd (α : R' →ₐ[R] R') : Loc t R' →+* Loc t R' :=
  IsLocalization.Away.lift (algebraMap R R' t)
    (g := (algebraMap R' (Loc t R')).comp α.toRingHom) (by
      simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
        using isUnit_tt t R')

theorem locEnd_algebraMap (α : R' →ₐ[R] R') (x : R') :
    locEnd (t := t) α (algebraMap R' (Loc t R') x) = algebraMap R' (Loc t R') (α x) :=
  IsLocalization.Away.lift_eq _ _ _

theorem locEnd_tt (α : R' →ₐ[R] R') : locEnd α (tt t R') = tt t R' := by
  rw [locEnd_algebraMap, AlgHom.commutes]

theorem locEnd_comp_locHom (α : R' →ₐ[R] R') :
    (locEnd (t := t) α).comp (locHom t R') = locHom t R' := by
  apply IsLocalization.ringHom_ext (Submonoid.powers t)
  ext x
  have h := RingHom.congr_fun (locHom_comp t R') x
  simp only [RingHom.comp_apply] at h ⊢
  rw [h, locEnd_algebraMap, AlgHom.commutes]

variable {t R'} in
/-- The endomorphism of the Kummer algebra which is `locEnd α` on `R'[1/t]` and fixes the
root. -/
def kumEnd {n : ℕ} (α : R' →ₐ[R] R') : Kum t R' n →+* Kum t R' n :=
  AdjoinRoot.lift ((AdjoinRoot.of _).comp (locEnd α)) (AdjoinRoot.root _) (by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, RingHom.comp_apply, locEnd_tt, root_pow, sub_self])

theorem kumEnd_comp_of {n : ℕ} (α : R' →ₐ[R] R') :
    (kumEnd (t := t) (n := n) α).comp (AdjoinRoot.of _) = (AdjoinRoot.of _).comp (locEnd α) :=
  AdjoinRoot.lift_comp_of _

theorem kumEnd_root {n : ℕ} (α : R' →ₐ[R] R') :
    kumEnd (t := t) (n := n) α (AdjoinRoot.root _) = AdjoinRoot.root _ :=
  AdjoinRoot.lift_root _

/-- `kumEnd α` intertwines scaling the root by `u` and by `α u`. -/
theorem kumEnd_comp_kappa {n : ℕ} (α : R' →ₐ[R] R') (u : R') (hu : u ^ n = 1) :
    (kumEnd α).comp (kappa t R' u hu) =
      (kappa t R' (α u) (by rw [← map_pow, hu, map_one])).comp (kumEnd α) := by
  apply AdjoinRoot.ringHom_ext
  · rw [RingHom.comp_assoc, kappa_comp_of, RingHom.comp_assoc, kumEnd_comp_of,
      ← RingHom.comp_assoc, kappa_comp_of]
  · rw [RingHom.comp_apply, RingHom.comp_apply, kappa_root, kumEnd_root, kappa_root, map_mul,
      kumEnd_root, ← RingHom.comp_apply (kumEnd α) (AdjoinRoot.of _), kumEnd_comp_of,
      RingHom.comp_apply, locEnd_algebraMap]


theorem kappa_congr {n : ℕ} {u v : R'} (h : u = v) (hu : u ^ n = 1) (hv : v ^ n = 1) :
    kappa t R' u hu = kappa t R' v hv := by
  subst h
  rfl

theorem kappa_one {n : ℕ} : kappa t R' (n := n) 1 (one_pow n) = RingHom.id _ := by
  apply AdjoinRoot.ringHom_ext
  · rw [kappa_comp_of, RingHom.id_comp]
  · rw [kappa_root, map_one, map_one, one_mul, RingHom.id_apply]

/-- `R[1/t] → R'[1/t]` is injective when `R → R'` is. -/
theorem locHom_injective (hinj : Function.Injective (algebraMap R R')) :
    Function.Injective (locHom t R') := by
  unfold locHom
  refine (IsLocalization.Away.map_injective_iff _ _ _).mpr fun a ha => ⟨0, ?_⟩
  rw [pow_zero, one_mul]
  exact hinj (ha.trans (map_zero _).symm)

/-- A nontrivial ring injects into its Kummer algebra of positive degree. -/
theorem of_injective [Nontrivial (Loc t R')] {n : ℕ} (hn0 : n ≠ 0) :
    Function.Injective (AdjoinRoot.of (kummerPoly t R' n)) := by
  have hdeg : 0 < (kummerPoly t R' n).degree := by
    rw [degree_X_pow_sub_C (Nat.pos_of_ne_zero hn0)]
    exact_mod_cast Nat.pos_of_ne_zero hn0
  exact AdjoinRoot.of.injective_of_monic_of_degree_pos (monic_X_pow_sub_C _ hn0) hdeg

section Covers

variable [Module.Finite R R'] [Algebra.Etale R R'] (n : ℕ)

/-- `Spec R'[1/t]` as a finite étale cover of `Spec R[1/t]`. -/
def coverU : Cover (Spec (.of (Localization.Away t))) :=
  @cover _ _ (projU t R') (isFinite_projU t R') (etale_projU t R')

omit [Algebra.Etale R R'] in
theorem isFinite_projXU (hn0 : n ≠ 0) : IsFinite (projX t R' n ≫ projU t R') := by
  have := isFinite_projX t R' n hn0
  have := isFinite_projU t R'
  infer_instance

omit [Module.Finite R R'] in
theorem etale_projXU (hn0 : n ≠ 0) (hn : IsUnit (n : R)) : Etale (projX t R' n ≫ projU t R') := by
  have := etale_projX t R' n hn0 hn
  have := etale_projU t R'
  infer_instance

/-- `Spec R'[1/t][X]/(X ^ n - t)` as a finite étale cover of `Spec R[1/t]`. -/
def coverX (hn0 : n ≠ 0) (hn : IsUnit (n : R)) : Cover (Spec (.of (Localization.Away t))) :=
  @cover _ _ (projX t R' n ≫ projU t R') (isFinite_projXU t R' n hn0)
    (etale_projXU t R' n hn0 hn)

/-- The projection of the Kummer cover onto `Spec R'[1/t]`, a map of covers. -/
def proj (hn0 : n ≠ 0) (hn : IsUnit (n : R)) : coverX t R' n hn0 hn ⟶ coverU t R' :=
  ObjectProperty.homMk (Over.homMk (projX t R' n) rfl)

/-- The endomorphism of the Kummer cover given by a ring endomorphism of the Kummer algebra
over `R[1/t]`. -/
def kumHom (hn0 : n ≠ 0) (hn : IsUnit (n : R)) (e : Kum t R' n →+* Kum t R' n)
    (he : (e.comp (algebraMap (Loc t R') (Kum t R' n))).comp (locHom t R') =
      (algebraMap (Loc t R') (Kum t R' n)).comp (locHom t R')) :
    coverX t R' n hn0 hn ⟶ coverX t R' n hn0 hn :=
  ObjectProperty.homMk (Over.homMk (Spec.map (CommRingCat.ofHom e)) (by
    change Spec.map _ ≫ projX t R' n ≫ projU t R' = projX t R' n ≫ projU t R'
    rw [specMap_comp, specMap_comp, ← RingHom.comp_assoc, he]))

theorem kumHom_left (hn0 : n ≠ 0) (hn : IsUnit (n : R)) (e : Kum t R' n →+* Kum t R' n) (he) :
    (kumHom t R' n hn0 hn e he).hom.left = Spec.map (CommRingCat.ofHom e) := rfl

theorem proj_left (hn0 : n ≠ 0) (hn : IsUnit (n : R)) : (proj t R' n hn0 hn).hom.left = projX t R' n := rfl

theorem kumHom_comp_proj (hn0 : n ≠ 0) (hn : IsUnit (n : R)) (e : Kum t R' n →+* Kum t R' n) (he)
    (he' : e.comp (algebraMap (Loc t R') (Kum t R' n)) = algebraMap (Loc t R') (Kum t R' n)) :
    kumHom t R' n hn0 hn e he ≫ proj t R' n hn0 hn = proj t R' n hn0 hn := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  rw [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, kumHom_left, proj_left,
    specMap_comp, he']

/-- The endomorphism of the Kummer cover induced by an `R`-algebra endomorphism `α` of `R'`,
fixing the root. -/
def AX (hn0 : n ≠ 0) (hn : IsUnit (n : R)) (α : R' →ₐ[R] R') :
    coverX t R' n hn0 hn ⟶ coverX t R' n hn0 hn :=
  kumHom t R' n hn0 hn (kumEnd α) (by
    rw [AdjoinRoot.algebraMap_eq, kumEnd_comp_of, RingHom.comp_assoc, locEnd_comp_locHom])

theorem AX_left (hn0 : n ≠ 0) (hn : IsUnit (n : R)) (α : R' →ₐ[R] R') :
    (AX t R' n hn0 hn α).hom.left = Spec.map (CommRingCat.ofHom (kumEnd α)) := rfl

/-- The endomorphism of `Spec R'[1/t]` induced by `α`, as a map of covers. -/
def AU (α : R' →ₐ[R] R') : coverU t R' ⟶ coverU t R' :=
  ObjectProperty.homMk (Over.homMk (Spec.map (CommRingCat.ofHom (locEnd (t := t) α))) (by
    change Spec.map _ ≫ projU t R' = projU t R'
    rw [specMap_comp, locEnd_comp_locHom]))

/-- `AX α` lies over `AU α`. -/
theorem AX_comp_proj (hn0 : n ≠ 0) (hn : IsUnit (n : R)) (α : R' →ₐ[R] R') :
    AX t R' n hn0 hn α ≫ proj t R' n hn0 hn = proj t R' n hn0 hn ≫ AU t R' α := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    Over.comp_left, Over.comp_left, AX_left, proj_left]
  change _ = _ ≫ Spec.map (CommRingCat.ofHom (locEnd (t := t) α))
  rw [specMap_comp, specMap_comp, AdjoinRoot.algebraMap_eq, kumEnd_comp_of]

variable {n} {ζ : R'}

variable (hn0 : n ≠ 0) (hn : IsUnit (n : R)) (hζn : ζ ^ n = 1)

/-- The automorphism of the Kummer cover multiplying the root by `ζ ^ c` (its inverse is
`K ((n - 1) * c)`, by `K_comp_K` and `ζ ^ n = 1`). -/
def K (c : ℕ) : coverX t R' n hn0 hn ⟶ coverX t R' n hn0 hn :=
  kumHom t R' n hn0 hn (kappa t R' (ζ ^ c) (pow_pow_eq_one hζn c)) (by
    rw [AdjoinRoot.algebraMap_eq, kappa_comp_of])

theorem K_left (c : ℕ) : (K t R' hn0 hn hζn c).hom.left =
    Spec.map (CommRingCat.ofHom (kappa t R' (ζ ^ c) (pow_pow_eq_one hζn c))) := rfl

/-- `K c` lies over the identity of `Spec R'[1/t]`. -/
theorem K_comp_proj (c : ℕ) : K t R' hn0 hn hζn c ≫ proj t R' n hn0 hn = proj t R' n hn0 hn :=
  kumHom_comp_proj t R' n hn0 hn _ _ (by rw [AdjoinRoot.algebraMap_eq, kappa_comp_of])

/-- `K c ≫ K d = K (c + d)`. -/
theorem K_comp_K (c d : ℕ) : K t R' hn0 hn hζn c ≫ K t R' hn0 hn hζn d =
    K t R' hn0 hn hζn (c + d) := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  rw [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, K_left, K_left, K_left,
    specMap_comp, kappa_comp_kappa]
  congr 2
  exact kappa_congr t R' (by rw [pow_add]) _ _

theorem K_zero : K t R' hn0 hn hζn 0 = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  rw [K_left, ObjectProperty.FullSubcategory.id_hom, Over.id_left,
    kappa_congr t R' (pow_zero ζ) _ (one_pow n), kappa_one, CommRingCat.ofHom_id, Spec.map_id]
  rfl

/-- **Commutation relation.** If `α ζ = ζ ^ q`, then `AX α ≫ K c = K (q * c) ≫ AX α`. -/
theorem AX_comp_K (α : R' →ₐ[R] R') {q : ℕ} (hα : α ζ = ζ ^ q) (c : ℕ) :
    AX t R' n hn0 hn α ≫ K t R' hn0 hn hζn c = K t R' hn0 hn hζn (q * c) ≫ AX t R' n hn0 hn α := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    Over.comp_left, Over.comp_left, AX_left, K_left, K_left, specMap_comp, specMap_comp,
    kumEnd_comp_kappa]
  congr 3
  exact kappa_congr t R' (by rw [map_pow, hα, ← pow_mul]) _ _

/-- **Fibres of the Kummer cover.** If `ζ ^ l - 1` is a unit for `0 < l < n`, two geometric
points of the Kummer cover with the same image in `Spec R'[1/t]` differ by some `K c`. -/
theorem exists_eq_comp_K (hζ : ∀ l, 0 < l → l < n → IsUnit (ζ ^ l - 1)) {Ω : Type u} [Field Ω]
    {x : Spec (.of Ω) ⟶ Spec (.of (Localization.Away t))}
    (p₁ p₂ : Fiber x (coverX t R' n hn0 hn))
    (h : p₁ ≫ (proj t R' n hn0 hn).hom = p₂ ≫ (proj t R' n hn0 hn).hom) :
    ∃ c : ℕ, p₂ = p₁ ≫ (K t R' hn0 hn hζn c).hom := by
  classical
  have : NeZero n := ⟨hn0⟩
  obtain ⟨f₁, hf₁⟩ : ∃ f, Spec.map f = p₁.left := ⟨_, Spec.map_preimage _⟩
  obtain ⟨f₂, hf₂⟩ : ∃ f, Spec.map f = p₂.left := ⟨_, Spec.map_preimage _⟩
  have hl : p₁.left ≫ projX t R' n = p₂.left ≫ projX t R' n := congrArg (fun p => p.left) h
  rw [← hf₁, ← hf₂, ← Spec.map_comp, ← Spec.map_comp] at hl
  have hof : f₁.hom.comp (AdjoinRoot.of (kummerPoly t R' n)) =
      f₂.hom.comp (AdjoinRoot.of (kummerPoly t R' n)) := by
    have := congrArg CommRingCat.Hom.hom (Spec.map_injective hl)
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, AdjoinRoot.algebraMap_eq] using this
  have hT : f₁.hom (AdjoinRoot.of _ (tt t R')) ≠ 0 :=
    (((isUnit_tt t R').map (AdjoinRoot.of (kummerPoly t R' n))).map f₁.hom).ne_zero
  have hr₁ : f₁.hom (AdjoinRoot.root _) ^ n = f₁.hom (AdjoinRoot.of _ (tt t R')) := by
    rw [← map_pow, root_pow]
  have hr₂ : f₂.hom (AdjoinRoot.root _) ^ n = f₁.hom (AdjoinRoot.of _ (tt t R')) := by
    rw [← map_pow, root_pow, ← RingHom.comp_apply, ← hof, RingHom.comp_apply]
  have hr₁0 : f₁.hom (AdjoinRoot.root _) ≠ 0 := fun h0 => hT (by rw [← hr₁, h0, zero_pow hn0])
  have hξ : (f₂.hom (AdjoinRoot.root _) / f₁.hom (AdjoinRoot.root _)) ^ n = 1 := by
    rw [div_pow, hr₁, hr₂, div_self hT]
  let φ : R' →+* Ω := f₁.hom.comp ((AdjoinRoot.of (kummerPoly t R' n)).comp
    (algebraMap R' (Loc t R')))
  have hprim : IsPrimitiveRoot (φ ζ) n := by
    refine IsPrimitiveRoot.mk_of_lt (φ ζ) (Nat.pos_of_ne_zero hn0)
      (by rw [← map_pow, hζn, map_one]) fun l hl0 hln heq => ?_
    have hu := (hζ l hl0 hln).map φ
    rw [map_sub, map_pow, heq, map_one, sub_self] at hu
    exact not_isUnit_zero hu
  obtain ⟨c, -, hc⟩ := hprim.eq_pow_of_pow_eq_one hξ
  refine ⟨c, Over.OverMorphism.ext ?_⟩
  rw [Over.comp_left, K_left, ← hf₁, ← hf₂, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  apply AdjoinRoot.ringHom_ext
  · rw [RingHom.comp_assoc, kappa_comp_of, hof]
  · rw [RingHom.comp_apply, kappa_root, map_mul]
    change f₂.hom (AdjoinRoot.root _) = φ (ζ ^ c) * f₁.hom (AdjoinRoot.root _)
    rw [map_pow, hc, div_mul_cancel₀ _ hr₁0]

omit hζn in
/-- **Nonempty geometric fibres.** If `R'` is a domain into which `R` injects and `t ≠ 0` in
`R'`, every geometric point of `Spec R[1/t]` with separably closed field lifts to the Kummer
cover. -/
theorem nonempty_fiber [IsDomain R'] (hinj : Function.Injective (algebraMap R R'))
    (ht : algebraMap R R' t ≠ 0) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ Spec (.of (Localization.Away t))) :
    Nonempty (Fiber x (coverX t R' n hn0 hn)) := by
  have : IsDomain (Loc t R') := IsLocalization.isDomain_of_le_nonZeroDivisors _
    (M := Submonoid.powers (algebraMap R R' t)) (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
  have hfin := isFinite_projXU t R' n hn0
  have het := etale_projXU t R' n hn0 hn
  have hfin' : IsFinite (Spec.map (CommRingCat.ofHom
      ((algebraMap (Loc t R') (Kum t R' n)).comp (locHom t R')))) := by
    rw [← specMap_comp]
    exact hfin
  rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom] at hfin'
  have hinj' : Function.Injective ((algebraMap (Loc t R') (Kum t R' n)).comp (locHom t R')) := by
    rw [RingHom.coe_comp, AdjoinRoot.algebraMap_eq]
    exact (of_injective t R' hn0).comp (locHom_injective t R' hinj)
  obtain ⟨y, hy⟩ := (RingHom.IsIntegral.of_finite hfin').comap_surjective hinj'
    (x (IsLocalRing.closedPoint Ω))
  obtain ⟨r, hr⟩ := Scheme.Hom.exists_lift_of_isSepClosed (projX t R' n ≫ projU t R') x
    ⟨IsLocalRing.closedPoint Ω, y, by rw [specMap_comp]; exact hy⟩
  exact ⟨Over.homMk r hr⟩

end Covers

end Langlands.AlgebraicGeometry.FiniteEtale.KummerCover
