import Langlands.AlgebraicGeometry.AlgebraicSpace.DilatedLineChain
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsNotClosedCharts
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopologyUniqueness
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# A separated locally finite type space whose integral points are not closed

The closedness assertion of Conrad's Corollary 5.7 fails without quasi-compactness. Over the
closed unit ball `O` of a nontrivially normed field `K`, choose `p ∈ O` with `0 < ‖p‖ < 1`.
Glue the affine lines `Spec O[u_j]`, `j ∈ ℕ`, along `Spec O[t][1/p]` by `t = p^j + p^(j+1) u_j`
(`DilatedLineChain`). The result `X` is separated and locally of finite type over `O`.

The `O`-point `u_n = 0` of the `n`-th line is the point `t = pⁿ`, which is the point
`u_0 = (pⁿ - 1)/p` of the line `0`. These converge to `u_0 = -1/p`, that is `t = 0`, which is
not the image of an `O`-point: on the `j`-th line it would have coordinate `u_j = -1/p ∉ O`.
So the image of `X(O)` in `X_K(K)` is not closed. Separatedness is proved with the valuative
criterion: two points over a valuation ring `V` that agree over its fraction field either lie
on the same line, or force `p` to be a unit in `V` and then lie in the common open.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology Polynomial Filter
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint ringTest ringTestMap ringTestMap_comp schemePointTopology ringBaseChange
    ringPointBaseChangeEquiv schemeBaseChangeTopology_proof affineRingPointEquiv)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open HenselianIntegralPointsNotClosed

namespace HenselianIntegralPointsNotClosed

/-- A scheme whose structure morphism is separated is a separated algebraic space. -/
theorem isSeparated_schemeToSpace {S : Scheme.{u}} (U : Over S)
    [_root_.AlgebraicGeometry.IsSeparated U.hom] : IsSeparated ((schemeToSpace S).obj U) := by
  have : MorphismProperty.RespectsIso @_root_.AlgebraicGeometry.IsClosedImmersion.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact relative_diag_schemeYoneda @_root_.AlgebraicGeometry.IsClosedImmersion U inferInstance

end HenselianIntegralPointsNotClosed

namespace DilatedLineChain

variable (R : Type u) [CommRing R] (p : R)

section Algebra

variable {R p} {B : Type u} [CommRing B]

/-- Maps out of the common open are determined on the coordinate of one line. -/
theorem σ_ext (j : ℕ) {f f' : L R p →+* B} (h : f.comp (σ R p j) = f'.comp (σ R p j)) :
    f = f' := by
  have h' : f.comp (σ' R p j) = f'.comp (σ' R p j) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (C p : R[X]))
    rw [RingHom.comp_assoc, RingHom.comp_assoc, σ'_comp, h]
  calc f = (f.comp (σ' R p j)).comp (τ' R p j) := by
        rw [RingHom.comp_assoc, σ'_τ', RingHom.comp_id]
    _ = (f'.comp (σ' R p j)).comp (τ' R p j) := by rw [h']
    _ = f' := by rw [RingHom.comp_assoc, σ'_τ', RingHom.comp_id]

/-- A map out of the `j`-th line sending `p` to a unit factors through the common open. -/
theorem exists_comp_σ (j : ℕ) (φ : R[X] →+* B) (hφ : IsUnit (φ (C p))) :
    ∃ ν : L R p →+* B, ν.comp (σ R p j) = φ := by
  refine ⟨(IsLocalization.Away.lift (C p) hφ).comp (τ' R p j), ?_⟩
  rw [← σ'_comp, RingHom.comp_assoc, ← RingHom.comp_assoc (algebraMap R[X] (L R p)),
    τ'_σ', RingHom.id_comp, IsLocalization.Away.lift_comp]

/-- The coordinate of the `j`-th line under a map out of the common open. -/
theorem comp_σ_X (j : ℕ) (ω : L R p →+* B) :
    ω (σ R p j X) = (ω (T R p) - ω (P R p) ^ j) * ω (e R p) ^ (j + 1) := by
  rw [σ_X, map_mul, map_sub, map_pow, map_pow]

/-- Under a map out of the common open, `t = p^j + p^(j+1) u_j`. -/
theorem t_eq (j : ℕ) (ω : L R p →+* B) :
    ω (T R p) = ω (P R p) ^ j + ω (P R p) ^ (j + 1) * ω (σ R p j X) := by
  have h : ω (P R p) * ω (e R p) = 1 := by rw [← map_mul, P_mul_e, map_one]
  have h' : ω (P R p) ^ (j + 1) * ω (e R p) ^ (j + 1) = 1 := by rw [← mul_pow, h, one_pow]
  rw [comp_σ_X]
  linear_combination (ω (P R p) ^ j - ω (T R p)) * h'

/-- If two points of different lines over a domain have the same `t`, then `p` is a unit. -/
theorem isUnit_of_eq [IsDomain B] {π α β : B} (hπ : π ≠ 0) {i j : ℕ} (hij : i ≠ j)
    (h : π ^ i + π ^ (i + 1) * α = π ^ j + π ^ (j + 1) * β) : IsUnit π := by
  wlog hlt : i < j generalizing i j α β
  · exact this (Ne.symm hij) h.symm (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hij))
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hlt
  have h₁ : π ^ i * (1 + π * α) = π ^ i * (π ^ (m + 1) * (1 + π * β)) := by
    linear_combination h
  have h₂ := mul_left_cancel₀ (pow_ne_zero i hπ) h₁
  exact IsUnit.of_mul_eq_one (π ^ m * (1 + π * β) - α) (by linear_combination -h₂)

end Algebra

/-- The glued scheme as a scheme over `Spec R`. -/
def overBase : Over (Spec (CommRingCat.of R)) := Over.mk (toBase R p)

/-- The lines as morphisms over `Spec R`. -/
def chart (j : ULift.{u} ℕ) : ringTest R R[X] ⟶ overBase R p :=
  Over.homMk (ι R p j) (ι_toBase R p j)

@[simp] theorem chart_left (j : ULift.{u} ℕ) : (chart R p j).left = ι R p j := rfl

/-- The point of the glued scheme given by a point of the line `j`. -/
def chartPoint {B : Type u} [CommRing B] [Algebra R B] (j : ULift.{u} ℕ)
    (q : RingPoint R (ringTest R R[X]) B) : RingPoint R (overBase R p) B :=
  q ≫ chart R p j

instance : QuasiSeparatedSpace (glued R p) :=
  CommonOpenGluing.quasiSeparatedSpace

instance quasiSeparated_hom : QuasiSeparated (overBase R p).hom :=
  (quasiSeparated_iff_quasiSeparatedSpace (overBase R p).hom).mpr
    (inferInstanceAs (QuasiSeparatedSpace (glued R p)))

set_option backward.isDefEq.respectTransparency false in
theorem locallyOfFiniteType_hom : LocallyOfFiniteType (overBase R p).hom := by
  refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (CommonOpenGluing.glueData _ _ (g R p)).openCover fun j => ?_
  change LocallyOfFiniteType (ι R p j ≫ toBase R p)
  rw [ι_toBase]
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

variable {R p}

/-- Two morphisms from the spectrum of a local domain `V` to the glued scheme that agree on
the spectrum of a field containing `V` are equal. -/
theorem eq_of_comp_eq {V F : Type u} [CommRing V] [IsDomain V] [IsLocalRing V] [Field F]
    [Algebra V F] (hinj : Function.Injective (algebraMap V F))
    (l₁ l₂ : Spec (CommRingCat.of V) ⟶ glued R p)
    (h : Spec.map (CommRingCat.ofHom (algebraMap V F)) ≫ l₁ =
      Spec.map (CommRingCat.ofHom (algebraMap V F)) ≫ l₂) : l₁ = l₂ := by
  obtain ⟨i, a₀, rfl⟩ := CommonOpenGluing.exists_lift_of_isLocalRing (g := g R p) l₁
  obtain ⟨j, b₀, rfl⟩ := CommonOpenGluing.exists_lift_of_isLocalRing (g := g R p) l₂
  let a : Spec (CommRingCat.of V) ⟶ Spec (CommRingCat.of R[X]) := a₀
  let b : Spec (CommRingCat.of V) ⟶ Spec (CommRingCat.of R[X]) := b₀
  let s : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of V) :=
    Spec.map (CommRingCat.ofHom (algebraMap V F))
  have h' : (s ≫ a) ≫ ι R p i = (s ≫ b) ≫ ι R p j := by
    simpa only [Category.assoc] using h
  have hα : Spec.map (Spec.preimage a) = a := Spec.map_preimage a
  have hβ : Spec.map (Spec.preimage b) = b := Spec.map_preimage b
  set α' := (Spec.preimage a).hom
  set β' := (Spec.preimage b).hom
  by_cases hij : i = j
  · subst hij
    have hab : s ≫ a = s ≫ b := (cancel_mono (ι R p i)).1 h'
    have hring₀ : Spec.preimage a ≫ CommRingCat.ofHom (algebraMap V F) =
        Spec.preimage b ≫ CommRingCat.ofHom (algebraMap V F) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_comp, hα, hβ]
      exact hab
    have hring : (algebraMap V F).comp α' = (algebraMap V F).comp β' := by
      have := congrArg (fun φ => φ.hom) hring₀
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] using this
    have : α' = β' :=
      RingHom.ext fun q => hinj (congrArg (fun φ => φ q) hring)
    change a ≫ ι R p i = b ≫ ι R p i
    rw [← hα, ← hβ]
    exact congrArg (fun φ => Spec.map φ ≫ ι R p i) (CommRingCat.hom_ext this)
  · obtain ⟨w₀, hw₁, hw₂⟩ := CommonOpenGluing.exists_of_comp_eq _ _ (g R p) hij _ _ h'
    let w : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of (L R p)) := w₀
    let ω := (Spec.preimage w).hom
    have hω : ∀ (k : ULift.{u} ℕ) (c : Spec (CommRingCat.of V) ⟶ Spec (CommRingCat.of R[X])),
        w ≫ g R p k = s ≫ c → ω.comp (σ R p k.down) = (algebraMap V F).comp
          (Spec.preimage c).hom := by
      intro k c hc
      have h₀ : CommRingCat.ofHom (σ R p k.down) ≫ Spec.preimage w =
          Spec.preimage c ≫ CommRingCat.ofHom (algebraMap V F) := by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
        exact hc
      have := congrArg (fun φ => φ.hom) h₀
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] using this
    have hωa := hω i a hw₁
    have hωb := hω j b hw₂
    have hP : ∀ (k : ULift.{u} ℕ) (φ : R[X] →+* V), ω.comp (σ R p k.down) =
        (algebraMap V F).comp φ → ω (P R p) = algebraMap V F (φ (C p)) := by
      intro k φ hφ
      have h₀ : ω (P R p) = ω (σ R p k.down (C p)) := by rw [σ_C]
      rw [h₀, ← RingHom.comp_apply, hφ, RingHom.comp_apply]
    have hX : ∀ (k : ULift.{u} ℕ) (φ : R[X] →+* V), ω.comp (σ R p k.down) =
        (algebraMap V F).comp φ → ω (σ R p k.down X) = algebraMap V F (φ X) := by
      intro k φ hφ
      rw [← RingHom.comp_apply, hφ, RingHom.comp_apply]
    let π := α' (C p)
    have hππ : β' (C p) = π := hinj ((hP j β' hωb).symm.trans (hP i α' hωa))
    have hωP : ω (P R p) * ω (e R p) = 1 := by rw [← map_mul, P_mul_e, map_one]
    have hπ : π ≠ 0 := by
      intro h0
      have : ω (P R p) = 0 := by rw [hP i α' hωa]; simp [π, h0]
      rw [this, zero_mul] at hωP
      exact zero_ne_one hωP
    have heq : π ^ i.down + π ^ (i.down + 1) * α' X =
        π ^ j.down + π ^ (j.down + 1) * β' X := by
      apply hinj
      have ti := t_eq i.down ω
      have tj := t_eq j.down ω
      rw [hP i α' hωa, hX i α' hωa] at ti
      rw [hP j β' hωb, hX j β' hωb, hππ] at tj
      simp only [map_add, map_mul, map_pow]
      exact ti.symm.trans tj
    have hunit : IsUnit π :=
      isUnit_of_eq hπ (fun h => hij (ULift.ext _ _ h)) heq
    obtain ⟨νa, hνa⟩ := exists_comp_σ i.down α' hunit
    obtain ⟨νb, hνb⟩ := exists_comp_σ j.down β' (hππ ▸ hunit)
    have hν : νa = νb := by
      have e₁ : (algebraMap V F).comp νa = ω := σ_ext i.down (by
        rw [RingHom.comp_assoc, hνa, hωa])
      have e₂ : (algebraMap V F).comp νb = ω := σ_ext j.down (by
        rw [RingHom.comp_assoc, hνb, hωb])
      exact RingHom.ext fun x => hinj (by
        have := congrArg (fun φ => φ x) (e₁.trans e₂.symm)
        simpa only [RingHom.comp_apply] using this)
    have ha : a = Spec.map (CommRingCat.ofHom νa) ≫ g R p i := by
      rw [← hα, g, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hνa]
      rfl
    have hb : b = Spec.map (CommRingCat.ofHom νb) ≫ g R p j := by
      rw [← hβ, g, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hνb]
      rfl
    change a ≫ ι R p i = b ≫ ι R p j
    rw [ha, hb, hν, Category.assoc, Category.assoc, CommonOpenGluing.g_ι _ _ (g R p) i j]

variable (R p)

/-- The glued scheme is separated over `Spec R` (valuative criterion). -/
instance isSeparated_hom : _root_.AlgebraicGeometry.IsSeparated (overBase R p).hom := by
  refine _root_.AlgebraicGeometry.IsSeparated.of_valuativeCriterion _ fun S => ?_
  constructor
  rintro ⟨l₁, hl₁, -⟩ ⟨l₂, hl₂, -⟩
  ext : 1
  exact eq_of_comp_eq (IsFractionRing.injective S.R S.K) l₁ l₂ (hl₁.trans hl₂.symm)

/-- The space of the glued scheme is separated. -/
theorem isSeparated : IsSeparated ((schemeToSpace _).obj (overBase R p)) :=
  isSeparated_schemeToSpace _

/-- The space of the glued scheme is locally of finite type. -/
theorem locallyOfFiniteTypeOverBase :
    LocallyOfFiniteTypeOverBase ((schemeToSpace _).obj (overBase R p)) :=
  HasAtlasProperty.of_scheme _ (locallyOfFiniteType_hom R p)

section Points

variable {R p}

/-- Each line of the glued scheme is an open immersion. -/
instance (j : ULift.{u} ℕ) : _root_.AlgebraicGeometry.IsOpenImmersion (chart R p j).left :=
  inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion (ι R p j))

instance (j : ULift.{u} ℕ) : Mono (chart R p j) := by
  have : Mono (chart R p j).left := inferInstance
  exact (Over.forget _).mono_of_mono_map this

/-- Over a local ring, every point of the glued scheme factors through one of the lines. -/
theorem exists_chart_factor {S : Type u} [CommRing S] [Algebra R S] [IsLocalRing S]
    (x : RingPoint R (overBase R p) S) :
    ∃ (j : ULift.{u} ℕ) (a : RingPoint R (ringTest R R[X]) S), a ≫ chart R p j = x := by
  obtain ⟨j, a₀, ha₀⟩ := CommonOpenGluing.exists_lift_of_isLocalRing (g := g R p) x.left
  refine ⟨j, Over.homMk a₀ ?_, ?_⟩
  · change a₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R[X])) = Spec.algebraMap R S
    rw [← ι_toBase R p j, ← Category.assoc, ha₀]
    exact Over.w x
  · exact Over.OverMorphism.ext ha₀

/-- If the point `u_i = α` of the line `i` is the point `u_j = s` of the line `j`, they have the
same coordinate `t = p^i + p^(i+1) α = p^j + p^(j+1) s`. -/
theorem t_eq_of_chart_eq {B : Type u} [CommRing B] [Algebra R B] {i j : ULift.{u} ℕ} {α s : B}
    (h : linePoint R α ≫ chart R p i = linePoint R s ≫ chart R p j) :
    algebraMap R B p ^ i.down + algebraMap R B p ^ (i.down + 1) * α =
      algebraMap R B p ^ j.down + algebraMap R B p ^ (j.down + 1) * s := by
  by_cases hij : i = j
  · subst hij
    have h' := (cancel_mono (chart R p i)).1 h
    have := congrArg (fun q => affineRingPointEquiv R R[X] B q X) h'
    simp only [linePoint, affineRingPointEquiv_ringTestMap, aeval_X] at this
    rw [this]
  · have hl : Spec.map (CommRingCat.ofHom (aeval α).toRingHom) ≫ ι R p i =
        Spec.map (CommRingCat.ofHom (aeval s).toRingHom) ≫ ι R p j :=
      congrArg (fun f => f.left) h
    obtain ⟨w₀, hw₁, hw₂⟩ := CommonOpenGluing.exists_of_comp_eq _ _ (g R p) hij _ _ hl
    let w : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (L R p)) := w₀
    let ω : L R p →+* B := (Spec.preimage w).hom
    have hω : ∀ (k : ULift.{u} ℕ) (γ : B),
        w ≫ g R p k = Spec.map (CommRingCat.ofHom (aeval γ).toRingHom) →
          ω.comp (σ R p k.down) = (aeval γ).toRingHom := by
      intro k γ hk
      have h₀ : CommRingCat.ofHom (σ R p k.down) ≫ Spec.preimage w =
          CommRingCat.ofHom (aeval γ).toRingHom := by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_preimage]
        exact hk
      have := congrArg (fun φ => φ.hom) h₀
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] using this
    have hi := hω i α hw₁
    have hj := hω j s hw₂
    have hP : ω (P R p) = algebraMap R B p := by
      have h₀ : ω (P R p) = ω (σ R p i.down (C p)) := by rw [σ_C]
      rw [h₀, ← RingHom.comp_apply, hi]
      simp
    have hXi : ω (σ R p i.down X) = α := by
      rw [← RingHom.comp_apply, hi]
      simp
    have hXj : ω (σ R p j.down X) = s := by
      rw [← RingHom.comp_apply, hj]
      simp
    have ti := t_eq i.down ω
    have tj := t_eq j.down ω
    rw [hP, hXi] at ti
    rw [hP, hXj] at tj
    exact ti.symm.trans tj

/-- Conversely, if `p` is a unit and the coordinates `t` agree, the point `u_i = α` of the line
`i` is the point `u_j = s` of the line `j`. -/
theorem chart_eq_of_t_eq {B : Type u} [CommRing B] [Algebra R B] {i j : ULift.{u} ℕ} {α s : B}
    (hp : IsUnit (algebraMap R B p))
    (h : algebraMap R B p ^ i.down + algebraMap R B p ^ (i.down + 1) * α =
      algebraMap R B p ^ j.down + algebraMap R B p ^ (j.down + 1) * s) :
    linePoint R α ≫ chart R p i = linePoint R s ≫ chart R p j := by
  let t₀ := algebraMap R B p ^ i.down + algebraMap R B p ^ (i.down + 1) * α
  have hu : IsUnit ((aeval t₀).toRingHom (C p)) := by simpa using hp
  let ω : L R p →+* B := IsLocalization.Away.lift (C p) hu
  have hωa : ω.comp (algebraMap R[X] (L R p)) = (aeval t₀).toRingHom :=
    IsLocalization.Away.lift_comp _ _
  have hωP : ω (P R p) = algebraMap R B p := by
    rw [← RingHom.comp_apply, hωa]
    simp
  have hωT : ω (T R p) = t₀ := by
    rw [← RingHom.comp_apply, hωa]
    simp
  have hωe : ω (e R p) * algebraMap R B p = 1 := by
    rw [← hωP, ← map_mul, mul_comm, P_mul_e, map_one]
  have key : ∀ (k : ULift.{u} ℕ) (γ : B),
      algebraMap R B p ^ k.down + algebraMap R B p ^ (k.down + 1) * γ = t₀ →
        ω.comp (σ R p k.down) = (aeval γ).toRingHom := by
    intro k γ hk
    apply Polynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, σ_C, ← RingHom.comp_apply, hωa]
      simp
    · rw [RingHom.comp_apply, comp_σ_X, hωT, hωP]
      have h' : ω (e R p) ^ (k.down + 1) * algebraMap R B p ^ (k.down + 1) = 1 := by
        rw [← mul_pow, hωe, one_pow]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      rw [← hk]
      linear_combination γ * h'
  have hi := key i α rfl
  have hj := key j s h.symm
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (aeval α).toRingHom) ≫ ι R p i =
    Spec.map (CommRingCat.ofHom (aeval s).toRingHom) ≫ ι R p j
  rw [← hi, ← hj, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
    Category.assoc, Category.assoc]
  exact congrArg (Spec.map (CommRingCat.ofHom ω) ≫ ·) (CommonOpenGluing.g_ι _ _ (g R p) i j)

end Points

end DilatedLineChain

open DilatedLineChain in
/-- **The closedness assertion of Conrad's Corollary 5.7 fails for separated spaces locally of
finite type.** Countably many affine lines over `O`, glued along the generic fibre by
`t = p^j + p^(j+1) u_j`, form a separated scheme locally of finite type whose image of
`O`-points in the rational points of the generic fibre is not closed. -/
theorem henselianIntegralPointsNotClosedOfSeparated :
    HenselianIntegralPointsNotClosedOfSeparatedStatement.{u} := by
  intro K _ O hO _
  obtain ⟨p₀, hp₀, hp₁⟩ := NormedField.exists_norm_lt_one K
  let p : O := ⟨p₀, (hO p₀).mpr hp₁.le⟩
  have hp₀' : p₀ ≠ 0 := norm_pos_iff.mp hp₀
  have hpK : algebraMap O K p = p₀ := rfl
  refine ⟨(schemeToSpace _).obj (overBase O p), DilatedLineChain.isSeparated O p,
    locallyOfFiniteTypeOverBase O p, ?_⟩
  let 𝒳 := (schemeToSpace _).obj (overBase O p)
  let XK := baseChange (Spec.algebraMap O K) 𝒳
  let : TopologicalSpace (RingPoints K XK K) := etaleChartTopology K XK
  let U := ringTest O O[X]
  let f : (schemeToSpace _).obj U ⟶ 𝒳 := (schemeToSpace _).map (chart O p ⟨0⟩)
  have hf : IsEtale (hom f) := isEtale_map _ inferInstance
  let d := baseChangeChart K U f hf
  let Φ : K → RingPoints K XK K := fun s =>
    d.pointMap (ringPointBaseChangeEquiv O K K U (linePoint O s))
  have hΦ : Continuous Φ := by
    have h₁ := d.continuous_pointMap
    have h₂ := @IsHomeomorph.continuous _ _ (schemePointTopology O U K)
      (schemePointTopology K (ringBaseChange O K U) K) _ (schemeBaseChangeTopology_proof O K K U)
    have h₃ := continuous_linePoint (O := O) K
    exact @Continuous.comp _ _ _ _ (schemePointTopology K d.scheme K) _ _ _ h₁
      (@Continuous.comp _ _ _ _ (schemePointTopology O U K) (schemePointTopology K d.scheme K)
        _ _ h₂ h₃)
  have hΦeq : ∀ s : K, baseChangeRingPointsEquiv O K K 𝒳 (Φ s) =
      (schemeRingPointsEquiv O (overBase O p) K).symm (chartPoint O p ⟨0⟩ (linePoint O s)) := by
    intro s
    rw [baseChangeRingPointsEquiv_baseChangeChart_pointMap, Equiv.symm_apply_apply]
    rfl
  have hcomp : ∀ a : O, ringTestMap O (Algebra.ofId O K) ≫ linePoint O a =
      linePoint O (algebraMap O K a) := by
    intro a
    rw [linePoint, linePoint, ← ringTestMap_comp]
    congr 1
    apply Polynomial.algHom_ext
    simp
  let c : K := -p₀⁻¹
  have hnot : Φ c ∉ Set.range fun x : RingPoints O 𝒳 O =>
      (baseChangeRingPointsEquiv O K K 𝒳).symm (RingPoints.changeRing (Algebra.ofId O K) x) := by
    rintro ⟨x, hx⟩
    have h₁ : RingPoints.changeRing (Algebra.ofId O K) x =
        (schemeRingPointsEquiv O (overBase O p) K).symm
          (chartPoint O p ⟨0⟩ (linePoint O c)) := by
      have := congrArg (baseChangeRingPointsEquiv O K K 𝒳) hx
      simp only [Equiv.apply_symm_apply] at this
      rw [this, hΦeq]
    have hx' := congrArg (schemeRingPointsEquiv O (overBase O p) K) h₁
    rw [Equiv.apply_symm_apply, schemeRingPointsEquiv_changeRing] at hx'
    obtain ⟨j, a, ha⟩ := exists_chart_factor (schemeRingPointsEquiv O (overBase O p) O x)
    rw [← ha, eq_linePoint a] at hx'
    have h₂ : linePoint O (algebraMap O K (affineRingPointEquiv O O[X] O a X)) ≫ chart O p j =
        linePoint O c ≫ chart O p ⟨0⟩ := by
      rw [← hcomp]
      exact (Category.assoc _ _ _).trans hx'
    have ht := t_eq_of_chart_eq h₂
    rw [hpK] at ht
    have hα : (algebraMap O K (affineRingPointEquiv O O[X] O a X)) = -p₀⁻¹ := by
      have h₃ : p₀ ^ j.down * (1 + p₀ * algebraMap O K (affineRingPointEquiv O O[X] O a X)) =
          0 := by
        have : p₀ ^ (0 : ℕ) + p₀ ^ ((0 : ℕ) + 1) * c = 0 := by
          simp only [pow_zero, zero_add, pow_one, c]
          field_simp
          ring
        linear_combination ht.trans this
      have h₄ := (mul_eq_zero.mp h₃).resolve_left (pow_ne_zero _ hp₀')
      field_simp
      linear_combination h₄
    have hle : ‖algebraMap O K (affineRingPointEquiv O O[X] O a X)‖ ≤ 1 :=
      (hO _).mp (affineRingPointEquiv O O[X] O a X).2
    rw [hα, norm_neg, norm_inv] at hle
    exact absurd hle (not_le.mpr ((one_lt_inv₀ hp₀).mpr hp₁))
  let s : ℕ → K := fun n => (p₀ ^ n - 1) * p₀⁻¹
  have hs : Tendsto s atTop (𝓝 c) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp₁).sub_const 1).mul_const p₀⁻¹
    simpa [s, c] using h
  have hmem : ∀ n, Φ (s n) ∈ Set.range fun x : RingPoints O 𝒳 O =>
      (baseChangeRingPointsEquiv O K K 𝒳).symm (RingPoints.changeRing (Algebra.ofId O K) x) := by
    intro n
    refine ⟨(schemeRingPointsEquiv O (overBase O p) O).symm
      (chartPoint O p ⟨n⟩ (linePoint O 0)), ?_⟩
    apply (baseChangeRingPointsEquiv O K K 𝒳).injective
    rw [hΦeq, Equiv.apply_symm_apply]
    apply (schemeRingPointsEquiv O (overBase O p) K).injective
    rw [schemeRingPointsEquiv_changeRing, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have h := chart_eq_of_t_eq (R := O) (p := p) (i := ⟨n⟩) (j := ⟨0⟩)
      (α := algebraMap O K 0) (s := s n) (by rw [hpK]; exact isUnit_iff_ne_zero.mpr hp₀') (by
        rw [hpK, map_zero]
        simp only [mul_zero, add_zero, pow_zero, zero_add, pow_one, s]
        field_simp
        ring)
    rw [← hcomp] at h
    exact (Category.assoc _ _ _).symm.trans h
  intro hclosed
  exact hnot (hclosed.mem_of_tendsto ((hΦ.tendsto c).comp hs) (Eventually.of_forall hmem))

end Langlands.AlgebraicGeometry.AlgebraicSpace
