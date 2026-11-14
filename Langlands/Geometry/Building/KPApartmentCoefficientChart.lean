import Langlands.Geometry.Building.KPBuilding
import Langlands.GroupScheme.Rational.NormalizerPointsInfiniteFieldProof
import Langlands.GroupScheme.Rational.SplitTorusRationalDetection
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Torus.SplittingAssembly
import Langlands.Geometry.Building.CrossTorusRootMetric
import Langlands.Geometry.Building.ApartmentQuotientMovingSemilinearAction

/-! # Coefficient charts on a KP apartment -/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

section TorusPoints

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The value `χ(t)` of a character of `S` at a rational point `t` of `S`. -/
def torusCharacterValue (χ : characterLattice S) (t : rationalPoints S.toGrp) : kˣ :=
  rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm χ) t

/-- Precomposing a character with the inverse of a torus automorphism. -/
theorem torusCharacterValue_inv_comp (e : S ≅ S) (χ : characterLattice S)
    (t : rationalPoints S.toGrp) :
    torusCharacterValue (e.inv ≫ χ) t =
      torusCharacterValue χ (rationalPoints.map (CommGroupScheme.groupHom e.inv) t) := by
  unfold torusCharacterValue
  rw [← rationalCharacterEval_characterRestrict]
  rfl

/-- Over an infinite field, characters of a split torus are determined by their values at
rational points. -/
theorem torusCharacterValue_injective [Infinite k] (hS : IsSplitTorus S.toGrp)
    {χ ψ : characterLattice S}
    (h : ∀ t, torusCharacterValue χ t = torusCharacterValue ψ t) : χ = ψ := by
  have h' : ∀ t : rationalPoints S.toGrp,
      t ≫ (CommGroupScheme.groupHom χ).hom.hom = t ≫ (CommGroupScheme.groupHom ψ).hom.hom := by
    intro t
    have ht := h t
    unfold torusCharacterValue at ht
    rw [rationalCharacterEval_apply, rationalCharacterEval_apply] at ht
    exact (Gm.affinePointsEquiv _).injective ht
  have : IsAffine (Gm (Spec (CommRingCat.of k))).X.left :=
    SplittingAssembly.isAffine_of_isTorus _ isSplitTorus_gm.isTorus
  have hf := hS.hom_ext_kpoints h'
  apply (rationalCharacters.equivCharacterLattice S).symm.injective
  apply Additive.toMul.injective
  apply Grp.hom_ext
  exact hf

omit [Field k] in
private theorem map_comp_apply {k : Type u} [Field k]
    {G₁ G₂ G₃ : GroupScheme (Spec (CommRingCat.of k))}
    (f : G₁ ⟶ G₂) (g : G₂ ⟶ G₃) (x : rationalPoints G₁) :
    rationalPoints.map (f ≫ g) x = rationalPoints.map g (rationalPoints.map f x) := by
  simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]

/-- A monomorphism of schemes is injective on rational points. -/
theorem rationalPoints_map_injective (i : S.toGrp ⟶ G) [Mono i.hom.hom.left] :
    Function.Injective (rationalPoints.map i) := by
  intro t t' h
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  exact (cancel_mono i.hom.hom).1 h

/-- A normalizer point conjugates the rational points of the torus through its normalizing
automorphism. -/
theorem normalizerPoints_conj_map (i : S.toGrp ⟶ G) (n : normalizerPoints i)
    (t : rationalPoints S.toGrp) :
    (n : rationalPoints G) * rationalPoints.map i t * (n : rationalPoints G)⁻¹ =
      rationalPoints.map i
        (rationalPoints.map (CommGroupScheme.groupHom (normalizingAut i n).hom) t) := by
  have h := congrArg (fun f => rationalPoints.map f t) (isNormalizingPoint_normalizingAut i n)
  simp only [map_comp_apply, rationalPoints_map_innerIso] at h
  exact h

/-- Conjugation by the inverse of a normalizer point stays in the torus. -/
theorem normalizerPoints_inv_conj_map (i : S.toGrp ⟶ G) (n : normalizerPoints i)
    (t : rationalPoints S.toGrp) :
    ∃ t', (n : rationalPoints G)⁻¹ * rationalPoints.map i t * (n : rationalPoints G) =
      rationalPoints.map i t' := by
  refine ⟨rationalPoints.map (CommGroupScheme.groupHom (normalizingAut i n⁻¹).hom) t, ?_⟩
  have h := normalizerPoints_conj_map i n⁻¹ t
  simp only [Subgroup.coe_inv, inv_inv] at h
  exact h

/-- The Weyl action on characters, evaluated at rational points. -/
theorem weylAction_torusCharacterValue (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]
    (n : normalizerPoints i) (χ : characterLattice S) {t t' : rationalPoints S.toGrp}
    (h : rationalPoints.map i t' =
      (n : rationalPoints G)⁻¹ * rationalPoints.map i t * (n : rationalPoints G)) :
    torusCharacterValue (weylAction i n χ) t = torusCharacterValue χ t' := by
  rw [weylAction_apply, torusCharacterValue_inv_comp]
  congr 1
  apply rationalPoints_map_injective i
  rw [h]
  have hc := normalizerPoints_conj_map i n
    (rationalPoints.map (CommGroupScheme.groupHom (normalizingAut i n).inv) t)
  have he : rationalPoints.map (CommGroupScheme.groupHom (normalizingAut i n).hom)
      (rationalPoints.map (CommGroupScheme.groupHom (normalizingAut i n).inv) t) = t := by
    rw [← map_comp_apply]
    change rationalPoints.map
      (CommGroupScheme.groupHom ((normalizingAut i n).inv ≫ (normalizingAut i n).hom)) t = t
    rw [Iso.inv_hom_id, rationalPoints.map_apply]
    exact Category.comp_id t
  rw [he] at hc
  rw [← hc]
  group

/-- Over an infinite field, an element of `G(k)` whose conjugation preserves the torus points
in both directions is a normalizer point. -/
theorem mem_normalizerPoints_of_conj [Infinite k] (hG : IsConnectedReductive G)
    (i : S.toGrp ⟶ G) (hi : IsSplitSubtorus i) (g : rationalPoints G)
    (h₁ : ∀ t, ∃ t', g * rationalPoints.map i t * g⁻¹ = rationalPoints.map i t')
    (h₂ : ∀ t, ∃ t', g⁻¹ * rationalPoints.map i t * g = rationalPoints.map i t') :
    g ∈ normalizerPoints i := by
  rw [(normalizerPointsInfiniteField k G hG S i hi).1, Subgroup.mem_set_normalizer_iff]
  intro x
  simp only [SetLike.mem_coe, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨t', ht'⟩ := h₁ t
    exact ⟨t', ht'.symm⟩
  · rintro ⟨t, ht⟩
    obtain ⟨t', ht'⟩ := h₂ t
    refine ⟨t', ?_⟩
    change rationalPoints.map i t' = x
    have ht2 : rationalPoints.map i t = g * x * g⁻¹ := ht
    rw [← ht', ht2]
    group

end TorusPoints

namespace KPApartmentData

section Chart

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]
  [IsAffineHom G.X.hom] {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- The automorphism `u ↦ c⁻¹ θ(u) c` of `G(k)`. -/
def chartConj (θ : MulAut (rationalPoints G)) (c : rationalPoints G) :
    MulAut (rationalPoints G) :=
  θ.trans (MulAut.conj c⁻¹)

omit [Mono i.hom.hom.left] [IsAffineHom G.X.hom] in
@[simp] theorem chartConj_apply (θ : MulAut (rationalPoints G)) (c u : rationalPoints G) :
    chartConj θ c u = c⁻¹ * θ u * c := by
  simp [chartConj]

/-- A coefficient chart of the apartment `D` along a group automorphism `θ` of `G(k)` and a
map `s` on `kˣ`. With `Ψ(u) = c⁻¹ θ(u) c`, the map `a` on apartment points is the transport
`(a x)_b(Ψ u) = x_{β b}(u)`; the bijection `τ` of `S(k)` satisfies `Ψ(i(τ t)) = i(t)`, and the
character relabelling `β` satisfies `(β χ)(τ t) = s(χ(t))`. -/
structure CoefficientChart (θ : MulAut (rationalPoints G)) (s : kˣ → kˣ) where
  /-- The correcting element `c`. -/
  c : rationalPoints G
  /-- The relabelling of characters. -/
  β : characterLattice S ≃ characterLattice S
  /-- The map on apartment points. -/
  a : D.Apartment → D.Apartment
  /-- The transport formula for apartment points. -/
  a_val : ∀ (x : D.Apartment) (b : characterLattice S) (u : rationalPoints G),
    (a x).val b (c⁻¹ * θ u * c) = x.val (β b) u
  /-- The bijection of torus points. -/
  τ : rationalPoints S.toGrp ≃ rationalPoints S.toGrp
  /-- The corrected automorphism carries the torus points to the torus points. -/
  torus : ∀ t : rationalPoints S.toGrp,
    c⁻¹ * θ (rationalPoints.map i (τ t)) * c = rationalPoints.map i t
  /-- The character relabelling matches the torus bijection through `s`. -/
  char : ∀ (χ : characterLattice S) (t : rationalPoints S.toGrp),
    torusCharacterValue (β χ) (τ t) = s (torusCharacterValue χ t)

namespace CoefficientChart

variable {D} {θ : MulAut (rationalPoints G)} {s : kˣ → kˣ} (A : D.CoefficientChart θ s)

/-- The corrected automorphism `Ψ(u) = c⁻¹ θ(u) c` of a chart. -/
def conj : MulAut (rationalPoints G) :=
  chartConj θ A.c

@[simp] theorem conj_apply (u : rationalPoints G) : A.conj u = A.c⁻¹ * θ u * A.c :=
  chartConj_apply θ A.c u

theorem val_conj (x : D.Apartment) (b : characterLattice S) (u : rationalPoints G) :
    (A.a x).val b (A.conj u) = x.val (A.β b) u := by
  rw [conj_apply]
  exact A.a_val x b u

theorem conj_map_torus (t : rationalPoints S.toGrp) :
    A.conj (rationalPoints.map i (A.τ t)) = rationalPoints.map i t := by
  rw [conj_apply]
  exact A.torus t

theorem conj_map (t : rationalPoints S.toGrp) :
    A.conj (rationalPoints.map i t) = rationalPoints.map i (A.τ.symm t) := by
  have h := A.conj_map_torus (A.τ.symm t)
  rwa [Equiv.apply_symm_apply] at h

/-- The relabelling `β` preserves the relative roots. -/
theorem mem_relativeRoots_iff (b : characterLattice S) :
    A.β b ∈ relativeRoots i ↔ b ∈ relativeRoots i := by
  obtain ⟨x⟩ : Nonempty D.Apartment := inferInstance
  constructor
  · intro hβ
    obtain ⟨u, -, hne⟩ := x.isValuation.exists_ne_top hβ
    by_contra hb
    have h := (A.a x).isValuation.eq_top_of_not_mem_roots b hb (A.conj u)
    rw [A.val_conj] at h
    exact hne h
  · intro hb
    obtain ⟨g, -, hne⟩ := (A.a x).isValuation.exists_ne_top hb
    by_contra hβ
    have h := x.isValuation.eq_top_of_not_mem_roots (A.β b) hβ (A.conj.symm g)
    rw [← A.val_conj, MulEquiv.apply_symm_apply] at h
    exact hne h

/-- On root groups of relative roots, `Ψ` carries `U_{β b}(k)` onto `U_b(k)`. -/
theorem conj_mem_rootGroupPoints_iff {b : characterLattice S} (hb : b ∈ relativeRoots i)
    (u : rationalPoints G) :
    A.conj u ∈ rootGroupPoints i b ↔ u ∈ rootGroupPoints i (A.β b) := by
  obtain ⟨x⟩ : Nonempty D.Apartment := inferInstance
  have hβ := (A.mem_relativeRoots_iff b).2 hb
  constructor
  · intro hΨ
    by_contra hu
    have h := x.isValuation.eq_top_of_not_mem (A.β b) hβ u hu
    rw [← A.val_conj] at h
    have h1 := ((A.a x).isValuation.eq_top_iff b hb (A.conj u) hΨ).1 h
    rw [map_eq_one_iff _ A.conj.injective] at h1
    exact hu (h1 ▸ (rootGroupPoints i (A.β b)).one_mem)
  · intro hu
    by_contra hΨ
    have h := (A.a x).isValuation.eq_top_of_not_mem b hb (A.conj u) hΨ
    rw [A.val_conj] at h
    have h1 := (x.isValuation.eq_top_iff (A.β b) hβ u hu).1 h
    rw [h1, map_one] at hΨ
    exact hΨ (rootGroupPoints i b).one_mem

/-- The relabelling of relative roots induced by a chart. -/
def rootsEquiv : relativeRoots i ≃ relativeRoots i where
  toFun α := ⟨A.β α, (A.mem_relativeRoots_iff α).2 α.2⟩
  invFun α := ⟨A.β.symm α, (A.mem_relativeRoots_iff _).1 (by rw [Equiv.apply_symm_apply]; exact α.2)⟩
  left_inv α := Subtype.ext (A.β.symm_apply_apply α)
  right_inv α := Subtype.ext (A.β.apply_symm_apply α)

@[simp] theorem coe_rootsEquiv (α : relativeRoots i) : (A.rootsEquiv α : characterLattice S) = A.β α :=
  rfl

/-- Values of two apartment points differ by the root form of their difference. -/
theorem val_eq_val_add_rootForm (x y : D.Apartment) (α : relativeRoots i) (g : rationalPoints G) :
    x.val α g = y.val α g + ((rootForm i α (x -ᵥ y) : ℝ) : WithTop ℝ) := by
  obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (x -ᵥ y)
  have hx : x = (Submodule.Quotient.mk w : TranslationSpace i) +ᵥ y := by
    rw [hw, vsub_vadd]
  conv_lhs => rw [hx]
  rw [val_mk_vadd, RootFunctionFamily.vadd_apply, ← hw, rootForm_mk]

/-- The chart map multiplies root coordinates by the relabelling of roots. -/
theorem rootForm_vsub (x y : D.Apartment) (α : relativeRoots i) :
    rootForm i α (A.a x -ᵥ A.a y) = rootForm i (A.rootsEquiv α) (x -ᵥ y) := by
  obtain ⟨u, -, hne⟩ := y.isValuation.exists_ne_top (A.rootsEquiv α).2
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
  have h₁ := val_eq_val_add_rootForm (A.a x) (A.a y) α (A.conj u)
  have h₂ := val_eq_val_add_rootForm x y (A.rootsEquiv α) u
  rw [A.val_conj, A.val_conj] at h₁
  rw [coe_rootsEquiv] at h₂ hr
  rw [h₂, ← hr, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_inj] at h₁
  exact (add_left_cancel h₁).symm

attribute [local instance] RootTranslationMetric.normedAddCommGroup in
/-- The chart map preserves the root-coordinate norm of differences. -/
theorem norm_vsub [Fintype (relativeRoots i)] (x y : D.Apartment) :
    ‖(A.a x -ᵥ A.a y : TranslationSpace i)‖ = ‖(x -ᵥ y : TranslationSpace i)‖ :=
  RootTranslationMetric.norm_eq_of_rootForm_equiv i i A.rootsEquiv.symm _ _ fun α => by
    rw [A.rootForm_vsub, Equiv.apply_symm_apply]

/-- `Ψ` carries the sharp fixer of a point to the sharp fixer of its image. -/
theorem conj_mem_sharpFixer (x : D.Apartment) (p : rationalPoints G)
    (hp : p ∈ D.sharpFixer {x}) :
    A.conj p ∈ D.sharpFixer {A.a x} := by
  rw [← MulEquiv.coe_toMonoidHom, ← Subgroup.mem_comap]
  revert p
  rw [← SetLike.le_def]
  refine iSup_le fun α u hu => ?_
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
  obtain ⟨b, hb⟩ := A.β.surjective α
  have hbroot : b ∈ relativeRoots i := (A.mem_relativeRoots_iff b).1 (hb ▸ α.2)
  refine D.rootFixer_le_sharpFixer ⟨b, hbroot⟩ {A.a x} ?_
  rw [rootFixer_singleton, mem_filtration]
  rw [rootFixer_singleton, mem_filtration, ← hb] at hu
  exact ⟨(A.conj_mem_rootGroupPoints_iff hbroot u).2 hu.1, by rw [A.val_conj]; exact hu.2⟩

section InfiniteField

variable [Infinite k] (hG : IsConnectedReductive G) (hi : IsSplitSubtorus i)
include hG hi

/-- Over an infinite field, `Ψ` preserves the normalizer points. -/
theorem conj_mem_normalizerPoints (n : normalizerPoints i) :
    A.conj n ∈ normalizerPoints i := by
  apply mem_normalizerPoints_of_conj hG i hi
  · intro t
    obtain ⟨t', ht'⟩ := normalizerPoints_inv_conj_map i n⁻¹ (A.τ t)
    simp only [Subgroup.coe_inv, inv_inv] at ht'
    refine ⟨A.τ.symm t', ?_⟩
    rw [← A.conj_map, ← ht', ← A.conj_map_torus t, map_mul, map_mul, map_inv]
  · intro t
    obtain ⟨t', ht'⟩ := normalizerPoints_inv_conj_map i n (A.τ t)
    refine ⟨A.τ.symm t', ?_⟩
    rw [← A.conj_map, ← ht', ← A.conj_map_torus t, map_mul, map_mul, map_inv]

/-- The normalizer point `Ψ(n)`. -/
def normalizerMap (n : normalizerPoints i) : normalizerPoints i :=
  ⟨A.conj n, A.conj_mem_normalizerPoints hG hi n⟩

@[simp] theorem coe_normalizerMap (n : normalizerPoints i) :
    (A.normalizerMap hG hi n : rationalPoints G) = A.c⁻¹ * θ n * A.c :=
  A.conj_apply n

theorem coe_normalizerMap' (n : normalizerPoints i) :
    (A.normalizerMap hG hi n : rationalPoints G) = A.conj n :=
  rfl

theorem normalizerMap_inv (n : normalizerPoints i) :
    A.normalizerMap hG hi n⁻¹ = (A.normalizerMap hG hi n)⁻¹ := by
  apply Subtype.ext
  rw [coe_normalizerMap', Subgroup.coe_inv, Subgroup.coe_inv, coe_normalizerMap', map_inv]

/-- The relabelling `β` intertwines the Weyl actions of `n` and `Ψ(n)`. -/
theorem β_weylAction (n : normalizerPoints i) (b : characterLattice S) :
    A.β (weylAction i (A.normalizerMap hG hi n) b) = weylAction i n (A.β b) := by
  apply torusCharacterValue_injective hi.1
  intro t
  obtain ⟨t₀, rfl⟩ := A.τ.surjective t
  obtain ⟨t₁, ht₁⟩ := normalizerPoints_inv_conj_map i (A.normalizerMap hG hi n) t₀
  obtain ⟨t₂, ht₂⟩ := normalizerPoints_inv_conj_map i n (A.τ t₀)
  have h₂₁ : t₂ = A.τ t₁ := by
    apply rationalPoints_map_injective i
    apply A.conj.injective
    rw [A.conj_map_torus, ← ht₂, ← ht₁, map_mul, map_mul, map_inv, A.conj_map_torus,
      coe_normalizerMap']
  rw [A.char, weylAction_torusCharacterValue i _ b ht₁.symm,
    weylAction_torusCharacterValue i n (A.β b) ht₂.symm, h₂₁, A.char]

/-- The chart map intertwines the normalizer actions through `Ψ`. -/
theorem a_smul (n : normalizerPoints i) (x : D.Apartment) :
    A.a (n • x) = A.normalizerMap hG hi n • A.a x := by
  apply Apartment.ext
  ext b u'
  obtain ⟨u, rfl⟩ := A.conj.surjective u'
  rw [A.val_conj, val_smul, val_smul, RootFunctionFamily.smul_apply,
    RootFunctionFamily.smul_apply]
  have hu : ((A.normalizerMap hG hi n : normalizerPoints i) : rationalPoints G)⁻¹ *
        A.conj u * ((A.normalizerMap hG hi n : normalizerPoints i) : rationalPoints G) =
      A.conj (((n : normalizerPoints i) : rationalPoints G)⁻¹ * u * (n : rationalPoints G)) := by
    rw [coe_normalizerMap', map_mul, map_mul, map_inv]
  rw [hu, A.val_conj, ← A.normalizerMap_inv, A.β_weylAction]

end InfiniteField

section Coherence

variable {θ₁ θ₂ θ₃ : MulAut (rationalPoints G)} {s₁ s₂ s₃ : kˣ → kˣ}
  (A₁ : D.CoefficientChart θ₁ s₁) (A₂ : D.CoefficientChart θ₂ s₂)
  (A₃ : D.CoefficientChart θ₃ s₃)

/-- The defect `c₃⁻¹ θ₁(c₂) c₁` of three charts. -/
def defect : rationalPoints G :=
  A₃.c⁻¹ * θ₁ A₂.c * A₁.c

variable {A₁ A₂ A₃} (hθ : ∀ u, θ₃ u = θ₁ (θ₂ u))
include hθ

/-- Composing two corrected automorphisms gives the third up to conjugation by the defect. -/
theorem conj_conj (u : rationalPoints G) :
    A₁.conj (A₂.conj u) = (defect A₁ A₂ A₃)⁻¹ * A₃.conj u * defect A₁ A₂ A₃ := by
  simp only [conj_apply, defect, hθ, map_mul, map_inv, mul_inv_rev, inv_inv]
  group

theorem defect_conj_map (t : rationalPoints S.toGrp) :
    defect A₁ A₂ A₃ * rationalPoints.map i t * (defect A₁ A₂ A₃)⁻¹ =
      rationalPoints.map i (A₃.τ.symm (A₂.τ (A₁.τ t))) := by
  have h := conj_conj (A₁ := A₁) (A₂ := A₂) (A₃ := A₃) hθ
    (rationalPoints.map i (A₂.τ (A₁.τ t)))
  rw [A₂.conj_map_torus, A₁.conj_map_torus, A₃.conj_map] at h
  rw [h]
  group

theorem defect_inv_conj_map (t : rationalPoints S.toGrp) :
    (defect A₁ A₂ A₃)⁻¹ * rationalPoints.map i t * defect A₁ A₂ A₃ =
      rationalPoints.map i (A₁.τ.symm (A₂.τ.symm (A₃.τ t))) := by
  have h := conj_conj (A₁ := A₁) (A₂ := A₂) (A₃ := A₃) hθ (rationalPoints.map i (A₃.τ t))
  rw [A₃.conj_map_torus, A₂.conj_map, A₁.conj_map] at h
  exact h.symm

variable [Infinite k] (hG : IsConnectedReductive G) (hi : IsSplitSubtorus i)
include hG hi

/-- Over an infinite field, the defect is a normalizer point. -/
theorem defect_mem : defect A₁ A₂ A₃ ∈ normalizerPoints i :=
  mem_normalizerPoints_of_conj hG i hi _
    (fun t => ⟨_, defect_conj_map (A₁ := A₁) (A₂ := A₂) (A₃ := A₃) hθ t⟩)
    (fun t => ⟨_, defect_inv_conj_map (A₁ := A₁) (A₂ := A₂) (A₃ := A₃) hθ t⟩)

variable (A₁ A₂ A₃) in
/-- The defect as a normalizer point. -/
def defectPoint : normalizerPoints i :=
  ⟨defect A₁ A₂ A₃, defect_mem hθ hG hi⟩

variable (A₁ A₂ A₃) in
@[simp] theorem coe_defectPoint :
    (defectPoint A₁ A₂ A₃ hθ hG hi : rationalPoints G) = defect A₁ A₂ A₃ :=
  rfl

variable {hθ} (hs : ∀ z, s₃ z = s₂ (s₁ z))
include hs

/-- The character relabellings compose up to the Weyl action of the defect. -/
theorem β_comp (b : characterLattice S) :
    A₂.β (A₁.β (weylAction i (defectPoint A₁ A₂ A₃ hθ hG hi)⁻¹ b)) = A₃.β b := by
  apply torusCharacterValue_injective hi.1
  intro t
  obtain ⟨t₀, rfl⟩ : ∃ t₀, A₂.τ (A₁.τ t₀) = t :=
    ⟨A₁.τ.symm (A₂.τ.symm t), by simp⟩
  have h₁ : rationalPoints.map i (A₃.τ.symm (A₂.τ (A₁.τ t₀))) =
      (((defectPoint A₁ A₂ A₃ hθ hG hi)⁻¹ : normalizerPoints i) : rationalPoints G)⁻¹ *
        rationalPoints.map i t₀ *
          (((defectPoint A₁ A₂ A₃ hθ hG hi)⁻¹ : normalizerPoints i) : rationalPoints G) := by
    rw [Subgroup.coe_inv, inv_inv, coe_defectPoint]
    exact (defect_conj_map (A₁ := A₁) (A₂ := A₂) (A₃ := A₃) hθ t₀).symm
  rw [A₂.char, A₁.char, weylAction_torusCharacterValue i _ b h₁]
  conv_rhs => rw [← Equiv.apply_symm_apply A₃.τ (A₂.τ (A₁.τ t₀)), A₃.char]
  rw [hs]

/-- The third chart map is the composite of the first two followed by the defect. -/
theorem a_mul (x : D.Apartment) :
    A₃.a x = defectPoint A₁ A₂ A₃ hθ hG hi • A₁.a (A₂.a x) := by
  apply Apartment.ext
  ext b g
  obtain ⟨u, rfl⟩ := A₃.conj.surjective g
  rw [A₃.val_conj, val_smul, RootFunctionFamily.smul_apply, coe_defectPoint,
    ← conj_conj (A₁ := A₁) (A₂ := A₂) (A₃ := A₃) hθ, A₁.val_conj, A₂.val_conj,
    β_comp (A₁ := A₁) (A₂ := A₂) (A₃ := A₃) (hθ := hθ) hG hi hs]

end Coherence

variable (D) in
/-- The identity chart. -/
def refl : D.CoefficientChart 1 id where
  c := 1
  β := Equiv.refl _
  a := id
  a_val x b u := by simp
  τ := Equiv.refl _
  torus t := by simp
  char χ t := rfl

@[simp] theorem refl_c : (refl D).c = 1 :=
  rfl

@[simp] theorem refl_a (x : D.Apartment) : (refl D).a x = x :=
  rfl

end CoefficientChart

section Assembly

variable [Infinite k] (hG : IsConnectedReductive G) (hi : IsSplitSubtorus i)
  {Γ : Type*} [Group Γ] (ρ : Γ →* MulAut (rationalPoints G)) (s : Γ → kˣ → kˣ)
  (hs : ∀ (σ τ : Γ) (z : kˣ), s (σ * τ) z = s τ (s σ z))
  (A : ∀ σ : Γ, D.CoefficientChart (ρ σ) (s σ))
  (hc : (A 1).c = 1) (ha : ∀ x, (A 1).a x = x)

omit [Infinite k] [IsAffineHom G.X.hom] in
theorem coherent_hom (σ τ : Γ) (u : rationalPoints G) : ρ (σ * τ) u = ρ σ (ρ τ u) := by
  rw [map_mul, MulAut.mul_apply]

/-- A family of coefficient charts along a group of automorphisms of `G(k)`, normalized at the
identity, with the maps on `kˣ` composing contravariantly, is moving semilinear action data for
the sharp-fixer family of `D`. -/
def CoefficientChart.movingSemilinearActionData :
    ApartmentQuotient.MovingSemilinearActionData D.sharpFixerFamily ρ where
  correction σ := (A σ).c
  apartment σ := (A σ).a
  normalizer_mem σ n := by
    have h := (A σ).conj_mem_normalizerPoints hG hi n
    rwa [CoefficientChart.conj_apply] at h
  normalizer_smul σ n x := by
    rw [(A σ).a_smul hG hi n x]
    congr 1
    exact Subtype.ext ((A σ).coe_normalizerMap hG hi n)
  subgroup_mem σ x p hp := by
    have h := (A σ).conj_mem_sharpFixer x p hp
    rwa [CoefficientChart.conj_apply] at h
  correction_one := hc
  apartment_one := ha
  defect σ τ := CoefficientChart.defectPoint (A σ) (A τ) (A (σ * τ))
    (coherent_hom ρ σ τ) hG hi
  correction_mul σ τ := by
    rw [CoefficientChart.coe_defectPoint, CoefficientChart.defect]
    group
  apartment_mul σ τ x := CoefficientChart.a_mul hG hi (hs σ τ) x

@[simp] theorem CoefficientChart.movingSemilinearActionData_correction (σ : Γ) :
    (CoefficientChart.movingSemilinearActionData D hG hi ρ s hs A hc ha).correction σ =
      (A σ).c :=
  rfl

@[simp] theorem CoefficientChart.movingSemilinearActionData_apartment (σ : Γ) :
    (CoefficientChart.movingSemilinearActionData D hG hi ρ s hs A hc ha).apartment σ =
      (A σ).a :=
  rfl

end Assembly

end Chart

end KPApartmentData

end Langlands.Geometry.Building
