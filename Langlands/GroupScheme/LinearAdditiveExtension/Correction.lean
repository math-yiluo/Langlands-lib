import Langlands.GroupScheme.LinearAdditiveExtension.CrossedHom

/-! # Correcting a crossed homomorphism into the closed additive subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LinearAdditiveExtension

open RelativeRoot.AdditiveGroupQuotient

variable {k : Type u} [Field k] {Λ : Type u} [AddCommGroup Λ]

local notation "𝔾ₐ" => VectorGroup.groupScheme (CommRingCat.of k) 1
local notation "𝔻" => Diagonalizable.groupScheme (CommRingCat.of k) Λ

variable {E : GroupScheme (Spec (CommRingCat.of k))}
  (q : E ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
  (a : kernel q ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
  (χ : characterLattice (Diagonalizable.groupScheme (CommRingCat.of k) Λ))

/-- The base `Spec k`, as a test scheme over itself. -/
abbrev base : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 (Spec (CommRingCat.of k)))

instance isAffineHom_base : IsAffineHom (base (k := k)).hom := by
  change IsAffineHom (𝟙 _)
  infer_instance

/-- The unique map from a test scheme to the base. -/
abbrev toBase (T : Over (Spec (CommRingCat.of k))) : T ⟶ base :=
  AutomorphicAction.Cocycle.baseMap T

theorem comp_toBase {T T' : Over (Spec (CommRingCat.of k))} (b : T' ⟶ T) :
    b ≫ toBase T = toBase T' :=
  AutomorphicAction.Cocycle.comp_baseMap b

theorem pow_comp' {X Y : Over (Spec (CommRingCat.of k))} (f : X ⟶ Y)
    (g : Y ⟶ (𝔻).X) (n : ℕ) : f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

/-- The polynomial of the closed subgroup, applied to a point of `𝔾ₐ`. -/
theorem cd_polyEndo {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ (𝔾ₐ).X) (p : k[X]) :
    cd (x ≫ polyEndo ClosedAdditivePolynomial.ga p) = p.eval₂ (structureMap T) (cd x) :=
  coord_comp_polyEndo _ ClosedAdditivePolynomial.ga_comp x p

/-- The structure map of the base is surjective onto its global functions. -/
theorem structureMap_base_surjective :
    Function.Surjective (structureMap (base (k := k))) := by
  intro m
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom m, ?_⟩
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    Scheme.Hom.appTop (𝟙 (Spec (CommRingCat.of k)))).hom
    ((Scheme.ΓSpecIso (CommRingCat.of k)).hom m) = m
  rw [Scheme.Hom.id_appTop, Category.comp_id]
  exact (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id_apply m

theorem structureMap_toBase {T : Over (Spec (CommRingCat.of k))} (c : k) :
    (toBase T).left.appTop.hom (structureMap base c) = structureMap T c := by
  rw [← RingHom.comp_apply, structureMap_comp]

section Correction

variable [IsAffineHom E.X.hom]
  [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
  (b : AutomorphicAction (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp (kernel q))
  (hlin : ∀ (T : Over (Spec (CommRingCat.of k)))
    (d : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X) (x : T ⟶ (kernel q).X),
    b.act d x ≫ a.hom.hom = (VectorGroup.weightAction (n := 1) χ).act d (x ≫ a.hom.hom))

omit [IsAffineHom E.X.hom] [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left]
  [Surjective q.hom.hom.left] in
include hlin in
theorem weight_stable {T : Over (Spec (CommRingCat.of k))}
    (d : T ⟶ (𝔻).X) (x : T ⟶ (𝔾ₐ).X) (hx : x ∈ (SubgroupFunctor.range a).carrier T) :
    (VectorGroup.weightAction (n := 1) χ).act d x ∈ (SubgroupFunctor.range a).carrier T := by
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  exact SubgroupFunctor.mem_range.mpr ⟨b.act d y, hlin T d y⟩

omit [IsAffineHom E.X.hom] in
include hlin in
/-- A crossed homomorphism `c'` extending `a` can be corrected by a coboundary of `D` so that
all its values lie in the closed subgroup. -/
theorem exists_corrected [IsAlgClosed k] (ha : IsClosedSubgroup a) (c' : E.X ⟶ (𝔾ₐ).X)
    (hc₁ : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ E.X),
      cd ((g * h) ≫ c') = cd (g ≫ c') + chi q χ g * cd (h ≫ c'))
    (hc₂ : ∀ (T : Over (Spec (CommRingCat.of k))) (u : T ⟶ (kernel q).X),
      cd ((u ≫ (kernelι q).hom.hom) ≫ c') = cd (u ≫ a.hom.hom)) :
    ∃ c'' : E.X ⟶ (𝔾ₐ).X,
      (∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ E.X),
        cd ((g * h) ≫ c'') = cd (g ≫ c'') + chi q χ g * cd (h ≫ c'')) ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (u : T ⟶ (kernel q).X),
        cd ((u ≫ (kernelι q).hom.hom) ≫ c'') = cd (u ≫ a.hom.hom)) ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X),
        g ≫ c'' ∈ (SubgroupFunctor.range a).carrier T := by
  set f := ClosedAdditivePolynomial.closedPolynomial a
  by_cases hf : f = 0
  · refine ⟨c', hc₁, hc₂, fun T g => ?_⟩
    rw [ClosedAdditivePolynomial.mem_range_iff_eval a ha]
    change f.eval₂ _ _ = 0
    rw [hf, eval₂_zero]
  set N := f.natDegree
  have hst := fun T d x hx => weight_stable q a χ b hlin (T := T) d x hx
  have hadd : ∀ {T : Over (Spec (CommRingCat.of k))} (y z : Γ(T.left, ⊤)),
      f.eval₂ (structureMap T) (y + z) =
        f.eval₂ (structureMap T) y + f.eval₂ (structureMap T) z :=
    fun y z => ClosedAdditivePolynomial.eval₂_add a ha hf _ y z
  have hscale := fun T d y =>
    ClosedAdditivePolynomial.eval₂_charValue_mul a χ ha hf hst (T := T) d y
  have hpos := ClosedAdditivePolynomial.natDegree_pos a ha hf
  have h0 : ∀ {T : Over (Spec (CommRingCat.of k))}, f.eval₂ (structureMap T) 0 = 0 := by
    intro T
    rw [eval₂_at_zero, coeff_zero_eq_eval_zero, ClosedAdditivePolynomial.eval_zero a ha,
      map_zero]
  have hneg : ∀ {T : Over (Spec (CommRingCat.of k))} (y : Γ(T.left, ⊤)),
      f.eval₂ (structureMap T) (-y) = -f.eval₂ (structureMap T) y := by
    intro T y
    have h := hadd (-y) y
    rw [neg_add_cancel, h0] at h
    linear_combination -h
  -- `f ∘ c'` descends to `D`.
  have hΨ : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X) (u : T ⟶ (kernel q).X),
      (g * (u ≫ (kernelι q).hom.hom)) ≫ c' ≫ polyEndo ClosedAdditivePolynomial.ga f =
        g ≫ c' ≫ polyEndo ClosedAdditivePolynomial.ga f := by
    intro T g u
    apply cd_injective
    have hu : f.eval₂ (structureMap T) (chi q χ g * cd (u ≫ a.hom.hom)) = 0 := by
      rw [← cd_act, ← hlin]
      exact (ClosedAdditivePolynomial.mem_range_iff_eval a ha _).mp
        (SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩)
    rw [← Category.assoc, ← Category.assoc, cd_polyEndo, cd_polyEndo, hc₁, hc₂, hadd, hu,
      add_zero]
  obtain ⟨hD, hfac⟩ : ∃ hD : (𝔻).X ⟶ (𝔾ₐ).X,
      q.hom.hom ≫ hD = c' ≫ polyEndo ClosedAdditivePolynomial.ga f :=
    ⟨descend q _ hΨ, fac_descend q _ hΨ⟩
  have hqD : ∀ {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ E.X),
      cd ((g ≫ q.hom.hom) ≫ hD) = f.eval₂ (structureMap T) (cd (g ≫ c')) := by
    intro T g
    rw [Category.assoc, hfac, ← Category.assoc, cd_polyEndo]
  -- `hD` is a crossed homomorphism for `χ^N`.
  have hDmul : (fst (𝔻).X (𝔻).X * snd (𝔻).X (𝔻).X) ≫ hD =
      (fst (𝔻).X (𝔻).X ≫ hD) * (VectorGroup.weightAction (n := 1) χ).act
        (fst (𝔻).X (𝔻).X ^ N) (snd (𝔻).X (𝔻).X ≫ hD) := by
    have := FpqcHomDescent.epi_tensorHom q
    apply (cancel_epi (q.hom.hom ⊗ₘ q.hom.hom)).mp
    apply hom_ext_lift
    intro T g h
    apply cd_injective
    rw [lift_map_assoc, lift_map_assoc, ← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd,
      ← MonObj.mul_comp, MonObj.comp_mul, AutomorphicAction.naturality, pow_comp',
      lift_fst_assoc, lift_fst, lift_snd_assoc, cd_mul, cd_act, hqD, hqD, hqD, hc₁, hadd,
      charValue_pow, hscale]
  have hDmul_pt : ∀ {T : Over (Spec (CommRingCat.of k))} (z z' : T ⟶ (𝔻).X),
      cd ((z * z') ≫ hD) = cd (z ≫ hD) + VectorGroup.charValue χ T z ^ N * cd (z' ≫ hD) := by
    intro T z z'
    have := congrArg (fun m => cd (lift z z' ≫ m)) hDmul
    simp only [MonObj.comp_mul, lift_fst, lift_snd, ← Category.assoc, cd_mul] at this
    rw [this, AutomorphicAction.naturality, cd_act, pow_comp', lift_fst, lift_snd_assoc,
      charValue_pow]
  -- Averaging `hD` gives a constant `mu` with `mu = hD + χ^N mu`.
  obtain ⟨mu, hmudef⟩ : ∃ mu : base ⟶ (𝔾ₐ).X,
      mu = DiagonalizableAverage.average Λ (fst (𝔻).X base ≫ hD) := ⟨_, rfl⟩
  have hmu : ∀ {T : Over (Spec (CommRingCat.of k))} (z : T ⟶ (𝔻).X),
      cd (toBase T ≫ mu) =
        cd (z ≫ hD) + VectorGroup.charValue χ T z ^ N * cd (toBase T ≫ mu) := by
    have h1a : toBase (𝔻).X ≫ mu = DiagonalizableAverage.average Λ (fst (𝔻).X (𝔻).X ≫ hD) := by
      rw [hmudef, DiagonalizableAverage.comp_average_eq, whiskerLeft_fst_assoc]
    have h1b : DiagonalizableAverage.average Λ ((fst (𝔻).X (𝔻).X * snd (𝔻).X (𝔻).X) ≫ hD) =
        DiagonalizableAverage.average Λ (fst (𝔻).X (𝔻).X ≫ hD) := by
      have ht := DiagonalizableAverage.average_translate Λ (𝟙 (𝔻).X)
        (fst (𝔻).X (𝔻).X ≫ hD)
      rw [lift_fst_assoc, Category.comp_id] at ht
      exact ht
    have h2 : (fst (𝔻).X (𝔻).X * snd (𝔻).X (𝔻).X) ≫ hD =
        (snd (𝔻).X (𝔻).X ≫ hD) * (VectorGroup.weightAction (n := 1) χ).act
          (snd (𝔻).X (𝔻).X ≫ (𝟙 (𝔻).X) ^ N) (fst (𝔻).X (𝔻).X ≫ hD) := by
      apply cd_injective
      rw [mul_comm (fst _ _), hDmul_pt, cd_mul, cd_act, pow_comp', Category.comp_id,
        charValue_pow]
    have h3 : toBase (𝔻).X ≫ mu = hD * (VectorGroup.weightAction (n := 1) χ).act
        ((𝟙 (𝔻).X) ^ N) (toBase (𝔻).X ≫ mu) := by
      rw [h1a]
      nth_rewrite 1 [← h1b]
      rw [h2, DiagonalizableAverage.average_mul, DiagonalizableAverage.average_snd,
        DiagonalizableAverage.average_weightAction]
    intro T z
    have := congrArg (fun m => cd (z ≫ m)) h3
    simp only [MonObj.comp_mul, cd_mul, AutomorphicAction.naturality, cd_act, pow_comp',
      Category.comp_id, ← Category.assoc, comp_toBase] at this
    rw [charValue_pow] at this
    exact this
  -- A root of `f - mu`.
  obtain ⟨m₀, hm₀⟩ := structureMap_base_surjective (k := k) (cd mu)
  have hdeg : (f - C m₀).degree ≠ 0 := by
    have hd0 : 0 < f.degree := by
      rw [degree_eq_natDegree hf]
      exact_mod_cast hpos
    rw [degree_sub_C hd0, degree_eq_natDegree hf]
    exact_mod_cast hpos.ne'
  obtain ⟨r₀, hr₀⟩ := IsAlgClosed.exists_root (f - C m₀) hdeg
  have hfr : f.eval r₀ = m₀ := by
    rw [IsRoot, eval_sub, eval_C, sub_eq_zero] at hr₀
    exact hr₀
  obtain ⟨rpt, hrpt⟩ : ∃ rpt : base ⟶ (𝔾ₐ).X, cd rpt = structureMap base r₀ :=
    ⟨_, cd_ofCoord _⟩
  have hrT : ∀ {T : Over (Spec (CommRingCat.of k))},
      cd (toBase T ≫ rpt) = structureMap T r₀ := by
    intro T
    rw [cd_comp, hrpt, structureMap_toBase]
  have hmuT : ∀ {T : Over (Spec (CommRingCat.of k))},
      cd (toBase T ≫ mu) = structureMap T m₀ := by
    intro T
    rw [cd_comp, ← hm₀, structureMap_toBase]
  have hfrT : ∀ {T : Over (Spec (CommRingCat.of k))},
      f.eval₂ (structureMap T) (structureMap T r₀) = structureMap T m₀ := by
    intro T
    rw [Polynomial.eval₂_at_apply, hfr]
  -- The corrected crossed homomorphism `c'' = c' + λ (χ ∘ q - 1)`.
  have hc'' : ∀ {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ E.X),
      cd (g ≫ (c' * (VectorGroup.weightAction (n := 1) χ).act q.hom.hom (toBase E.X ≫ rpt) *
        (toBase E.X ≫ rpt)⁻¹)) =
        cd (g ≫ c') + chi q χ g * structureMap T r₀ - structureMap T r₀ := by
    intro T g
    rw [MonObj.comp_mul, MonObj.comp_mul, cd_mul, cd_mul, AutomorphicAction.naturality,
      cd_act, GrpObj.comp_inv, cd_inv, ← Category.assoc, comp_toBase, hrT, sub_eq_add_neg]
  refine ⟨c' * (VectorGroup.weightAction (n := 1) χ).act q.hom.hom (toBase E.X ≫ rpt) *
    (toBase E.X ≫ rpt)⁻¹, fun T g h => ?_, fun T u => ?_, fun T g => ?_⟩
  · rw [hc'', hc'', hc'', hc₁, chi_mul]
    ring
  · rw [hc'', hc₂, chi_kernel]
    ring
  · rw [ClosedAdditivePolynomial.mem_range_iff_eval a ha]
    change f.eval₂ _ (cd (g ≫ _)) = 0
    rw [hc'', sub_eq_add_neg, hadd, hadd, hneg, ← hqD, hscale, hfrT]
    have hm := hmu (g ≫ q.hom.hom)
    rw [hmuT] at hm
    linear_combination -hm

end Correction

end Langlands.GroupScheme.LinearAdditiveExtension
