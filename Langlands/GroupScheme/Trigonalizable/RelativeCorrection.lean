import Langlands.GroupScheme.LinearAdditiveExtension.Section
import Langlands.GroupScheme.Trigonalizable.CorrectionOfSolvable

/-! # One-step splitting compatible with a given partial section -/

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

section Vanishing

variable {E : GroupScheme (Spec (CommRingCat.of k))}
  (q : E ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
  (a : kernel q ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
  (χ : characterLattice (Diagonalizable.groupScheme (CommRingCat.of k) Λ))
  (b : AutomorphicAction (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp (kernel q))
  (hlin : ∀ (T : Over (Spec (CommRingCat.of k)))
    (d : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X) (x : T ⟶ (kernel q).X),
    b.act d x ≫ a.hom.hom = (VectorGroup.weightAction (n := 1) χ).act d (x ≫ a.hom.hom))
  (c : E.X ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X)
  (hc₁ : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ E.X),
    cd ((g * h) ≫ c) = cd (g ≫ c) + chi q χ g * cd (h ≫ c))
  (hc₂ : ∀ (T : Over (Spec (CommRingCat.of k))) (u : T ⟶ (kernel q).X),
    cd ((u ≫ (kernelι q).hom.hom) ≫ c) = cd (u ≫ a.hom.hom))

variable [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]

include hlin hc₁ hc₂ in
/-- The Library's `exists_section`, also recording that `c` vanishes on the image of the section
at every point coming from `E`. -/
theorem exists_section_vanishing (ha : IsClosedSubgroup a)
    (hc₃ : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X),
      g ≫ c ∈ (SubgroupFunctor.range a).carrier T) :
    ∃ s : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ E, s ≫ q = 𝟙 _ ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X),
        cd ((g ≫ q.hom.hom ≫ s.hom.hom) ≫ c) = 0 := by
  obtain ⟨c₀, hc₀⟩ := SubgroupFunctor.mem_range.mp (hc₃ E.X (𝟙 _))
  rw [Category.id_comp] at hc₀
  -- The correction `w(g) = (b(q(g)⁻¹, c₀(g)))⁻¹` and `σ(g) = g · w(g)`.
  set w : E.X ⟶ (kernel q).X := (b.act (q.hom.hom⁻¹) c₀)⁻¹ with hw
  set σ : E.X ⟶ E.X := 𝟙 E.X * (w ≫ (kernelι q).hom.hom) with hσ
  have hgσ : ∀ {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ E.X),
      g ≫ σ = g * ((g ≫ w) ≫ (kernelι q).hom.hom) := by
    intro T g
    rw [hσ, MonObj.comp_mul, Category.comp_id, Category.assoc]
  have hσq : σ ≫ q.hom.hom = q.hom.hom := by
    rw [hσ, MonObj.mul_comp, kernel_comp_q, Category.id_comp, mul_one]
  have hσc : ∀ {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ E.X), cd ((g ≫ σ) ≫ c) = 0 := by
    intro T g
    rw [hgσ, hc₁, hc₂, hw, GrpObj.comp_inv, GrpObj.inv_comp, cd_inv,
      AutomorphicAction.naturality, hlin, cd_act, GrpObj.comp_inv, Category.assoc, hc₀]
    have e := charValue_mul_inv χ (g ≫ q.hom.hom)
    linear_combination -(cd (g ≫ c)) * e
  have hσinv : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X) (u : T ⟶ (kernel q).X),
      (g * (u ≫ (kernelι q).hom.hom)) ≫ σ = g ≫ σ := by
    intro T g u
    apply eq_of_cd_eq_zero q a χ c hc₁ hc₂ ha _ (hσc _) (hσc _)
    rw [Category.assoc, Category.assoc, hσq, mul_kernel_comp_q]
  obtain ⟨s, hs⟩ : ∃ s : (𝔻).X ⟶ E.X, q.hom.hom ≫ s = σ :=
    ⟨descend q σ hσinv, fac_descend q σ hσinv⟩
  have hsq : s ≫ q.hom.hom = 𝟙 _ := by
    apply (cancel_epi q.hom.hom).mp
    rw [← Category.assoc, hs, hσq, Category.comp_id]
  have hone : η[(𝔻).X] ≫ s = η[E.X] := by
    rw [← IsMonHom.one_hom q.hom.hom, Category.assoc, hs]
    have h1 : (η[E.X] : 𝟙_ _ ⟶ E.X) = (1 : 𝟙_ _ ⟶ E.X) := by
      rw [CategoryTheory.Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [h1]
    exact eq_of_cd_eq_zero q a χ c hc₁ hc₂ ha (by rw [Category.assoc, hσq]) (hσc _)
      (cd_one_comp q χ c hc₁)
  have hmul : μ[(𝔻).X] ≫ s = (s ⊗ₘ s) ≫ μ[E.X] := by
    have := FpqcHomDescent.epi_tensorHom q
    apply (cancel_epi (q.hom.hom ⊗ₘ q.hom.hom)).mp
    rw [← IsMonHom.mul_hom_assoc, hs, tensorHom_comp_tensorHom_assoc, hs]
    apply hom_ext_lift
    intro T g h
    rw [lift_map_assoc, ← CategoryTheory.Hom.mul_def, ← Category.assoc,
      ← CategoryTheory.Hom.mul_def]
    apply eq_of_cd_eq_zero q a χ c hc₁ hc₂ ha
    · simp only [Category.assoc, hσq, MonObj.mul_comp]
    · exact hσc _
    · rw [hc₁, hσc, hσc, mul_zero, add_zero]
  refine ⟨Grp.homMk'' s hone hmul, Grp.hom_ext _ _ (by
    change s ≫ q.hom.hom = 𝟙 _
    exact hsq), fun T g => ?_⟩
  change cd ((g ≫ q.hom.hom ≫ s) ≫ c) = 0
  rw [hs]
  exact hσc g

end Vanishing

section Average

variable {Λ₁ : Type u} [AddCommGroup Λ₁]
  (χ : characterLattice (Diagonalizable.groupScheme (CommRingCat.of k) Λ))

/-- **Averaging a crossed homomorphism.** A crossed homomorphism `φ` of `D(Λ₁)` into `𝔾ₐ`, for
the weight `z ↦ χ(e z)` given by a map `e` to `D(Λ)` and a character `χ` of `D(Λ)`, is
`r (1 - χ ∘ e)` for the constant `r` given by its average. -/
theorem exists_average_crossed
    (e : (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).X ⟶ (𝔻).X)
    (φ : (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).X ⟶ (𝔾ₐ).X)
    (hφ : ∀ (T : Over (Spec (CommRingCat.of k)))
      (z z' : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).X),
      cd ((z * z') ≫ φ) = cd (z ≫ φ) + VectorGroup.charValue χ T (z ≫ e) * cd (z' ≫ φ)) :
    ∃ r : base ⟶ (𝔾ₐ).X, ∀ {T : Over (Spec (CommRingCat.of k))}
      (z : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).X),
      cd (toBase T ≫ r) = cd (z ≫ φ) + VectorGroup.charValue χ T (z ≫ e) * cd (toBase T ≫ r) := by
  let D₁ := Diagonalizable.groupScheme (CommRingCat.of k) Λ₁
  refine ⟨DiagonalizableAverage.average Λ₁ (fst D₁.X base ≫ φ), ?_⟩
  set mu := DiagonalizableAverage.average Λ₁ (fst D₁.X base ≫ φ) with hmudef
  have h1a : toBase D₁.X ≫ mu = DiagonalizableAverage.average Λ₁ (fst D₁.X D₁.X ≫ φ) := by
    rw [hmudef, DiagonalizableAverage.comp_average_eq, whiskerLeft_fst_assoc]
  have h1b : DiagonalizableAverage.average Λ₁ ((fst D₁.X D₁.X * snd D₁.X D₁.X) ≫ φ) =
      DiagonalizableAverage.average Λ₁ (fst D₁.X D₁.X ≫ φ) := by
    have ht := DiagonalizableAverage.average_translate Λ₁ (𝟙 D₁.X) (fst D₁.X D₁.X ≫ φ)
    rw [lift_fst_assoc, Category.comp_id] at ht
    exact ht
  have h2 : (fst D₁.X D₁.X * snd D₁.X D₁.X) ≫ φ =
      (snd D₁.X D₁.X ≫ φ) * (VectorGroup.weightAction (n := 1) χ).act
        (snd D₁.X D₁.X ≫ e) (fst D₁.X D₁.X ≫ φ) := by
    apply cd_injective
    rw [mul_comm (fst _ _), hφ, cd_mul, cd_act]
  have h3 : toBase D₁.X ≫ mu = φ * (VectorGroup.weightAction (n := 1) χ).act e
      (toBase D₁.X ≫ mu) := by
    rw [h1a]
    nth_rewrite 1 [← h1b]
    rw [h2, DiagonalizableAverage.average_mul, DiagonalizableAverage.average_snd,
      DiagonalizableAverage.average_weightAction]
  intro T z
  have := congrArg (fun m => cd (z ≫ m)) h3
  simp only [MonObj.comp_mul, cd_mul, AutomorphicAction.naturality, cd_act,
    ← Category.assoc] at this
  have hz : z ≫ toBase (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).X = toBase T :=
    comp_toBase z
  rw [hz] at this
  exact this

end Average

section Relative

variable {E : GroupScheme (Spec (CommRingCat.of k))}
  (q : E ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
  (a : kernel q ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
  (χ : characterLattice (Diagonalizable.groupScheme (CommRingCat.of k) Λ))
  [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
  (b : AutomorphicAction (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp (kernel q))
  (hlin : ∀ (T : Over (Spec (CommRingCat.of k)))
    (d : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X) (x : T ⟶ (kernel q).X),
    b.act d x ≫ a.hom.hom = (VectorGroup.weightAction (n := 1) χ).act d (x ≫ a.hom.hom))

include hlin in
/-- **Correction compatible with a partial section.** Given a homomorphism
`σ₁ : D(Λ₁) ⟶ E`, the correction of `exists_corrected_of_solvable` can be chosen to vanish on
the image of `σ₁`, under the two hypotheses `hrel₁` and `hrel₂` on the weight `χ ∘ q ∘ σ₁`. -/
theorem exists_corrected_relative {Λ₁ : Type u} [AddCommGroup Λ₁] (ha : IsClosedSubgroup a)
    (σ₁ : (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).toGrp ⟶ E)
    (hrel₁ : ClosedAdditivePolynomial.closedPolynomial a ≠ 0 →
      (∀ (T : Over (Spec (CommRingCat.of k)))
        (z : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).X),
        VectorGroup.charValue χ T (z ≫ σ₁.hom.hom ≫ q.hom.hom) ^
          (ClosedAdditivePolynomial.closedPolynomial a).natDegree = 1) →
      ∀ (T : Over (Spec (CommRingCat.of k)))
        (z : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).X),
        VectorGroup.charValue χ T (z ≫ σ₁.hom.hom ≫ q.hom.hom) = 1)
    (hrel₂ : ClosedAdditivePolynomial.closedPolynomial a ≠ 0 →
      (∀ (T : Over (Spec (CommRingCat.of k)))
        (z : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).X),
        VectorGroup.charValue χ T (z ≫ σ₁.hom.hom ≫ q.hom.hom) = 1) →
      (∀ m : k, ∃ r : k, (ClosedAdditivePolynomial.closedPolynomial a).eval r = m) ∨
        ∀ (T : Over (Spec (CommRingCat.of k))) (d : T ⟶ (𝔻).X),
          VectorGroup.charValue χ T d ^
            (ClosedAdditivePolynomial.closedPolynomial a).natDegree = 1)
    (c' : E.X ⟶ (𝔾ₐ).X)
    (hc₁ : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ E.X),
      cd ((g * h) ≫ c') = cd (g ≫ c') + chi q χ g * cd (h ≫ c'))
    (hc₂ : ∀ (T : Over (Spec (CommRingCat.of k))) (u : T ⟶ (kernel q).X),
      cd ((u ≫ (kernelι q).hom.hom) ≫ c') = cd (u ≫ a.hom.hom)) :
    ∃ c'' : E.X ⟶ (𝔾ₐ).X,
      (∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ E.X),
        cd ((g * h) ≫ c'') = cd (g ≫ c'') + chi q χ g * cd (h ≫ c'')) ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (u : T ⟶ (kernel q).X),
        cd ((u ≫ (kernelι q).hom.hom) ≫ c'') = cd (u ≫ a.hom.hom)) ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X),
        g ≫ c'' ∈ (SubgroupFunctor.range a).carrier T) ∧
      ∀ (T : Over (Spec (CommRingCat.of k)))
        (z : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).X),
        cd ((z ≫ σ₁.hom.hom) ≫ c'') = 0 := by
  set f := ClosedAdditivePolynomial.closedPolynomial a
  -- The restriction of `c'` along `σ₁` and its average `m₁`.
  have hφ : ∀ (T : Over (Spec (CommRingCat.of k)))
      (z z' : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).X),
      cd ((z * z') ≫ σ₁.hom.hom ≫ c') = cd (z ≫ σ₁.hom.hom ≫ c') +
        VectorGroup.charValue χ T (z ≫ σ₁.hom.hom ≫ q.hom.hom) *
          cd (z' ≫ σ₁.hom.hom ≫ c') := by
    intro T z z'
    have h := hc₁ T (z ≫ σ₁.hom.hom) (z' ≫ σ₁.hom.hom)
    rw [← MonObj.mul_comp] at h
    simpa only [chi, Category.assoc] using h
  obtain ⟨r₁, hr₁⟩ := exists_average_crossed χ (σ₁.hom.hom ≫ q.hom.hom)
    (σ₁.hom.hom ≫ c') hφ
  obtain ⟨m₁, hm₁⟩ := structureMap_base_surjective (k := k) (cd r₁)
  have hφval : ∀ (T : Over (Spec (CommRingCat.of k)))
      (z : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).X),
      cd ((z ≫ σ₁.hom.hom) ≫ c') = structureMap T m₁ *
        (1 - VectorGroup.charValue χ T (z ≫ σ₁.hom.hom ≫ q.hom.hom)) := by
    intro T z
    have h := hr₁ z
    rw [cd_comp, ← hm₁, structureMap_toBase] at h
    rw [Category.assoc]
    linear_combination -h
  -- The corrected candidates `c' + r (χ ∘ q - 1)`.
  have hcand : ∀ r : k, ∃ c'' : E.X ⟶ (𝔾ₐ).X, ∀ (T : Over (Spec (CommRingCat.of k)))
      (g : T ⟶ E.X), cd (g ≫ c'') = cd (g ≫ c') + chi q χ g * structureMap T r -
        structureMap T r := by
    intro r
    obtain ⟨rpt, hrpt⟩ : ∃ rpt : base ⟶ (𝔾ₐ).X, cd rpt = structureMap base r :=
      ⟨_, cd_ofCoord _⟩
    have hrT : ∀ {T : Over (Spec (CommRingCat.of k))},
        cd (toBase T ≫ rpt) = structureMap T r := by
      intro T
      rw [cd_comp, hrpt, structureMap_toBase]
    refine ⟨c' * (VectorGroup.weightAction (n := 1) χ).act q.hom.hom (toBase E.X ≫ rpt) *
      (toBase E.X ≫ rpt)⁻¹, fun T g => ?_⟩
    rw [MonObj.comp_mul, MonObj.comp_mul, cd_mul, cd_mul, AutomorphicAction.naturality,
      cd_act, GrpObj.comp_inv, cd_inv, ← Category.assoc, comp_toBase, hrT, sub_eq_add_neg]
  -- Finishing from a value `r` with the range and vanishing properties.
  have hfinish : ∀ r : k, (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X),
      f.eval₂ (structureMap T) (cd (g ≫ c') + chi q χ g * structureMap T r -
        structureMap T r) = 0) →
      (∀ (T : Over (Spec (CommRingCat.of k)))
        (z : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).X),
        (structureMap T m₁ - structureMap T r) *
          (1 - VectorGroup.charValue χ T (z ≫ σ₁.hom.hom ≫ q.hom.hom)) = 0) →
      ∃ c'' : E.X ⟶ (𝔾ₐ).X,
      (∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ E.X),
        cd ((g * h) ≫ c'') = cd (g ≫ c'') + chi q χ g * cd (h ≫ c'')) ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (u : T ⟶ (kernel q).X),
        cd ((u ≫ (kernelι q).hom.hom) ≫ c'') = cd (u ≫ a.hom.hom)) ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X),
        g ≫ c'' ∈ (SubgroupFunctor.range a).carrier T) ∧
      ∀ (T : Over (Spec (CommRingCat.of k)))
        (z : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).X),
        cd ((z ≫ σ₁.hom.hom) ≫ c'') = 0 := by
    intro r hrange hvan
    obtain ⟨c'', hc''⟩ := hcand r
    refine ⟨c'', fun T g h => ?_, fun T u => ?_, fun T g => ?_, fun T z => ?_⟩
    · rw [hc'', hc'', hc'', hc₁, chi_mul]
      ring
    · rw [hc'', hc₂, chi_kernel]
      ring
    · rw [ClosedAdditivePolynomial.mem_range_iff_eval a ha]
      change f.eval₂ _ (cd (g ≫ c'')) = 0
      rw [hc'']
      exact hrange T g
    · rw [hc'', hφval, chi, Category.assoc]
      linear_combination hvan T z
  by_cases hf : f = 0
  · refine hfinish m₁ (fun T g => ?_) (fun T z => by ring)
    rw [hf, eval₂_zero]
  set N := f.natDegree with hNdef
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
  obtain ⟨m₀, hm₀⟩ := structureMap_base_surjective (k := k) (cd mu)
  have hmuT : ∀ {T : Over (Spec (CommRingCat.of k))},
      cd (toBase T ≫ mu) = structureMap T m₀ := by
    intro T
    rw [cd_comp, ← hm₀, structureMap_toBase]
  have hfeval : ∀ {T : Over (Spec (CommRingCat.of k))} (r : k),
      f.eval₂ (structureMap T) (structureMap T r) = structureMap T (f.eval r) := by
    intro T r
    rw [Polynomial.eval₂_at_apply]
  -- The value of `f` on a candidate.
  have hval : ∀ (r : k) (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X),
      f.eval₂ (structureMap T) (cd (g ≫ c') + chi q χ g * structureMap T r -
        structureMap T r) = (structureMap T (f.eval r) - structureMap T m₀) *
          (VectorGroup.charValue χ T (g ≫ q.hom.hom) ^ N - 1) := by
    intro r T g
    rw [sub_eq_add_neg, hadd, hadd, hneg, ← hqD, hscale, hfeval]
    have hm := hmu (g ≫ q.hom.hom)
    rw [hmuT] at hm
    linear_combination -hm
  -- Comparison on the image of `σ₁`.
  have hkey : ∀ (T : Over (Spec (CommRingCat.of k)))
      (z : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).X),
      (structureMap T (f.eval m₁) - structureMap T m₀) *
        (1 - VectorGroup.charValue χ T (z ≫ σ₁.hom.hom ≫ q.hom.hom) ^ N) = 0 := by
    intro T z
    have h1 := hqD (z ≫ σ₁.hom.hom)
    rw [hφval, mul_sub, mul_one, sub_eq_add_neg, hadd, hneg, mul_comm, hscale, hfeval] at h1
    have hm := hmu (z ≫ σ₁.hom.hom ≫ q.hom.hom)
    rw [hmuT] at hm
    have e : (ClosedAdditivePolynomial.closedPolynomial a).natDegree = N := rfl
    rw [e] at h1
    simp only [Category.assoc] at h1 hm
    linear_combination -h1 - hm
  by_cases hfm : f.eval m₁ = m₀
  · refine hfinish m₁ (fun T g => ?_) (fun T z => by ring)
    rw [hval, hfm, sub_self, zero_mul]
  · have hN1 : ∀ (T : Over (Spec (CommRingCat.of k)))
        (z : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).X),
        VectorGroup.charValue χ T (z ≫ σ₁.hom.hom ≫ q.hom.hom) ^ N = 1 := by
      intro T z
      have hu : IsUnit (structureMap T (f.eval m₁ - m₀)) :=
        (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hfm)).map _
      have h := hkey T z
      rw [← map_sub] at h
      have := (hu.mul_right_eq_zero).mp h
      exact (sub_eq_zero.mp this).symm
    have h1 := hrel₁ hf hN1
    rcases hrel₂ hf h1 with hsurj | hone
    · obtain ⟨r, hr⟩ := hsurj m₀
      refine hfinish r (fun T g => ?_) (fun T z => ?_)
      · rw [hval, hr, sub_self, zero_mul]
      · rw [h1 T z, sub_self, mul_zero]
    · refine hfinish m₁ (fun T g => ?_) (fun T z => by ring)
      rw [hval, hone T (g ≫ q.hom.hom), sub_self, mul_zero]

end Relative

end Langlands.GroupScheme.LinearAdditiveExtension
