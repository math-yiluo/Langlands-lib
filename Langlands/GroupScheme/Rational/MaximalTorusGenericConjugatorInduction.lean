import Langlands.GroupScheme.Rational.MaximalTorusGenericConjugatorBaseChange
import Langlands.GroupScheme.Rational.MaximalTorusGenericConjugatorLift
import Langlands.AlgebraicGeometry.PointTopology.IteratedAffineSpace
import Langlands.GroupScheme.Lie.DimensionInduction
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Induction on the Lie dimension for generic torus conjugators -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

section Reduces

variable (k : Type u) [Field k]

/-- Over a rational function field `K = k(𝔸(m; Spec k))`, every rational function field over
`K` is a rational function field over `k`. -/
theorem reducesRationalFunctionFields_rationalFunctionFieldOver (m : Type u) [Finite m] :
    ReducesRationalFunctionFields (K := (𝔸(m; Spec (CommRingCat.of k))).functionField)
      (rationalFunctionFieldOver k m).hom := by
  intro n hn
  refine ⟨m ⊕ n, inferInstance, ⟨?_⟩⟩
  have e := iteratedFunctionFieldOverIso m n (Spec (CommRingCat.of k))
  refine Over.isoMk (Iso.refl _) ?_ ≪≫ e
  simp [rationalFunctionFieldOver]

end Reduces

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- If `P₁` and `P₂` conjugate `F` onto `F'` after every refinement, then `P₁⁻¹ * N * P₂`
normalizes `F` whenever `N` normalizes `F'`. -/
theorem inv_mul_mul_mem_normalizer {F F' : SubgroupFunctor G} {U : Over S}
    {P₁ P₂ N : U ⟶ G.X}
    (h₁ : ∀ (V : Over S) (a : V ⟶ U) (t : V ⟶ G.X),
      t ∈ F.carrier V ↔ (a ≫ P₁) * t * (a ≫ P₁)⁻¹ ∈ F'.carrier V)
    (h₂ : ∀ (V : Over S) (a : V ⟶ U) (t : V ⟶ G.X),
      t ∈ F.carrier V ↔ (a ≫ P₂) * t * (a ≫ P₂)⁻¹ ∈ F'.carrier V)
    (hN : N ∈ F'.normalizer.carrier U) : P₁⁻¹ * N * P₂ ∈ F.normalizer.carrier U := by
  intro V a t ht
  have hc : a ≫ (P₁⁻¹ * N * P₂) = (a ≫ P₁)⁻¹ * (a ≫ N) * (a ≫ P₂) := by
    rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv]
  rw [hc]
  constructor
  · rw [h₁ V a]
    obtain ⟨hN₁, -⟩ := hN V a _ ((h₂ V a t).1 ht)
    convert hN₁ using 1
    group
  · rw [h₂ V a]
    obtain ⟨-, hN₂⟩ := hN V a _ ((h₁ V a t).1 ht)
    convert hN₂ using 1
    group

/-- A homomorphism sends points normalizing the range of `j` to points normalizing the range
of `j ≫ i`. -/
theorem comp_mem_normalizer_range {K : GroupScheme S} (j : K ⟶ H) (i : H ⟶ G) {U : Over S}
    {x : U ⟶ H.X} (hx : x ∈ (range j).normalizer.carrier U) :
    x ≫ i.hom.hom ∈ (range (j ≫ i)).normalizer.carrier U := by
  intro V a z hz
  obtain ⟨s, rfl⟩ := mem_range.1 hz
  obtain ⟨h₁, h₂⟩ := hx V a (s ≫ j.hom.hom) (mem_range.2 ⟨s, rfl⟩)
  obtain ⟨s₁, h₁⟩ := mem_range.1 h₁
  obtain ⟨s₂, h₂⟩ := mem_range.1 h₂
  let f := IsMonHom.monoidHom i.hom.hom V
  have hf : ∀ y : V ⟶ H.X, f y = y ≫ i.hom.hom := fun _ => rfl
  constructor
  · refine mem_range.2 ⟨s₁, ?_⟩
    have := congrArg f h₁
    rw [map_mul, map_mul, map_inv] at this
    simp only [hf, Category.assoc] at this
    exact this
  · refine mem_range.2 ⟨s₂, ?_⟩
    have := congrArg f h₂
    rw [map_mul, map_mul, map_inv] at this
    simp only [hf, Category.assoc] at this
    exact this

end SubgroupFunctor

section Transfer

variable {k K : Type u} [Field k] [Field K]
  (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T₀ : CommGroupScheme (Spec (CommRingCat.of k))}
  {H : GroupScheme (Spec (CommRingCat.of K))} {T : CommGroupScheme (Spec (CommRingCat.of K))}

/-- Transfer data from a torus `j : T ⟶ H` of a group `H` over `K` with a homomorphism
`i : H ⟶ G_K` to the torus `j₀ : T₀ ⟶ G` over `k`, along `b : Spec K ⟶ Spec k`: a flat,
surjective, quasi-compact `Y` over `K` and `p : Y ⟶ G_K` such that every point of `p`
conjugates the base change of the torus `j₀` onto the torus `j ≫ i`, and such that the map
`H ×_K Y ⟶ G`, `(h, y) ↦ i(h) · p(y)`, has dense range. -/
def IsTorusConjugatorTransfer (j₀ : T₀.toGrp ⟶ G) (j : T.toGrp ⟶ H)
    (i : H ⟶ (GroupScheme.baseChange b).obj G) (Y : Over (Spec (CommRingCat.of K)))
    (p : Y ⟶ ((GroupScheme.baseChange b).obj G).X) : Prop :=
  Flat Y.hom ∧ Surjective Y.hom ∧ QuasiCompact Y.hom ∧
    (∀ (V : Over (Spec (CommRingCat.of K))) (y : V ⟶ Y)
        (t : V ⟶ ((GroupScheme.baseChange b).obj G).X),
      t ∈ ((SubgroupFunctor.range j₀).baseChange b).carrier V ↔
        (y ≫ p) * t * (y ≫ p)⁻¹ ∈ (SubgroupFunctor.range (j ≫ i)).carrier V) ∧
    DenseRange (baseChangePointsEquiv b G
      (Over.mk (pullback.snd H.X.hom Y.hom ≫ Y.hom))
      ((Over.homMk (pullback.fst H.X.hom Y.hom) pullback.condition ≫ i.hom.hom) *
        (Over.homMk (pullback.snd H.X.hom Y.hom) rfl ≫ p))).left

variable {b} {j₀ : T₀.toGrp ⟶ G} {j : T.toGrp ⟶ H}
  {i : H ⟶ (GroupScheme.baseChange b).obj G} {Y : Over (Spec (CommRingCat.of K))}
  {p : Y ⟶ ((GroupScheme.baseChange b).obj G).X}

/-- A generic conjugator for the torus `j` of `H` transfers to a generic conjugator for `j₀`
along transfer data, when rational function fields over `K` are rational function fields
over `k`. -/
theorem HasGenericTorusConjugator.of_transfer (hb : ReducesRationalFunctionFields b)
    (htr : IsTorusConjugatorTransfer b j₀ j i Y p) (h : HasGenericTorusConjugator j) :
    HasGenericTorusConjugator j₀ := by
  obtain ⟨hYflat, hYsurj, hYqc, hconj, hdense⟩ := htr
  obtain ⟨n, hn, X', π', g', hflat, hsurj, hqc, hdesc, hgdense⟩ := h
  obtain ⟨n', hn', ⟨e⟩⟩ := hb n hn
  -- The fibre product `X' ×_K Y` with its projections.
  let X₂ : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd X'.hom Y.hom ≫ Y.hom)
  let pr₁ : X₂ ⟶ X' := Over.homMk (pullback.fst X'.hom Y.hom) pullback.condition
  let pr₂ : X₂ ⟶ Y := Over.homMk (pullback.snd X'.hom Y.hom) rfl
  let GK := (GroupScheme.baseChange b).obj G
  let g₂ : X₂ ⟶ GK.X := (pr₁ ≫ g' ≫ i.hom.hom) * (pr₂ ≫ p)
  let π₂ : X₂ ⟶ rationalFunctionFieldOver K n := pr₁ ≫ π'
  -- The descended data over `k`.
  let X : Over (Spec (CommRingCat.of k)) := (Over.map b).obj X₂
  let π : X ⟶ rationalFunctionFieldOver k n' := (Over.map b).map π₂ ≫ e.hom
  let g : X ⟶ G.X := baseChangePointsEquiv b G X₂ g₂
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have := hflat
  have := hsurj
  have := hqc
  have hpr₁surj : Surjective (pullback.fst X'.hom Y.hom) := by
    rw [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_fst, range_eq_univ,
      Set.preimage_univ]
  refine ⟨n', hn', X, π, g, ?_, ?_, ?_, ?_, ?_⟩
  · change Flat (pullback.fst X'.hom Y.hom ≫ π'.left ≫ e.hom.left)
    infer_instance
  · change Surjective (pullback.fst X'.hom Y.hom ≫ π'.left ≫ e.hom.left)
    infer_instance
  · change QuasiCompact (pullback.fst X'.hom Y.hom ≫ π'.left ≫ e.hom.left)
    infer_instance
  · -- Descent over `K`.
    have hdescK : ∀ (U : Over (Spec (CommRingCat.of K))) (a₁ a₂ : U ⟶ X₂),
        a₁ ≫ π₂ = a₂ ≫ π₂ →
          (a₁ ≫ g₂)⁻¹ * (a₂ ≫ g₂) ∈
            ((SubgroupFunctor.range j₀).baseChange b).normalizer.carrier U := by
      intro U a₁ a₂ ha
      have hn₀ := hdesc U (a₁ ≫ pr₁) (a₂ ≫ pr₁) (by simpa only [Category.assoc] using ha)
      have hN := SubgroupFunctor.comp_mem_normalizer_range j i hn₀
      have hP : ∀ (a₀ : U ⟶ X₂) (V : Over (Spec (CommRingCat.of K))) (a : V ⟶ U)
          (t : V ⟶ GK.X),
          t ∈ ((SubgroupFunctor.range j₀).baseChange b).carrier V ↔
            (a ≫ a₀ ≫ pr₂ ≫ p) * t * (a ≫ a₀ ≫ pr₂ ≫ p)⁻¹ ∈
              (SubgroupFunctor.range (j ≫ i)).carrier V := by
        intro a₀ V a t
        simpa only [Category.assoc] using hconj V (a ≫ a₀ ≫ pr₂) t
      have hmem := SubgroupFunctor.inv_mul_mul_mem_normalizer (hP a₁) (hP a₂) hN
      let f := IsMonHom.monoidHom i.hom.hom U
      have hf : ∀ y : U ⟶ H.X, f y = y ≫ i.hom.hom := fun _ => rfl
      have hfm : ((a₁ ≫ pr₁ ≫ g')⁻¹ * (a₂ ≫ pr₁ ≫ g')) ≫ i.hom.hom =
          (a₁ ≫ pr₁ ≫ g' ≫ i.hom.hom)⁻¹ * (a₂ ≫ pr₁ ≫ g' ≫ i.hom.hom) := by
        rw [← hf, map_mul, map_inv, hf, hf]
        simp only [Category.assoc]
      have hg₂ : ∀ a₀ : U ⟶ X₂,
          a₀ ≫ g₂ = (a₀ ≫ pr₁ ≫ g' ≫ i.hom.hom) * (a₀ ≫ pr₂ ≫ p) := by
        intro a₀
        rw [MonObj.comp_mul]
      simp only [Category.assoc] at hmem
      rw [hfm] at hmem
      rw [hg₂, hg₂]
      convert hmem using 1
      group
    intro U a₁ a₂ ha
    have ha' : a₁ ≫ (Over.map b).map π₂ = a₂ ≫ (Over.map b).map π₂ := by
      simpa only [π, ← Category.assoc, cancel_mono] using ha
    let U' : Over (Spec (CommRingCat.of K)) := Over.mk (a₁.left ≫ X₂.hom)
    have hleft : a₁.left ≫ π₂.left = a₂.left ≫ π₂.left := congrArg (fun f => f.left) ha'
    have h₂ : a₂.left ≫ X₂.hom = a₁.left ≫ X₂.hom := by
      rw [← Over.w π₂, ← Category.assoc, ← hleft, Category.assoc]
    let a₁' : U' ⟶ X₂ := Over.homMk a₁.left rfl
    let a₂' : U' ⟶ X₂ := Over.homMk a₂.left h₂
    have h' := hdescK U' a₁' a₂' (by ext; exact hleft)
    have h'' := SubgroupFunctor.normalizer_le_baseChange b _ U' h'
    rw [SubgroupFunctor.mem_baseChange, map_mul, map_inv] at h''
    let isoU : U ≅ (Over.map b).obj U' :=
      Over.isoMk (Iso.refl _) (by simpa [U', X] using Over.w a₁)
    have hU := (SubgroupFunctor.range j₀).normalizer.comp_mem isoU.hom h''
    have e₁ : isoU.hom ≫ baseChangePointsEquiv b G U' (a₁' ≫ g₂) = a₁ ≫ g := by
      rw [baseChangePointsEquiv_naturality, ← Category.assoc]
      congr 1
    have e₂ : isoU.hom ≫ baseChangePointsEquiv b G U' (a₂' ≫ g₂) = a₂ ≫ g := by
      rw [baseChangePointsEquiv_naturality, ← Category.assoc]
      congr 1
    rw [MonObj.comp_mul, GrpObj.comp_inv, e₁, e₂] at hU
    exact hU
  · -- Density: `X' ×_K Y ⟶ H ×_K Y` has dense range, and so does `H ×_K Y ⟶ G`.
    let P : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd H.X.hom Y.hom ≫ Y.hom)
    let f₁ : P ⟶ H.X := Over.homMk (pullback.fst H.X.hom Y.hom) pullback.condition
    let f₂ : P ⟶ Y := Over.homMk (pullback.snd H.X.hom Y.hom) rfl
    let m : P ⟶ GK.X := (f₁ ≫ i.hom.hom) * (f₂ ≫ p)
    let q : X₂ ⟶ P := Over.homMk
      (pullback.map X'.hom Y.hom H.X.hom Y.hom g'.left (𝟙 _) (𝟙 _)
        (by simp) (by simp)) (by
          simp only [P, X₂, Over.mk_hom]
          rw [pullback.lift_snd_assoc, Category.comp_id])
    have e₁ : q ≫ f₁ = pr₁ ≫ g' := by
      ext
      simp only [q, f₁, pr₁, Over.comp_left, Over.homMk_left]
      rw [pullback.lift_fst]
    have e₂ : q ≫ f₂ = pr₂ := by
      ext
      simp only [q, f₂, pr₂, Over.comp_left, Over.homMk_left]
      rw [pullback.lift_snd, Category.comp_id]
    have hqm : g₂ = q ≫ m := by
      rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, e₁, e₂, Category.assoc]
    have hid : Set.range ⇑(𝟙 Y.left) = Set.univ := Set.range_eq_univ.2 fun y => ⟨y, rfl⟩
    have hq : DenseRange q.left := by
      change DenseRange (pullback.map X'.hom Y.hom H.X.hom Y.hom g'.left (𝟙 _) (𝟙 _)
        (by simp) (by simp))
      rw [DenseRange, Scheme.Pullback.range_map, hid, Set.preimage_univ, Set.inter_univ]
      exact hgdense.preimage (Scheme.Hom.isOpenMap (pullback.fst H.X.hom Y.hom))
    have hdense' : DenseRange (baseChangePointsEquiv b G P m).left := hdense
    change DenseRange (baseChangePointsEquiv b G X₂ g₂).left
    rw [hqm, baseChangePointsEquiv_naturality, Over.comp_left]
    exact hdense'.comp hq (Scheme.Hom.continuous _)

end Transfer

section Induction

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T₀ : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Reduction of the torus `j₀` to a maximal torus of a group of Lie dimension below `d`: a
field `K` with `b : Spec K ⟶ Spec k` whose rational function fields are rational function
fields over `k`, a smooth connected affine group `H` over `K` with Lie dimension below `d`, a
maximal torus `j` of `H`, a homomorphism `i : H ⟶ G_K` and transfer data from `j` to `j₀`. -/
def HasSmallerTorusConjugatorReduction (j₀ : T₀.toGrp ⟶ G) (d : ℕ) : Prop :=
  ∃ (K : Type u) (_ : Field K) (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)),
    ReducesRationalFunctionFields b ∧
    ∃ (H : GroupScheme (Spec (CommRingCat.of K))) (_ : Smooth H.X.hom)
      (_ : IsAffineHom H.X.hom) (_ : ConnectedSpace H.X.left)
      (T : CommGroupScheme (Spec (CommRingCat.of K))) (j : T.toGrp ⟶ H)
      (i : H ⟶ (GroupScheme.baseChange b).obj G) (Y : Over (Spec (CommRingCat.of K)))
      (p : Y ⟶ ((GroupScheme.baseChange b).obj G).X),
      IsMaximalTorus j ∧ Lie.dimension H < d ∧ IsTorusConjugatorTransfer b j₀ j i Y p

/-- A reduction to groups of Lie dimension below `d` gives a generic conjugator, when all
maximal tori of smooth connected affine groups of Lie dimension below `d` have one. -/
theorem HasSmallerTorusConjugatorReduction.hasGenericTorusConjugator {j₀ : T₀.toGrp ⟶ G}
    {d : ℕ} (h : HasSmallerTorusConjugatorReduction j₀ d)
    (ih : ∀ (K : Type u) [Field K] (H : GroupScheme (Spec (CommRingCat.of K)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
      Lie.dimension H < d → ∀ (T : CommGroupScheme (Spec (CommRingCat.of K)))
        (j : T.toGrp ⟶ H), IsMaximalTorus j → HasGenericTorusConjugator j) :
    HasGenericTorusConjugator j₀ := by
  obtain ⟨K, _, b, hb, H, _, _, _, T, j, i, Y, p, hj, hd, htr⟩ := h
  exact HasGenericTorusConjugator.of_transfer hb htr (ih K H hd T j hj)

/-- Every maximal torus of a smooth connected affine group over a field reduces, along a
flat, surjective, quasi-compact, universally open homomorphism reflecting torus normalizers,
either to a torus normalized by every point or to a maximal torus of a group of smaller Lie
dimension. -/
def MaximalTorusConjugatorReductionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T₀ : CommGroupScheme (Spec (CommRingCat.of k))) (j₀ : T₀.toGrp ⟶ G),
    IsMaximalTorus j₀ →
      ∃ (G' : GroupScheme (Spec (CommRingCat.of k))) (_ : Flat G'.X.hom)
        (_ : QuasiCompact G'.X.hom) (T₀' : CommGroupScheme (Spec (CommRingCat.of k)))
        (j₀' : T₀'.toGrp ⟶ G') (φ : G ⟶ G'),
        Flat φ.hom.hom.left ∧ Surjective φ.hom.hom.left ∧ QuasiCompact φ.hom.hom.left ∧
          UniversallyOpen φ.hom.hom.left ∧ ReflectsTorusNormalizer φ j₀ j₀' ∧
          ((∀ (U : Over (Spec (CommRingCat.of k))) (g : U ⟶ G'.X),
              g ∈ (torusNormalizer j₀').carrier U) ∨
            HasSmallerTorusConjugatorReduction j₀' (Lie.dimension G))

/-- The reduction statement implies the generic conjugator statement, by strong induction on
the Lie dimension across all fields. -/
theorem maximalTorusGenericConjugator_of_reduction
    (h : MaximalTorusConjugatorReductionStatement.{u}) :
    MaximalTorusGenericConjugatorStatement.{u} := by
  have key : ∀ (d : ℕ) (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
      Lie.dimension G = d → ∀ (T₀ : CommGroupScheme (Spec (CommRingCat.of k)))
        (j₀ : T₀.toGrp ⟶ G), IsMaximalTorus j₀ → HasGenericTorusConjugator j₀ := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro k _ G _ _ _ hd T₀ j₀ hj₀
      obtain ⟨G', _, _, T₀', j₀', φ, h₁, h₂, h₃, h₄, hφ, hcase⟩ := h k G T₀ j₀ hj₀
      have := h₁
      have := h₂
      have := h₃
      have := h₄
      apply HasGenericTorusConjugator.of_hom φ hφ
      rcases hcase with hN | hC
      · exact hasGenericTorusConjugator_of_normalizer_eq_top hN
      · apply hC.hasGenericTorusConjugator
        intro K _ H _ _ _ hH T j hj
        exact ih _ (hd ▸ hH) K H rfl T j hj
  intro k _ G _ _ _ T₀ j₀ hj₀
  exact key _ k G rfl T₀ j₀ hj₀

/-- The reduction statement implies unirationality of every actual parameter scheme. -/
theorem maximalTorusParameterUnirational_of_reduction
    (h : MaximalTorusConjugatorReductionStatement.{u}) :
    MaximalTorusParameterUnirationalStatement.{u} :=
  maximalTorusParameterUnirational_of_genericConjugator
    (maximalTorusGenericConjugator_of_reduction h)

end Induction

end Langlands.GroupScheme
