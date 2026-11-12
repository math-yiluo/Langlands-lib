import Langlands.AbelianScheme.SeparatingLineBundle.TensorFamily
import Langlands.AbelianScheme.SeparatingLineBundle.RationalPoints
import Langlands.AbelianScheme.AlgebraicallyClosedSeparatingLineBundleStatement
import Langlands.AlgebraicGeometry.Picard.GeometricPicardZero
import Langlands.AlgebraicGeometry.Modules.TensorPowerDistributivity
import Langlands.AlgebraicGeometry.Picard.FiniteSectionSeed
import Langlands.AbelianScheme.FieldTheoremOfTheSquareStatement
import Langlands.AbelianScheme.AlgebraicallyClosedSectionSeedExistenceProof

/-!
# Assembly of a separating line bundle from a section seed and the theorem of the square

Let `G` be a commutative group scheme over an algebraically closed field `K`, irreducible
and locally of finite type. Suppose finitely many line-bundle sections `s i` of `L i`
vanish at the unit, each is nonzero at some rational point, and together they detect
every other rational point and every nonzero tangent vector at the unit. Suppose also
that the theorem of the square holds for each `L i`. Then the tensor product of the
line bundles `(L i ⊗ L i) ⊗ L i` separates rational points and tangent vectors. The
theorem of the square enters through the published statement
`FieldTheoremOfTheSquareStatement`, and the seed through the published statement
`AlgebraicallyClosedSectionSeedExistenceStatement`.

For rational points `a, b` and `c = (a b)⁻¹`, the square theorem identifies
`τ_c^* L ⊗ (τ_a^* L ⊗ τ_b^* L)` with `(L ⊗ L) ⊗ L`. This turns the product of the three
translated sections into a section of the fixed line bundle. Choosing `a, b` for each
factor follows the construction in Milne's proof of Theorem 7.1 (pp.10–11).
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.GroupScheme.SeparatingLineBundle

open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-! ### The square conclusion for one line bundle -/

/-- The conclusion of the theorem of the square for one line bundle:
`τ_{ab}^* L ⊗ L ≅ τ_a^* L ⊗ τ_b^* L` for all rational points `a, b`. It is the body of
`FieldTheoremOfTheSquareStatement` for fixed `G` and `L`. -/
def SquareFor {K : Type u} [Field K] (G : Grp (Over (Spec (CommRingCat.of K))))
    (L : LineBundle G.X.left) : Prop :=
  ∀ a b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X,
    Nonempty (tensorObj ((Scheme.Modules.pullback (translation G (a * b)).left).obj L.obj)
        L.obj ≅
      tensorObj ((Scheme.Modules.pullback (translation G a).left).obj L.obj)
        ((Scheme.Modules.pullback (translation G b).left).obj L.obj))

/-! ### Translations by rational points -/

section Translation

variable {K : Type u} [Field K] {G : Grp (Over (Spec (CommRingCat.of K)))}

/-- Translating a rational point multiplies it. -/
lemma comp_translation (c d : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    d ≫ translation G c = c * d := by
  rw [points_translation, Over.mkIdTerminal.hom_ext (Over.mkIdTerminal.from _) (𝟙 _),
    Category.id_comp]

/-- The underlying-scheme form of `comp_translation`. -/
lemma left_comp_translation (c d : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    d.left ≫ (translation G c).left = (c * d).left := by
  rw [← Over.comp_left, comp_translation]

/-- Composite translations multiply. -/
lemma translation_comp_translation (a b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    translation G a ≫ translation G b = translation G (b * a) := by
  rw [points_translation]
  simp only [translation, MonObj.comp_mul, mul_assoc]

/-- The underlying-scheme form of `translation_comp_translation`. -/
lemma left_translation_comp (a b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    (translation G a).left ≫ (translation G b).left = (translation G (b * a)).left := by
  rw [← Over.comp_left, translation_comp_translation]

/-- The underlying morphism of a rational point over `K` is a rational point. -/
lemma isRationalPoint_left (d : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    IsRationalPoint G.X.hom d.left :=
  Over.w d

/-- A translate of a nonzero tangent vector at a rational point `d` back to the unit is a
nonzero tangent vector at the unit. -/
lemma isNonzeroTangentVectorAt_translate (d : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X)
    {t : Spec (CommRingCat.of (DualNumber K)) ⟶ G.X.left}
    (ht : IsNonzeroTangentVectorAt G.X.hom d.left t) :
    IsNonzeroTangentVectorAt G.X.hom (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X).left
      (t ≫ (translation G d⁻¹).left) := by
  refine ⟨⟨?_, ?_⟩, fun h ↦ ht.2 ?_⟩
  · rw [Category.assoc, Over.w (translation G d⁻¹)]
    exact ht.1.1
  · rw [← Category.assoc, ht.1.2, left_comp_translation, inv_mul_cancel]
  · have ht' : t = (t ≫ (translation G d⁻¹).left) ≫ (translation G d).left := by
      rw [Category.assoc, left_translation_comp, mul_inv_cancel, translation_one, Over.id_left,
        Category.comp_id]
    rw [ht', h, Category.assoc, left_comp_translation, mul_one]

end Translation

/-! ### Common nonvanishing points -/

section Generic

variable {K : Type u} [Field K] [IsAlgClosed K] (G : Grp (Over (Spec (CommRingCat.of K))))
  [LocallyOfFiniteType G.X.hom] [IrreducibleSpace G.X.left]

/-- If, for finitely many endomorphisms `φ k` and sections `u k`, each `u k` is nonzero at
`b ≫ φ k` for some rational point `b`, then one rational point `b` works for all `k`. -/
theorem exists_forall_not_vanishesAlong {J : Type*} [Finite J] (φ : J → (G.X ⟶ G.X))
    (N : J → LineBundle G.X.left) (u : (k : J) → GlobalSections (N k).obj)
    (h : ∀ k, ∃ b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X,
      ¬ VanishesAlong (N k) (b ≫ φ k).left (u k)) :
    ∃ b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X,
      ∀ k, ¬ VanishesAlong (N k) (b ≫ φ k).left (u k) := by
  obtain ⟨x, hx, hmem⟩ := exists_rationalPoint_mem_of_isOpen G.X.hom
    (fun k ↦ ((φ k).left ⁻¹ᵁ trivializationOpen (N k).obj (u k) : Set G.X.left))
    (fun k ↦ ((φ k).left ⁻¹ᵁ trivializationOpen (N k).obj (u k)).isOpen)
    (fun k ↦ by
      obtain ⟨b, hb⟩ := h k
      rw [Over.comp_left] at hb
      exact ⟨b.left (IsLocalRing.closedPoint K),
        (mem_preimage_trivializationOpen_iff _ _ _ _ _).mpr hb⟩)
  refine ⟨Over.homMk x hx, fun k ↦ ?_⟩
  rw [Over.comp_left]
  exact (mem_preimage_trivializationOpen_iff _ _ _ _ _).mp (hmem k)

variable [IsCommMonObj G.X]

/-- Given `d` and `a`, some `b` keeps both `b d` and `(a b)⁻¹ d` off the zero locus of a
section that is nonzero at some rational point. -/
theorem exists_good_second (L : LineBundle G.X.left) (s : GlobalSections L.obj)
    (hs : ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X, ¬ VanishesAlong L y.left s)
    (d a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    ∃ b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X,
      ¬ VanishesAlong L (b * d).left s ∧ ¬ VanishesAlong L ((a * b)⁻¹ * d).left s := by
  obtain ⟨y, hy⟩ := hs
  have key := exists_forall_not_vanishesAlong G
    ![translation G d, (𝟙 G.X)⁻¹ ≫ translation G (a⁻¹ * d)] (fun _ ↦ L) (fun _ ↦ s) (by
      rw [Fin.forall_fin_two]
      refine ⟨⟨d⁻¹ * y, ?_⟩, ⟨y⁻¹ * (a⁻¹ * d), ?_⟩⟩
      · simp only [Matrix.cons_val_zero]
        rw [comp_translation, mul_inv_cancel_left]
        exact hy
      · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [← Category.assoc, GrpObj.comp_inv, Category.comp_id, comp_translation, mul_inv_rev,
          inv_inv, mul_inv_cancel_left]
        exact hy)
  obtain ⟨b, hb⟩ := key
  refine ⟨b, ?_, ?_⟩
  · have h0 := hb 0
    simp only [Matrix.cons_val_zero] at h0
    rwa [comp_translation, mul_comm] at h0
  · have h1 := hb 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
    rwa [← Category.assoc, GrpObj.comp_inv, Category.comp_id, comp_translation, mul_right_comm,
      ← mul_inv] at h1

/-- For every rational point `d`, some `a, b` keep `a d`, `b d` and `(a b)⁻¹ d` off the
zero locus of a section that is nonzero at some rational point. -/
theorem exists_good_pair (L : LineBundle G.X.left) (s : GlobalSections L.obj)
    (hs : ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X, ¬ VanishesAlong L y.left s)
    (d : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    ∃ a b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X,
      ¬ VanishesAlong L (a * d).left s ∧ ¬ VanishesAlong L (b * d).left s ∧
        ¬ VanishesAlong L ((a * b)⁻¹ * d).left s := by
  obtain ⟨y, hy⟩ := hs
  obtain ⟨b, hb⟩ := exists_good_second G L s ⟨y, hy⟩ d (y * d⁻¹)
  refine ⟨y * d⁻¹, b, ?_, hb⟩
  rwa [inv_mul_cancel_right]

end Generic

/-! ### Triple translates -/

section Triple

variable {K : Type u} [Field K] (G : Grp (Over (Spec (CommRingCat.of K))))
  (L : LineBundle G.X.left) (s : GlobalSections L.obj)

/-- The pullback of a line bundle along translation by a rational point. -/
abbrev transLB (c : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) : LineBundle G.X.left :=
  (LineBundle.pullback (translation G c).left).obj L

/-- The pullback of a section along translation by a rational point. -/
abbrev transSection (c : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    GlobalSections (transLB G L c).obj :=
  pullbackSection (translation G c).left L.obj s

/-- The fixed line bundle `(L ⊗ L) ⊗ L` carrying the triple-translate sections. -/
abbrev cubeLB : LineBundle G.X.left := tensorLB (tensorLB L L) L

/-- Pullback along the translation by a point equal to the unit is the identity. -/
def transOneIso (c : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) (hc : c = 1) :
    (Scheme.Modules.pullback (translation G c).left).obj L.obj ≅ L.obj :=
  eqToIso (by rw [hc, translation_one]; rfl) ≪≫ (Scheme.Modules.pullbackId G.X.left).app L.obj

variable {G L} in
/-- The square theorem, applied twice, identifies the triple translate with `(L ⊗ L) ⊗ L`. -/
def tripleIso (hsq : SquareFor G L) (a b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    (tensorLB (transLB G L (a * b)⁻¹) (tensorLB (transLB G L a) (transLB G L b))).obj ≅
      (cubeLB G L).obj :=
  tensorMapIso (Iso.refl _) (hsq a b).some.symm ≪≫
    (tensorAssociator _ _ _).symm ≪≫
      tensorMapIso (hsq (a * b)⁻¹ (a * b)).some.symm (Iso.refl _) ≪≫
        tensorMapIso (tensorMapIso (transOneIso G L _ (inv_mul_cancel (a * b))) (Iso.refl _))
          (Iso.refl _)

variable {G L} in
/-- The triple-translate section `τ_c^* s ⊗ (τ_a^* s ⊗ τ_b^* s)`, `c = (a b)⁻¹`, as a
section of `(L ⊗ L) ⊗ L`. -/
def tripleSection (hsq : SquareFor G L) (a b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    GlobalSections (cubeLB G L).obj :=
  (tripleIso hsq a b).hom.app ⊤
    (tensorSection _ _ (transSection G L s (a * b)⁻¹)
      (tensorSection _ _ (transSection G L s a) (transSection G L s b)))

/-- A translated section vanishes along `f` exactly when the section vanishes along the
translate of `f`. -/
lemma vanishesAlong_transSection_iff {Y : Scheme.{u}}
    (c : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) (f : Y ⟶ G.X.left) :
    VanishesAlong (transLB G L c) f (transSection G L s c) ↔
      VanishesAlong L (f ≫ (translation G c).left) s :=
  vanishesAlong_pullback_iff f _ L s

variable {G L} in
/-- At a rational point `d` the triple section vanishes exactly when `s` vanishes at
`(a b)⁻¹ d`, `a d` or `b d`. -/
theorem vanishesAlong_tripleSection_point_iff (hsq : SquareFor G L)
    (a b d : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    VanishesAlong (cubeLB G L) d.left (tripleSection s hsq a b) ↔
      VanishesAlong L ((a * b)⁻¹ * d).left s ∨ VanishesAlong L (a * d).left s ∨
        VanishesAlong L (b * d).left s := by
  rw [tripleSection, vanishesAlong_mapIso_iff, vanishesAlong_tensor_field_iff,
    vanishesAlong_tensor_field_iff, vanishesAlong_transSection_iff,
    vanishesAlong_transSection_iff, vanishesAlong_transSection_iff, left_comp_translation,
    left_comp_translation, left_comp_translation]

variable {G L} in
/-- Along a tangent vector at a rational point `d` where `s` is nonzero at `b d` and at
`(a b)⁻¹ d`, the triple section vanishes exactly when `s` vanishes along the
`a`-translate of the tangent vector. -/
theorem vanishesAlong_tripleSection_tangent_iff (hsq : SquareFor G L)
    (a b d : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X)
    {t : Spec (CommRingCat.of (DualNumber K)) ⟶ G.X.left}
    (ht : IsTangentVectorAt G.X.hom d.left t) (hb : ¬ VanishesAlong L (b * d).left s)
    (hc : ¬ VanishesAlong L ((a * b)⁻¹ * d).left s) :
    VanishesAlong (cubeLB G L) t (tripleSection s hsq a b) ↔
      VanishesAlong L (t ≫ (translation G a).left) s := by
  rw [← left_comp_translation, ← vanishesAlong_transSection_iff] at hb hc
  rw [tripleSection, vanishesAlong_mapIso_iff,
    vanishesAlong_tensor_left_iff _ _ _ _ t (mem_trivializationOpen_of_isTangentVectorAt ht hc),
    vanishesAlong_tensor_right_iff _ _ _ _ t (mem_trivializationOpen_of_isTangentVectorAt ht hb),
    vanishesAlong_transSection_iff]

end Triple

/-! ### Assembly -/

section Assembly

variable {K : Type u} [Field K] [IsAlgClosed K] (G : Grp (Over (Spec (CommRingCat.of K))))
  [IsCommMonObj G.X] [LocallyOfFiniteType G.X.hom] [IrreducibleSpace G.X.left]

/-- The tensor product of the line bundles `(L i ⊗ L i) ⊗ L i` of a section seed at the
unit separates rational points and tangent vectors, provided the theorem of the square
holds for every `L i`. -/
theorem separatesPointsAndTangents_of_isSeed {n : ℕ} (L : Fin n → LineBundle G.X.left)
    (s : (i : Fin n) → GlobalSections (L i).obj) (hsq : ∀ i, SquareFor G (L i))
    (hseed : IsFinitePointTangentSectionSeed G.X.hom
      (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X).left n L s) :
    SeparatesPointsAndTangents G.X.hom (famBundle n (fun i ↦ cubeLB G (L i))) := by
  have hs : ∀ i, ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X,
      ¬ VanishesAlong (L i) y.left (s i) := fun i ↦ by
    obtain ⟨y, hy, hny⟩ := hseed.2.1 i
    exact ⟨Over.homMk y hy, hny⟩
  -- every rational point comes from a point over the base
  have hpt : ∀ x : Spec (CommRingCat.of K) ⟶ G.X.left, IsRationalPoint G.X.hom x →
      ∃ d : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X, d.left = x :=
    fun x hx ↦ ⟨Over.homMk x hx, rfl⟩
  -- the section for a choice of translation parameters
  let sec : (Fin n → (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X)) →
      (Fin n → (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X)) →
        GlobalSections (famBundle n (fun i ↦ cubeLB G (L i))).obj :=
    fun A B ↦ famSection n _ (fun i ↦ tripleSection (s i) (hsq i) (A i) (B i))
  -- a factor with `a = d⁻¹` vanishes at `d`
  have hvan : ∀ (d : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) A B i0, A i0 = d⁻¹ →
      VanishesAlong _ d.left (sec A B) := by
    intro d A B i0 hA
    rw [vanishesAlong_famSection_field_iff]
    refine ⟨i0, (vanishesAlong_tripleSection_point_iff _ _ _ _ _).mpr (Or.inr (Or.inl ?_))⟩
    rw [hA, inv_mul_cancel]
    exact hseed.1 i0
  refine ⟨fun x hx ↦ ?_, fun x y hx hy hxy ↦ ?_, fun x hx t ht ↦ ?_⟩
  · -- base-point freeness
    obtain ⟨d, rfl⟩ := hpt x hx
    choose a b hab using fun i ↦ exists_good_pair G (L i) (s i) (hs i) d
    refine ⟨sec a b, ?_⟩
    rw [vanishesAlong_famSection_field_iff]
    rintro ⟨i, hi⟩
    rcases (vanishesAlong_tripleSection_point_iff _ _ _ _ _).mp hi with h | h | h
    exacts [(hab i).2.2 h, (hab i).1 h, (hab i).2.1 h]
  · -- separation of rational points
    obtain ⟨dx, rfl⟩ := hpt x hx
    obtain ⟨dy, rfl⟩ := hpt y hy
    have hne : (dx⁻¹ * dy).left ≠ (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X).left := by
      intro h
      apply hxy
      rw [inv_mul_eq_one.mp (Over.OverMorphism.ext h)]
    obtain ⟨i0, hi0⟩ := hseed.2.2.1 _ (isRationalPoint_left _) hne
    obtain ⟨b0, hb0⟩ := exists_good_second G (L i0) (s i0) (hs i0) dy dx⁻¹
    choose a b hab using fun i ↦ exists_good_pair G (L i) (s i) (hs i) dy
    refine ⟨sec (Function.update a i0 dx⁻¹) (Function.update b i0 b0),
      hvan dx _ _ i0 (Function.update_self _ _ _), ?_⟩
    rw [vanishesAlong_famSection_field_iff]
    rintro ⟨i, hi⟩
    rw [vanishesAlong_tripleSection_point_iff] at hi
    by_cases h : i = i0
    · subst h
      simp only [Function.update_self] at hi
      rcases hi with h | h | h
      exacts [hb0.2 h, hi0 h, hb0.1 h]
    · simp only [Function.update_of_ne h] at hi
      rcases hi with h | h | h
      exacts [(hab i).2.2 h, (hab i).1 h, (hab i).2.1 h]
  · -- separation of tangent vectors
    obtain ⟨dx, rfl⟩ := hpt x hx
    obtain ⟨i0, hi0⟩ := hseed.2.2.2 _ (isNonzeroTangentVectorAt_translate dx ht)
    obtain ⟨b0, hb0⟩ := exists_good_second G (L i0) (s i0) (hs i0) dx dx⁻¹
    choose a b hab using fun i ↦ exists_good_pair G (L i) (s i) (hs i) dx
    refine ⟨sec (Function.update a i0 dx⁻¹) (Function.update b i0 b0),
      hvan dx _ _ i0 (Function.update_self _ _ _), ?_⟩
    have ht1 : IsTangentVectorAt G.X.hom dx.left t := ht.1
    rw [vanishesAlong_famSection_iff_of_mem n _ _ t i0 (fun i hi ↦ ?_)]
    · rw [vanishesAlong_tripleSection_tangent_iff _ _ _ _ _ ht1]
      · simpa only [Function.update_self] using hi0
      · simpa only [Function.update_self] using hb0.1
      · simpa only [Function.update_self] using hb0.2
    · refine mem_trivializationOpen_of_isTangentVectorAt ht1 ?_
      rw [vanishesAlong_tripleSection_point_iff]
      simp only [Function.update_of_ne hi]
      rintro (h | h | h)
      exacts [(hab i).2.2 h, (hab i).1 h, (hab i).2.1 h]

end Assembly

/-- The target proposition follows from the published seed existence statement and the
field theorem of the square. -/
theorem algebraicallyClosedSeparatingLineBundle_of_seedExistence
    (hseed : AlgebraicallyClosedSectionSeedExistenceStatement.{u})
    (hsquare : FieldTheoremOfTheSquareStatement.{u}) :
    AlgebraicallyClosedSeparatingLineBundleStatement.{u} := by
  intro K _ _ G _ hsm hpr hgc
  have : Smooth G.X.hom := hsm
  have : IsProper G.X.hom := hpr
  have : GeometricallyConnected G.X.hom := hgc
  have : IrreducibleSpace G.X.left := irreducibleSpace_of_smooth_of_isProper G
  obtain ⟨n, L, s, hs⟩ := hseed K G hsm hpr hgc
  exact ⟨_, separatesPointsAndTangents_of_isSeed G L s
    (fun i ↦ hsquare K G hsm hpr hgc (L i)) hs⟩

/-- The target proposition follows from the field theorem of the square, with the seed
supplied by the published proof `algebraicallyClosedSectionSeedExistence`. -/
theorem algebraicallyClosedSeparatingLineBundle_of_square
    (hsquare : FieldTheoremOfTheSquareStatement.{u}) :
    AlgebraicallyClosedSeparatingLineBundleStatement.{u} :=
  algebraicallyClosedSeparatingLineBundle_of_seedExistence
    algebraicallyClosedSectionSeedExistence hsquare

end Langlands.GroupScheme.SeparatingLineBundle
