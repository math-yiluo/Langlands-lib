/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
# The hom complex of a bifunctor

Let `H : Cᵒᵖ ⥤ D ⥤ E` be a bifunctor, contravariant in the first variable and additive in each
variable, with values in a preadditive category `E` with countable products. For cochain
complexes `K` in `C` and `Y` in `D`, the *hom complex* `CochainComplex.bifunctorHomObj H K Y`
has in degree `n` the product `∏_{p + n = q} H(K^p, Y^q)`, and differential with component
`(-1)ᵖ • (π_{p, q - 1} ≫ H(K^p, d_Y) - π_{p + 1, q} ≫ H(d_K, Y^q))` on the factor indexed by
`(p, q)`. For `H` the internal hom of a closed monoidal category this is
`CochainComplex.internalHomObj`; here `H` is arbitrary, which allows internal homs of module
objects or of sheaves with an extra structure, which do not come from a monoidal structure.

The hom complex is functorial in `Y` (`CochainComplex.bifunctorHomMapRight`) and
contravariantly in `K` (`CochainComplex.bifunctorHomMapLeft`).

Suppose given an object `P` of `E` and a functor `T : C ⥤ D` with natural bijections
`(P ⟶ H(M, N)) ≃ (T M ⟶ N)` (for instance `P` the free module on a point and `H` an internal
hom, `T = P ⊗ -`). Then morphisms `P ⟶ (bifunctorHomObj H K Y)^n` are the cochains of degree
`n` from `T K` to `Y` (`CochainComplex.BifunctorHom.cochainEquiv`), compatibly with the
differentials. Hence, if `T K` is acyclic and `Y` is K-injective, every morphism from `P` to the
cycles of `bifunctorHomObj H K Y` lifts to the previous degree
(`CochainComplex.BifunctorHom.exists_comp_d_eq`): this is the acyclicity of the hom complex
"seen from `P`".
-/

@[expose] public section

open CategoryTheory Category Limits Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CochainComplex

open HomComplex

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] [Preadditive C] [Preadditive D] [Preadditive E]
  [HasCountableProducts E] (H : Cᵒᵖ ⥤ D ⥤ E)

namespace BifunctorHom

/-- The differential of the hom complex `bifunctorHomObj H K Y`. Use `bifunctorHomObj_d_π`
instead of unfolding it. -/
noncomputable def d (K : CochainComplex C ℤ) (Y : CochainComplex D ℤ) (n m : ℤ) :
    (∏ᶜ fun T : Triplet n ↦ (H.obj (op (K.X T.p))).obj (Y.X T.q)) ⟶
      ∏ᶜ fun T : Triplet m ↦ (H.obj (op (K.X T.p))).obj (Y.X T.q) :=
  Pi.lift fun T ↦ T.p.negOnePow •
    (Pi.π (fun T : Triplet n ↦ (H.obj (op (K.X T.p))).obj (Y.X T.q)) ⟨T.p, T.p + n, rfl⟩ ≫
        (H.obj _).map (Y.d (T.p + n) T.q) -
      Pi.π (fun T : Triplet n ↦ (H.obj (op (K.X T.p))).obj (Y.X T.q))
          ⟨T.p + m - n, T.q, by grind [T.hpq]⟩ ≫
        (H.map (K.d T.p (T.p + m - n)).op).app _)

lemma d_π (K : CochainComplex C ℤ) (Y : CochainComplex D ℤ) (n m p q : ℤ) (hpq : p + m = q)
    (q' p' : ℤ) (hq' : p + n = q') (hp' : p' + n = q) :
    d H K Y n m ≫ Pi.π _ (⟨p, q, hpq⟩ : Triplet m) = p.negOnePow •
      (Pi.π (fun T : Triplet n ↦ (H.obj (op (K.X T.p))).obj (Y.X T.q)) ⟨p, q', hq'⟩ ≫
          (H.obj _).map (Y.d q' q) -
        Pi.π (fun T : Triplet n ↦ (H.obj (op (K.X T.p))).obj (Y.X T.q)) ⟨p', q, hp'⟩ ≫
          (H.map (K.d p p').op).app _) := by
  subst hq'
  obtain rfl : p' = p + m - n := by lia
  simp only [d, Pi.lift_comp_π]

variable [∀ X, (H.obj X).Additive] [H.Additive] (K : CochainComplex C ℤ)
  (Y : CochainComplex D ℤ)

lemma shape (n m : ℤ) (hnm : ¬ n + 1 = m) : d H K Y n m = 0 := by
  refine Pi.hom_ext _ _ fun ⟨p, q, hpq⟩ ↦ ?_
  rw [d_π H K Y n m p q hpq (p + n) (p + m - n) rfl (by lia), Y.shape, K.shape]
  · simp
  all_goals
    simp only [ComplexShape.up_Rel]
    lia

lemma d_comp_d (n₁ n₂ n₃ : ℤ) : d H K Y n₁ n₂ ≫ d H K Y n₂ n₃ = 0 := by
  by_cases h₁₂ : n₁ + 1 = n₂
  · by_cases h₂₃ : n₂ + 1 = n₃
    · refine Pi.hom_ext _ _ fun ⟨p, q, hpq⟩ ↦ ?_
      rw [assoc, d_π H K Y n₂ n₃ p q hpq (q - 1) (p + 1) (by lia) (by lia),
        Linear.comp_units_smul, Preadditive.comp_sub,
        reassoc_of% (d_π H K Y n₁ n₂ p (q - 1) (by lia) (q - 2) (p + 1) (by lia) (by lia)),
        reassoc_of% (d_π H K Y n₁ n₂ (p + 1) q (by lia) (q - 1) (p + 2) (by lia) (by lia))]
      simp only [Linear.units_smul_comp, Preadditive.sub_comp, assoc, ← Functor.map_comp,
        HomologicalComplex.d_comp_d, Functor.map_zero, comp_zero, ← NatTrans.comp_app,
        ← op_comp, op_zero, NatTrans.app_zero, zero_comp, NatTrans.naturality,
        zero_sub, Int.negOnePow_succ, Units.neg_smul, Preadditive.neg_comp, smul_neg, smul_sub,
        smul_smul, Int.units_mul_self, one_smul]
      abel
    · rw [shape H K Y n₂ n₃ h₂₃, comp_zero]
  · rw [shape H K Y n₁ n₂ h₁₂, zero_comp]

end BifunctorHom

variable [∀ X, (H.obj X).Additive] [H.Additive] (K : CochainComplex C ℤ)
  (Y : CochainComplex D ℤ)

/-- The hom complex of a bifunctor `H`: in degree `n`, the product of the `H(K^p, Y^q)` for
`p + n = q`. -/
noncomputable def bifunctorHomObj : CochainComplex E ℤ where
  X n := ∏ᶜ fun T : Triplet n ↦ (H.obj (op (K.X T.p))).obj (Y.X T.q)
  d := BifunctorHom.d H K Y
  shape n m h := BifunctorHom.shape H K Y n m h
  d_comp_d' _ _ _ _ _ := BifunctorHom.d_comp_d H K Y _ _ _

/-- The projection from the object of degree `n` of `bifunctorHomObj H K Y` to the factor
`H(K^p, Y^q)`, for `p + n = q`. -/
noncomputable def bifunctorHomπ (n p q : ℤ) (h : p + n = q) :
    (bifunctorHomObj H K Y).X n ⟶ (H.obj (op (K.X p))).obj (Y.X q) :=
  Pi.π _ (⟨p, q, h⟩ : Triplet n)

variable {H K Y} in
@[ext]
lemma bifunctorHomObj_hom_ext {A : E} {n : ℤ} {f g : A ⟶ (bifunctorHomObj H K Y).X n}
    (h : ∀ p q hpq, f ≫ bifunctorHomπ H K Y n p q hpq = g ≫ bifunctorHomπ H K Y n p q hpq) :
    f = g :=
  Pi.hom_ext _ _ fun T ↦ h T.p T.q T.hpq

/-- A morphism into the object of degree `n` of the hom complex, from its components. -/
noncomputable def bifunctorHomLift {A : E} (n : ℤ)
    (f : ∀ p q (_ : p + n = q), A ⟶ (H.obj (op (K.X p))).obj (Y.X q)) :
    A ⟶ (bifunctorHomObj H K Y).X n :=
  Pi.lift fun T ↦ f T.p T.q T.hpq

@[reassoc (attr := simp)]
lemma bifunctorHomLift_π {A : E} (n : ℤ)
    (f : ∀ p q (_ : p + n = q), A ⟶ (H.obj (op (K.X p))).obj (Y.X q)) (p q : ℤ)
    (hpq : p + n = q) :
    bifunctorHomLift H K Y n f ≫ bifunctorHomπ H K Y n p q hpq = f p q hpq :=
  Pi.lift_comp_π _ _

/-- The components of the differential of the hom complex. -/
@[reassoc]
lemma bifunctorHomObj_d_π (n m p q : ℤ) (hpq : p + m = q) (q' p' : ℤ) (hq' : p + n = q')
    (hp' : p' + n = q) :
    (bifunctorHomObj H K Y).d n m ≫ bifunctorHomπ H K Y m p q hpq = p.negOnePow •
      (bifunctorHomπ H K Y n p q' hq' ≫ (H.obj _).map (Y.d q' q) -
        bifunctorHomπ H K Y n p' q hp' ≫ (H.map (K.d p p').op).app _) :=
  BifunctorHom.d_π H K Y n m p q hpq q' p' hq' hp'

section Functoriality

variable {H K Y}

/-- The morphism of hom complexes induced by a morphism `g : Y ⟶ Y'` in the second variable. -/
noncomputable def bifunctorHomMapRight {Y' : CochainComplex D ℤ} (g : Y ⟶ Y') :
    bifunctorHomObj H K Y ⟶ bifunctorHomObj H K Y' where
  f n := bifunctorHomLift H K Y' n fun p q hpq ↦
    bifunctorHomπ H K Y n p q hpq ≫ (H.obj _).map (g.f q)
  comm' n m hnm := by
    ext p q hpq
    simp only [ComplexShape.up_Rel] at hnm
    rw [assoc, bifunctorHomObj_d_π H K Y' n m p q hpq (q - 1) (p + 1) (by lia) (by lia), assoc,
      bifunctorHomLift_π, bifunctorHomObj_d_π_assoc H K Y n m p q hpq (q - 1) (p + 1) (by lia)
        (by lia)]
    simp only [Linear.comp_units_smul, Linear.units_smul_comp, Preadditive.comp_sub,
      Preadditive.sub_comp, assoc, bifunctorHomLift_π_assoc, ← Functor.map_comp, g.comm,
      NatTrans.naturality]

@[reassoc (attr := simp)]
lemma bifunctorHomMapRight_f_π {Y' : CochainComplex D ℤ} (g : Y ⟶ Y') (n p q : ℤ)
    (hpq : p + n = q) :
    (bifunctorHomMapRight (H := H) (K := K) g).f n ≫ bifunctorHomπ H K Y' n p q hpq =
      bifunctorHomπ H K Y n p q hpq ≫ (H.obj _).map (g.f q) :=
  by simp [bifunctorHomMapRight]

/-- The morphism of hom complexes induced by a morphism `f : K' ⟶ K` in the first variable. -/
noncomputable def bifunctorHomMapLeft {K' : CochainComplex C ℤ} (f : K' ⟶ K) :
    bifunctorHomObj H K Y ⟶ bifunctorHomObj H K' Y where
  f n := bifunctorHomLift H K' Y n fun p q hpq ↦
    bifunctorHomπ H K Y n p q hpq ≫ (H.map (f.f p).op).app _
  comm' n m hnm := by
    ext p q hpq
    simp only [ComplexShape.up_Rel] at hnm
    rw [assoc, bifunctorHomObj_d_π H K' Y n m p q hpq (q - 1) (p + 1) (by lia) (by lia), assoc,
      bifunctorHomLift_π, bifunctorHomObj_d_π_assoc H K Y n m p q hpq (q - 1) (p + 1) (by lia)
        (by lia)]
    simp only [Linear.comp_units_smul, Linear.units_smul_comp, Preadditive.comp_sub,
      Preadditive.sub_comp, assoc, bifunctorHomLift_π_assoc, NatTrans.naturality,
      ← NatTrans.comp_app, ← Functor.map_comp, ← op_comp, f.comm]

@[reassoc (attr := simp)]
lemma bifunctorHomMapLeft_f_π {K' : CochainComplex C ℤ} (f : K' ⟶ K) (n p q : ℤ)
    (hpq : p + n = q) :
    (bifunctorHomMapLeft (H := H) (Y := Y) f).f n ≫ bifunctorHomπ H K' Y n p q hpq =
      bifunctorHomπ H K Y n p q hpq ≫ (H.map (f.f p).op).app _ :=
  by simp [bifunctorHomMapLeft]

lemma bifunctorHomMapRight_id : bifunctorHomMapRight (H := H) (K := K) (𝟙 Y) = 𝟙 _ := by
  ext n p q hpq
  simp

lemma bifunctorHomMapRight_comp {Y' Y'' : CochainComplex D ℤ} (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    bifunctorHomMapRight (H := H) (K := K) (g ≫ g') =
      bifunctorHomMapRight g ≫ bifunctorHomMapRight g' := by
  ext n p q hpq
  simp

lemma bifunctorHomMapLeft_id : bifunctorHomMapLeft (H := H) (Y := Y) (𝟙 K) = 𝟙 _ := by
  ext n p q hpq
  simp

lemma bifunctorHomMapLeft_comp {K' K'' : CochainComplex C ℤ} (f : K' ⟶ K) (f' : K'' ⟶ K') :
    bifunctorHomMapLeft (H := H) (Y := Y) (f' ≫ f) =
      bifunctorHomMapLeft f ≫ bifunctorHomMapLeft f' := by
  ext n p q hpq
  simp [← NatTrans.comp_app, ← Functor.map_comp]

/-- The cochain of degree `a` between hom complexes induced by a cochain `c : Cochain K' K a` in
the first variable, with the sign `(-1)^(p a)` on the factor indexed by `(p, q)`. -/
noncomputable def bifunctorHomMapLeftCochain {K' : CochainComplex C ℤ} {a : ℤ}
    (c : Cochain K' K a) : Cochain (bifunctorHomObj H K Y) (bifunctorHomObj H K' Y) a :=
  Cochain.mk fun n n' _ ↦ bifunctorHomLift H K' Y n' fun p' q' _ ↦
    (p' * a).negOnePow • (bifunctorHomπ H K Y n (p' + a) q' (by lia) ≫
      (H.map (c.v p' (p' + a) rfl).op).app _)

@[reassoc]
lemma bifunctorHomMapLeftCochain_v_π {K' : CochainComplex C ℤ} {a : ℤ} (c : Cochain K' K a)
    (n n' : ℤ) (hnn' : n + a = n') (p' q' : ℤ) (hpq' : p' + n' = q') (p : ℤ) (hp : p' + a = p)
    (hpq : p + n = q') :
    (bifunctorHomMapLeftCochain (H := H) (Y := Y) c).v n n' hnn' ≫
        bifunctorHomπ H K' Y n' p' q' hpq' =
      (p' * a).negOnePow • (bifunctorHomπ H K Y n p q' hpq ≫ (H.map (c.v p' p hp).op).app _) := by
  subst hp
  simp [bifunctorHomMapLeftCochain]

lemma bifunctorHomMapLeftCochain_ofHom {K' : CochainComplex C ℤ} (f : K' ⟶ K) :
    bifunctorHomMapLeftCochain (H := H) (Y := Y) (Cochain.ofHom f) =
      Cochain.ofHom (bifunctorHomMapLeft f) := by
  ext n p' q' hpq'
  rw [bifunctorHomMapLeftCochain_v_π _ n n (add_zero n) p' q' hpq' p' (add_zero p') hpq',
    Cochain.ofHom_v, Cochain.ofHom_v, bifunctorHomMapLeft_f_π, mul_zero, Int.negOnePow_zero,
    one_smul]

lemma bifunctorHomMapLeftCochain_add {K' : CochainComplex C ℤ} {a : ℤ} (c₁ c₂ : Cochain K' K a) :
    bifunctorHomMapLeftCochain (H := H) (Y := Y) (c₁ + c₂) =
      bifunctorHomMapLeftCochain c₁ + bifunctorHomMapLeftCochain c₂ := by
  ext n n' hnn' p' q' hpq'
  simp only [Cochain.add_v, Preadditive.add_comp,
    bifunctorHomMapLeftCochain_v_π _ n n' hnn' p' q' hpq' (p' + a) rfl (by lia), op_add,
    Functor.map_add, NatTrans.app_add, Preadditive.comp_add, smul_add]

lemma δ_bifunctorHomMapLeftCochain {K' : CochainComplex C ℤ} (a b : ℤ) (hab : a + 1 = b)
    (c : Cochain K' K a) :
    δ a b (bifunctorHomMapLeftCochain (H := H) (Y := Y) c) =
      bifunctorHomMapLeftCochain (δ a b c) := by
  obtain rfl : b = a + 1 := hab.symm
  ext n n' hnn' p' q' hpq'
  have e1 := bifunctorHomObj_d_π H K' Y (n' - 1) n' p' q' hpq' (q' - 1) (p' + 1) (by lia) (by lia)
  have e2 := bifunctorHomMapLeftCochain_v_π (H := H) (Y := Y) c (n + 1) n' (by lia) p' q' hpq'
    (p' + a) rfl (by lia)
  have e3 := bifunctorHomMapLeftCochain_v_π (H := H) (Y := Y) c n (n' - 1) (by lia) p'
    (q' - 1) (by lia) (p' + a) rfl (by lia)
  have e4 := bifunctorHomMapLeftCochain_v_π (H := H) (Y := Y) c n (n' - 1) (by lia)
    (p' + 1) q' (by lia) (p' + a + 1) (by lia) (by lia)
  have e5 := bifunctorHomObj_d_π H K Y n (n + 1) (p' + a) q' (by lia) (q' - 1) (p' + a + 1)
    (by lia) (by lia)
  have e6 := bifunctorHomMapLeftCochain_v_π (H := H) (Y := Y) (δ a (a + 1) c) n n' hnn' p' q'
    hpq' (p' + a + 1) (by lia) (by lia)
  have e7 := δ_v a (a + 1) rfl c p' (p' + a + 1) (by lia) (p' + a) (p' + 1) (by lia) rfl
  rw [δ_v a (a + 1) rfl _ n n' hnn' (n' - 1) (n + 1) (by lia) rfl]
  simp only [Preadditive.add_comp, assoc, e1, e2, e6, e7, Linear.units_smul_comp,
    Linear.comp_units_smul, Preadditive.comp_sub, Preadditive.sub_comp, reassoc_of% e3,
    reassoc_of% e4, reassoc_of% e5]
  simp only [Units.smul_def, op_comp, op_add, Functor.map_comp, Functor.map_add,
    NatTrans.comp_app, NatTrans.app_add, NatTrans.naturality, Preadditive.comp_add,
    Preadditive.comp_zsmul, smul_sub, smul_add, smul_smul, op_zsmul, Functor.map_zsmul,
    NatTrans.app_zsmul, ← Units.val_mul, ← Int.negOnePow_add]
  have h₁ : (a + 1 + (p' * a + (p' + a))).negOnePow = -(p' + p' * a).negOnePow := by
    rw [← Int.negOnePow_succ]
    exact (Int.negOnePow_eq_iff _ _).2 ⟨a, by ring⟩
  have h₂ : (a + 1 + (p' * a + (p' + a))).negOnePow = -(p' * (a + 1)).negOnePow := by
    rw [← Int.negOnePow_succ]
    exact (Int.negOnePow_eq_iff _ _).2 ⟨a, by ring⟩
  have h₃ : (p' * (a + 1) + (a + 1)).negOnePow = -(p' + (p' + 1) * a).negOnePow := by
    rw [← Int.negOnePow_succ]
    exact (Int.negOnePow_eq_iff _ _).2 ⟨0, by ring⟩
  rw [h₃]
  nth_rw 1 [h₁]
  rw [h₂]
  simp only [Units.val_neg, neg_smul]
  abel

/-- A homotopy between `f, g : K' ⟶ K` induces a homotopy between the induced morphisms of hom
complexes. -/
noncomputable def bifunctorHomMapLeftHomotopy {K' : CochainComplex C ℤ} {f g : K' ⟶ K}
    (h : Homotopy f g) :
    Homotopy (bifunctorHomMapLeft (H := H) (Y := Y) f) (bifunctorHomMapLeft g) :=
  (Cochain.equivHomotopy _ _).symm ⟨bifunctorHomMapLeftCochain (Cochain.ofHomotopy h), by
    rw [← bifunctorHomMapLeftCochain_ofHom, ← bifunctorHomMapLeftCochain_ofHom,
      δ_bifunctorHomMapLeftCochain (-1) 0 (by lia), ← bifunctorHomMapLeftCochain_add,
      δ_ofHomotopy, sub_add_cancel]⟩

end Functoriality

section KInjective

variable {C' : Type*} [Category* C'] [Abelian C']

/-- A cocycle of degree `n` from an acyclic complex to a K-injective complex is a coboundary. -/
lemma HomComplex.exists_δ_eq_of_isKInjective {A Y : CochainComplex C' ℤ} (hA : A.Acyclic)
    [Y.IsKInjective] {n : ℤ} (z : Cochain A Y n) (hz : δ n (n + 1) z = 0) (m : ℤ)
    (hm : m + 1 = n) : ∃ w : Cochain A Y m, δ m n w = z := by
  let z₀ : Cocycle A (Y⟦n⟧) 0 := (Cocycle.mk z (n + 1) rfl hz).rightShift n 0 (zero_add n)
  obtain ⟨h, hh⟩ := Cochain.equivHomotopy (Cocycle.homOf z₀) 0
    (IsKInjective.homotopyZero (Cocycle.homOf z₀) hA)
  rw [Cocycle.cochain_ofHom_homOf_eq_coe, Cochain.ofHom_zero, add_zero] at hh
  refine ⟨n.negOnePow • h.rightUnshift m (by lia), ?_⟩
  rw [δ_units_smul, Cochain.δ_rightUnshift _ m (by lia) n 0 (zero_add n), ← hh, smul_smul,
    Int.units_mul_self, one_smul]
  exact Cochain.rightUnshift_rightShift z n 0 (zero_add n)

end KInjective

namespace BifunctorHom

variable {H} {K Y} (P : E) (T : C ⥤ D) [T.Additive]
  (e : ∀ M N, (P ⟶ (H.obj (op M)).obj N) ≃+ (T.obj M ⟶ N))
  (he₁ : ∀ M N N' (φ : P ⟶ (H.obj (op M)).obj N) (g : N ⟶ N'),
    e M N' (φ ≫ (H.obj _).map g) = e M N φ ≫ g)
  (he₂ : ∀ M M' N (φ : P ⟶ (H.obj (op M)).obj N) (u : M' ⟶ M),
    e M' N (φ ≫ (H.map u.op).app N) = T.map u ≫ e M N φ)

/-- Morphisms from `P` to the object of degree `n` of the hom complex are the cochains of degree
`n` from `T K` to `Y`, when `P ⟶ H(M, N)` is naturally `T M ⟶ N`. The sign `(-1)^(p n)` makes
this compatible with the differentials (`BifunctorHom.cochainEquiv_comp_d`). -/
noncomputable def cochainEquiv (n : ℤ) :
    (P ⟶ (bifunctorHomObj H K Y).X n) ≃+ Cochain ((T.mapHomologicalComplex _).obj K) Y n where
  toFun φ := Cochain.mk fun p q hpq ↦ (p * n).negOnePow •
    e (K.X p) (Y.X q) (φ ≫ bifunctorHomπ H K Y n p q hpq)
  invFun z := bifunctorHomLift H K Y n fun p q hpq ↦ (p * n).negOnePow •
    (e (K.X p) (Y.X q)).symm (z.v p q hpq)
  left_inv φ := by
    ext p q hpq
    simp [smul_smul]
  right_inv z := by
    ext p q hpq
    simp [smul_smul]
  map_add' φ φ' := by
    ext p q hpq
    simp [Preadditive.add_comp]

lemma cochainEquiv_v (n : ℤ) (φ : P ⟶ (bifunctorHomObj H K Y).X n) (p q : ℤ) (hpq : p + n = q) :
    (cochainEquiv P T e n φ).v p q hpq =
      (p * n).negOnePow • e (K.X p) (Y.X q) (φ ≫ bifunctorHomπ H K Y n p q hpq) := by
  simp [cochainEquiv]

include he₁ he₂ in
/-- `BifunctorHom.cochainEquiv` commutes with the differentials. -/
lemma cochainEquiv_comp_d (n m : ℤ) (hnm : n + 1 = m) (φ : P ⟶ (bifunctorHomObj H K Y).X n) :
    cochainEquiv P T e m (φ ≫ (bifunctorHomObj H K Y).d n m) =
      δ n m (cochainEquiv P T e n φ) := by
  ext p q hpq
  rw [cochainEquiv_v, δ_v n m hnm _ p q hpq (q - 1) (p + 1) (by lia) rfl, cochainEquiv_v,
    cochainEquiv_v, assoc, bifunctorHomObj_d_π H K Y n m p q hpq (q - 1) (p + 1) (by lia)
      (by lia)]
  subst hnm
  simp only [Units.smul_def, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Preadditive.comp_sub,
    map_zsmul, map_sub, ← assoc, he₁, he₂,
    Functor.mapHomologicalComplex_obj_d, smul_sub, smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
  have h₁ : (p * (n + 1) + p).negOnePow = (p * n).negOnePow :=
    (Int.negOnePow_eq_iff _ _).2 ⟨p, by ring⟩
  have h₂ : (n + 1 + (p + 1) * n).negOnePow = -(p * (n + 1) + p).negOnePow := by
    rw [← Int.negOnePow_succ]
    exact (Int.negOnePow_eq_iff _ _).2 ⟨n - p, by ring⟩
  rw [h₂, h₁, Units.val_neg, neg_smul, sub_eq_add_neg]

include he₁ he₂ in
/-- **Acyclicity of the hom complex seen from `P`.** If every cocycle of degree `n` from `T K` to
`Y` is a coboundary (for instance if `T K` is acyclic and `Y` is K-injective,
`CochainComplex.HomComplex.exists_δ_eq_of_isKInjective`), then a morphism
`φ : P ⟶ (bifunctorHomObj H K Y)^n` whose composition with the differential vanishes is the
image of a morphism `P ⟶ (bifunctorHomObj H K Y)^m`, `m + 1 = n`. -/
theorem exists_comp_d_eq (n m : ℤ) (hmn : m + 1 = n)
    (hex : ∀ z : Cochain ((T.mapHomologicalComplex _).obj K) Y n, δ n (n + 1) z = 0 →
      ∃ w : Cochain ((T.mapHomologicalComplex _).obj K) Y m, δ m n w = z)
    (φ : P ⟶ (bifunctorHomObj H K Y).X n)
    (hφ : φ ≫ (bifunctorHomObj H K Y).d n (n + 1) = 0) :
    ∃ ψ : P ⟶ (bifunctorHomObj H K Y).X m, ψ ≫ (bifunctorHomObj H K Y).d m n = φ := by
  obtain ⟨w, hw⟩ := hex (cochainEquiv P T e n φ)
    (by rw [← cochainEquiv_comp_d P T e he₁ he₂ n (n + 1) rfl, hφ, map_zero])
  refine ⟨(cochainEquiv P T e m).symm w, (cochainEquiv P T e n).injective ?_⟩
  rw [cochainEquiv_comp_d P T e he₁ he₂ m n hmn, AddEquiv.apply_symm_apply, hw]

end BifunctorHom

end CochainComplex
