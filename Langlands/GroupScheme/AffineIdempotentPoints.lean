import Langlands.GroupScheme.AffinePointProducts
import Langlands.Algebra.EtaleGraphIdempotent
import Mathlib.RingTheory.Idempotents

/-! # Points of an affine group scheme over a ring split by an idempotent -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdempotentPoints

open Langlands.Algebra.GraphIdempotent

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (K : GroupScheme (Spec (CommRingCat.of R)))
variable {C : Type u} [CommRing C] [Algebra R C]

/-- Restriction of points to the factor `C/(1 - e)`. -/
abbrev fst (e : C) : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C) →*
    K.affinePoints (CommAlgCat.of (CommRingCat.of R) (C ⧸ Ideal.span {1 - e})) :=
  K.affinePointMap (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R (Ideal.span {1 - e})))

/-- Restriction of points to the factor `C/(e)`. -/
abbrev snd (e : C) : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C) →*
    K.affinePoints (CommAlgCat.of (CommRingCat.of R) (C ⧸ Ideal.span {e})) :=
  K.affinePointMap (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R (Ideal.span {e})))

/-- Coordinate evaluation of a point over `C`. -/
abbrev ev (x : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)) (a : Γ(K.X.left, ⊤)) : C :=
  K.affinePointEvaluation (CommAlgCat.of (CommRingCat.of R) C) x a

theorem ev_map {C' : Type u} [CommRing C'] [Algebra R C'] (f : C →ₐ[R] C')
    (x : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)) (a : Γ(K.X.left, ⊤)) :
    ev K (K.affinePointMap (CommAlgCat.ofHom f) x) a = f (ev K x a) :=
  K.affinePointEvaluation_map _ x a

theorem ev_injective [IsAffine K.X.left] {x y : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)}
    (h : ∀ a, ev K x a = ev K y a) : x = y :=
  K.affinePointEvaluation_injective _ (funext h)

/-- A point over `C` is determined by its restrictions to the two factors of an idempotent. -/
theorem ext_of_idempotent [IsAffine K.X.left] {e : C} (he : IsIdempotentElem e)
    {x y : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)}
    (h₁ : fst K e x = fst K e y) (h₂ : snd K e x = snd K e y) : x = y := by
  apply ev_injective K
  intro a
  have h₁' : (Ideal.Quotient.mkₐ R (Ideal.span {1 - e})) (ev K x a) =
      (Ideal.Quotient.mkₐ R (Ideal.span {1 - e})) (ev K y a) := by
    rw [← ev_map, ← ev_map]; exact congrArg (fun z => ev K z a) h₁
  have h₂' : (Ideal.Quotient.mkₐ R (Ideal.span {e})) (ev K x a) =
      (Ideal.Quotient.mkₐ R (Ideal.span {e})) (ev K y a) := by
    rw [← ev_map, ← ev_map]; exact congrArg (fun z => ev K z a) h₂
  rw [Ideal.Quotient.mkₐ_eq_mk] at h₁' h₂'
  rw [← sub_eq_zero]
  exact eq_zero_of_mem_span_of_mem_span he (Ideal.Quotient.eq.mp h₁') (Ideal.Quotient.eq.mp h₂')

variable (R) in
/-- The Chinese remainder isomorphism of an idempotent. -/
abbrev crt {e : C} (he : IsIdempotentElem e) :
    C ≃ₐ[R] (C ⧸ Ideal.span {1 - e}) × (C ⧸ Ideal.span {e}) :=
  AlgEquiv.prodQuotientOfIsIdempotentElem R (S := C) (e := 1 - e) (f := e) he.one_sub he
    (sub_add_cancel 1 e) (by rw [sub_mul, one_mul, he.eq, sub_self])

theorem crt_symm_mk {e : C} (he : IsIdempotentElem e) (u w : C) :
    (crt R he).symm (Ideal.Quotient.mk _ u, Ideal.Quotient.mk _ w) = e * u + (1 - e) * w := by
  apply (crt R he).injective
  rw [AlgEquiv.apply_symm_apply]
  ext
  · rw [AlgEquiv.prodQuotientOfIsIdempotentElem_apply_fst, Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton'.mpr ⟨u - w, by ring⟩
  · rw [AlgEquiv.prodQuotientOfIsIdempotentElem_apply_snd, Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton'.mpr ⟨w - u, by ring⟩

/-- Glue points over the two factors of an idempotent. -/
def mixQ [IsAffine K.X.left] {e : C} (he : IsIdempotentElem e)
    (g₁ : K.affinePoints (CommAlgCat.of (CommRingCat.of R) (C ⧸ Ideal.span {1 - e})))
    (g₂ : K.affinePoints (CommAlgCat.of (CommRingCat.of R) (C ⧸ Ideal.span {e}))) :
    K.affinePoints (CommAlgCat.of (CommRingCat.of R) C) :=
  K.affinePointMap (CommAlgCat.ofHom (crt R he).symm.toAlgHom)
    (K.affinePointPair (CommAlgCat.of (CommRingCat.of R) (C ⧸ Ideal.span {1 - e}))
      (CommAlgCat.of (CommRingCat.of R) (C ⧸ Ideal.span {e})) g₁ g₂)

/-- Points over `C` combining the `e`-component of `g` with the `(1 - e)`-component of `h`. -/
def mix [IsAffine K.X.left] {e : C} (he : IsIdempotentElem e)
    (g h : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)) :
    K.affinePoints (CommAlgCat.of (CommRingCat.of R) C) :=
  mixQ K he (fst K e g) (snd K e h)

theorem ev_mix [IsAffine K.X.left] {e : C} (he : IsIdempotentElem e)
    (g h : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)) (a : Γ(K.X.left, ⊤)) :
    ev K (mix K he g h) a = e * ev K g a + (1 - e) * ev K h a := by
  have h1 : ev K (mix K he g h) a = (crt R he).symm
      (K.affinePointEvaluation _ (K.affinePointPair
        (CommAlgCat.of (CommRingCat.of R) (C ⧸ Ideal.span {1 - e}))
        (CommAlgCat.of (CommRingCat.of R) (C ⧸ Ideal.span {e})) (fst K e g) (snd K e h)) a) :=
    K.affinePointEvaluation_map _ _ a
  have h2 := K.affinePointPair_evaluation
    (CommAlgCat.of (CommRingCat.of R) (C ⧸ Ideal.span {1 - e}))
    (CommAlgCat.of (CommRingCat.of R) (C ⧸ Ideal.span {e})) (fst K e g) (snd K e h) a
  have h3 : K.affinePointEvaluation _ (fst K e g) a =
      Ideal.Quotient.mk (Ideal.span {1 - e}) (ev K g a) := ev_map K _ g a
  have h4 : K.affinePointEvaluation _ (snd K e h) a =
      Ideal.Quotient.mk (Ideal.span {e}) (ev K h a) := ev_map K _ h a
  rw [h1, h2, h3, h4, crt_symm_mk]

theorem ev_fst (e : C) (x : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C))
    (a : Γ(K.X.left, ⊤)) :
    ev K (fst K e x) a = Ideal.Quotient.mk (Ideal.span {1 - e}) (ev K x a) :=
  ev_map K _ x a

theorem ev_snd (e : C) (x : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C))
    (a : Γ(K.X.left, ⊤)) :
    ev K (snd K e x) a = Ideal.Quotient.mk (Ideal.span {e}) (ev K x a) :=
  ev_map K _ x a

theorem mk_fst_self (e : C) : Ideal.Quotient.mk (Ideal.span {1 - e}) e = 1 := by
  have h : Ideal.Quotient.mk (Ideal.span {1 - e}) (1 - e) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rw [map_sub, map_one, sub_eq_zero] at h
  exact h.symm

theorem mk_snd_self (e : C) : Ideal.Quotient.mk (Ideal.span {e}) e = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

variable [IsAffine K.X.left]

theorem fst_mix {e : C} (he : IsIdempotentElem e)
    (g h : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)) :
    fst K e (mix K he g h) = fst K e g := by
  apply ev_injective K
  intro a
  rw [ev_fst, ev_fst, ev_mix, map_add, map_mul, map_mul, map_sub, map_one, mk_fst_self,
    sub_self, zero_mul, add_zero, one_mul]

theorem snd_mix {e : C} (he : IsIdempotentElem e)
    (g h : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)) :
    snd K e (mix K he g h) = snd K e h := by
  apply ev_injective K
  intro a
  rw [ev_snd, ev_snd, ev_mix, map_add, map_mul, map_mul, map_sub, map_one, mk_snd_self,
    sub_zero, zero_mul, zero_add, one_mul]

/-- The projection onto the `e`-component, as a homomorphism, for an idempotent `e`. -/
def projAux {e : C} (he : IsIdempotentElem e) :
    K.affinePoints (CommAlgCat.of (CommRingCat.of R) C) →*
      K.affinePoints (CommAlgCat.of (CommRingCat.of R) C) where
  toFun g := mix K he g 1
  map_one' := ext_of_idempotent K he (by rw [fst_mix]) (by rw [snd_mix])
  map_mul' g g' := ext_of_idempotent K he
    (by rw [map_mul, fst_mix, fst_mix, fst_mix, map_mul])
    (by rw [map_mul, snd_mix, snd_mix, snd_mix, map_one, mul_one])

open Classical in
/-- The projection onto the `e`-component (the trivial map if `e` is not idempotent). -/
def proj (e : C) : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C) →*
    K.affinePoints (CommAlgCat.of (CommRingCat.of R) C) :=
  if he : IsIdempotentElem e then projAux K he else 1

theorem proj_eq {e : C} (he : IsIdempotentElem e) : proj K e = projAux K he := by
  classical
  simp only [proj, he, dite_true]

theorem proj_apply {e : C} (he : IsIdempotentElem e)
    (g : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)) :
    proj K e g = mix K he g 1 := by
  rw [proj_eq K he]; rfl

theorem fst_proj {e : C} (he : IsIdempotentElem e)
    (g : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)) :
    fst K e (proj K e g) = fst K e g := by
  rw [proj_apply K he, fst_mix]

theorem snd_proj {e : C} (he : IsIdempotentElem e)
    (g : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)) :
    snd K e (proj K e g) = 1 := by
  rw [proj_apply K he, snd_mix, map_one]

theorem ev_proj {e : C} (he : IsIdempotentElem e)
    (g : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)) (a : Γ(K.X.left, ⊤)) :
    ev K (proj K e g) a = e * ev K g a + (1 - e) * ev K 1 a := by
  rw [proj_apply K he, ev_mix]

theorem eq_proj_iff {e : C} (he : IsIdempotentElem e)
    {g y : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)} :
    y = proj K e g ↔ fst K e y = fst K e g ∧ snd K e y = 1 := by
  constructor
  · rintro rfl
    exact ⟨fst_proj K he g, snd_proj K he g⟩
  · rintro ⟨h₁, h₂⟩
    exact ext_of_idempotent K he (by rw [h₁, fst_proj K he]) (by rw [h₂, snd_proj K he])

theorem proj_map {C' : Type u} [CommRing C'] [Algebra R C'] (f : C →ₐ[R] C') {e : C}
    (he : IsIdempotentElem e) {e' : C'} (h : f e = e')
    (g : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)) :
    K.affinePointMap (CommAlgCat.ofHom f) (proj K e g) =
      proj K e' (K.affinePointMap (CommAlgCat.ofHom f) g) := by
  have he' : IsIdempotentElem e' := h ▸ he.map f
  apply ev_injective K
  intro a
  have h1 : ev K (1 : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C')) a =
      f (ev K 1 a) := by
    rw [← ev_map, map_one]
  rw [ev_map, ev_proj K he, ev_proj K he', ev_map, h1, map_add, map_mul, map_mul, map_sub,
    map_one, h]

theorem proj_proj {e f : C} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (g : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)) :
    proj K e (proj K f g) = proj K (e * f) g := by
  apply ev_injective K
  intro a
  rw [ev_proj K he, ev_proj K hf, ev_proj K (he.mul hf)]
  ring

theorem proj_one (g : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)) :
    proj K 1 g = g := by
  apply ev_injective K
  intro a
  rw [ev_proj K IsIdempotentElem.one]
  ring

theorem proj_zero (g : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)) :
    proj K 0 g = 1 := by
  apply ev_injective K
  intro a
  rw [ev_proj K IsIdempotentElem.zero]
  ring

theorem proj_conj {e : C} (he : IsIdempotentElem e)
    (g x : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)) :
    proj K e (g * x * g⁻¹) = g * proj K e x * g⁻¹ := by
  apply ext_of_idempotent K he
  · rw [fst_proj K he, map_mul, map_mul, map_mul, map_mul, fst_proj K he]
  · rw [snd_proj K he, map_mul, map_mul, snd_proj K he, mul_one, map_inv, mul_inv_cancel]

theorem fst_mixQ {e : C} (he : IsIdempotentElem e)
    (g₁ : K.affinePoints (CommAlgCat.of (CommRingCat.of R) (C ⧸ Ideal.span {1 - e})))
    (g₂ : K.affinePoints (CommAlgCat.of (CommRingCat.of R) (C ⧸ Ideal.span {e}))) :
    fst K e (mixQ K he g₁ g₂) = g₁ := by
  apply ev_injective K
  intro a
  have h1 : ev K (mixQ K he g₁ g₂) a = (crt R he).symm
      (K.affinePointEvaluation _ (K.affinePointPair
        (CommAlgCat.of (CommRingCat.of R) (C ⧸ Ideal.span {1 - e}))
        (CommAlgCat.of (CommRingCat.of R) (C ⧸ Ideal.span {e})) g₁ g₂) a) :=
    K.affinePointEvaluation_map _ _ a
  have h2 := K.affinePointPair_evaluation
    (CommAlgCat.of (CommRingCat.of R) (C ⧸ Ideal.span {1 - e}))
    (CommAlgCat.of (CommRingCat.of R) (C ⧸ Ideal.span {e})) g₁ g₂ a
  rw [ev_fst, h1, h2]
  have h3 := AlgEquiv.prodQuotientOfIsIdempotentElem_apply_fst R (S := C) (e := 1 - e) (f := e)
    he.one_sub he (sub_add_cancel 1 e) (by rw [sub_mul, one_mul, he.eq, sub_self])
    ((crt R he).symm (K.affinePointEvaluation _ g₁ a, K.affinePointEvaluation _ g₂ a))
  rw [← h3]
  change ((crt R he) ((crt R he).symm _)).1 = _
  rw [AlgEquiv.apply_symm_apply]

theorem snd_mixQ {e : C} (he : IsIdempotentElem e)
    (g₁ : K.affinePoints (CommAlgCat.of (CommRingCat.of R) (C ⧸ Ideal.span {1 - e})))
    (g₂ : K.affinePoints (CommAlgCat.of (CommRingCat.of R) (C ⧸ Ideal.span {e}))) :
    snd K e (mixQ K he g₁ g₂) = g₂ := by
  apply ev_injective K
  intro a
  have h1 : ev K (mixQ K he g₁ g₂) a = (crt R he).symm
      (K.affinePointEvaluation _ (K.affinePointPair
        (CommAlgCat.of (CommRingCat.of R) (C ⧸ Ideal.span {1 - e}))
        (CommAlgCat.of (CommRingCat.of R) (C ⧸ Ideal.span {e})) g₁ g₂) a) :=
    K.affinePointEvaluation_map _ _ a
  have h2 := K.affinePointPair_evaluation
    (CommAlgCat.of (CommRingCat.of R) (C ⧸ Ideal.span {1 - e}))
    (CommAlgCat.of (CommRingCat.of R) (C ⧸ Ideal.span {e})) g₁ g₂ a
  rw [ev_snd, h1, h2]
  have h3 := AlgEquiv.prodQuotientOfIsIdempotentElem_apply_snd R (S := C) (e := 1 - e) (f := e)
    he.one_sub he (sub_add_cancel 1 e) (by rw [sub_mul, one_mul, he.eq, sub_self])
    ((crt R he).symm (K.affinePointEvaluation _ g₁ a, K.affinePointEvaluation _ g₂ a))
  rw [← h3]
  change ((crt R he) ((crt R he).symm _)).2 = _
  rw [AlgEquiv.apply_symm_apply]

section FactorEquiv

variable {D : Type u} [CommRing D] [Algebra R D]

/-- The identification `D ≃ C/(1 - e)` induced by a surjection `mu : C → D` with kernel
`(1 - e)`. -/
def quotEquiv {e : C} {mu : C →ₐ[R] D} (hmu : Function.Surjective mu)
    (hker : RingHom.ker mu = Ideal.span {1 - e}) : D ≃ₐ[R] C ⧸ Ideal.span {1 - e} :=
  (Ideal.quotientKerAlgEquivOfSurjective hmu).symm.trans (Ideal.quotientEquivAlgOfEq R hker)

omit [IsAffine K.X.left] in
theorem quotEquiv_apply {e : C} {mu : C →ₐ[R] D} (hmu : Function.Surjective mu)
    (hker : RingHom.ker mu = Ideal.span {1 - e}) (c : C) :
    quotEquiv hmu hker (mu c) = Ideal.Quotient.mk _ c := by
  have h : (Ideal.quotientKerAlgEquivOfSurjective hmu).symm (mu c) =
      Ideal.Quotient.mk (RingHom.ker mu) c := by
    rw [AlgEquiv.symm_apply_eq]
    rfl
  rw [quotEquiv, AlgEquiv.trans_apply, h]
  rfl

omit [IsAffine K.X.left] in
theorem quotEquiv_symm_mk {e : C} {mu : C →ₐ[R] D} (hmu : Function.Surjective mu)
    (hker : RingHom.ker mu = Ideal.span {1 - e}) (c : C) :
    (quotEquiv hmu hker).symm (Ideal.Quotient.mk _ c) = mu c := by
  rw [AlgEquiv.symm_apply_eq, quotEquiv_apply]

/-- Points over `C` that are trivial on the `(1 - e)`-component are the points over
`D = C/(1 - e)`. -/
def factorEquiv {e : C} (he : IsIdempotentElem e) {mu : C →ₐ[R] D}
    (hmu : Function.Surjective mu) (hker : RingHom.ker mu = Ideal.span {1 - e}) :
    (snd K e).ker ≃* K.affinePoints (CommAlgCat.of (CommRingCat.of R) D) where
  toFun k := K.affinePointMap (CommAlgCat.ofHom mu) k
  invFun g := ⟨mixQ K he
      (K.affinePointMap (CommAlgCat.ofHom (quotEquiv hmu hker).toAlgHom) g) 1, by
    rw [MonoidHom.mem_ker, snd_mixQ]⟩
  left_inv k := by
    apply Subtype.ext
    apply ext_of_idempotent K he
    · rw [fst_mixQ]
      apply ev_injective K
      intro a
      rw [ev_map, ev_map, ev_fst]
      exact quotEquiv_apply hmu hker _
    · rw [snd_mixQ]
      exact k.2.symm
  right_inv g := by
    apply ev_injective K
    intro a
    have h1 : ev K (K.affinePointMap (CommAlgCat.ofHom mu) (mixQ K he
        (K.affinePointMap (CommAlgCat.ofHom (quotEquiv hmu hker).toAlgHom) g) 1)) a =
        (quotEquiv hmu hker).symm (ev K (fst K e (mixQ K he
          (K.affinePointMap (CommAlgCat.ofHom (quotEquiv hmu hker).toAlgHom) g) 1)) a) := by
      rw [ev_map, ev_fst, quotEquiv_symm_mk]
    change ev K (K.affinePointMap (CommAlgCat.ofHom mu) (mixQ K he
        (K.affinePointMap (CommAlgCat.ofHom (quotEquiv hmu hker).toAlgHom) g) 1)) a = ev K g a
    rw [h1, fst_mixQ, ev_map]
    exact (quotEquiv hmu hker).symm_apply_apply _
  map_mul' k k' := map_mul (K.affinePointMap (CommAlgCat.ofHom mu)) k.1 k'.1

theorem factorEquiv_apply {e : C} (he : IsIdempotentElem e) {mu : C →ₐ[R] D}
    (hmu : Function.Surjective mu) (hker : RingHom.ker mu = Ideal.span {1 - e})
    (k : (snd K e).ker) :
    factorEquiv K he hmu hker k = K.affinePointMap (CommAlgCat.ofHom mu) k := rfl

end FactorEquiv

end Langlands.GroupScheme.IdempotentPoints
