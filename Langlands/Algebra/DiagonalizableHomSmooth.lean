import Langlands.Algebra.FiniteBialgebraHom
import Langlands.GroupScheme.Torus.FixedPointLifting
import Langlands.TauCeti.RingTheory.WeilRestriction.Smooth
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.Finiteness.Finsupp

/-! # Smoothness of homomorphisms out of a finite diagonalizable group

Let `A` be a commutative Hopf algebra over `R`, formally smooth and finitely presented, and let
`M` be a finite abelian group. The algebra `HomAlgebra R A R[M]` representing Hopf points
`A → C ⊗[R] R[M]` is formally smooth, hence smooth.

The characters `t : M → Cˣ` act on all algebra maps `φ : A → C ⊗[R] R[M]` (the points of the
Weil restriction) by the normalised translation `(t • φ)(h) = φ(h t) φ(t)⁻¹ φ(1)`, computed in
the convolution group of `A`. Hopf points are fixed; conversely, a point fixed after every
refinement becomes a Hopf point after dividing by its value at `1`. The Library fixed-point
lifting for actions of diagonalizable groups on smooth affine schemes then lifts Hopf points
through nilpotent thickenings. -/

noncomputable section

universe u v w

open TensorProduct WithConv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.FiniteBialgebraHom

section ConvGroup

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
  {D : Type w} [CommRing D] [Algebra R D]

/-- Algebra maps from a commutative Hopf algebra into a commutative algebra form a group under
convolution; the inverse is precomposition with the antipode. -/
@[instance_reducible]
def convGroup : Group (WithConv (A →ₐ[R] D)) :=
  { (inferInstance : Monoid (WithConv (A →ₐ[R] D))) with
    inv := fun f => toConv (f.ofConv.comp (HopfAlgebra.antipodeAlgHom R A))
    inv_mul_cancel := fun f => by
      have H : (Algebra.TensorProduct.lmul' R).comp
          (Algebra.TensorProduct.map f.ofConv f.ofConv) =
          f.ofConv.comp (Algebra.TensorProduct.lmul' R) := by ext <;> simp
      change toConv ((Algebra.TensorProduct.lmul' R).comp
        ((Algebra.TensorProduct.map (f.ofConv.comp (HopfAlgebra.antipodeAlgHom R A))
          f.ofConv).comp (Bialgebra.comulAlgHom R A))) = 1
      trans toConv <| ((Algebra.TensorProduct.lmul' R).comp
        (Algebra.TensorProduct.map f.ofConv f.ofConv)).comp
          ((Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom R A) (.id _ _)).comp
            (Bialgebra.comulAlgHom R A))
      · rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc (Algebra.TensorProduct.map f.ofConv f.ofConv),
          ← Algebra.TensorProduct.map_comp]; rfl
      rw [H, AlgHom.comp_assoc, WithConv.ext_iff, ← AlgHom.toLinearMap_injective.eq_iff]
      change f.ofConv.toLinearMap.comp
          (toConv (HopfAlgebra.antipode R (A := A)) * toConv LinearMap.id).ofConv =
        ofConv (1 : WithConv <| A →ₗ[R] D)
      rw [LinearMap.antipode_mul_id]
      ext
      simp }

attribute [local instance] convGroup

variable {E : Type*} [CommRing E] [Algebra R E]

/-- Postcomposition with an algebra map is a homomorphism of convolution groups. -/
def postComp (h : D →ₐ[R] E) : WithConv (A →ₐ[R] D) →* WithConv (A →ₐ[R] E) where
  toFun f := toConv (h.comp f.ofConv)
  map_one' := by
    rw [AlgHom.convOne_def, AlgHom.convOne_def]
    exact congrArg toConv (AlgHom.ext fun a => h.commutes _)
  map_mul' f g := by
    rw [AlgHom.comp_convMul_distrib, toConv_ofConv]

theorem postComp_apply (h : D →ₐ[R] E) (f : WithConv (A →ₐ[R] D)) :
    postComp h f = toConv (h.comp f.ofConv) := rfl

theorem postComp_postComp {F : Type*} [CommRing F] [Algebra R F] (k : E →ₐ[R] F)
    (h : D →ₐ[R] E) (f : WithConv (A →ₐ[R] D)) :
    postComp k (postComp h f) = postComp (k.comp h) f := rfl

theorem postComp_id (f : WithConv (A →ₐ[R] D)) : postComp (AlgHom.id R D) f = f := rfl

end ConvGroup

attribute [local instance] convGroup

section Characters

variable (R : Type u) [CommRing R] {M : Type u} [AddCommGroup M]
  {C : Type w} [CommRing C] [Algebra R C] {D : Type*} [CommRing D] [Algebra R D]

/-- Evaluation of the group algebra at a character. -/
def charEval (t : Multiplicative M →* Cˣ) : AddMonoidAlgebra R M →ₐ[R] C :=
  AddMonoidAlgebra.lift R C M ((Units.coeHom C).comp t)

@[simp]
theorem charEval_single (t : Multiplicative M →* Cˣ) (m : M) (r : R) :
    charEval R t (AddMonoidAlgebra.single m r) = r • (t (.ofAdd m) : C) := by
  simp [charEval]

/-- The inclusion `C → C ⊗[R] R[M]`. -/
abbrev incl : C →ₐ[R] C ⊗[R] AddMonoidAlgebra R M := Algebra.TensorProduct.includeLeft

/-- Evaluation of `C ⊗[R] R[M]` at a character with values in `C`. -/
def evalAt (t : Multiplicative M →* Cˣ) : C ⊗[R] AddMonoidAlgebra R M →ₐ[R] C :=
  Algebra.TensorProduct.lift (AlgHom.id R C) (charEval R t) fun _ _ => Commute.all _ _

@[simp]
theorem evalAt_tmul (t : Multiplicative M →* Cˣ) (c : C) (q : AddMonoidAlgebra R M) :
    evalAt R t (c ⊗ₜ q) = c * charEval R t q :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- The character `m ↦ t(m) ⊗ Xᵐ` with values in `C ⊗[R] R[M]`. -/
def translateChar (t : Multiplicative M →* Cˣ) :
    Multiplicative M →* C ⊗[R] AddMonoidAlgebra R M where
  toFun x := (t x : C) ⊗ₜ AddMonoidAlgebra.single x.toAdd 1
  map_one' := by
    rw [map_one, Units.val_one, toAdd_one, ← AddMonoidAlgebra.one_def,
      Algebra.TensorProduct.one_def]
  map_mul' x y := by
    rw [map_mul, Units.val_mul, toAdd_mul, Algebra.TensorProduct.tmul_mul_tmul,
      AddMonoidAlgebra.single_mul_single, mul_one]

/-- Translation by a character: `c ⊗ Xᵐ ↦ c t(m) ⊗ Xᵐ`. -/
def translate (t : Multiplicative M →* Cˣ) :
    C ⊗[R] AddMonoidAlgebra R M →ₐ[R] C ⊗[R] AddMonoidAlgebra R M :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft
    (AddMonoidAlgebra.lift R _ M (translateChar R t)) fun _ _ => Commute.all _ _

@[simp]
theorem translate_tmul_one (t : Multiplicative M →* Cˣ) (c : C) :
    translate R t (c ⊗ₜ 1) = c ⊗ₜ 1 := by
  simp [translate]

@[simp]
theorem translate_tmul_single (t : Multiplicative M →* Cˣ) (c : C) (m : M) :
    translate R t (c ⊗ₜ AddMonoidAlgebra.single m 1) =
      (c * t (.ofAdd m)) ⊗ₜ AddMonoidAlgebra.single m 1 := by
  simp [translate, translateChar, Algebra.TensorProduct.tmul_mul_tmul]

/-- Algebra maps out of `C ⊗[R] R[M]` agree once they agree on `C` and on the monomials. -/
theorem tensor_algHom_ext {E : Type*} [Semiring E] [Algebra R E]
    {f g : C ⊗[R] AddMonoidAlgebra R M →ₐ[R] E}
    (h₁ : ∀ c : C, f (c ⊗ₜ 1) = g (c ⊗ₜ 1))
    (h₂ : ∀ m : M, f (1 ⊗ₜ AddMonoidAlgebra.single m 1) =
      g (1 ⊗ₜ AddMonoidAlgebra.single m 1)) :
    f = g :=
  Algebra.TensorProduct.ext (AlgHom.ext h₁)
    (AddMonoidAlgebra.algHom_ext h₂ (Subsingleton.elim _ _))

theorem translate_one : translate R (1 : Multiplicative M →* Cˣ) = AlgHom.id R _ :=
  tensor_algHom_ext R (fun c => by simp) (fun m => by simp)

theorem translate_comp_translate (t s : Multiplicative M →* Cˣ) :
    (translate R t).comp (translate R s) = translate R (t * s) :=
  tensor_algHom_ext R (fun c => by simp) (fun m => by simp [mul_comm])

theorem translate_comp_incl (t : Multiplicative M →* Cˣ) :
    (translate R t).comp (incl R) = incl R (M := M) :=
  AlgHom.ext fun c => by simp

theorem evalAt_comp_translate (t s : Multiplicative M →* Cˣ) :
    (evalAt R t).comp (translate R s) = evalAt R (t * s) :=
  tensor_algHom_ext R (fun c => by simp) (fun m => by simp [mul_comm])

theorem evalAt_comp_incl (t : Multiplicative M →* Cˣ) :
    (evalAt R t).comp (incl R (M := M)) = AlgHom.id R C :=
  AlgHom.ext fun c => by simp

/-- Change the coefficients of a character. -/
abbrev mapChar (g : C →ₐ[R] D) (t : Multiplicative M →* Cˣ) : Multiplicative M →* Dˣ :=
  (Units.map g.toRingHom.toMonoidHom).comp t

theorem map_comp_translate (g : C →ₐ[R] D) (t : Multiplicative M →* Cˣ) :
    (Algebra.TensorProduct.map g (AlgHom.id R (AddMonoidAlgebra R M))).comp (translate R t) =
      (translate R (M := M) (mapChar R g t)).comp
        (Algebra.TensorProduct.map g (AlgHom.id R (AddMonoidAlgebra R M))) :=
  tensor_algHom_ext R (fun c => by simp) (fun m => by simp)

theorem comp_evalAt (g : C →ₐ[R] D) (t : Multiplicative M →* Cˣ) :
    g.comp (evalAt R t) =
      (evalAt R (M := M) (mapChar R g t)).comp
        (Algebra.TensorProduct.map g (AlgHom.id R (AddMonoidAlgebra R M))) :=
  tensor_algHom_ext R (fun c => by simp) (fun m => by simp)

theorem map_comp_incl (g : C →ₐ[R] D) :
    (Algebra.TensorProduct.map g (AlgHom.id R (AddMonoidAlgebra R M))).comp (incl R) =
      (incl R (M := M)).comp g :=
  AlgHom.ext fun c => by simp

theorem char_one_mul (s : Multiplicative M →* Cˣ) : 1 * s = s := one_mul s

theorem mapChar_one (g : C →ₐ[R] D) : mapChar R g (1 : Multiplicative M →* Cˣ) = 1 :=
  MonoidHom.comp_one _

theorem evalAt_one_eq_counit :
    evalAt R (1 : Multiplicative M →* Cˣ) =
      (Algebra.TensorProduct.rid R R C).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id R C)
          (Bialgebra.counitAlgHom R (AddMonoidAlgebra R M))) :=
  tensor_algHom_ext R (fun c => by simp) (fun m => by simp)

theorem comulAlgHom_single_one (m : M) :
    Bialgebra.comulAlgHom R (AddMonoidAlgebra R M) (AddMonoidAlgebra.single m 1) =
      AddMonoidAlgebra.single m 1 ⊗ₜ AddMonoidAlgebra.single m 1 := by
  simp [Bialgebra.comulAlgHom_apply]

/-- `c ⊗ p ⊗ q ↦ c t(q) ⊗ p`. -/
def splitEval (t : Multiplicative M →* Cˣ) :
    C ⊗[R] (AddMonoidAlgebra R M ⊗[R] AddMonoidAlgebra R M) →ₐ[R]
      C ⊗[R] AddMonoidAlgebra R M :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft
    (Algebra.TensorProduct.lift Algebra.TensorProduct.includeRight
      ((incl R).comp (charEval R t)) fun _ _ => Commute.all _ _)
    fun _ _ => Commute.all _ _

theorem splitEval_comp_comul (t : Multiplicative M →* Cˣ) :
    (splitEval R t).comp (Algebra.TensorProduct.map (AlgHom.id R C)
      (Bialgebra.comulAlgHom R (AddMonoidAlgebra R M))) = translate R t :=
  tensor_algHom_ext R (fun c => by simp [splitEval])
    (fun m => by
      rw [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, comulAlgHom_single_one]
      simp [splitEval, Algebra.TensorProduct.tmul_mul_tmul])

theorem splitEval_comp_inclFirst (t : Multiplicative M →* Cˣ) :
    (splitEval R t).comp (inclFirst R (C := C) (P := AddMonoidAlgebra R M)) = AlgHom.id R _ :=
  tensor_algHom_ext R (fun c => by simp [splitEval])
    (fun m => by simp [splitEval, Algebra.TensorProduct.tmul_mul_tmul])

theorem splitEval_comp_inclSecond (t : Multiplicative M →* Cˣ) :
    (splitEval R t).comp (inclSecond R (C := C) (P := AddMonoidAlgebra R M)) =
      (incl R (M := M)).comp (evalAt R t) :=
  tensor_algHom_ext R (fun c => by simp [splitEval])
    (fun m => by simp [splitEval, Algebra.TensorProduct.tmul_mul_tmul])

/-- The universal character `m ↦ 1 ⊗ Xᵐ` with values in `C ⊗[R] R[M]`. -/
def universalChar : Multiplicative M →* (C ⊗[R] AddMonoidAlgebra R M)ˣ :=
  (Units.map (Algebra.TensorProduct.includeRight :
    AddMonoidAlgebra R M →ₐ[R] C ⊗[R] AddMonoidAlgebra R M).toRingHom.toMonoidHom).comp
    (AddMonoidAlgebra.of R M).toHomUnits

@[simp]
theorem universalChar_apply (m : M) :
    ((universalChar R (C := C) (.ofAdd m) : (C ⊗[R] AddMonoidAlgebra R M)ˣ) :
      C ⊗[R] AddMonoidAlgebra R M) = 1 ⊗ₜ AddMonoidAlgebra.single m 1 :=
  rfl

/-- `(c ⊗ q) ⊗ p ↦ c ⊗ (p ⊗ q)`. -/
def swapAssoc {P : Type*} [CommRing P] [Algebra R P] :
    (C ⊗[R] P) ⊗[R] P →ₐ[R] C ⊗[R] (P ⊗[R] P) :=
  (Algebra.TensorProduct.map (AlgHom.id R C) (Algebra.TensorProduct.comm R P P).toAlgHom).comp
    (Algebra.TensorProduct.assoc R R R C P P).toAlgHom

@[simp]
theorem swapAssoc_tmul {P : Type*} [CommRing P] [Algebra R P] (c : C) (q p : P) :
    swapAssoc R ((c ⊗ₜ q) ⊗ₜ p) = c ⊗ₜ (p ⊗ₜ q) :=
  rfl

theorem swapAssoc_comp_translate :
    (swapAssoc R (C := C) (P := AddMonoidAlgebra R M)).comp
      ((translate R (universalChar R)).comp
      (Algebra.TensorProduct.map (incl R) (AlgHom.id R (AddMonoidAlgebra R M)))) =
      Algebra.TensorProduct.map (AlgHom.id R C)
        (Bialgebra.comulAlgHom R (AddMonoidAlgebra R M)) :=
  tensor_algHom_ext R (fun c => by simp [swapAssoc, ← Algebra.TensorProduct.one_def])
    (fun m => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.map_tmul, comulAlgHom_single_one]
      simp [swapAssoc, Algebra.TensorProduct.tmul_mul_tmul])

theorem swapAssoc_comp_map :
    (swapAssoc R (C := C) (P := AddMonoidAlgebra R M)).comp
      (Algebra.TensorProduct.map (incl R) (AlgHom.id R (AddMonoidAlgebra R M))) =
      inclFirst R :=
  tensor_algHom_ext R (fun c => by simp [swapAssoc]) (fun m => by simp [swapAssoc])

theorem swapAssoc_comp_evalAt :
    (swapAssoc R (C := C) (P := AddMonoidAlgebra R M)).comp
      ((incl R).comp ((evalAt R (universalChar R)).comp
      (Algebra.TensorProduct.map (incl R) (AlgHom.id R (AddMonoidAlgebra R M))))) =
      inclSecond R :=
  tensor_algHom_ext R (fun c => by simp [swapAssoc])
    (fun m => by simp [swapAssoc])

end Characters

section Action

variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [HopfAlgebra R A]
  {M : Type u} [AddCommGroup M] {C : Type*} [CommRing C] [Algebra R C]
  {D : Type*} [CommRing D] [Algebra R D]

private theorem group_aux₁ {G : Type*} [Group G] (a b c k : G) :
    a * c⁻¹ * k = a * b⁻¹ * k * (c * b⁻¹ * k)⁻¹ * (b * b⁻¹ * k) := by
  group

private theorem group_aux₂ {G : Type*} [Group G] (a c k : G) :
    k⁻¹ * a * (k⁻¹ * c)⁻¹ * (k⁻¹ * k) = (c * c⁻¹ * k)⁻¹ * (a * c⁻¹ * k) := by
  group

private theorem group_aux₃ {G : Type*} [Group G] (a : G) : (1 : G)⁻¹ * a = a := by
  group

/-- Points `A → C ⊗[R] R[M]`, with their convolution group structure. -/
abbrev Pt (A : Type u) [CommRing A] [HopfAlgebra R A] (M : Type u) [AddCommGroup M]
    (C : Type*) [CommRing C] [Algebra R C] :=
  WithConv (A →ₐ[R] C ⊗[R] AddMonoidAlgebra R M)

/-- Translation of points by a character. -/
abbrev transPt (t : Multiplicative M →* Cˣ) : Pt R A M C →* Pt R A M C :=
  postComp (translate R t)

/-- The constant point `h ↦ φ(t)`. -/
abbrev constPt (t : Multiplicative M →* Cˣ) : Pt R A M C →* Pt R A M C :=
  postComp ((incl R).comp (evalAt R t))

/-- The value `φ(1)` of a point at the unit section. -/
abbrev unitValue : Pt R A M C →* WithConv (A →ₐ[R] C) :=
  postComp (evalAt R 1)

/-- Coefficient change of points. -/
abbrev pushPt (g : C →ₐ[R] D) : Pt R A M C →* Pt R A M D :=
  postComp (Algebra.TensorProduct.map g (AlgHom.id R (AddMonoidAlgebra R M)))

/-- The normalised translation action `(t • φ)(h) = φ(h t) φ(t)⁻¹ φ(1)`. -/
def actPt (t : Multiplicative M →* Cˣ) (φ : Pt R A M C) : Pt R A M C :=
  transPt R t φ * (constPt R t φ)⁻¹ * constPt R 1 φ

theorem transPt_transPt (t s : Multiplicative M →* Cˣ) (φ : Pt R A M C) :
    transPt R t (transPt R s φ) = transPt R (t * s) φ := by
  rw [postComp_postComp, translate_comp_translate]

theorem transPt_constPt (t s : Multiplicative M →* Cˣ) (φ : Pt R A M C) :
    transPt R t (constPt R s φ) = constPt R s φ := by
  rw [postComp_postComp, ← AlgHom.comp_assoc, translate_comp_incl]

theorem constPt_transPt (t s : Multiplicative M →* Cˣ) (φ : Pt R A M C) :
    constPt R t (transPt R s φ) = constPt R (t * s) φ := by
  rw [postComp_postComp, AlgHom.comp_assoc, evalAt_comp_translate]

theorem constPt_constPt (t s : Multiplicative M →* Cˣ) (φ : Pt R A M C) :
    constPt R t (constPt R s φ) = constPt R s φ := by
  rw [postComp_postComp, AlgHom.comp_assoc, ← AlgHom.comp_assoc (evalAt R t),
    evalAt_comp_incl, AlgHom.id_comp]

theorem unitValue_constPt (s : Multiplicative M →* Cˣ) (φ : Pt R A M C) :
    unitValue R (constPt R s φ) = postComp (evalAt R s) φ := by
  rw [postComp_postComp, ← AlgHom.comp_assoc, evalAt_comp_incl, AlgHom.id_comp]

theorem constPt_eq (s : Multiplicative M →* Cˣ) (φ : Pt R A M C) :
    constPt R s φ = postComp (incl R) (postComp (evalAt R s) φ) := rfl

theorem actPt_one (φ : Pt R A M C) : actPt R 1 φ = φ := by
  rw [actPt, transPt, translate_one, postComp_id, inv_mul_cancel_right]

theorem actPt_mul (t s : Multiplicative M →* Cˣ) (φ : Pt R A M C) :
    actPt R (t * s) φ = actPt R t (actPt R s φ) := by
  simp only [actPt, map_mul, map_inv, transPt_transPt, transPt_constPt, constPt_transPt,
    constPt_constPt, char_one_mul]
  exact group_aux₁ _ _ _ _

theorem pushPt_transPt (g : C →ₐ[R] D) (t : Multiplicative M →* Cˣ) (φ : Pt R A M C) :
    pushPt R g (transPt R t φ) = transPt R (mapChar R g t) (pushPt R g φ) := by
  rw [postComp_postComp, postComp_postComp, map_comp_translate]

theorem pushPt_constPt (g : C →ₐ[R] D) (t : Multiplicative M →* Cˣ) (φ : Pt R A M C) :
    pushPt R g (constPt R t φ) = constPt R (mapChar R g t) (pushPt R g φ) := by
  rw [postComp_postComp, postComp_postComp, ← AlgHom.comp_assoc, map_comp_incl,
    AlgHom.comp_assoc, comp_evalAt, AlgHom.comp_assoc]

theorem pushPt_actPt (g : C →ₐ[R] D) (t : Multiplicative M →* Cˣ) (φ : Pt R A M C) :
    pushPt R g (actPt R t φ) = actPt R (mapChar R g t) (pushPt R g φ) := by
  rw [actPt, actPt, map_mul, map_mul, map_inv, pushPt_transPt, pushPt_constPt, pushPt_constPt,
    mapChar_one]

theorem unitValue_pushPt (g : C →ₐ[R] D) (φ : Pt R A M C) :
    unitValue R (pushPt R g φ) = postComp g (unitValue R φ) := by
  rw [postComp_postComp, postComp_postComp, comp_evalAt, mapChar_one]

/-- Divide a point by its value at the unit section. -/
def normalize (φ : Pt R A M C) : Pt R A M C :=
  (constPt R 1 φ)⁻¹ * φ

theorem unitValue_normalize (φ : Pt R A M C) : unitValue R (normalize R φ) = 1 := by
  rw [normalize, map_mul, map_inv, unitValue_constPt, inv_mul_cancel]

theorem actPt_normalize (t : Multiplicative M →* Cˣ) (φ : Pt R A M C) :
    actPt R t (normalize R φ) = normalize R (actPt R t φ) := by
  simp only [actPt, normalize, map_mul, map_inv, transPt_constPt, constPt_constPt,
    constPt_transPt, char_one_mul]
  exact group_aux₂ _ _ _

theorem pushPt_normalize (g : C →ₐ[R] D) (φ : Pt R A M C) :
    pushPt R g (normalize R φ) = normalize R (pushPt R g φ) := by
  rw [normalize, normalize, map_mul, map_inv, pushPt_constPt, mapChar_one]

theorem comulRight_eq (f : A →ₐ[R] C ⊗[R] AddMonoidAlgebra R M) :
    toConv (comulRight R f) =
      toConv ((inclFirst R).comp f) * toConv ((inclSecond R).comp f) := by
  rw [AlgHom.convMul_def, comulRight]
  congr 1
  rw [← AlgHom.comp_assoc]
  congr 1
  exact Algebra.TensorProduct.ext' fun a b => by simp

theorem counitMap_eq (f : A →ₐ[R] C ⊗[R] AddMonoidAlgebra R M) :
    counitMap R f = (evalAt R 1).comp f := by
  rw [counitMap, evalAt_one_eq_counit]

/-- A Hopf point has value `1` at the unit section. -/
theorem constPt_one_of_isHopfPoint {φ : Pt R A M C} (hφ : IsHopfPoint R φ.ofConv) :
    constPt R 1 φ = 1 := by
  have h1 : unitValue R φ = 1 := by
    rw [AlgHom.convOne_def, ← hφ.2, counitMap_eq]
    rfl
  rw [constPt_eq R 1, h1, map_one]

theorem normalize_of_isHopfPoint {φ : Pt R A M C} (hφ : IsHopfPoint R φ.ofConv) :
    normalize R φ = φ := by
  rw [normalize, constPt_one_of_isHopfPoint R hφ]
  exact group_aux₃ φ

/-- A Hopf point is fixed by the normalised translation action. -/
theorem actPt_of_isHopfPoint {φ : Pt R A M C} (hφ : IsHopfPoint R φ.ofConv)
    (t : Multiplicative M →* Cˣ) : actPt R t φ = φ := by
  have h2 : transPt R t φ = φ * constPt R t φ := calc
    transPt R t φ = postComp (splitEval R t) (toConv (comulLeft R φ.ofConv)) := by
      rw [transPt, ← splitEval_comp_comul]; rfl
    _ = postComp (splitEval R t) (toConv (comulRight R φ.ofConv)) := by rw [hφ.1]
    _ = postComp (splitEval R t)
        (postComp (inclFirst R) φ * postComp (inclSecond R) φ) := by
      rw [comulRight_eq]; rfl
    _ = φ * constPt R t φ := by
      rw [map_mul, postComp_postComp, postComp_postComp, splitEval_comp_inclFirst,
        splitEval_comp_inclSecond, postComp_id]
  rw [actPt, h2, constPt_one_of_isHopfPoint R hφ,
    mul_one (φ * constPt R t φ * (constPt R t φ)⁻¹)]
  exact mul_inv_cancel_right φ _

/-- A point fixed by the universal character after the universal refinement, with value `1` at
the unit section, is a Hopf point. -/
theorem isHopfPoint_of_actPt {φ : Pt R A M C} (h1 : unitValue R φ = 1)
    (hfix : actPt R (universalChar R) (pushPt R (incl R) φ) = pushPt R (incl R) φ) :
    IsHopfPoint R φ.ofConv := by
  set ψ := pushPt R (incl R (M := M)) φ
  have hψ : constPt R 1 ψ = 1 := by
    rw [constPt_eq, unitValue_pushPt, h1, map_one, map_one]
  have h : transPt R (universalChar R) ψ = ψ * constPt R (universalChar R) ψ := by
    rw [actPt, hψ, mul_one (transPt R (universalChar R) ψ *
      (constPt R (universalChar R) ψ)⁻¹)] at hfix
    exact eq_mul_of_mul_inv_eq hfix
  refine ⟨?_, ?_⟩
  · apply toConv_injective
    rw [comulRight_eq]
    calc toConv (comulLeft R φ.ofConv)
        = toConv ((swapAssoc R).comp (transPt R (universalChar R) ψ).ofConv) := by
          rw [comulLeft, ← swapAssoc_comp_translate]; rfl
      _ = toConv ((swapAssoc R).comp (ψ * constPt R (universalChar R) ψ).ofConv) := by
          rw [h]
      _ = toConv ((swapAssoc R).comp ψ.ofConv) *
            toConv ((swapAssoc R).comp (constPt R (universalChar R) ψ).ofConv) := by
          rw [AlgHom.comp_convMul_distrib, toConv_ofConv]
      _ = toConv ((inclFirst R).comp φ.ofConv) * toConv ((inclSecond R).comp φ.ofConv) := by
          rw [← swapAssoc_comp_map, ← swapAssoc_comp_evalAt]; rfl
  · rw [counitMap_eq]
    have := congrArg ofConv h1
    rw [AlgHom.convOne_def] at this
    exact this

end Action

section Smooth

open CategoryTheory GroupScheme

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [HopfAlgebra R A]
  [Algebra.FinitePresentation R A] (M : Type u) [AddCommGroup M] [Finite M]

/-- The Weil restriction `Weil R A R[M]`, whose points are algebra maps `A → C ⊗[R] R[M]`, as
an object of `CommAlgCat`. -/
abbrev weilObj : CommAlgCat.{u} (CommRingCat.of R) :=
  CommAlgCat.of (CommRingCat.of R) (Weil R A (AddMonoidAlgebra R M))

variable {R A M}

/-- Points of the Weil restriction are algebra maps `A → C ⊗[R] R[M]`. -/
def weilPtEquiv (C : CommAlgCat.{u} (CommRingCat.of R)) : (weilObj R A M ⟶ C) ≃ Pt R A M C where
  toFun x := toConv
    (TauCeti.Algebra.WeilRestriction.tensorHomEquiv R (AddMonoidAlgebra R M) A C x.hom)
  invFun φ := CommAlgCat.ofHom
    ((TauCeti.Algebra.WeilRestriction.tensorHomEquiv R (AddMonoidAlgebra R M) A C).symm φ.ofConv)
  left_inv x := by
    apply CommAlgCat.hom_ext
    exact (TauCeti.Algebra.WeilRestriction.tensorHomEquiv R (AddMonoidAlgebra R M) A
      C).symm_apply_apply x.hom
  right_inv φ := by
    change toConv (TauCeti.Algebra.WeilRestriction.tensorHomEquiv R (AddMonoidAlgebra R M) A C
      ((TauCeti.Algebra.WeilRestriction.tensorHomEquiv R (AddMonoidAlgebra R M) A C).symm
        φ.ofConv)) = φ
    rw [Equiv.apply_symm_apply]

theorem weilPtEquiv_comp {C D : CommAlgCat.{u} (CommRingCat.of R)} (x : weilObj R A M ⟶ C)
    (f : C ⟶ D) : weilPtEquiv D (x ≫ f) = pushPt R f.hom (weilPtEquiv C x) :=
  congrArg toConv (TauCeti.Algebra.WeilRestriction.tensorHomEquiv_comp x.hom f.hom)

/-- The normalised translation action of characters on the points of the Weil restriction. -/
def weilAction : CharacterAction.Action (M := M) (weilObj R A M) where
  act t x := (weilPtEquiv _).symm (actPt R t (weilPtEquiv _ x))
  one x := by rw [actPt_one, Equiv.symm_apply_apply]
  mul t s x := by rw [Equiv.apply_symm_apply, actPt_mul]
  naturality f t x := by
    rw [Equiv.symm_apply_eq, weilPtEquiv_comp, weilPtEquiv_comp, Equiv.apply_symm_apply,
      pushPt_actPt]

theorem weilPtEquiv_act {C : CommAlgCat.{u} (CommRingCat.of R)} (t : Multiplicative M →* Cˣ)
    (x : weilObj R A M ⟶ C) :
    weilPtEquiv C ((weilAction (R := R) (A := A) (M := M)).act t x) =
      actPt R t (weilPtEquiv C x) :=
  Equiv.apply_symm_apply _ _

/-- Hopf points of the Weil restriction are fixed after every refinement. -/
theorem isFixed_of_isHopfPoint {C : CommAlgCat.{u} (CommRingCat.of R)} {x : weilObj R A M ⟶ C}
    (hx : IsHopfPoint R (weilPtEquiv C x).ofConv) :
    CharacterAction.IsFixed (weilAction (R := R) (A := A) (M := M)) x := by
  intro D f t
  apply (weilPtEquiv D).injective
  rw [weilPtEquiv_act, weilPtEquiv_comp]
  exact actPt_of_isHopfPoint R (hx.pushPoint R f.hom) t

/-- A point of the Weil restriction fixed after every refinement becomes a Hopf point after
division by its value at the unit section. -/
theorem isHopfPoint_normalize_of_isFixed {C : CommAlgCat.{u} (CommRingCat.of R)}
    {x : weilObj R A M ⟶ C}
    (hx : CharacterAction.IsFixed (weilAction (R := R) (A := A) (M := M)) x) :
    IsHopfPoint R (normalize R (weilPtEquiv C x)).ofConv := by
  apply isHopfPoint_of_actPt R (unitValue_normalize R _)
  have h := congrArg (weilPtEquiv _)
    (hx (CommAlgCat.of (CommRingCat.of R) (C ⊗[R] AddMonoidAlgebra R M))
      (CommAlgCat.ofHom (incl R)) (universalChar R))
  rw [weilPtEquiv_act, weilPtEquiv_comp] at h
  rw [pushPt_normalize, actPt_normalize]
  exact congrArg (normalize R) h

/-- Hopf points `A → C ⊗[R] R[M]` lift through square-zero thickenings. -/
instance formallySmooth_homAlgebra [Algebra.FormallySmooth R A] :
    Algebra.FormallySmooth R (HomAlgebra R A (AddMonoidAlgebra R M)) := by
  refine Algebra.FormallySmooth.of_comp_surjective fun B _ _ I hI g => ?_
  let Bc : CommAlgCat.{u} (CommRingCat.of R) := CommAlgCat.of (CommRingCat.of R) B
  let x : weilObj R A M ⟶ CommAlgCat.of (CommRingCat.of R) (Bc ⧸ I) :=
    CommAlgCat.ofHom (g.comp (Ideal.Quotient.mkₐ R _))
  have hxpt : (weilPtEquiv _ x).ofConv = (homEquiv R A _ (B ⧸ I) g).1 := by
    change TauCeti.Algebra.WeilRestriction.tensorHomEquiv R (AddMonoidAlgebra R M) A (B ⧸ I)
      (g.comp (Ideal.Quotient.mkₐ R _)) = _
    rw [tensorHomEquiv_eq, homEquiv_apply, universalPoint, pushPoint_pushPoint]
  have hxH : IsHopfPoint R (weilPtEquiv _ x).ofConv := hxpt ▸ (homEquiv R A _ (B ⧸ I) g).2
  have : Algebra.FormallySmooth (CommRingCat.of R) (weilObj R A M) :=
    inferInstanceAs (Algebra.FormallySmooth R (Weil R A (AddMonoidAlgebra R M)))
  obtain ⟨y, hy, hyx⟩ := CharacterAction.exists_fixed_lift (C := Bc) weilAction I ⟨2, hI⟩ x
    (isFixed_of_isHopfPoint hxH)
  refine ⟨(homEquiv R A _ B).symm ⟨_, isHopfPoint_normalize_of_isFixed hy⟩, ?_⟩
  refine (homEquiv R A _ (B ⧸ I)).injective (Subtype.ext ?_)
  rw [homEquiv_apply, ← pushPoint_pushPoint, ← homEquiv_apply, Equiv.apply_symm_apply, ← hxpt,
    ← normalize_of_isHopfPoint R hxH, ← hyx, weilPtEquiv_comp, ← pushPt_normalize]
  rfl

instance smooth_homAlgebra [Algebra.FormallySmooth R A] :
    Algebra.Smooth R (HomAlgebra R A (AddMonoidAlgebra R M)) where

end Smooth

end Langlands.FiniteBialgebraHom
