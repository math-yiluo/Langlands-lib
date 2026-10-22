import Langlands.Shimura.Unitary.Similitude
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.CategoryTheory.Yoneda

/-! # Coordinate rings representing similitude functors

For a finite basis `b` of `A` over `R`, the similitudes of `S ⊗[R] A` are the
`R`-algebra maps to `S` from a quotient of a polynomial ring by finitely many
coordinate equations.
-/

noncomputable section

universe r u v w z

namespace Langlands.Shimura

open scoped TensorProduct
open MvPolynomial CategoryTheory

/-- Polynomial variables for similitudes: the basis coordinates of an algebra
element and of its inverse, the multiplier, and the inverse multiplier. -/
inductive SimilitudeVariable (ι : Type v) : Type v
  | unit : ι → SimilitudeVariable ι
  | unitInv : ι → SimilitudeVariable ι
  | multiplier : SimilitudeVariable ι
  | multiplierInv : SimilitudeVariable ι

namespace SimilitudeVariable

variable {ι : Type v}

/-- An injective code of the variables in an evidently finite type. -/
def code : SimilitudeVariable ι → Option (Option (ι ⊕ ι))
  | unit i => some (some (Sum.inl i))
  | unitInv i => some (some (Sum.inr i))
  | multiplier => some none
  | multiplierInv => none

theorem code_injective : Function.Injective (code (ι := ι)) := by
  intro v w h
  cases v <;> cases w <;> simp_all [code]

instance [Finite ι] : Finite (SimilitudeVariable ι) :=
  Finite.of_injective code code_injective

end SimilitudeVariable

namespace AlgebraInvolution

variable {R : Type r} {A : Type u} [CommRing R] [Ring A] [Algebra R A]

section General

variable {ι : Type v} [Fintype ι] (b : Module.Basis ι R A)

section Coordinates

variable {S : Type w} {T : Type z} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

/-- The `i`-th coordinate of `x ∈ S ⊗[R] A` in the scalar-extended basis `1 ⊗ b`. -/
def coordinate (x : S ⊗[R] A) (i : ι) : S :=
  (Algebra.TensorProduct.basis S b).repr x i

/-- The element `∑ i, c i ⊗ b i` of `S ⊗[R] A` with prescribed coordinates. -/
def ofCoordinates (c : ι → S) : S ⊗[R] A :=
  ∑ i, c i ⊗ₜ[R] b i

theorem ofCoordinates_eq_sum_smul (c : ι → S) :
    ofCoordinates b c = ∑ i, c i • Algebra.TensorProduct.basis S b i := by
  simp only [ofCoordinates, Algebra.TensorProduct.basis_repr_symm_apply']

@[simp] theorem coordinate_ofCoordinates (c : ι → S) (i : ι) :
    coordinate b (ofCoordinates b c) i = c i := by
  rw [coordinate, ofCoordinates_eq_sum_smul, (Algebra.TensorProduct.basis S b).repr_sum_self]

@[simp] theorem ofCoordinates_coordinate (x : S ⊗[R] A) :
    ofCoordinates b (fun i => coordinate b x i) = x := by
  rw [ofCoordinates_eq_sum_smul]
  exact (Algebra.TensorProduct.basis S b).sum_repr x

omit [Fintype ι] in
@[simp] theorem coordinate_zero (i : ι) : coordinate b (0 : S ⊗[R] A) i = 0 := by
  simp [coordinate]

theorem ext_coordinate {x y : S ⊗[R] A} (h : ∀ i, coordinate b x i = coordinate b y i) :
    x = y := by
  rw [← ofCoordinates_coordinate b x, ← ofCoordinates_coordinate b y]
  exact congrArg _ (funext h)

@[simp] theorem changeCoefficients_ofCoordinates (f : S →ₐ[R] T) (c : ι → S) :
    changeCoefficients (A := A) f (ofCoordinates b c) = ofCoordinates b (fun i => f (c i)) := by
  simp [ofCoordinates, map_sum]

theorem coordinate_changeCoefficients (f : S →ₐ[R] T) (x : S ⊗[R] A) (i : ι) :
    coordinate b (changeCoefficients f x) i = f (coordinate b x i) := by
  conv_lhs => rw [← ofCoordinates_coordinate b x]
  rw [changeCoefficients_ofCoordinates, coordinate_ofCoordinates]

end Coordinates

theorem changeCoefficients_changeCoefficients {S : Type w} {T : Type z} {U : Type*}
    [CommRing S] [Algebra R S] [CommRing T] [Algebra R T] [CommRing U] [Algebra R U]
    (f : S →ₐ[R] T) (g : T →ₐ[R] U) (x : S ⊗[R] A) :
    changeCoefficients g (changeCoefficients f x) = changeCoefficients (g.comp f) x := by
  rw [changeCoefficients_comp]
  rfl

section Universal

variable (σ : AlgebraInvolution R A)

/-- The generic algebra element whose coordinates are the variables `unit i`. -/
def genericUnit : MvPolynomial (SimilitudeVariable ι) R ⊗[R] A :=
  ofCoordinates b fun i => X (SimilitudeVariable.unit i)

/-- The generic algebra element whose coordinates are the variables `unitInv i`. -/
def genericUnitInv : MvPolynomial (SimilitudeVariable ι) R ⊗[R] A :=
  ofCoordinates b fun i => X (SimilitudeVariable.unitInv i)

/-- The polynomial equations: the coordinates of `g h - 1`, `h g - 1` and
`g σ(g) - c` for the generic `g`, `h`, `c`, and the scalar equation `c d - 1`. -/
def similitudeRelations : Set (MvPolynomial (SimilitudeVariable ι) R) :=
  Set.range (coordinate b (genericUnit b * genericUnitInv b - 1)) ∪
    Set.range (coordinate b (genericUnitInv b * genericUnit b - 1)) ∪
    Set.range (coordinate b (genericUnit b *
      σ.baseChange (MvPolynomial (SimilitudeVariable ι) R) (genericUnit b) -
        algebraMap (MvPolynomial (SimilitudeVariable ι) R)
          (MvPolynomial (SimilitudeVariable ι) R ⊗[R] A)
          (X SimilitudeVariable.multiplier))) ∪
    {(X SimilitudeVariable.multiplier * X SimilitudeVariable.multiplierInv - 1 :
      MvPolynomial (SimilitudeVariable ι) R)}

theorem similitudeRelations_finite : (σ.similitudeRelations b).Finite :=
  (((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)).union
    (Set.finite_singleton _)

/-- The ideal generated by the similitude equations. -/
def similitudeIdeal : Ideal (MvPolynomial (SimilitudeVariable ι) R) :=
  Ideal.span (σ.similitudeRelations b)

theorem similitudeIdeal_fg : (σ.similitudeIdeal b).FG :=
  ⟨(σ.similitudeRelations_finite b).toFinset, by simp [similitudeIdeal]⟩

/-- The coordinate ring of the similitude functor in the basis `b`. -/
abbrev similitudeCoordinateRing :=
  MvPolynomial (SimilitudeVariable ι) R ⧸ σ.similitudeIdeal b

instance : Algebra.FinitePresentation R (σ.similitudeCoordinateRing b) :=
  Algebra.FinitePresentation.quotient (σ.similitudeIdeal_fg b)

/-- The quotient map from the polynomial ring. -/
abbrev similitudeQuotient :
    MvPolynomial (SimilitudeVariable ι) R →ₐ[R] σ.similitudeCoordinateRing b :=
  Ideal.Quotient.mkₐ R (σ.similitudeIdeal b)

/-- A polynomial map kills the similitude ideal once it satisfies the equations. -/
theorem similitudeIdeal_le_ker {S : Type w} [CommRing S] [Algebra R S]
    (ψ : MvPolynomial (SimilitudeVariable ι) R →ₐ[R] S)
    (h₁ : changeCoefficients ψ (genericUnit b) * changeCoefficients ψ (genericUnitInv b) = 1)
    (h₂ : changeCoefficients ψ (genericUnitInv b) * changeCoefficients ψ (genericUnit b) = 1)
    (h₃ : changeCoefficients ψ (genericUnit b) *
        σ.baseChange S (changeCoefficients ψ (genericUnit b)) =
      algebraMap S (S ⊗[R] A) (ψ (X SimilitudeVariable.multiplier)))
    (h₄ : ψ (X SimilitudeVariable.multiplier) * ψ (X SimilitudeVariable.multiplierInv) = 1) :
    σ.similitudeIdeal b ≤ RingHom.ker ψ := by
  refine Ideal.span_le.mpr ?_
  rintro _ (((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | rfl) <;>
    simp only [SetLike.mem_coe, RingHom.mem_ker]
  · rw [← coordinate_changeCoefficients, map_sub, _root_.map_mul, _root_.map_one, h₁,
      sub_self, coordinate_zero]
  · rw [← coordinate_changeCoefficients, map_sub, _root_.map_mul, _root_.map_one, h₂,
      sub_self, coordinate_zero]
  · rw [← coordinate_changeCoefficients, map_sub, _root_.map_mul,
      changeCoefficients_involution, changeCoefficients_scalar, h₃, sub_self, coordinate_zero]
  · rw [map_sub, _root_.map_mul, _root_.map_one, h₄, sub_self]

theorem changeCoefficients_similitudeQuotient_eq_zero
    (x : MvPolynomial (SimilitudeVariable ι) R ⊗[R] A)
    (hx : ∀ i, coordinate b x i ∈ σ.similitudeIdeal b) :
    changeCoefficients (σ.similitudeQuotient b) x = 0 := by
  apply ext_coordinate b
  intro i
  rw [coordinate_changeCoefficients, coordinate_zero, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem]
  exact hx i

theorem universalUnit_mul_inv :
    changeCoefficients (σ.similitudeQuotient b) (genericUnit b) *
      changeCoefficients (σ.similitudeQuotient b) (genericUnitInv b) = 1 := by
  have h := σ.changeCoefficients_similitudeQuotient_eq_zero b
    (genericUnit b * genericUnitInv b - 1)
    (fun i => Ideal.subset_span (Or.inl (Or.inl (Or.inl ⟨i, rfl⟩))))
  rwa [map_sub, _root_.map_mul, _root_.map_one, sub_eq_zero] at h

theorem universalUnit_inv_mul :
    changeCoefficients (σ.similitudeQuotient b) (genericUnitInv b) *
      changeCoefficients (σ.similitudeQuotient b) (genericUnit b) = 1 := by
  have h := σ.changeCoefficients_similitudeQuotient_eq_zero b
    (genericUnitInv b * genericUnit b - 1)
    (fun i => Ideal.subset_span (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))))
  rwa [map_sub, _root_.map_mul, _root_.map_one, sub_eq_zero] at h

theorem universalMultiplier_mul_inv :
    σ.similitudeQuotient b (X SimilitudeVariable.multiplier) *
      σ.similitudeQuotient b (X SimilitudeVariable.multiplierInv) = 1 := by
  rw [← _root_.map_mul, ← _root_.map_one (σ.similitudeQuotient b), Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq]
  exact Ideal.subset_span (Or.inr rfl)

/-- The universal invertible algebra element over the coordinate ring. -/
def universalUnit : (σ.similitudeCoordinateRing b ⊗[R] A)ˣ where
  val := changeCoefficients (σ.similitudeQuotient b) (genericUnit b)
  inv := changeCoefficients (σ.similitudeQuotient b) (genericUnitInv b)
  val_inv := σ.universalUnit_mul_inv b
  inv_val := σ.universalUnit_inv_mul b

/-- The universal invertible multiplier in the coordinate ring. -/
def universalMultiplier : (σ.similitudeCoordinateRing b)ˣ where
  val := σ.similitudeQuotient b (X SimilitudeVariable.multiplier)
  inv := σ.similitudeQuotient b (X SimilitudeVariable.multiplierInv)
  val_inv := σ.universalMultiplier_mul_inv b
  inv_val := (mul_comm _ _).trans (σ.universalMultiplier_mul_inv b)

/-- The universal similitude over the coordinate ring. -/
def universalSimilitude :
    (σ.baseChange (σ.similitudeCoordinateRing b)).similitudes :=
  ⟨(σ.universalUnit b, σ.universalMultiplier b), by
    rw [mem_similitudes_iff]
    change changeCoefficients (σ.similitudeQuotient b) (genericUnit b) *
        σ.baseChange _ (changeCoefficients (σ.similitudeQuotient b) (genericUnit b)) =
      algebraMap _ _ (σ.similitudeQuotient b (X SimilitudeVariable.multiplier))
    have h := σ.changeCoefficients_similitudeQuotient_eq_zero b
      (genericUnit b * σ.baseChange _ (genericUnit b) -
        algebraMap _ _ (X SimilitudeVariable.multiplier))
      (fun i => Ideal.subset_span (Or.inl (Or.inr ⟨i, rfl⟩)))
    rwa [map_sub, _root_.map_mul, changeCoefficients_involution, changeCoefficients_scalar,
      sub_eq_zero] at h⟩

end Universal

section Points

variable (σ : AlgebraInvolution R A)
variable {S : Type w} {T : Type z} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

/-- Specialize the universal similitude along an algebra map. -/
def similitudePoint (f : σ.similitudeCoordinateRing b →ₐ[R] S) :
    (σ.baseChange S).similitudes :=
  (σ.baseChange _).map (σ.baseChange S) (changeCoefficients f).toRingHom f.toRingHom
    (σ.changeCoefficients_involution f) (changeCoefficients_scalar f) (σ.universalSimilitude b)

@[simp] theorem similitudePoint_unit (f : σ.similitudeCoordinateRing b →ₐ[R] S) :
    ((σ.similitudePoint b f).1.1 : S ⊗[R] A) =
      ofCoordinates b fun i => f (σ.similitudeQuotient b (X (SimilitudeVariable.unit i))) := by
  change changeCoefficients f (changeCoefficients (σ.similitudeQuotient b) (genericUnit b)) = _
  simp [genericUnit]

@[simp] theorem similitudePoint_unitInv (f : σ.similitudeCoordinateRing b →ₐ[R] S) :
    (((σ.similitudePoint b f).1.1⁻¹ : (S ⊗[R] A)ˣ) : S ⊗[R] A) =
      ofCoordinates b fun i => f (σ.similitudeQuotient b (X (SimilitudeVariable.unitInv i))) := by
  change changeCoefficients f (changeCoefficients (σ.similitudeQuotient b) (genericUnitInv b)) = _
  simp [genericUnitInv]

@[simp] theorem similitudePoint_multiplier (f : σ.similitudeCoordinateRing b →ₐ[R] S) :
    ((σ.similitudePoint b f).1.2 : S) =
      f (σ.similitudeQuotient b (X SimilitudeVariable.multiplier)) :=
  rfl

@[simp] theorem similitudePoint_multiplierInv (f : σ.similitudeCoordinateRing b →ₐ[R] S) :
    (((σ.similitudePoint b f).1.2⁻¹ : Sˣ) : S) =
      f (σ.similitudeQuotient b (X SimilitudeVariable.multiplierInv)) :=
  rfl

theorem similitudePoint_comp (f : σ.similitudeCoordinateRing b →ₐ[R] S) (g : S →ₐ[R] T) :
    σ.similitudePoint b (g.comp f) =
      (σ.baseChange S).map (σ.baseChange T) (changeCoefficients g).toRingHom g.toRingHom
        (σ.changeCoefficients_involution g) (changeCoefficients_scalar g)
        (σ.similitudePoint b f) := by
  apply Subtype.ext
  apply Prod.ext <;> apply Units.ext
  · exact (changeCoefficients_changeCoefficients f g
      (changeCoefficients (σ.similitudeQuotient b) (genericUnit b))).symm
  · rfl

/-- The values of the polynomial variables at a similitude: its coordinates,
the coordinates of its inverse, its multiplier and the inverse multiplier. -/
def similitudeValues (x : (σ.baseChange S).similitudes) : SimilitudeVariable ι → S
  | .unit i => coordinate b (x.1.1 : S ⊗[R] A) i
  | .unitInv i => coordinate b ((x.1.1⁻¹ : (S ⊗[R] A)ˣ) : S ⊗[R] A) i
  | .multiplier => x.1.2
  | .multiplierInv => ((x.1.2⁻¹ : Sˣ) : S)

theorem changeCoefficients_aeval_genericUnit (x : (σ.baseChange S).similitudes) :
    changeCoefficients (aeval (σ.similitudeValues b x)) (genericUnit b) = x.1.1 := by
  simp [genericUnit, similitudeValues]

theorem changeCoefficients_aeval_genericUnitInv (x : (σ.baseChange S).similitudes) :
    changeCoefficients (aeval (σ.similitudeValues b x)) (genericUnitInv b) =
      ((x.1.1⁻¹ : (S ⊗[R] A)ˣ) : S ⊗[R] A) := by
  simp [genericUnitInv, similitudeValues]

/-- The algebra map from the coordinate ring classifying a similitude. -/
def similitudeHom (x : (σ.baseChange S).similitudes) :
    σ.similitudeCoordinateRing b →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (aeval (σ.similitudeValues b x)) fun _ ha =>
    RingHom.mem_ker.mp <| σ.similitudeIdeal_le_ker b _
      (by
        rw [changeCoefficients_aeval_genericUnit, changeCoefficients_aeval_genericUnitInv]
        exact x.1.1.mul_inv)
      (by
        rw [changeCoefficients_aeval_genericUnit, changeCoefficients_aeval_genericUnitInv]
        exact x.1.1.inv_mul)
      (by
        rw [changeCoefficients_aeval_genericUnit, aeval_X]
        exact (mem_similitudes_iff _ x.1).mp x.2)
      (by
        rw [aeval_X, aeval_X]
        exact x.1.2.mul_inv)
      ha

theorem similitudeHom_comp (x : (σ.baseChange S).similitudes) :
    (σ.similitudeHom b x).comp (σ.similitudeQuotient b) = aeval (σ.similitudeValues b x) :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[simp] theorem similitudeHom_quotient (x : (σ.baseChange S).similitudes)
    (p : MvPolynomial (SimilitudeVariable ι) R) :
    σ.similitudeHom b x (σ.similitudeQuotient b p) = aeval (σ.similitudeValues b x) p :=
  AlgHom.congr_fun (σ.similitudeHom_comp b x) p

/-- Algebra maps out of the coordinate ring are exactly the similitudes. -/
def similitudeHomEquiv :
    (σ.similitudeCoordinateRing b →ₐ[R] S) ≃ (σ.baseChange S).similitudes where
  toFun := σ.similitudePoint b
  invFun := σ.similitudeHom b
  left_inv f := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply, AlgHom.comp_apply, similitudeHom_quotient, aeval_X]
    cases v with
    | unit i => simp [similitudeValues]
    | unitInv i => simp [similitudeValues]
    | multiplier => rfl
    | multiplierInv => rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext <;> apply Units.ext
    · change changeCoefficients (σ.similitudeHom b x)
        (changeCoefficients (σ.similitudeQuotient b) (genericUnit b)) = _
      rw [changeCoefficients_changeCoefficients, similitudeHom_comp,
        changeCoefficients_aeval_genericUnit]
    · change σ.similitudeHom b x (σ.similitudeQuotient b (X SimilitudeVariable.multiplier)) = _
      rw [similitudeHom_quotient, aeval_X]
      rfl

@[simp] theorem similitudeHom_similitudePoint (f : σ.similitudeCoordinateRing b →ₐ[R] S) :
    σ.similitudeHom b (σ.similitudePoint b f) = f :=
  (σ.similitudeHomEquiv b).left_inv f

@[simp] theorem similitudePoint_similitudeHom (x : (σ.baseChange S).similitudes) :
    σ.similitudePoint b (σ.similitudeHom b x) = x :=
  (σ.similitudeHomEquiv b).right_inv x

/-- The classifying map is natural in the coefficient algebra. -/
theorem similitudeHom_map (g : S →ₐ[R] T) (x : (σ.baseChange S).similitudes) :
    σ.similitudeHom b ((σ.baseChange S).map (σ.baseChange T) (changeCoefficients g).toRingHom
        g.toRingHom (σ.changeCoefficients_involution g) (changeCoefficients_scalar g) x) =
      g.comp (σ.similitudeHom b x) := by
  apply (σ.similitudeHomEquiv b).injective
  change σ.similitudePoint b _ = σ.similitudePoint b _
  rw [similitudePoint_comp, similitudePoint_similitudeHom, similitudePoint_similitudeHom]

@[simp] theorem similitudePoint_id :
    σ.similitudePoint b (AlgHom.id R (σ.similitudeCoordinateRing b)) =
      σ.universalSimilitude b := by
  apply Subtype.ext
  apply Prod.ext <;> apply Units.ext
  · change changeCoefficients (AlgHom.id R _)
      ((σ.universalSimilitude b).1.1 : σ.similitudeCoordinateRing b ⊗[R] A) = _
    rw [changeCoefficients_id]
    rfl
  · rfl

/-- The universal similitude is classified by the identity map. -/
theorem similitudeHom_universalSimilitude :
    σ.similitudeHom b (σ.universalSimilitude b) = AlgHom.id R (σ.similitudeCoordinateRing b) := by
  rw [← σ.similitudePoint_id b, similitudeHom_similitudePoint]

end Points

end General

section Functor

variable {ι : Type u} [Fintype ι] (b : Module.Basis ι R A) (σ : AlgebraInvolution R A)

/-- The coordinate ring as an object of commutative `R`-algebras. -/
abbrev similitudeCoordinateAlgebra : CommAlgCat.{max r u} R :=
  CommAlgCat.of R (σ.similitudeCoordinateRing b)

/-- The similitude functor is corepresented by the coordinate ring. -/
def similitudeCorepresentableBy :
    (σ.similitudeFunctor.{r, u, max r u} ⋙ forget GrpCat.{max r u}).CorepresentableBy
      (σ.similitudeCoordinateAlgebra b) where
  homEquiv :=
    { toFun := fun f => σ.similitudePoint b f.hom
      invFun := fun x => CommAlgCat.ofHom (σ.similitudeHom b x)
      left_inv := fun f => CommAlgCat.hom_ext ((σ.similitudeHomEquiv b).left_inv f.hom)
      right_inv := fun x => (σ.similitudeHomEquiv b).right_inv x }
  homEquiv_comp g f := σ.similitudePoint_comp b f.hom g.hom

/-- The natural isomorphism from the functor corepresented by the coordinate
ring to the similitude points. -/
def similitudeCoyonedaIso :
    coyoneda.obj (Opposite.op (σ.similitudeCoordinateAlgebra b)) ≅
      σ.similitudeFunctor.{r, u, max r u} ⋙ forget GrpCat.{max r u} :=
  (σ.similitudeCorepresentableBy b).toIso

end Functor

end AlgebraInvolution

end Langlands.Shimura
