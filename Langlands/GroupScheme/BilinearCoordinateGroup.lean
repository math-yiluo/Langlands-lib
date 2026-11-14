import Langlands.GroupScheme.CorepresentedPoints
import Langlands.GroupScheme.CorepresentedSmooth
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Affine group schemes with a bilinear cocycle on `𝔸ⁿ × 𝔸¹`

For a commutative ring `R`, a finite index type `ι` and coefficients `c : ι → ι → R`, the
points `(a, b) ∈ (ι → A) × A` over a commutative `R`-algebra `A` form a group under
`(a, b) * (a', b') = (a + a', b + b' + ∑ᵢⱼ cᵢⱼ aᵢ a'ⱼ)`. This module builds the corresponding
actual affine group scheme over `Spec R`, corepresented by the polynomial ring
`R[xᵢ, y]`, proves that it is smooth, affine, flat, of finite type and geometrically
connected over `Spec R`, and constructs the homomorphisms given by a linear change of the
vector coordinate and a scaling of the scalar coordinate which preserve the cocycle.
-/

noncomputable section

universe u v w

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial

attribute [local instance] CategoryTheory.Hom.group

namespace Langlands.GroupScheme.BilinearCoordinate

/-! ### The algebraic group law -/

section Group

variable {ι : Type v} {S : Type w} [CommRing S]

/-- The bilinear cocycle `∑ᵢⱼ cᵢⱼ aᵢ a'ⱼ`. -/
def form [Fintype ι] (c : ι → ι → S) (a a' : ι → S) : S := ∑ i, ∑ j, c i j * a i * a' j

section Form

variable [Fintype ι] (c : ι → ι → S)

theorem form_add_left (a a' a'' : ι → S) :
    form c (a + a') a'' = form c a a'' + form c a' a'' := by
  simp only [form, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem form_add_right (a a' a'' : ι → S) :
    form c a (a' + a'') = form c a a' + form c a a'' := by
  simp only [form, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem form_neg_left (a a' : ι → S) : form c (-a) a' = -form c a a' := by
  simp only [form, Pi.neg_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

@[simp] theorem form_zero_left (a : ι → S) : form c 0 a = 0 := by
  simp [form]

@[simp] theorem form_zero_right (a : ι → S) : form c a 0 = 0 := by
  simp [form]

end Form

/-- Points `(a, b)` of the bilinear coordinate group with cocycle coefficients `c`. -/
@[ext] structure Coordinates (c : ι → ι → S) where
  /-- The vector coordinate `a ∈ Sⁱ`. -/
  vec : ι → S
  /-- The scalar coordinate `b ∈ S`. -/
  scalar : S

namespace Coordinates

variable {c : ι → ι → S}

instance : One (Coordinates c) := ⟨⟨0, 0⟩⟩

@[simp] theorem vec_one : (1 : Coordinates c).vec = 0 := rfl
@[simp] theorem scalar_one : (1 : Coordinates c).scalar = 0 := rfl

variable [Fintype ι]

instance : Mul (Coordinates c) :=
  ⟨fun x y => ⟨x.vec + y.vec, x.scalar + y.scalar + form c x.vec y.vec⟩⟩

instance : Inv (Coordinates c) := ⟨fun x => ⟨-x.vec, -x.scalar + form c x.vec x.vec⟩⟩

@[simp] theorem vec_mul (x y : Coordinates c) : (x * y).vec = x.vec + y.vec := rfl
@[simp] theorem scalar_mul (x y : Coordinates c) :
    (x * y).scalar = x.scalar + y.scalar + form c x.vec y.vec := rfl
@[simp] theorem vec_inv (x : Coordinates c) : x⁻¹.vec = -x.vec := rfl
@[simp] theorem scalar_inv (x : Coordinates c) :
    x⁻¹.scalar = -x.scalar + form c x.vec x.vec := rfl

instance : Group (Coordinates c) where
  mul_assoc x y z := by
    ext
    · simp [add_assoc]
    · simp only [scalar_mul, vec_mul, form_add_left, form_add_right]
      ring
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  inv_mul_cancel x := by
    ext
    · simp
    · simp only [scalar_mul, scalar_inv, vec_inv, form_neg_left, scalar_one]
      ring

variable {T : Type*} [CommRing T] {d : ι → ι → T}

/-- A ring map carrying the cocycle coefficients to the cocycle coefficients induces a
homomorphism of bilinear coordinate groups. -/
def map (f : S →+* T) (hf : ∀ i j, f (c i j) = d i j) : Coordinates c →* Coordinates d where
  toFun x := ⟨fun i => f (x.vec i), f x.scalar⟩
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext
    · simp
    · simp [form, map_sum, hf]

@[simp] theorem vec_map (f : S →+* T) (hf : ∀ i j, f (c i j) = d i j) (x : Coordinates c)
    (i : ι) : (map f hf x).vec i = f (x.vec i) := rfl

@[simp] theorem scalar_map (f : S →+* T) (hf : ∀ i j, f (c i j) = d i j)
    (x : Coordinates c) : (map f hf x).scalar = f x.scalar := rfl

end Coordinates

/-! ### Linear coordinate changes -/

variable [Fintype ι] {κ : Type*} [Fintype κ]

/-- The vector coordinate change `a ↦ (∑ᵢ aᵢ Mᵢₖ)ₖ`. -/
def matrixVec (M : ι → κ → S) (a : ι → S) : κ → S := fun k => ∑ i, a i * M i k

/-- The compatibility of a matrix and a scalar with two cocycles. -/
def IsCompatible (c : ι → ι → S) (d : κ → κ → S) (M : ι → κ → S) (t : S) : Prop :=
  ∀ i j, ∑ k, ∑ l, M i k * M j l * d k l = t * c i j

theorem form_matrixVec {c : ι → ι → S} {d : κ → κ → S} {M : ι → κ → S} {t : S}
    (h : IsCompatible c d M t) (a a' : ι → S) :
    form d (matrixVec M a) (matrixVec M a') = t * form c a a' := by
  calc form d (matrixVec M a) (matrixVec M a')
      = ∑ k, ∑ l, ∑ i, ∑ j, d k l * (a i * M i k) * (a' j * M j l) := by
        simp only [form, matrixVec, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ l, ∑ j, d k l * (a i * M i k) * (a' j * M j l) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ l, ∑ j, d k l * (a i * M i k) * (a' j * M j l) := Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ j, ∑ l, d k l * (a i * M i k) * (a' j * M j l) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, ∑ l, d k l * (a i * M i k) * (a' j * M j l) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ j, (∑ k, ∑ l, M i k * M j l * d k l) * (a i * a' j) := by
        simp only [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    _ = t * form c a a' := by
        simp only [form, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [h i j]
        ring

namespace Coordinates

variable {c : ι → ι → S} {d : κ → κ → S}

/-- The homomorphism `(a, b) ↦ (M a, t b)` attached to compatible `M` and `t`. -/
def linearMap (M : ι → κ → S) (t : S) (h : IsCompatible c d M t) :
    Coordinates c →* Coordinates d where
  toFun x := ⟨matrixVec M x.vec, t * x.scalar⟩
  map_one' := by
    ext
    · simp [matrixVec]
    · simp
  map_mul' x y := by
    ext
    · simp [matrixVec, add_mul, Finset.sum_add_distrib]
    · change t * (x.scalar + y.scalar + form c x.vec y.vec) =
        t * x.scalar + t * y.scalar + form d (matrixVec M x.vec) (matrixVec M y.vec)
      rw [form_matrixVec h]
      ring

@[simp] theorem vec_linearMap (M : ι → κ → S) (t : S) (h : IsCompatible c d M t)
    (x : Coordinates c) : (linearMap M t h x).vec = matrixVec M x.vec := rfl

@[simp] theorem scalar_linearMap (M : ι → κ → S) (t : S) (h : IsCompatible c d M t)
    (x : Coordinates c) : (linearMap M t h x).scalar = t * x.scalar := rfl

end Coordinates

omit [Fintype ι] in
theorem IsCompatible.map {T : Type*} [CommRing T] {c : ι → ι → S} {d : κ → κ → S}
    {M : ι → κ → S} {t : S} (h : IsCompatible c d M t) (f : S →+* T) :
    IsCompatible (fun i j => f (c i j)) (fun k l => f (d k l)) (fun i k => f (M i k)) (f t) := by
  intro i j
  have := congrArg f (h i j)
  simpa [map_sum, map_mul] using this

end Group

/-! ### The functor and its corepresentation -/

section Functor

variable (R : CommRingCat.{u}) {ι : Type u} [Fintype ι] (c : ι → ι → R)

/-- The cocycle coefficients transported to an `R`-algebra. -/
abbrev algebraCoefficients (A : Type*) [CommRing A] [Algebra R A] : ι → ι → A :=
  fun i j => algebraMap R A (c i j)

/-- The group-valued functor `A ↦ Coordinates (algebraMap R A ∘ c)`. -/
def functor : CommAlgCat.{u} R ⥤ GrpCat.{u} where
  obj A := GrpCat.of (Coordinates (algebraCoefficients R c A))
  map f := GrpCat.ofHom (Coordinates.map f.hom.toRingHom (fun i j => f.hom.commutes (c i j)))
  map_id _ := rfl
  map_comp _ _ := rfl

theorem functor_map_vec {A A' : CommAlgCat.{u} R} (f : A ⟶ A')
    (x : Coordinates (algebraCoefficients R c A)) (i : ι) :
    ((functor R c).map f x).vec i = f.hom (x.vec i) := rfl

theorem functor_map_scalar {A A' : CommAlgCat.{u} R} (f : A ⟶ A')
    (x : Coordinates (algebraCoefficients R c A)) :
    ((functor R c).map f x).scalar = f.hom x.scalar := rfl

/-- The polynomial ring `R[xᵢ, y]`; the variable `some i` is `xᵢ` and `none` is `y`. -/
abbrev coordinateAlgebra (ι : Type u) : CommAlgCat.{u} R := CommAlgCat.of R (MvPolynomial (Option ι) R)

/-- The point with coordinates `(a, b)`, as a valuation of the variables. -/
def valuation {A : Type*} (a : ι → A) (b : A) : Option ι → A := fun o => Option.elim o b a

/-- The polynomial ring corepresents the bilinear coordinate group functor. -/
def corepresentableBy : (functor R c ⋙ forget GrpCat).CorepresentableBy (coordinateAlgebra R ι) where
  homEquiv :=
    { toFun := fun f => ⟨fun i => f.hom (X (some i)), f.hom (X none)⟩
      invFun := fun x => CommAlgCat.ofHom (aeval (valuation x.vec x.scalar))
      left_inv := fun f => by
        apply CommAlgCat.hom_ext
        apply algHom_ext
        intro o
        cases o <;> simp [valuation]
      right_inv := fun x => by
        apply Coordinates.ext <;> simp [valuation] }
  homEquiv_comp _ _ := rfl

theorem corepresentableBy_homEquiv {A : CommAlgCat.{u} R} (f : coordinateAlgebra R ι ⟶ A) :
    (corepresentableBy R c).homEquiv f = ⟨fun i => f.hom (X (some i)), f.hom (X none)⟩ := rfl

theorem corepresentableBy_homEquiv_symm {A : CommAlgCat.{u} R}
    (x : Coordinates (algebraCoefficients R c A)) :
    (corepresentableBy R c).homEquiv.symm x =
      CommAlgCat.ofHom (aeval (valuation x.vec x.scalar)) := rfl

end Functor

/-! ### The group scheme -/

section Scheme

variable (R : CommRingCat.{u}) {ι : Type u} [Fintype ι] (c : ι → ι → R)

/-- The bilinear coordinate group scheme over `Spec R`. -/
abbrev groupScheme : GroupScheme (Spec R) :=
  Corepresented.groupScheme (functor R c) (corepresentableBy R c)

/-- Points over any test scheme `T` are bilinear coordinates in `Γ(T)`. -/
def pointsEquiv (T : Over (Spec R)) :
    (T ⟶ (groupScheme R c).X) ≃* Coordinates (algebraCoefficients R c ((algΓ R).obj T).unop) :=
  Corepresented.pointsEquiv (functor R c) (corepresentableBy R c) T

theorem pointsEquiv_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme R c).X) :
    pointsEquiv R c T' (a ≫ x) = (functor R c).map ((algΓ R).map a).unop (pointsEquiv R c T x) :=
  Corepresented.pointsEquiv_naturality (functor R c) (corepresentableBy R c) a x

theorem groupScheme_hom :
    (groupScheme R c).X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Option ι) R))) := rfl

instance isAffineHom : IsAffineHom (groupScheme R c).X.hom := by
  change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Option ι) R))))
  infer_instance

theorem smooth : Smooth (groupScheme R c).X.hom := by
  rw [Corepresented.smooth_groupScheme_iff]
  change Algebra.Smooth R (MvPolynomial (Option ι) R)
  exact ⟨inferInstance, inferInstance⟩

instance : Smooth (groupScheme R c).X.hom := smooth R c

instance flat : Flat (groupScheme R c).X.hom := by
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Option ι) R))))
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  change (algebraMap R (MvPolynomial (Option ι) R)).Flat
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

instance locallyOfFiniteType : LocallyOfFiniteType (groupScheme R c).X.hom := by
  change LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Option ι) R))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  change (algebraMap R (MvPolynomial (Option ι) R)).FiniteType
  rw [RingHom.finiteType_algebraMap]
  infer_instance

/-- Affine space is geometrically connected, since it is geometrically irreducible. -/
theorem geometricallyConnected_affineSpace (n : Type u) (S : Scheme.{u}) :
    GeometricallyConnected (𝔸(n; S) ↘ S) := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have : IrreducibleSpace Z :=
    GeometricallyIrreducible.geometrically_irreducibleSpace (f := 𝔸(n; S) ↘ S) y fst snd h
  exact IrreducibleSpace.connectedSpace Z

/-- The spectrum of a polynomial ring is geometrically connected over the base. -/
theorem geometricallyConnected_spec_mvPolynomial (n : Type u) :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial n R)))) := by
  have := geometricallyConnected_affineSpace n (Spec R)
  have : MorphismProperty.RespectsIso @GeometricallyConnected.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [MvPolynomial.algebraMap_eq, ← AffineSpace.SpecIso_inv_over (n := n) R,
    MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyConnected.{u})]
  infer_instance

instance geometricallyConnected : GeometricallyConnected (groupScheme R c).X.hom :=
   geometricallyConnected_spec_mvPolynomial R (Option ι)

end Scheme

/-! ### Homomorphisms from compatible coordinate changes -/

section Hom

variable (R : CommRingCat.{u}) {ι κ : Type u} [Fintype ι] [Fintype κ]
  {c : ι → ι → R} {d : κ → κ → R} (M : ι → κ → R) (t : R) (h : IsCompatible c d M t)

/-- The natural transformation `(a, b) ↦ (M a, t b)` of bilinear coordinate functors. -/
def linearNatTrans : functor R c ⟶ functor R d where
  app A := GrpCat.ofHom (Coordinates.linearMap (fun i k => algebraMap R A (M i k))
    (algebraMap R A t) (h.map (algebraMap R A)))
  naturality A A' f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    change Coordinates.linearMap (fun i k => algebraMap R A' (M i k)) (algebraMap R A' t)
        (h.map (algebraMap R A')) (Coordinates.map f.hom.toRingHom
          (fun i j => f.hom.commutes (c i j)) x) =
      Coordinates.map f.hom.toRingHom (fun i j => f.hom.commutes (d i j))
        (Coordinates.linearMap (fun i k => algebraMap R A (M i k)) (algebraMap R A t)
          (h.map (algebraMap R A)) x)
    apply Coordinates.ext
    · funext k
      change ∑ i, f.hom (x.vec i) * algebraMap R A' (M i k) =
        f.hom (∑ i, x.vec i * algebraMap R A (M i k))
      simp [map_sum]
    · change algebraMap R A' t * f.hom x.scalar = f.hom (algebraMap R A t * x.scalar)
      simp

/-- The group-scheme homomorphism induced by a compatible coordinate change. -/
def linearHom : groupScheme R c ⟶ groupScheme R d :=
  Corepresented.groupSchemeMap (corepresentableBy R c) (corepresentableBy R d)
    (linearNatTrans R M t h)

/-- On points over any test scheme, the homomorphism is `(a, b) ↦ (M a, t b)`. -/
theorem pointsEquiv_linearHom {T : Over (Spec R)} (x : T ⟶ (groupScheme R c).X) :
    pointsEquiv R d T (x ≫ (linearHom R M t h).hom.hom) =
      Coordinates.linearMap (fun i k => algebraMap R _ (M i k)) (algebraMap R _ t)
        ((h.map (algebraMap R _))) (pointsEquiv R c T x) :=
  Corepresented.groupSchemeMap_points (corepresentableBy R c) (corepresentableBy R d)
    (linearNatTrans R M t h) x

end Hom

end Langlands.GroupScheme.BilinearCoordinate
