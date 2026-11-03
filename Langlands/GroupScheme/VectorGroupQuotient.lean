import Langlands.GroupScheme.Rational.WeightVectorUniqueness
import Langlands.GroupScheme.CorepresentedPoints
import Langlands.GroupScheme.CentralIsogeny.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Vector groups, weight actions on them, and quotients by primitive coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-! ### Actions from natural actions on points -/

namespace AutomorphicAction

variable {S : Scheme.{u}} {H G : GroupScheme S}
  (φ : ∀ T : Over S, (T ⟶ H.X) → (T ⟶ G.X) → (T ⟶ G.X))
  (hnat : ∀ {T T' : Over S} (a : T' ⟶ T) (h : T ⟶ H.X) (g : T ⟶ G.X),
    a ≫ φ T h g = φ T' (a ≫ h) (a ≫ g))
  (hone : ∀ (T : Over S) (g : T ⟶ G.X), φ T 1 g = g)
  (hmul : ∀ (T : Over S) (h h' : T ⟶ H.X) (g : T ⟶ G.X), φ T (h * h') g = φ T h (φ T h' g))
  (hmulr : ∀ (T : Over S) (h : T ⟶ H.X) (g g' : T ⟶ G.X),
    φ T h (g * g') = φ T h g * φ T h g')

/-- The action by automorphisms induced by a natural family of actions on points; its action
morphism is the action of the universal point. -/
def ofPoints : AutomorphicAction H G where
  hom := φ _ (fst H.X G.X) (snd H.X G.X)
  one_left g := by rw [hnat, lift_fst, lift_snd, hone]
  mul_left h h' g := by
    simp only [hnat, lift_fst, lift_snd]
    exact hmul _ h h' g
  mul_right h g g' := by
    simp only [hnat, lift_fst, lift_snd]
    exact hmulr _ h g g'

theorem ofPoints_act {T : Over S} (h : T ⟶ H.X) (g : T ⟶ G.X) :
    (ofPoints φ hnat hone hmul hmulr).act h g = φ T h g := by
  rw [act_eq]
  change lift h g ≫ φ _ (fst H.X G.X) (snd H.X G.X) = _
  rw [hnat, lift_fst, lift_snd]

end AutomorphicAction

/-! ### The vector group -/

namespace VectorGroup

section Functor

variable (R : CommRingCat.{u}) (n : ℕ)

/-- The functor `A ↦ Aⁿ` of additive groups, written multiplicatively. -/
def functor : CommAlgCat.{u} R ⥤ GrpCat.{u} where
  obj A := GrpCat.of (Multiplicative (Fin n → A))
  map f := GrpCat.ofHom
    (AddMonoidHom.toMultiplicative (f.hom.toRingHom.toAddMonoidHom.compLeft (Fin n)))
  map_id _ := rfl
  map_comp _ _ := rfl

variable {R n} in
theorem functor_map_apply {A A' : CommAlgCat.{u} R} (f : A ⟶ A')
    (x : Multiplicative (Fin n → A)) :
    ((functor R n).map f x).toAdd = fun i => f.hom (x.toAdd i) := rfl

/-- The polynomial ring in `n` variables as a commutative `R`-algebra. -/
abbrev coordinateAlgebra : CommAlgCat.{u} R := CommAlgCat.of R (MvPolynomial (Fin n) R)

/-- The polynomial ring corepresents `A ↦ Aⁿ`: an algebra map corresponds to the images of
the variables. -/
def corepresentableBy :
    (functor R n ⋙ forget GrpCat).CorepresentableBy (coordinateAlgebra R n) where
  homEquiv :=
    { toFun := fun f => Multiplicative.ofAdd fun i => f.hom (X i)
      invFun := fun x => CommAlgCat.ofHom (aeval (Multiplicative.toAdd x))
      left_inv := fun f => CommAlgCat.hom_ext (algHom_ext fun i => aeval_X _ _)
      right_inv := fun x => by
        apply Multiplicative.toAdd.injective
        funext i
        exact aeval_X _ i }
  homEquiv_comp _ _ := rfl

theorem corepresentableBy_homEquiv {A : CommAlgCat.{u} R} (f : coordinateAlgebra R n ⟶ A) :
    ((corepresentableBy R n).homEquiv f).toAdd = fun i => f.hom (X i) := rfl

theorem corepresentableBy_homEquiv_symm {A : CommAlgCat.{u} R}
    (x : Multiplicative (Fin n → A)) :
    (corepresentableBy R n).homEquiv.symm x = CommAlgCat.ofHom (aeval x.toAdd) := rfl

end Functor

section Scheme

variable (R : CommRingCat.{u}) (n : ℕ)

/-- The vector group `𝔾ₐⁿ` over `Spec R`, the spectrum of the polynomial ring in `n`
variables. -/
abbrev groupScheme : GroupScheme (Spec R) :=
  Corepresented.groupScheme (functor R n) (corepresentableBy R n)

/-- The global coordinate function `xᵢ` on the vector group. -/
def coordinateSection (i : Fin n) : Γ((groupScheme R n).X.left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) R))).inv (X i)

/-- The linear coordinates of points of the vector group. -/
def coordinates (T : Over (Spec R)) :
    (T ⟶ (groupScheme R n).X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤)) :=
  Corepresented.pointsEquiv (functor R n) (corepresentableBy R n) T

end Scheme

end VectorGroup

namespace Corepresented

variable {R : CommRingCat.{u}} {B : CommAlgCat.{u} R}

/-- The algebra map adjoint to a point of `Spec B` is pullback of global functions. -/
theorem adjunction_homEquiv_symm_apply {T : Over (Spec R)} (x : T ⟶ (algSpec R).obj (op B))
    (b : B) :
    (((algΓAlgSpecAdjunction R).homEquiv T (op B)).symm x).unop.hom b =
      x.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) := by
  rw [Adjunction.homEquiv_counit]
  rfl

end Corepresented

namespace VectorGroup

variable {R : CommRingCat.{u}} {n : ℕ}

/-- The `i`-th coordinate of a point is the pullback of the coordinate function `xᵢ`. -/
theorem coordinates_apply (T : Over (Spec R)) (x : T ⟶ (groupScheme R n).X) (i : Fin n) :
    (coordinates R n T x).toAdd i = x.left.appTop (coordinateSection R n i) :=
  Corepresented.adjunction_homEquiv_symm_apply x (X i)

/-- The coordinates are natural in the test scheme. -/
theorem coordinates_comp {T W : Over (Spec R)} (f : W ⟶ T) (x : T ⟶ (groupScheme R n).X) :
    (coordinates R n W (f ≫ x)).toAdd = fun j => f.left.appTop ((coordinates R n T x).toAdd j) :=
  congrArg Multiplicative.toAdd
    (Corepresented.pointsEquiv_naturality (functor R n) (corepresentableBy R n) f x)

/-- Points of the vector group are determined by their coordinates. -/
theorem points_ext {T : Over (Spec R)} {x x' : T ⟶ (groupScheme R n).X}
    (h : ∀ i, (coordinates R n T x).toAdd i = (coordinates R n T x').toAdd i) : x = x' :=
  (coordinates R n T).injective (Multiplicative.toAdd.injective (funext h))

theorem coordinates_mul {T : Over (Spec R)} (x x' : T ⟶ (groupScheme R n).X) :
    (coordinates R n T (x * x')).toAdd =
      (coordinates R n T x).toAdd + (coordinates R n T x').toAdd := by
  rw [map_mul, toAdd_mul]

/-! ### Torus actions through a character -/

section Weight

variable {S : CommGroupScheme (Spec R)} (χ : characterLattice S)

/-- The value of a character at a point of the torus, as a global function. -/
def charValue (T : Over (Spec R)) (s : T ⟶ S.X) : Γ(T.left, ⊤) :=
  (Gm.pointsEquiv _ T (s ≫ (CommGroupScheme.groupHom χ).hom.hom) : Γ(T.left, ⊤))

theorem charValue_one (T : Over (Spec R)) : charValue χ T 1 = 1 := by
  rw [charValue, MonObj.one_comp, map_one, Units.val_one]

theorem charValue_mul (T : Over (Spec R)) (s s' : T ⟶ S.X) :
    charValue χ T (s * s') = charValue χ T s * charValue χ T s' := by
  rw [charValue, MonObj.mul_comp, map_mul, Units.val_mul]
  rfl

theorem charValue_comp {T T' : Over (Spec R)} (a : T' ⟶ T) (s : T ⟶ S.X) :
    charValue χ T' (a ≫ s) = a.left.appTop (charValue χ T s) := by
  rw [charValue, Category.assoc, Gm.pointsEquiv_naturality]
  rfl

/-- Scaling the coordinates of a point by the value of `χ` at a torus point. -/
def weightPointAction (T : Over (Spec R)) (s : T ⟶ S.X) (v : T ⟶ (groupScheme R n).X) :
    T ⟶ (groupScheme R n).X :=
  (coordinates R n T).symm (Multiplicative.ofAdd (charValue χ T s • (coordinates R n T v).toAdd))

theorem coordinates_weightPointAction (T : Over (Spec R)) (s : T ⟶ S.X)
    (v : T ⟶ (groupScheme R n).X) :
    (coordinates R n T (weightPointAction χ T s v)).toAdd =
      charValue χ T s • (coordinates R n T v).toAdd := by
  rw [weightPointAction, MulEquiv.apply_symm_apply, toAdd_ofAdd]

theorem weightPointAction_comp {T T' : Over (Spec R)} (a : T' ⟶ T) (s : T ⟶ S.X)
    (v : T ⟶ (groupScheme R n).X) :
    a ≫ weightPointAction χ T s v = weightPointAction χ T' (a ≫ s) (a ≫ v) :=
  points_ext fun i => by
    rw [coordinates_comp, coordinates_weightPointAction, coordinates_weightPointAction,
      coordinates_comp, charValue_comp]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]

theorem weightPointAction_one (T : Over (Spec R)) (v : T ⟶ (groupScheme R n).X) :
    weightPointAction χ T 1 v = v :=
  points_ext fun i => by rw [coordinates_weightPointAction, charValue_one, one_smul]

theorem weightPointAction_mul (T : Over (Spec R)) (s s' : T ⟶ S.X)
    (v : T ⟶ (groupScheme R n).X) :
    weightPointAction χ T (s * s') v = weightPointAction χ T s (weightPointAction χ T s' v) :=
  points_ext fun i => by
    rw [coordinates_weightPointAction, coordinates_weightPointAction,
      coordinates_weightPointAction, charValue_mul, mul_smul]

theorem weightPointAction_mul_right (T : Over (Spec R)) (s : T ⟶ S.X)
    (v v' : T ⟶ (groupScheme R n).X) :
    weightPointAction χ T s (v * v') = weightPointAction χ T s v * weightPointAction χ T s v' :=
  points_ext fun i => by
    rw [coordinates_weightPointAction, coordinates_mul, coordinates_mul,
      coordinates_weightPointAction, coordinates_weightPointAction, smul_add]

/-- The torus acts on the vector group through the character `χ`, scaling all coordinates
by its value. -/
def weightAction : AutomorphicAction S.toGrp (groupScheme R n) :=
  AutomorphicAction.ofPoints (weightPointAction χ) (weightPointAction_comp χ)
    (weightPointAction_one χ) (weightPointAction_mul χ) (weightPointAction_mul_right χ)

theorem weightAction_act {T : Over (Spec R)} (s : T ⟶ S.X) (v : T ⟶ (groupScheme R n).X) :
    (weightAction (n := n) χ).act s v = weightPointAction χ T s v :=
  AutomorphicAction.ofPoints_act _ (weightPointAction_comp χ) (weightPointAction_one χ)
    (weightPointAction_mul χ) (weightPointAction_mul_right χ) s v

theorem coordinates_weightAction_act {T : Over (Spec R)} (s : T ⟶ S.X)
    (v : T ⟶ (groupScheme R n).X) :
    (coordinates R n T ((weightAction χ).act s v)).toAdd =
      charValue χ T s • (coordinates R n T v).toAdd := by
  rw [weightAction_act, coordinates_weightPointAction]

end Weight

end VectorGroup

/-! ### Weight vector structures over a field -/

namespace VectorGroup

variable {k : Type u} [Field k] {n : ℕ}

theorem isNaturalVectorCoordinates :
    RelativeRoot.IsNaturalVectorCoordinates (coordinates (CommRingCat.of k) n) :=
  fun _ _ f v => coordinates_comp f v

variable {S : CommGroupScheme (Spec (CommRingCat.of k))} (χ : characterLattice S)

/-- The linear coordinates are weight vector coordinates of weight `χ` for the action
through `χ`. -/
theorem isWeightVectorCoordinates_weightAction :
    RelativeRoot.IsWeightVectorCoordinates (weightAction (n := n) χ) χ
      (coordinates (CommRingCat.of k) n) :=
  ⟨isNaturalVectorCoordinates, fun _ s v => coordinates_weightAction_act χ s v⟩

/-- For a nonzero character of a split torus, the action through `χ` has a unique weight
vector structure of weight `χ`. -/
theorem hasUniqueWeightVectorStructure_weightAction (hS : IsSplitTorus S.toGrp) (hχ : χ ≠ 0) :
    RelativeRoot.HasUniqueWeightVectorStructure (weightAction (n := n) χ) χ :=
  RelativeRoot.hasUniqueWeightVectorStructure_of_coordinates hS hχ
    (isWeightVectorCoordinates_weightAction χ)

end VectorGroup

/-! ### Polynomial algebras over a subring of variables -/

namespace VectorGroup

section Algebra

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {n : ℕ} {κ : Type u}
  {y : Fin n → B} {z : κ → B}

/-- Polynomials in the remaining variables over the polynomial ring in the first ones,
mapped to `B` through `Sum.elim y z`. -/
def extensionMap (y : Fin n → B) (z : κ → B) : MvPolynomial κ (MvPolynomial (Fin n) R) →+* B :=
  (aeval (Sum.elim y z) : MvPolynomial (Fin n ⊕ κ) R →ₐ[R] B).toRingHom.comp
    ((renameEquiv R (Equiv.sumComm κ (Fin n))).toRingEquiv.toRingHom.comp
      (sumAlgEquiv R κ (Fin n)).symm.toRingEquiv.toRingHom)

theorem extensionMap_bijective
    (hyz : Function.Bijective (aeval (Sum.elim y z) : MvPolynomial (Fin n ⊕ κ) R →ₐ[R] B)) :
    Function.Bijective (extensionMap (R := R) y z) :=
  hyz.comp ((renameEquiv R (Equiv.sumComm κ (Fin n))).bijective.comp
    (sumAlgEquiv R κ (Fin n)).symm.bijective)

/-- `aeval y` is the inclusion of coefficients followed by `extensionMap y z`. -/
theorem aeval_eq_extensionMap_comp :
    (aeval y : MvPolynomial (Fin n) R →ₐ[R] B).toRingHom =
      (extensionMap y z).comp
        (algebraMap (MvPolynomial (Fin n) R) (MvPolynomial κ (MvPolynomial (Fin n) R))) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [extensionMap, MvPolynomial.algebraMap_eq, sumAlgEquiv_symm_C_C]
  · intro i
    simp [extensionMap, MvPolynomial.algebraMap_eq, sumAlgEquiv_symm_C_X]

theorem flat_aeval
    (hyz : Function.Bijective (aeval (Sum.elim y z) : MvPolynomial (Fin n ⊕ κ) R →ₐ[R] B)) :
    (aeval y : MvPolynomial (Fin n) R →ₐ[R] B).toRingHom.Flat := by
  rw [aeval_eq_extensionMap_comp (z := z)]
  exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr inferInstance)
    (RingHom.Flat.of_bijective (extensionMap_bijective hyz))

theorem finitePresentation_aeval [Finite κ]
    (hyz : Function.Bijective (aeval (Sum.elim y z) : MvPolynomial (Fin n ⊕ κ) R →ₐ[R] B)) :
    (aeval y : MvPolynomial (Fin n) R →ₐ[R] B).toRingHom.FinitePresentation := by
  rw [aeval_eq_extensionMap_comp (z := z)]
  exact RingHom.FinitePresentation.comp
    (RingHom.FinitePresentation.of_bijective (extensionMap_bijective hyz))
    (RingHom.finitePresentation_algebraMap.mpr inferInstance)

/-- Setting the remaining variables to zero retracts `aeval y`. -/
theorem exists_retraction_aeval
    (hyz : Function.Bijective (aeval (Sum.elim y z) : MvPolynomial (Fin n ⊕ κ) R →ₐ[R] B)) :
    ∃ r : B →+* MvPolynomial (Fin n) R,
      r.comp (aeval y : MvPolynomial (Fin n) R →ₐ[R] B).toRingHom = RingHom.id _ := by
  let E := RingEquiv.ofBijective (aeval (Sum.elim y z) : MvPolynomial (Fin n ⊕ κ) R →ₐ[R] B) hyz
  refine ⟨(aeval (Sum.elim X 0) : MvPolynomial (Fin n ⊕ κ) R →ₐ[R] MvPolynomial (Fin n) R).toRingHom.comp
    E.symm.toRingHom, ?_⟩
  have hE : ∀ p : MvPolynomial (Fin n) R, E.symm (aeval y p) = rename Sum.inl p := by
    intro p
    rw [RingEquiv.symm_apply_eq]
    change aeval y p = aeval (Sum.elim y z) (rename Sum.inl p)
    rw [aeval_rename]
    rfl
  apply RingHom.ext
  intro p
  change aeval (Sum.elim X 0) (E.symm (aeval y p)) = p
  rw [hE, aeval_rename]
  exact aeval_X_left_apply p

end Algebra

/-! ### Quotients by primitive coordinates -/

section Primitive

variable {R : CommRingCat.{u}} {n : ℕ} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B) (y : Fin n → B)

/-- A family of functions on a corepresented group that are primitive: on points, the value of
the classifying map of a product is the sum of the values. -/
def IsPrimitiveFamily : Prop :=
  ∀ (A : CommAlgCat.{u} R) (x x' : F.obj A) (i : Fin n),
    (e.homEquiv.symm (x * x')).hom (y i) =
      (e.homEquiv.symm x).hom (y i) + (e.homEquiv.symm x').hom (y i)

variable {e y}

/-- The values of a primitive family, as a natural homomorphism to `A ↦ Aⁿ`. -/
def coordinateMap (hy : IsPrimitiveFamily e y) : F ⟶ functor R n where
  app A := GrpCat.ofHom (MonoidHom.mk'
    (fun x => Multiplicative.ofAdd fun i => (e.homEquiv.symm x).hom (y i))
    (fun x x' => Multiplicative.toAdd.injective (funext fun i => hy A x x' i)))
  naturality A A' f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Multiplicative.toAdd.injective
    funext i
    change (e.homEquiv.symm ((F ⋙ forget GrpCat).map f x)).hom (y i) =
      f.hom ((e.homEquiv.symm x).hom (y i))
    rw [← e.homEquiv_symm_comp]
    rfl

/-- The homomorphism to the vector group given by a primitive family. -/
def quotientMap (hy : IsPrimitiveFamily e y) :
    Corepresented.groupScheme F e ⟶ groupScheme R n :=
  Corepresented.groupSchemeMap e (corepresentableBy R n) (coordinateMap hy)

/-- The value of the classifying map of a point at a function is its pullback. -/
theorem homEquiv_symm_pointsEquiv_apply {T : Over (Spec R)}
    (h : T ⟶ (Corepresented.groupScheme F e).X) (b : B) :
    (e.homEquiv.symm (Corepresented.pointsEquiv F e T h)).hom b =
      h.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) := by
  rw [Corepresented.pointsEquiv_apply, Equiv.symm_apply_apply]
  exact Corepresented.adjunction_homEquiv_symm_apply h b

/-- The coordinates of the image of a point are the values of the primitive family. -/
theorem coordinates_quotientMap (hy : IsPrimitiveFamily e y) {T : Over (Spec R)}
    (h : T ⟶ (Corepresented.groupScheme F e).X) (i : Fin n) :
    (coordinates R n T (h ≫ (quotientMap hy).hom.hom)).toAdd i =
      (e.homEquiv.symm (Corepresented.pointsEquiv F e T h)).hom (y i) := by
  exact congrFun (congrArg Multiplicative.toAdd
    (Corepresented.groupSchemeMap_points e (corepresentableBy R n) (coordinateMap hy) h)) i

theorem coordinates_quotientMap_eq_appTop (hy : IsPrimitiveFamily e y) {T : Over (Spec R)}
    (h : T ⟶ (Corepresented.groupScheme F e).X) (i : Fin n) :
    (coordinates R n T (h ≫ (quotientMap hy).hom.hom)).toAdd i =
      h.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (y i)) := by
  rw [coordinates_quotientMap, homEquiv_symm_pointsEquiv_apply]

/-- The underlying scheme map is the spectrum of `aeval y`. -/
theorem quotientMap_left (hy : IsPrimitiveFamily e y) :
    (quotientMap hy).hom.hom.left =
      Spec.map (CommRingCat.ofHom (aeval y : MvPolynomial (Fin n) R →ₐ[R] B).toRingHom) := by
  rw [quotientMap, Corepresented.groupSchemeMap_hom]
  have h : (corepresentableBy R n).homEquiv.symm
      ((coordinateMap hy).app B (e.homEquiv (𝟙 B))) = CommAlgCat.ofHom (aeval y) := by
    change CommAlgCat.ofHom (aeval fun i => (e.homEquiv.symm (e.homEquiv (𝟙 B))).hom (y i)) = _
    rw [Equiv.symm_apply_apply]
    rfl
  rw [h]

/-- A point lies in the kernel exactly when all members of the primitive family vanish on it. -/
theorem mem_range_kernelι_quotientMap_iff (hy : IsPrimitiveFamily e y) {T : Over (Spec R)}
    (x : T ⟶ (Corepresented.groupScheme F e).X) :
    x ∈ (SubgroupFunctor.range (kernelι (quotientMap hy))).carrier T ↔
      ∀ i, (e.homEquiv.symm (Corepresented.pointsEquiv F e T x)).hom (y i) = 0 := by
  rw [mem_range_kernelι_iff]
  constructor
  · intro h i
    rw [← coordinates_quotientMap hy x i, h, map_one]
    rfl
  · intro h
    apply points_ext
    intro i
    rw [coordinates_quotientMap, h, map_one]
    rfl

variable (hy : IsPrimitiveFamily e y) {κ : Type u} {z : κ → B}
  (hyz : Function.Bijective (aeval (Sum.elim y z) : MvPolynomial (Fin n ⊕ κ) R →ₐ[R] B))
include hyz

theorem flat_quotientMap : Flat (quotientMap hy).hom.hom.left := by
  rw [quotientMap_left]
  exact (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (flat_aeval hyz)

theorem locallyOfFinitePresentation_quotientMap [Finite κ] :
    LocallyOfFinitePresentation (quotientMap hy).hom.hom.left := by
  rw [quotientMap_left]
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
    (finitePresentation_aeval hyz)

theorem surjective_quotientMap : Surjective (quotientMap hy).hom.hom.left := by
  obtain ⟨r, hr⟩ := exists_retraction_aeval hyz
  rw [quotientMap_left]
  have hid : Spec.map (CommRingCat.ofHom r) ≫
      Spec.map (CommRingCat.ofHom (aeval y : MvPolynomial (Fin n) R →ₐ[R] B).toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hr]
    exact Spec.map_id _
  have : Surjective (Spec.map (CommRingCat.ofHom r) ≫
      Spec.map (CommRingCat.ofHom (aeval y : MvPolynomial (Fin n) R →ₐ[R] B).toRingHom)) := by
    rw [hid]
    infer_instance
  exact @Surjective.of_comp _ _ _ (Spec.map (CommRingCat.ofHom r)) _ this

/-- If the primitive family is part of a set of polynomial generators, the map to the vector
group is an fppf quotient by the subgroup functor where the family vanishes. -/
theorem isFppfQuotient_quotientMap [Finite κ] (N : SubgroupFunctor (Corepresented.groupScheme F e))
    (hN : ∀ (T : Over (Spec R)) (x : T ⟶ (Corepresented.groupScheme F e).X),
      x ∈ N.carrier T ↔ ∀ i, (e.homEquiv.symm (Corepresented.pointsEquiv F e T x)).hom (y i) = 0) :
    RelativeRoot.IsFppfQuotient N (quotientMap hy) :=
  ⟨flat_quotientMap hy hyz, surjective_quotientMap hy hyz,
    locallyOfFinitePresentation_quotientMap hy hyz,
    SubgroupFunctor.ext fun T => Subgroup.ext fun x =>
      (mem_range_kernelι_quotientMap_iff hy x).trans (hN T x).symm⟩

end Primitive

end VectorGroup

end Langlands.GroupScheme
