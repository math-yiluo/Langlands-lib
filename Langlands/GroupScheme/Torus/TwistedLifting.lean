import Langlands.GroupScheme.Torus.CharacterTwist
import Langlands.GroupScheme.Torus.FixedPointLifting

/-! # Lifting twisted transporters along square-zero extensions

Let `F` be a group functor on commutative `R`-algebras, corepresented by a formally smooth
algebra `B`, with an embedded diagonalizable group `ι`. For an `R`-algebra `C`, a grouplike
family `s` over `C` defines a twisted action `t · g = ι(twist s t) * g * ι(t)⁻¹` of the
characters on the points of `F` over `C`-algebras. Its fixed points are the twisted
transporters. Fixed points over `C ⧸ N` lift to `C` when `N` is nilpotent, by the published
fixed-point smoothness of character actions, applied after base change of `B` to `C`.
-/

noncomputable section

universe u

open CategoryTheory
open scoped TensorProduct

namespace Langlands.GroupScheme.CharacterAction

variable {R : CommRingCat.{u}}

section RestrictScalars

variable (C : CommAlgCat.{u} R)

/-- The `R`-algebra `C` as a base ring. -/
abbrev baseRing : CommRingCat.{u} := CommRingCat.of C

/-- The `R`-algebra structure of a `C`-algebra. -/
abbrev restrictAlgebra (D : CommAlgCat.{u} (baseRing C)) : Algebra R D :=
  ((algebraMap C D).comp (algebraMap R C)).toAlgebra

/-- Restriction of scalars from `C`-algebras to `R`-algebras. -/
def restrictScalars (D : CommAlgCat.{u} (baseRing C)) : CommAlgCat.{u} R :=
  letI := restrictAlgebra C D
  CommAlgCat.of R D

variable {C}

/-- Restriction of scalars on morphisms. -/
def restrictScalarsMap {D D' : CommAlgCat.{u} (baseRing C)} (f : D ⟶ D') :
    restrictScalars C D ⟶ restrictScalars C D' :=
  letI := restrictAlgebra C D
  letI := restrictAlgebra C D'
  CommAlgCat.ofHom
    { f.hom.toRingHom with
      commutes' := fun r => f.hom.commutes (algebraMap R C r) }

@[simp] theorem restrictScalarsMap_apply {D D' : CommAlgCat.{u} (baseRing C)} (f : D ⟶ D')
    (d : D) : (restrictScalarsMap f).hom d = f.hom d :=
  rfl

theorem restrictScalarsMap_comp {D D' D'' : CommAlgCat.{u} (baseRing C)} (f : D ⟶ D')
    (f' : D' ⟶ D'') :
    restrictScalarsMap (f ≫ f') = restrictScalarsMap f ≫ restrictScalarsMap f' :=
  rfl

/-- The structure map `C ⟶ D` of a `C`-algebra, as a map of `R`-algebras. -/
def toRestrict (D : CommAlgCat.{u} (baseRing C)) : C ⟶ restrictScalars C D :=
  letI := restrictAlgebra C D
  CommAlgCat.ofHom
    { (algebraMap C D) with
      commutes' := fun _ => rfl }

@[simp] theorem toRestrict_apply (D : CommAlgCat.{u} (baseRing C)) (c : C) :
    (toRestrict D).hom c = algebraMap C D c :=
  rfl

theorem toRestrict_comp {D D' : CommAlgCat.{u} (baseRing C)} (f : D ⟶ D') :
    toRestrict D ≫ restrictScalarsMap f = toRestrict D' := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro c
  exact f.hom.commutes c

/-- An `R`-algebra that is also a `C`-algebra compatibly is the restriction of itself. -/
def restrictIso (D₀ : CommAlgCat.{u} R) [Algebra C D₀] [IsScalarTower R C D₀] :
    restrictScalars C (CommAlgCat.of (baseRing C) D₀) ≅ D₀ :=
  CommAlgCat.isoMk (AlgEquiv.ofRingEquiv (A₁ := restrictScalars C (CommAlgCat.of (baseRing C) D₀))
    (A₂ := D₀) (f := RingEquiv.refl D₀)
    fun r => (IsScalarTower.algebraMap_apply R C D₀ r).symm)

@[simp] theorem restrictIso_hom_apply (D₀ : CommAlgCat.{u} R) [Algebra C D₀]
    [IsScalarTower R C D₀] (d : D₀) : (restrictIso (C := C) D₀).hom.hom d = d :=
  rfl

@[simp] theorem restrictIso_inv_apply (D₀ : CommAlgCat.{u} R) [Algebra C D₀]
    [IsScalarTower R C D₀] (d : D₀) : (restrictIso (C := C) D₀).inv.hom d = d :=
  rfl

end RestrictScalars

section BaseChange

variable (C B : CommAlgCat.{u} R)

/-- The base change `C ⊗[R] B` as a `C`-algebra. -/
abbrev baseChange : CommAlgCat.{u} (baseRing C) :=
  CommAlgCat.of (baseRing C) (C ⊗[R] B)

variable {C B}

/-- Points of the base change over a `C`-algebra are points of `B` over its restriction. -/
def baseChangeEquiv (D : CommAlgCat.{u} (baseRing C)) :
    (baseChange C B ⟶ D) ≃ (B ⟶ restrictScalars C D) :=
  letI := restrictAlgebra C D
  haveI : IsScalarTower R C D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  { toFun := fun x => CommAlgCat.ofHom ((AlgHom.liftEquiv R C B D).symm x.hom)
    invFun := fun φ => CommAlgCat.ofHom (AlgHom.liftEquiv R C B D φ.hom)
    left_inv := fun x => by
      apply CommAlgCat.hom_ext
      exact (AlgHom.liftEquiv R C B D).apply_symm_apply x.hom
    right_inv := fun φ => by
      apply CommAlgCat.hom_ext
      exact (AlgHom.liftEquiv R C B D).symm_apply_apply φ.hom }

@[simp] theorem baseChangeEquiv_apply {D : CommAlgCat.{u} (baseRing C)}
    (x : baseChange C B ⟶ D) (b : B) :
    (baseChangeEquiv D x).hom b = x.hom (1 ⊗ₜ b) :=
  rfl

theorem baseChangeEquiv_comp {D D' : CommAlgCat.{u} (baseRing C)} (x : baseChange C B ⟶ D)
    (f : D ⟶ D') :
    baseChangeEquiv D' (x ≫ f) = baseChangeEquiv D x ≫ restrictScalarsMap f :=
  rfl

end BaseChange

section TwistedAction

variable {M : Type u} [AddCommGroup M] {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B) (ι : CharacterEmbedding F M)
  {C : CommAlgCat.{u} R} (s : Multiplicative M →* (algebra (M := M) C)ˣ)

/-- A character over a `C`-algebra, viewed over its restriction of scalars. -/
def restrictChar {D : CommAlgCat.{u} (baseRing C)} (t : Multiplicative M →* Dˣ) :
    Multiplicative M →* (restrictScalars C D)ˣ :=
  t

omit s in
@[simp] theorem restrictChar_one {D : CommAlgCat.{u} (baseRing C)} :
    restrictChar (C := C) (1 : Multiplicative M →* Dˣ) = 1 :=
  rfl

omit s in
@[simp] theorem restrictChar_mul {D : CommAlgCat.{u} (baseRing C)}
    (t t' : Multiplicative M →* Dˣ) :
    restrictChar (C := C) (t * t') = restrictChar t * restrictChar t' :=
  rfl

omit s in
theorem mapCharacter_restrictChar {D D' : CommAlgCat.{u} (baseRing C)} (f : D ⟶ D')
    (t : Multiplicative M →* Dˣ) :
    mapCharacter (restrictScalarsMap f) (restrictChar (C := C) t) =
      restrictChar (mapCharacter f t) :=
  rfl

omit s in
/-- The point of `F` over the restriction of a `C`-algebra given by a point of the base
change. -/
abbrev basePoint {D : CommAlgCat.{u} (baseRing C)} (x : baseChange C B ⟶ D) :
    F.obj (restrictScalars C D) :=
  e.homEquiv (baseChangeEquiv D x)

omit s in
theorem basePoint_comp {D D' : CommAlgCat.{u} (baseRing C)} (x : baseChange C B ⟶ D)
    (f : D ⟶ D') : basePoint e (x ≫ f) = F.map (restrictScalarsMap f) (basePoint e x) := by
  rw [basePoint, baseChangeEquiv_comp, e.homEquiv_comp]
  rfl

omit s in
theorem basePoint_symm {D : CommAlgCat.{u} (baseRing C)} (g : F.obj (restrictScalars C D)) :
    basePoint e ((baseChangeEquiv D).symm (e.homEquiv.symm g)) = g := by
  rw [basePoint, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The twisted action `t · g = ι(twist s t) * g * ι(t)⁻¹` on the points of `F` over
`C`-algebras, written on the base change `C ⊗[R] B`. -/
def twistedAction (hs : IsGrouplikeHom s) : Action (R := baseRing C) (M := M) (baseChange C B) where
  act {D} t x := (baseChangeEquiv D).symm (e.homEquiv.symm
    (ι.hom (restrictScalars C D) (twist s (toRestrict D) (restrictChar t)) *
      basePoint e x * (ι.hom (restrictScalars C D) (restrictChar t))⁻¹))
  one {D} x := by
    rw [restrictChar_one, twist_one hs, map_one, inv_one, one_mul, mul_one,
      basePoint, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  mul {D} t t' x := by
    rw [basePoint_symm, restrictChar_mul, twist_mul hs, (ι.hom _).map_mul,
      (ι.hom _).map_mul, mul_inv_rev]
    congr 2
    group
  naturality {D D'} f t x := by
    apply (baseChangeEquiv D').injective
    rw [Equiv.apply_symm_apply, baseChangeEquiv_comp, Equiv.apply_symm_apply,
      e.homEquiv_symm_comp]
    congr 1
    rw [basePoint_comp, ← mapCharacter_restrictChar, ← toRestrict_comp f, ← mapCharacter_twist]
    change _ = F.map (restrictScalarsMap f) _
    rw [map_mul, map_mul, map_inv, ι.naturality, ι.naturality]

theorem twistedAction_act (hs : IsGrouplikeHom s) {D : CommAlgCat.{u} (baseRing C)}
    (t : Multiplicative M →* Dˣ) (x : baseChange C B ⟶ D) :
    basePoint e ((twistedAction e ι s hs).act t x) =
      ι.hom (restrictScalars C D) (twist s (toRestrict D) (restrictChar t)) * basePoint e x *
        (ι.hom (restrictScalars C D) (restrictChar t))⁻¹ :=
  basePoint_symm e _

end TwistedAction

section TwistedLift

variable {M : Type u} [AddCommGroup M] {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  (ι : CharacterEmbedding F M)
  {C : CommAlgCat.{u} R} {s : Multiplicative M →* (algebra (M := M) C)ˣ}

theorem basePoint_injective (e : (F ⋙ forget GrpCat).CorepresentableBy B) {D : CommAlgCat.{u} (baseRing C)} :
    Function.Injective (basePoint e (D := D)) :=
  e.homEquiv.injective.comp (baseChangeEquiv D).injective

/-- The universal twisted transporter equation implies all its specializations. -/
theorem twisted_of_universal {g : F.obj C}
    (h : ι.hom (algebra (M := M) C) s * F.map (constant C) g =
      F.map (constant C) g * ι.hom (algebra (M := M) C) (universal C))
    {D : CommAlgCat.{u} R} (f : C ⟶ D) (t : Multiplicative M →* Dˣ) :
    ι.hom D (twist s f t) * F.map f g = F.map f g * ι.hom D t := by
  have h' := congrArg (F.map (evaluate f t)) h
  rw [map_mul, map_mul, ι.naturality, ι.naturality, ← ConcreteCategory.comp_apply,
    ← F.map_comp, constant_evaluate, mapCharacter_evaluate_universal] at h'
  exact h'

/-- **Lifting twisted transporters.** Let `B` be formally smooth over `R`, `N` a nilpotent
ideal of `C`, and `s` a grouplike family over `C`. A point over `C ⧸ N` satisfying the twisted
transporter equation `ι(twist s t) * g = g * ι(t)` after every refinement lifts to a point over
`C` with the same property. -/
theorem exists_twisted_lift (e : (F ⋙ forget GrpCat).CorepresentableBy B) [Algebra.FormallySmooth R B] (hs : IsGrouplikeHom s) (N : Ideal C)
    (hN : IsNilpotent N) (g₀ : F.obj (CommAlgCat.of R (C ⧸ N)))
    (hg₀ : ∀ (D : CommAlgCat.{u} R) (f : CommAlgCat.of R (C ⧸ N) ⟶ D)
      (t : Multiplicative M →* Dˣ),
      ι.hom D (twist s (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R N) ≫ f) t) * F.map f g₀ =
        F.map f g₀ * ι.hom D t) :
    ∃ g : F.obj C, F.map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R N)) g = g₀ ∧
      ∀ (D : CommAlgCat.{u} R) (f : C ⟶ D) (t : Multiplicative M →* Dˣ),
        ι.hom D (twist s f t) * F.map f g = F.map f g * ι.hom D t := by
  let A' : CommAlgCat.{u} (baseRing C) := CommAlgCat.of (baseRing C) (C ⧸ N)
  let C' : CommAlgCat.{u} (baseRing C) := CommAlgCat.of (baseRing C) C
  let isoA : restrictScalars C A' ≅ CommAlgCat.of R (C ⧸ N) :=
    restrictIso (C := C) (CommAlgCat.of R (C ⧸ N))
  let isoC : restrictScalars C C' ≅ C := restrictIso (C := C) C
  let a := twistedAction e ι s hs
  let x₀ : baseChange C B ⟶ A' := (baseChangeEquiv A').symm (e.homEquiv.symm (F.map isoA.inv g₀))
  have hx₀ : IsFixed a x₀ := by
    intro D f t
    apply basePoint_injective e
    rw [twistedAction_act, basePoint_comp, basePoint_symm, ← ConcreteCategory.comp_apply,
      ← F.map_comp]
    have hred : CommAlgCat.ofHom (Ideal.Quotient.mkₐ R N) ≫ isoA.inv ≫ restrictScalarsMap f =
        toRestrict D := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro c
      exact f.hom.commutes c
    have key := hg₀ (restrictScalars C D) (isoA.inv ≫ restrictScalarsMap f) (restrictChar t)
    rw [hred] at key
    rw [key, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨y, hyfix, hyred⟩ := exists_fixed_lift a (C := C') N hN x₀ hx₀
  refine ⟨F.map isoC.hom (basePoint e y), ?_, ?_⟩
  · have h₁ : isoC.hom ≫ CommAlgCat.ofHom (Ideal.Quotient.mkₐ R N) =
        restrictScalarsMap (CommAlgCat.ofHom (Ideal.Quotient.mkₐ (baseRing C) N)) ≫ isoA.hom := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro c
      rfl
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, h₁, F.map_comp, ConcreteCategory.comp_apply,
      ← basePoint_comp, hyred, basePoint_symm, ← ConcreteCategory.comp_apply, ← F.map_comp,
      Iso.inv_hom_id, F.map_id]
    rfl
  · apply twisted_of_universal ι
    let U' : CommAlgCat.{u} (baseRing C) := CommAlgCat.of (baseRing C) (algebra (M := M) C)
    let isoU : restrictScalars C U' ≅ algebra (M := M) C := restrictIso (C := C) (algebra C)
    let f' : C' ⟶ U' := CommAlgCat.ofHom (Algebra.ofId C (AddMonoidAlgebra C M))
    let t' : Multiplicative M →* (U')ˣ := universal C
    have h₂ := congrArg (basePoint e) (hyfix U' f' t')
    rw [twistedAction_act, basePoint_comp] at h₂
    have h₃ := congrArg (F.map isoU.hom) h₂
    rw [map_mul, map_mul, map_inv, ι.naturality, ι.naturality, mapCharacter_twist,
      ← ConcreteCategory.comp_apply, ← F.map_comp] at h₃
    have e₁ : toRestrict U' ≫ isoU.hom = constant C := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro c
      rfl
    have e₂ : mapCharacter isoU.hom (restrictChar t') = universal C := by
      ext m
      rfl
    have e₃ : restrictScalarsMap f' ≫ isoU.hom = isoC.hom ≫ constant C := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro c
      rfl
    rw [e₁, e₂, e₃, twist_constant_universal, F.map_comp, ConcreteCategory.comp_apply] at h₃
    exact mul_inv_eq_iff_eq_mul.1 h₃

end TwistedLift

end Langlands.GroupScheme.CharacterAction
