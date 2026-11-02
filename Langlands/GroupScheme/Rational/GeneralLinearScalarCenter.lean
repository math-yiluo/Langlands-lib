import Langlands.GroupScheme.Rational.GeneralLinearCharacterSchemes

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

theorem scalarMatrix_injective (A : Type*) [CommRing A] :
    Function.Injective (Matrix.GeneralLinearGroup.scalar n (R := A)) := by
  intro a b h
  obtain ⟨i⟩ := ‹Nonempty n›
  apply Units.ext
  have he := congrArg (fun g : GL n A => g i i) h
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using he

/-- A scalar unit is exactly a central invertible matrix, over any coefficient ring. -/
def scalarCenterEquiv (A : Type*) [CommRing A] :
    Aˣ ≃* Subgroup.center (GL n A) :=
  (MonoidHom.ofInjective (scalarMatrix_injective (n := n) A)).trans
    (MulEquiv.subgroupCongr Matrix.GeneralLinearGroup.center_eq_range_scalar.symm)

@[simp] theorem scalarCenterEquiv_val {A : Type*} [CommRing A] (a : Aˣ) :
    (scalarCenterEquiv (n := n) A a).val = Matrix.GeneralLinearGroup.scalar n a := rfl

@[simp] theorem scalarCenterEquiv_symm_scalar {A : Type*} [CommRing A]
    (g : Subgroup.center (GL n A)) :
    Matrix.GeneralLinearGroup.scalar n ((scalarCenterEquiv (n := n) A).symm g) = g.val :=
  congrArg Subtype.val ((scalarCenterEquiv (n := n) A).apply_symm_apply g)

variable {R : CommRingCat.{u}} {H : GroupScheme (Spec R)}

/-- The unit scalar attached to a central matrix-valued point. -/
def centralScalarMatrixPoints (j : H ⟶ groupScheme n R)
    (hj : ∀ (T : Over (Spec R)) (x : T ⟶ H.X),
      pointsEquiv n R T (x ≫ j.hom.hom) ∈ Subgroup.center (GL n Γ(T.left, ⊤)))
    (T : Over (Spec R)) : (T ⟶ H.X) →* (Γ(T.left, ⊤))ˣ :=
  (scalarCenterEquiv (n := n) Γ(T.left, ⊤)).symm.toMonoidHom.comp
    (((pointsEquiv n R T).toMonoidHom.comp ((pointsMap j).app (op T)).hom).codRestrict
      (Subgroup.center (GL n Γ(T.left, ⊤))) (hj T))

theorem scalar_centralScalarMatrixPoints (j : H ⟶ groupScheme n R)
    (hj : ∀ (T : Over (Spec R)) (x : T ⟶ H.X),
      pointsEquiv n R T (x ≫ j.hom.hom) ∈ Subgroup.center (GL n Γ(T.left, ⊤)))
    (T : Over (Spec R)) (x : T ⟶ H.X) :
    Matrix.GeneralLinearGroup.scalar n (centralScalarMatrixPoints j hj T x) =
      pointsEquiv n R T (x ≫ j.hom.hom) :=
  scalarCenterEquiv_symm_scalar _

theorem centralScalarMatrixPoints_naturality (j : H ⟶ groupScheme n R)
    (hj : ∀ (T : Over (Spec R)) (x : T ⟶ H.X),
      pointsEquiv n R T (x ≫ j.hom.hom) ∈ Subgroup.center (GL n Γ(T.left, ⊤)))
    {T T' : Over (Spec R)} (a : T' ⟶ T) (x : T ⟶ H.X) :
    centralScalarMatrixPoints j hj T' (a ≫ x) =
      Units.map a.left.appTop.hom.toMonoidHom (centralScalarMatrixPoints j hj T x) := by
  apply scalarMatrix_injective (n := n) Γ(T'.left, ⊤)
  have hm := Matrix.GeneralLinearGroup.map_scalar (n := n)
    a.left.appTop.hom (centralScalarMatrixPoints j hj T x)
  change Matrix.GeneralLinearGroup.map a.left.appTop.hom
      (Matrix.GeneralLinearGroup.scalar n (centralScalarMatrixPoints j hj T x)) =
    Matrix.GeneralLinearGroup.scalar n
      (Units.map a.left.appTop.hom.toMonoidHom (centralScalarMatrixPoints j hj T x)) at hm
  rw [scalar_centralScalarMatrixPoints, ← hm,
    scalar_centralScalarMatrixPoints, Category.assoc, pointsEquiv_naturality]

theorem centralScalarFactor_naturality (j : H ⟶ groupScheme n R)
    (hj : ∀ (T : Over (Spec R)) (x : T ⟶ H.X),
      pointsEquiv n R T (x ≫ j.hom.hom) ∈ Subgroup.center (GL n Γ(T.left, ⊤)))
    {T T' : Over (Spec R)} (a : T' ⟶ T) (x : T ⟶ H.X) :
    (fun T => (Gm.pointsEquiv (Spec R) T).symm.toMonoidHom.comp
      (centralScalarMatrixPoints j hj T)) T' (a ≫ x) =
    a ≫ (fun T => (Gm.pointsEquiv (Spec R) T).symm.toMonoidHom.comp
      (centralScalarMatrixPoints j hj T)) T x := by
  apply (Gm.pointsEquiv (Spec R) T').injective
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    Gm.pointsEquiv_naturality, centralScalarMatrixPoints_naturality]

/-- Every matrix-valued group-scheme morphism whose point matrices are central
has a canonical factor through the multiplicative group. -/
def centralScalarFactor (j : H ⟶ groupScheme n R)
    (hj : ∀ (T : Over (Spec R)) (x : T ⟶ H.X),
      pointsEquiv n R T (x ≫ j.hom.hom) ∈ Subgroup.center (GL n Γ(T.left, ⊤))) :
    H ⟶ (Gm (Spec R)).toGrp :=
  homOfPoints
    (fun T => (Gm.pointsEquiv (Spec R) T).symm.toMonoidHom.comp
      (centralScalarMatrixPoints j hj T))
    (centralScalarFactor_naturality j hj)

theorem pointsEquiv_centralScalarFactor (j : H ⟶ groupScheme n R)
    (hj : ∀ (T : Over (Spec R)) (x : T ⟶ H.X),
      pointsEquiv n R T (x ≫ j.hom.hom) ∈ Subgroup.center (GL n Γ(T.left, ⊤)))
    (T : Over (Spec R)) (x : T ⟶ H.X) :
    Gm.pointsEquiv (Spec R) T (x ≫ (centralScalarFactor j hj).hom.hom) =
      centralScalarMatrixPoints j hj T x := by
  rw [centralScalarFactor, comp_homOfPoints]
  exact MulEquiv.apply_symm_apply _ _

/-- The factor through `Gm` composes with any morphism having the scalar point
formula to recover the original central morphism. -/
theorem centralScalarFactor_comp (j : H ⟶ groupScheme n R)
    (hj : ∀ (T : Over (Spec R)) (x : T ⟶ H.X),
      pointsEquiv n R T (x ≫ j.hom.hom) ∈ Subgroup.center (GL n Γ(T.left, ⊤)))
    (s : (Gm (Spec R)).toGrp ⟶ groupScheme n R)
    (hs : ∀ (T : Over (Spec R)) (x : T ⟶ (Gm (Spec R)).X),
      pointsEquiv n R T (x ≫ s.hom.hom) =
        Matrix.GeneralLinearGroup.scalar n (Gm.pointsEquiv (Spec R) T x)) :
    centralScalarFactor j hj ≫ s = j := by
  apply hom_ext_points
  intro T x
  apply (pointsEquiv n R T).injective
  change pointsEquiv n R T (x ≫ (centralScalarFactor j hj).hom.hom ≫ s.hom.hom) = _
  rw [← Category.assoc, hs, pointsEquiv_centralScalarFactor,
    scalar_centralScalarMatrixPoints]

/-- A morphism with the scalar point formula is a monomorphism when `n` is nonempty. -/
theorem scalarPointFormula_mono
    (s : (Gm (Spec R)).toGrp ⟶ groupScheme n R)
    (hs : ∀ (T : Over (Spec R)) (x : T ⟶ (Gm (Spec R)).X),
      pointsEquiv n R T (x ≫ s.hom.hom) =
        Matrix.GeneralLinearGroup.scalar n (Gm.pointsEquiv (Spec R) T x)) : Mono s := by
  constructor
  intro Z f g h
  apply hom_ext_points
  intro T x
  apply (Gm.pointsEquiv (Spec R) T).injective
  apply scalarMatrix_injective (n := n) Γ(T.left, ⊤)
  rw [← hs, ← hs]
  have he := congrArg (fun q : Z ⟶ groupScheme n R => pointsEquiv n R T (x ≫ q.hom.hom)) h
  exact he

/-- A central monomorphism through which the scalar homomorphism factors is
isomorphic to the multiplicative group through that factorization. -/
theorem scalarPointFormula_factor_isIso
    (s : (Gm (Spec R)).toGrp ⟶ groupScheme n R)
    (hs : ∀ (T : Over (Spec R)) (x : T ⟶ (Gm (Spec R)).X),
      pointsEquiv n R T (x ≫ s.hom.hom) =
        Matrix.GeneralLinearGroup.scalar n (Gm.pointsEquiv (Spec R) T x))
    (j : H ⟶ groupScheme n R) [Mono j]
    (hj : ∀ (T : Over (Spec R)) (x : T ⟶ H.X),
      pointsEquiv n R T (x ≫ j.hom.hom) ∈ Subgroup.center (GL n Γ(T.left, ⊤)))
    (f : (Gm (Spec R)).toGrp ⟶ H) (hf : f ≫ j = s) : IsIso f := by
  have : Mono s := scalarPointFormula_mono s hs
  let p := centralScalarFactor j hj
  have hp : p ≫ s = j := centralScalarFactor_comp j hj s hs
  have hfp : f ≫ p = 𝟙 _ := by
    apply (cancel_mono s).mp
    rw [Category.assoc, hp, hf, Category.id_comp]
  have hpf : p ≫ f = 𝟙 _ := by
    apply (cancel_mono j).mp
    rw [Category.assoc, hf, hp, Category.id_comp]
  exact ⟨⟨p, hfp, hpf⟩⟩

end Langlands.GroupScheme.GeneralLinear
