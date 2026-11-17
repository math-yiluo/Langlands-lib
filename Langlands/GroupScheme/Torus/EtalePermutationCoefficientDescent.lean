import Langlands.GroupScheme.Torus.EtalePermutationCoefficientCocycle
import Langlands.AlgebraicGeometry.AffineCoverCoefficientTensors
import Langlands.AlgebraicGeometry.FaithfullyFlatAlgebraDescent

/-! # Algebra descent maps from finite affine permutation charts -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace Langlands.AlgebraicGeometry.FiniteProductCoefficients

variable {α : Type u} [Finite α] (R : Type u) [CommRing R]
  (A : α → Type u) [∀ a, CommRing (A a)] [∀ a, Algebra R (A a)]
  (I : α → Type u) [∀ a, Finite (I a)]

/-- Distribute the twice-extended coefficient algebra into triple tensor cells. -/
def tensorDoubleCoefficients :
    ((∀ a, A a) ⊗[R] ((∀ a, A a) ⊗[R] (∀ a, I a → A a))) ≃ₐ[R]
      (∀ a b c, I c → (A a ⊗[R] (A b ⊗[R] A c))) := by
  classical
  letI := Fintype.ofFinite α
  letI (a : α) := Fintype.ofFinite (I a)
  exact (Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) (A₁ := ∀ a, A a))
    (tensorCoefficients R A I)).trans
    ((tensorPi R A (fun b => ∀ c, I c → (A b ⊗[R] A c))).trans
      (AlgEquiv.piCongrRight fun a => AlgEquiv.piCongrRight fun b =>
        (Algebra.TensorProduct.piRight R R (A a) (fun c => I c → (A b ⊗[R] A c))).trans
          (AlgEquiv.piCongrRight fun c =>
            Algebra.TensorProduct.piRight R R (A a) (fun _ : I c => A b ⊗[R] A c))))

@[simp] theorem tensorDoubleCoefficients_tmul
    (x y : ∀ a, A a) (z : ∀ a, I a → A a) (a b c : α) (i : I c) :
    tensorDoubleCoefficients R A I (x ⊗ₜ[R] (y ⊗ₜ[R] z)) a b c i =
      x a ⊗ₜ[R] (y b ⊗ₜ[R] z c i) := rfl

end Langlands.AlgebraicGeometry.FiniteProductCoefficients

namespace Langlands.AlgebraicGeometry.AffineCoverCoefficientTensors

variable {S X Y : Scheme.{u}} [IsAffine S] [IsAffine X] [IsAffine Y]

/-- The overlap tensor equivalence with its common base-ring structure. -/
def overlapTensorAlgEquiv (f : X ⟶ S) (g : Y ⟶ S) :
    letI := f.appTop.hom.toAlgebra
    letI := g.appTop.hom.toAlgebra
    letI := (pullback.fst f g ≫ f).appTop.hom.toAlgebra
    Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(Y, ⊤) ≃ₐ[Γ(S, ⊤)] Γ(pullback f g, ⊤) := by
  letI := f.appTop.hom.toAlgebra
  letI := g.appTop.hom.toAlgebra
  letI := (pullback.fst f g ≫ f).appTop.hom.toAlgebra
  refine { overlapTensorEquiv f g with commutes' := ?_ }
  intro r
  change overlapTensorEquiv f g (f.appTop.hom r ⊗ₜ[Γ(S, ⊤)] 1) =
    (pullback.fst f g ≫ f).appTop.hom r
  rw [overlapTensorEquiv_tmul_one, Scheme.Hom.comp_appTop]
  rfl

end Langlands.AlgebraicGeometry.AffineCoverCoefficientTensors

namespace Langlands.GroupScheme.EtalePermutationAtlas

variable {S U U' V W : Scheme.{u}} {D : GroupScheme S}
  {I J : Type u} [Finite I] [Finite J]

omit [Finite I] [Finite J] in
/-- Pullback of coefficient data along a composite is iterated pullback. -/
theorem coefficientDatum_pullback_comp
    (A : LocalCoefficientReindexing.Datum V I J) (m : W ⟶ V) (n : U ⟶ W) :
    (A.pullback m).pullback n = A.pullback (n ≫ m) := rfl

/-- The coefficient datum on equal-composite chart maps commutes with arbitrary
base change of that common scheme. -/
theorem LocallyPermutes.coefficientDatumAlong_pullback (f : U ⟶ S) (g : U' ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange g).obj D ≅ splitTorus U' J)
    (H : LocallyPermutes f g e e')
    (q : V ⟶ U) (q' : V ⟶ U') (h : q ≫ f = q' ≫ g) (m : W ⟶ V) :
    (H.coefficientDatumAlong f g e e' q q' h).pullback m =
      H.coefficientDatumAlong f g e e' (m ≫ q) (m ≫ q')
        (by simp only [Category.assoc, h]) := by
  unfold LocallyPermutes.coefficientDatumAlong
  rw [coefficientDatum_pullback_comp]
  congr 1
  apply pullback.hom_ext <;> simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]

/-- The actual coefficient equivalence on a common scheme is natural for
pullback of global sections. -/
theorem LocallyPermutes.coefficientEquivAlong_naturality (f : U ⟶ S) (g : U' ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange g).obj D ≅ splitTorus U' J)
    (H : LocallyPermutes f g e e')
    (q : V ⟶ U) (q' : V ⟶ U') (h : q ≫ f = q' ≫ g) (m : W ⟶ V)
    (z : I → Γ(V, ⊤)) (j : J) :
    (H.coefficientDatumAlong f g e e' (m ≫ q) (m ≫ q')
        (by simp only [Category.assoc, h])).equiv (fun i => m.appTop.hom (z i)) j =
      m.appTop.hom ((H.coefficientDatumAlong f g e e' q q' h).equiv z j) := by
  rw [← H.coefficientDatumAlong_pullback f g e e' q q' h m]
  exact (H.coefficientDatumAlong f g e e' q q' h).equiv_pullback m z j

end Langlands.GroupScheme.EtalePermutationAtlas

namespace Langlands.GroupScheme.FiniteAffinePermutationCoefficients

open EtalePermutationAtlas
open Langlands.AlgebraicGeometry
open AffineCoverCoefficientTensors

variable {S : Scheme.{u}} [IsAffine S] {D : GroupScheme S}
  {α : Type u} [Finite α] (U : α → Scheme.{u}) [∀ a, IsAffine (U a)]
  (f : ∀ a, U a ⟶ S) (I : α → Type u) [∀ a, Finite (I a)]
  (e : ∀ a, (GroupScheme.baseChange (f a)).obj D ≅ splitTorus (U a) (I a))
  (H : ∀ a b, LocallyPermutes (f a) (f b) (e a) (e b))

/-- The overlap coefficient equivalence, expressed using maps to the two
original chart schemes. -/
def overlapEquiv (a b : α) :
    (I a → Γ(pullback (f a) (f b), ⊤)) ≃ₐ[Γ(pullback (f a) (f b), ⊤)]
      (I b → Γ(pullback (f a) (f b), ⊤)) :=
  ((H a b).coefficientDatumAlong (f a) (f b) (e a) (e b)
    (pullback.fst (f a) (f b)) (pullback.snd (f a) (f b)) pullback.condition).equiv

/-- Pull one chart component of a global coefficient family to an overlap. -/
def sourceSections (a b : α) :
    (∀ a, I a → Γ(U a, ⊤)) →+* (I a → Γ(pullback (f a) (f b), ⊤)) :=
  RingHom.pi (fun i => (pullback.fst (f a) (f b)).appTop.hom.comp
    ((Pi.evalRingHom (fun _ : I a => Γ(U a, ⊤)) i).comp
      (Pi.evalRingHom (fun a => I a → Γ(U a, ⊤)) a)))

/-- The coefficient transition on every pairwise overlap, applied to the source
component. This is an actual ring map. -/
def overlapMap : (∀ a, I a → Γ(U a, ⊤)) →+*
    (∀ a b, I b → Γ(pullback (f a) (f b), ⊤)) :=
  RingHom.pi (fun a => RingHom.pi (fun b =>
    (overlapEquiv U f I e H a b).toRingHom.comp (sourceSections U f I a b)))

/-- The ring map into the scalar-extension tensor product obtained from the
actual overlap coefficient transitions. -/
def tensorMap :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    (∀ a, I a → Γ(U a, ⊤)) →+*
      ((∀ a, Γ(U a, ⊤)) ⊗[Γ(S, ⊤)] (∀ a, I a → Γ(U a, ⊤))) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  exact (coefficientTensorEquiv U f I).symm.toRingHom.comp (overlapMap U f I e H)

/-- The tensor descent map has exactly the prescribed chart transition on each
actual overlap. -/
theorem tensorMap_formula (z : ∀ a, I a → Γ(U a, ⊤)) (a b : α) (j : I b) :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    coefficientTensorEquiv U f I (tensorMap U f I e H z) a b j =
      overlapEquiv U f I e H a b
        (fun i => (pullback.fst (f a) (f b)).appTop.hom (z a i)) j := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  exact congrFun (congrFun (congrFun
    ((coefficientTensorEquiv U f I).apply_symm_apply (overlapMap U f I e H z)) a) b) j

/-- The transition ring map is linear for the source product-base action,
so it is an actual algebra map into the scalar-extension algebra. -/
def transitionAlgebraMap :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
    letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
      (coverRingMap U f)).toAlgebra
    (∀ a, I a → Γ(U a, ⊤)) →ₐ[∀ a, Γ(U a, ⊤)]
      ((∀ a, Γ(U a, ⊤)) ⊗[Γ(S, ⊤)] (∀ a, I a → Γ(U a, ⊤))) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
  letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
    (coverRingMap U f)).toAlgebra
  refine { tensorMap U f I e H with commutes' := ?_ }
  intro x
  apply (coefficientTensorEquiv U f I).injective
  funext a b j
  change coefficientTensorEquiv U f I
      (tensorMap U f I e H (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I x)) a b j =
    coefficientTensorEquiv U f I (x ⊗ₜ[Γ(S, ⊤)] 1) a b j
  rw [tensorMap_formula]
  change overlapEquiv U f I e H a b
      (algebraMap Γ(pullback (f a) (f b), ⊤) (I a → Γ(pullback (f a) (f b), ⊤))
        ((pullback.fst (f a) (f b)).appTop.hom (x a))) j = _
  rw [AlgEquiv.commutes]
  rw [coefficientTensorEquiv_tmul]
  simp only [Pi.one_apply, map_one, mul_one]
  rfl

/-- The diagonal in a repeated affine chart overlap. -/
def diagonal (a : α) : U a ⟶ pullback (f a) (f a) :=
  pullback.lift (𝟙 _) (𝟙 _) (by simp)

omit [IsAffine S] [Finite α] [∀ a, IsAffine (U a)] in
@[simp] theorem diagonal_app_fst (a : α) (z : Γ(U a, ⊤)) :
    (diagonal U f a).appTop.hom ((pullback.fst (f a) (f a)).appTop.hom z) = z := by
  change ((pullback.fst (f a) (f a)).appTop ≫ (diagonal U f a).appTop).hom z = z
  rw [← Scheme.Hom.comp_appTop]
  simp [diagonal]

omit [IsAffine S] [Finite α] [∀ a, IsAffine (U a)] in
@[simp] theorem diagonal_app_snd (a : α) (z : Γ(U a, ⊤)) :
    (diagonal U f a).appTop.hom ((pullback.snd (f a) (f a)).appTop.hom z) = z := by
  change ((pullback.snd (f a) (f a)).appTop ≫ (diagonal U f a).appTop).hom z = z
  rw [← Scheme.Hom.comp_appTop]
  simp [diagonal]

/-- Multiplication is the counit candidate for the tensor extension. -/
def multiplication :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
    letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
      (coverRingMap U f)).toAlgebra
    ((∀ a, Γ(U a, ⊤)) ⊗[Γ(S, ⊤)] (∀ a, I a → Γ(U a, ⊤))) →ₐ[∀ a, Γ(U a, ⊤)]
      (∀ a, I a → Γ(U a, ⊤)) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
  letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
    (coverRingMap U f)).toAlgebra
  haveI : IsScalarTower Γ(S, ⊤) (∀ a, Γ(U a, ⊤)) (∀ a, I a → Γ(U a, ⊤)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact AlgHom.liftEquiv Γ(S, ⊤) (∀ a, Γ(U a, ⊤))
    (∀ a, I a → Γ(U a, ⊤)) (∀ a, I a → Γ(U a, ⊤)) (AlgHom.id _ _)

/-- Tensor multiplication is evaluation of the overlap tensor coordinates on
the diagonal. -/
theorem multiplication_diagonal
    (z : letI (a : α) := (f a).appTop.hom.toAlgebra
      (∀ a, Γ(U a, ⊤)) ⊗[Γ(S, ⊤)] (∀ a, I a → Γ(U a, ⊤)))
    (a : α) (i : I a) :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
    letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
      (coverRingMap U f)).toAlgebra
    multiplication U f I z a i =
      (diagonal U f a).appTop.hom (coefficientTensorEquiv U f I z a a i) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
  letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
    (coverRingMap U f)).toAlgebra
  induction z using TensorProduct.inductionOn with
  | tmul x z =>
    change x a * z a i = _
    rw [coefficientTensorEquiv_tmul, map_mul, diagonal_app_fst, diagonal_app_snd]
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy]

omit [IsAffine S] [Finite α] [∀ a, IsAffine (U a)] in
/-- On the diagonal the repeated-chart coefficient transition is the identity. -/
theorem diagonal_overlapEquiv (a : α)
    (z : I a → Γ(pullback (f a) (f a), ⊤)) (i : I a) :
    (diagonal U f a).appTop.hom (overlapEquiv U f I e H a a z i) =
      (diagonal U f a).appTop.hom (z i) := by
  have hn := (H a a).coefficientEquivAlong_naturality
    (f a) (f a) (e a) (e a) (pullback.fst (f a) (f a))
    (pullback.snd (f a) (f a)) pullback.condition (diagonal U f a) z i
  have he :
      ((H a a).coefficientDatumAlong (f a) (f a) (e a) (e a)
        (diagonal U f a ≫ pullback.fst (f a) (f a))
        (diagonal U f a ≫ pullback.snd (f a) (f a))
        (by simp only [Category.assoc, pullback.condition])).equiv =
        AlgEquiv.refl (R := Γ(U a, ⊤)) (A₁ := I a → Γ(U a, ⊤)) := by
    simpa only [diagonal, pullback.lift_fst, pullback.lift_snd] using
      coefficientEquivAlong_self (f a) (e a) (H a a) (𝟙 (U a))
  rw [he] at hn
  exact hn.symm

/-- The constructed multiplicative tensor map satisfies the counit law. -/
theorem multiplication_tensorMap (z : ∀ a, I a → Γ(U a, ⊤)) :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
    letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
      (coverRingMap U f)).toAlgebra
    multiplication U f I (tensorMap U f I e H z) = z := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
  letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
    (coverRingMap U f)).toAlgebra
  funext a i
  rw [multiplication_diagonal, tensorMap_formula, diagonal_overlapEquiv, diagonal_app_fst]

/-- The common scheme of three chart coordinates, associated on the right. -/
def tripleScheme (a b c : α) : Scheme.{u} :=
  pullback (f a) (pullback.fst (f b) (f c) ≫ f b)

def triple1 (a b c : α) : tripleScheme U f a b c ⟶ U a :=
  pullback.fst _ _

def triple23 (a b c : α) : tripleScheme U f a b c ⟶ pullback (f b) (f c) :=
  pullback.snd _ _

def triple2 (a b c : α) : tripleScheme U f a b c ⟶ U b :=
  triple23 U f a b c ≫ pullback.fst (f b) (f c)

def triple3 (a b c : α) : tripleScheme U f a b c ⟶ U c :=
  triple23 U f a b c ≫ pullback.snd (f b) (f c)

/-- A triple chart tensor ring is the ring of the actual triple overlap. -/
def tripleCellEquiv (a b c : α) :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    Γ(U a, ⊤) ⊗[Γ(S, ⊤)] (Γ(U b, ⊤) ⊗[Γ(S, ⊤)] Γ(U c, ⊤)) ≃+*
      Γ(tripleScheme U f a b c, ⊤) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  letI := (pullback.fst (f b) (f c) ≫ f b).appTop.hom.toAlgebra
  exact (Algebra.TensorProduct.congr (AlgEquiv.refl (R := Γ(S, ⊤)) (A₁ := Γ(U a, ⊤)))
    (overlapTensorAlgEquiv (f b) (f c))).toRingEquiv.trans
      (overlapTensorEquiv (f a) (pullback.fst (f b) (f c) ≫ f b))

/-- Joint triple-overlap tensor coordinates detect equality in the twice
extended coefficient algebra. -/
def tripleTensorEquiv :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    ((∀ a, Γ(U a, ⊤)) ⊗[Γ(S, ⊤)]
      ((∀ a, Γ(U a, ⊤)) ⊗[Γ(S, ⊤)] (∀ a, I a → Γ(U a, ⊤)))) ≃+*
      (∀ a b c, I c → Γ(tripleScheme U f a b c, ⊤)) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  exact (FiniteProductCoefficients.tensorDoubleCoefficients
    Γ(S, ⊤) (fun a => Γ(U a, ⊤)) I).toRingEquiv.trans
      (RingEquiv.piCongrRight fun a => RingEquiv.piCongrRight fun b =>
        RingEquiv.piCongrRight fun c => RingEquiv.piCongrRight fun _ : I c =>
          tripleCellEquiv U f a b c)

@[simp] theorem tripleTensorEquiv_tmul
    (x y : ∀ a, Γ(U a, ⊤)) (z : ∀ a, I a → Γ(U a, ⊤))
    (a b c : α) (i : I c) :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    tripleTensorEquiv U f I (x ⊗ₜ[Γ(S, ⊤)] (y ⊗ₜ[Γ(S, ⊤)] z)) a b c i =
      (triple1 U f a b c).appTop.hom (x a) *
        ((triple2 U f a b c).appTop.hom (y b) *
          (triple3 U f a b c).appTop.hom (z c i)) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  letI := (pullback.fst (f b) (f c) ≫ f b).appTop.hom.toAlgebra
  change overlapTensorEquiv (f a) (pullback.fst (f b) (f c) ≫ f b)
    (x a ⊗ₜ[Γ(S, ⊤)] overlapTensorEquiv (f b) (f c) (y b ⊗ₜ[Γ(S, ⊤)] z c i)) = _
  rw [overlapTensorEquiv_tmul, overlapTensorEquiv_tmul, map_mul]
  rfl

omit [IsAffine S] [Finite α] [∀ a, IsAffine (U a)] in
theorem triple12_base (a b c : α) :
    triple1 U f a b c ≫ f a = triple2 U f a b c ≫ f b := by
  exact pullback.condition

omit [IsAffine S] [Finite α] [∀ a, IsAffine (U a)] in
theorem triple23_base (a b c : α) :
    triple2 U f a b c ≫ f b = triple3 U f a b c ≫ f c := by
  simp only [triple2, triple3, Category.assoc, pullback.condition]

def triple12 (a b c : α) : tripleScheme U f a b c ⟶ pullback (f a) (f b) :=
  pullback.lift (triple1 U f a b c) (triple2 U f a b c) (triple12_base U f a b c)

def triple13 (a b c : α) : tripleScheme U f a b c ⟶ pullback (f a) (f c) :=
  pullback.lift (triple1 U f a b c) (triple3 U f a b c)
    ((triple12_base U f a b c).trans (triple23_base U f a b c))

omit [IsAffine S] [Finite α] [∀ a, IsAffine (U a)] in
@[reassoc (attr := simp)] theorem triple12_fst (a b c : α) :
    triple12 U f a b c ≫ pullback.fst (f a) (f b) = triple1 U f a b c :=
  pullback.lift_fst _ _ _

omit [IsAffine S] [Finite α] [∀ a, IsAffine (U a)] in
@[reassoc (attr := simp)] theorem triple12_snd (a b c : α) :
    triple12 U f a b c ≫ pullback.snd (f a) (f b) = triple2 U f a b c :=
  pullback.lift_snd _ _ _

omit [IsAffine S] [Finite α] [∀ a, IsAffine (U a)] in
@[reassoc (attr := simp)] theorem triple13_fst (a b c : α) :
    triple13 U f a b c ≫ pullback.fst (f a) (f c) = triple1 U f a b c :=
  pullback.lift_fst _ _ _

omit [IsAffine S] [Finite α] [∀ a, IsAffine (U a)] in
@[reassoc (attr := simp)] theorem triple13_snd (a b c : α) :
    triple13 U f a b c ≫ pullback.snd (f a) (f c) = triple3 U f a b c :=
  pullback.lift_snd _ _ _

theorem appTop_comp_apply {X Y Z : Scheme.{u}} (p : X ⟶ Y) (q : Y ⟶ Z)
    (z : Γ(Z, ⊤)) : p.appTop.hom (q.appTop.hom z) = (p ≫ q).appTop.hom z := by
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- Evaluate an outer pure tensor with an arbitrary inner tensor. -/
theorem tripleTensorEquiv_tmul_right
    (x : ∀ a, Γ(U a, ⊤))
    (z : letI (a : α) := (f a).appTop.hom.toAlgebra
      (∀ a, Γ(U a, ⊤)) ⊗[Γ(S, ⊤)] (∀ a, I a → Γ(U a, ⊤)))
    (a b c : α) (i : I c) :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    tripleTensorEquiv U f I (x ⊗ₜ[Γ(S, ⊤)] z) a b c i =
      (triple1 U f a b c).appTop.hom (x a) *
        (triple23 U f a b c).appTop.hom (coefficientTensorEquiv U f I z b c i) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  induction z using TensorProduct.inductionOn with
  | tmul y z =>
    rw [tripleTensorEquiv_tmul, coefficientTensorEquiv_tmul, map_mul]
    rfl
  | add y z hy hz =>
    have hE : tripleTensorEquiv U f I ((x ⊗ₜ[Γ(S, ⊤)] y) + (x ⊗ₜ[Γ(S, ⊤)] z)) =
        tripleTensorEquiv U f I (x ⊗ₜ[Γ(S, ⊤)] y) +
          tripleTensorEquiv U f I (x ⊗ₜ[Γ(S, ⊤)] z) :=
      (tripleTensorEquiv U f I).map_add' _ _
    have hC : coefficientTensorEquiv U f I (y + z) =
        coefficientTensorEquiv U f I y + coefficientTensorEquiv U f I z :=
      (coefficientTensorEquiv U f I).map_add' _ _
    rw [TensorProduct.tmul_add, hE, hC]
    change _ + _ = _ * (triple23 U f a b c).appTop.hom (_ + _)
    rw [map_add, hy, hz, mul_add]

section CoactionLaws

/-- Insert the middle unit in a twice-extended coefficient tensor. -/
def duplicate :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
    letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
      (coverRingMap U f)).toAlgebra
    ((∀ a, Γ(U a, ⊤)) ⊗[Γ(S, ⊤)] (∀ a, I a → Γ(U a, ⊤))) →ₐ[∀ a, Γ(U a, ⊤)]
      ((∀ a, Γ(U a, ⊤)) ⊗[Γ(S, ⊤)]
        ((∀ a, Γ(U a, ⊤)) ⊗[Γ(S, ⊤)] (∀ a, I a → Γ(U a, ⊤)))) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
  letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
    (coverRingMap U f)).toAlgebra
  exact Algebra.TensorProduct.map (AlgHom.id _ _) Algebra.TensorProduct.includeRight

omit [IsAffine S] [Finite α] [∀ a, IsAffine (U a)] [∀ a, Finite (I a)] in
@[simp] theorem duplicate_tmul (x : ∀ a, Γ(U a, ⊤)) (z : ∀ a, I a → Γ(U a, ⊤)) :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
    letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
      (coverRingMap U f)).toAlgebra
    duplicate U f I (x ⊗ₜ[Γ(S, ⊤)] z) = x ⊗ₜ[Γ(S, ⊤)] (1 ⊗ₜ[Γ(S, ⊤)] z) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
  letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
    (coverRingMap U f)).toAlgebra
  rfl

/-- Extend the actual chart transition in the inner tensor factor. -/
def extendTransition :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
    letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
      (coverRingMap U f)).toAlgebra
    ((∀ a, Γ(U a, ⊤)) ⊗[Γ(S, ⊤)] (∀ a, I a → Γ(U a, ⊤))) →ₐ[∀ a, Γ(U a, ⊤)]
      ((∀ a, Γ(U a, ⊤)) ⊗[Γ(S, ⊤)]
        ((∀ a, Γ(U a, ⊤)) ⊗[Γ(S, ⊤)] (∀ a, I a → Γ(U a, ⊤)))) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
  letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
    (coverRingMap U f)).toAlgebra
  haveI : IsScalarTower Γ(S, ⊤) (∀ a, Γ(U a, ⊤)) (∀ a, I a → Γ(U a, ⊤)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Algebra.TensorProduct.map (AlgHom.id _ _)
    ((transitionAlgebraMap U f I e H).restrictScalars Γ(S, ⊤))

@[simp] theorem extendTransition_tmul
    (x : ∀ a, Γ(U a, ⊤)) (z : ∀ a, I a → Γ(U a, ⊤)) :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
    letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
      (coverRingMap U f)).toAlgebra
    extendTransition U f I e H (x ⊗ₜ[Γ(S, ⊤)] z) =
      x ⊗ₜ[Γ(S, ⊤)] tensorMap U f I e H z := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
  letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
    (coverRingMap U f)).toAlgebra
  rfl

set_option maxHeartbeats 400000 in
/-- In triple coordinates insertion of the middle unit is pullback from the
first and third overlap. -/
theorem duplicate_formula
    (z : letI (a : α) := (f a).appTop.hom.toAlgebra
      (∀ a, Γ(U a, ⊤)) ⊗[Γ(S, ⊤)] (∀ a, I a → Γ(U a, ⊤)))
    (a b c : α) (i : I c) :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
    letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
      (coverRingMap U f)).toAlgebra
    tripleTensorEquiv U f I (duplicate U f I z) a b c i =
      (triple13 U f a b c).appTop.hom (coefficientTensorEquiv U f I z a c i) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
  letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
    (coverRingMap U f)).toAlgebra
  induction z using TensorProduct.inductionOn with
  | tmul x z =>
    simp only [duplicate_tmul, tripleTensorEquiv_tmul, coefficientTensorEquiv_tmul,
      Pi.one_apply, map_one, one_mul, map_mul, appTop_comp_apply,
      triple13_fst, triple13_snd]
  | add x y hx hy =>
    have hd : duplicate U f I (x + y) = duplicate U f I x + duplicate U f I y :=
      (duplicate U f I).map_add' _ _
    have hE : tripleTensorEquiv U f I (duplicate U f I x + duplicate U f I y) =
        tripleTensorEquiv U f I (duplicate U f I x) +
          tripleTensorEquiv U f I (duplicate U f I y) :=
      (tripleTensorEquiv U f I).map_add' _ _
    have hC : coefficientTensorEquiv U f I (x + y) =
        coefficientTensorEquiv U f I x + coefficientTensorEquiv U f I y :=
      (coefficientTensorEquiv U f I).map_add' _ _
    rw [hd, hE, hC]
    change _ + _ = (triple13 U f a b c).appTop.hom (_ + _)
    exact (congrArg₂ (fun s t : Γ(tripleScheme U f a b c, ⊤) => s + t) hx hy).trans
      ((triple13 U f a b c).appTop.hom.map_add' _ _).symm

set_option maxHeartbeats 600000 in
/-- Extending the chart transition acts in triple coordinates by the transition
from the second to the third chart on the first-second coefficient family. -/
theorem extendTransition_formula
    (z : letI (a : α) := (f a).appTop.hom.toAlgebra
      (∀ a, Γ(U a, ⊤)) ⊗[Γ(S, ⊤)] (∀ a, I a → Γ(U a, ⊤)))
    (a b c : α) (i : I c) :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
    letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
      (coverRingMap U f)).toAlgebra
    tripleTensorEquiv U f I (extendTransition U f I e H z) a b c i =
      ((H b c).coefficientDatumAlong (f b) (f c) (e b) (e c)
        (triple2 U f a b c) (triple3 U f a b c) (triple23_base U f a b c)).equiv
        (fun j => (triple12 U f a b c).appTop.hom (coefficientTensorEquiv U f I z a b j)) i := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
  letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
    (coverRingMap U f)).toAlgebra
  let E := ((H b c).coefficientDatumAlong (f b) (f c) (e b) (e c)
    (triple2 U f a b c) (triple3 U f a b c) (triple23_base U f a b c)).equiv
  change tripleTensorEquiv U f I (extendTransition U f I e H z) a b c i =
    E (fun j => (triple12 U f a b c).appTop.hom (coefficientTensorEquiv U f I z a b j)) i
  induction z using TensorProduct.inductionOn with
  | tmul x z =>
    have hn : E (fun j => (triple2 U f a b c).appTop.hom (z b j)) i =
        (triple23 U f a b c).appTop.hom
          (overlapEquiv U f I e H b c
            (fun j => (pullback.fst (f b) (f c)).appTop.hom (z b j)) i) := by
      exact (H b c).coefficientEquivAlong_naturality (f b) (f c) (e b) (e c)
        (pullback.fst (f b) (f c)) (pullback.snd (f b) (f c)) pullback.condition
        (triple23 U f a b c)
        (fun j => (pullback.fst (f b) (f c)).appTop.hom (z b j)) i
    have hs :
        (fun j => (triple12 U f a b c).appTop.hom
          (coefficientTensorEquiv U f I (x ⊗ₜ[Γ(S, ⊤)] z) a b j)) =
        (triple1 U f a b c).appTop.hom (x a) •
          (fun j => (triple2 U f a b c).appTop.hom (z b j)) := by
      funext j
      rw [coefficientTensorEquiv_tmul, map_mul, appTop_comp_apply, appTop_comp_apply,
        triple12_fst, triple12_snd]
      rfl
    rw [extendTransition_tmul, tripleTensorEquiv_tmul_right, tensorMap_formula, ← hn, hs]
    exact (congrFun (map_smul E.toLinearMap
      ((triple1 U f a b c).appTop.hom (x a))
      (fun j => (triple2 U f a b c).appTop.hom (z b j))) i).symm
  | add x y hx hy =>
    have hd : extendTransition U f I e H (x + y) =
        extendTransition U f I e H x + extendTransition U f I e H y :=
      (extendTransition U f I e H).map_add' _ _
    have hE : tripleTensorEquiv U f I
        (extendTransition U f I e H x + extendTransition U f I e H y) =
        tripleTensorEquiv U f I (extendTransition U f I e H x) +
          tripleTensorEquiv U f I (extendTransition U f I e H y) :=
      (tripleTensorEquiv U f I).map_add' _ _
    have hC : coefficientTensorEquiv U f I (x + y) =
        coefficientTensorEquiv U f I x + coefficientTensorEquiv U f I y :=
      (coefficientTensorEquiv U f I).map_add' _ _
    have hs :
        (fun j => (triple12 U f a b c).appTop.hom
          (coefficientTensorEquiv U f I (x + y) a b j)) =
        (fun j => (triple12 U f a b c).appTop.hom (coefficientTensorEquiv U f I x a b j)) +
          (fun j => (triple12 U f a b c).appTop.hom (coefficientTensorEquiv U f I y a b j)) := by
      rw [hC]
      funext j
      exact (triple12 U f a b c).appTop.hom.map_add' _ _
    rw [hd, hE, hs, map_add E]
    exact congrArg₂ (fun s t : Γ(tripleScheme U f a b c, ⊤) => s + t) hx hy

set_option maxHeartbeats 800000 in
/-- The original chart cocycle proves coassociativity of the multiplicative
tensor transition map. -/
theorem tensorMap_coassoc (z : ∀ a, I a → Γ(U a, ⊤)) :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
    letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
      (coverRingMap U f)).toAlgebra
    duplicate U f I (tensorMap U f I e H z) =
      extendTransition U f I e H (tensorMap U f I e H z) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
  letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
    (coverRingMap U f)).toAlgebra
  apply (tripleTensorEquiv U f I).injective
  funext a b c i
  rw [duplicate_formula, extendTransition_formula]
  let A12 := (H a b).coefficientDatumAlong (f a) (f b) (e a) (e b)
    (triple1 U f a b c) (triple2 U f a b c) (triple12_base U f a b c)
  let A23 := (H b c).coefficientDatumAlong (f b) (f c) (e b) (e c)
    (triple2 U f a b c) (triple3 U f a b c) (triple23_base U f a b c)
  let A13 := (H a c).coefficientDatumAlong (f a) (f c) (e a) (e c)
    (triple1 U f a b c) (triple3 U f a b c)
    ((triple12_base U f a b c).trans (triple23_base U f a b c))
  let v := fun j => (triple1 U f a b c).appTop.hom (z a j)
  have h12 :
      (fun j => (triple12 U f a b c).appTop.hom
        (coefficientTensorEquiv U f I (tensorMap U f I e H z) a b j)) = A12.equiv v := by
    funext j
    rw [tensorMap_formula]
    have hn := (H a b).coefficientEquivAlong_naturality (f a) (f b) (e a) (e b)
      (pullback.fst (f a) (f b)) (pullback.snd (f a) (f b)) pullback.condition
      (triple12 U f a b c) (fun j => (pullback.fst (f a) (f b)).appTop.hom (z a j)) j
    simpa only [A12, v, overlapEquiv, triple12_fst, triple12_snd, appTop_comp_apply] using hn.symm
  have h13 :
      (triple13 U f a b c).appTop.hom
        (coefficientTensorEquiv U f I (tensorMap U f I e H z) a c i) = A13.equiv v i := by
    rw [tensorMap_formula]
    have hn := (H a c).coefficientEquivAlong_naturality (f a) (f c) (e a) (e c)
      (pullback.fst (f a) (f c)) (pullback.snd (f a) (f c)) pullback.condition
      (triple13 U f a b c) (fun j => (pullback.fst (f a) (f c)).appTop.hom (z a j)) i
    simpa only [A13, v, overlapEquiv, triple13_fst, triple13_snd, appTop_comp_apply] using hn.symm
  rw [h12, h13]
  have hc : A12.equiv.trans A23.equiv = A13.equiv :=
    coefficientEquivAlong_cocycle (f a) (f b) (f c) (e a) (e b) (e c)
      (H a b) (H b c) (H a c)
      (triple1 U f a b c) (triple2 U f a b c) (triple3 U f a b c)
      (triple12_base U f a b c) (triple23_base U f a b c)
  exact (congrArg (fun E => E v i) hc).symm

set_option maxHeartbeats 800000 in
/-- Actual multiplicative faithfully flat descent coaction derived from the
finite affine chart transitions, with both comonad laws proved. -/
def coaction : FaithfullyFlatAlgebraDescent.Coaction (coverRingMap U f)
    (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I) := by
  refine { map := transitionAlgebraMap U f I e H, counit := ?_, coassoc := ?_ }
  · letI (a : α) := (f a).appTop.hom.toAlgebra
    letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
    letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
      (coverRingMap U f)).toAlgebra
    have hε : (FaithfullyFlatCoalgebraDescent.descentComonad (coverRingMap U f)).ε.app
        (ModuleCat.of (∀ a, Γ(U a, ⊤)) (∀ a, I a → Γ(U a, ⊤))) =
        ModuleCat.ofHom (multiplication U f I).toLinearMap := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul x z => rfl
      | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    rw [hε]
    apply ModuleCat.hom_ext
    ext z
    exact multiplication_tensorMap U f I e H z
  · letI (a : α) := (f a).appTop.hom.toAlgebra
    letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
    letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
      (coverRingMap U f)).toAlgebra
    have hδ : (FaithfullyFlatCoalgebraDescent.descentComonad (coverRingMap U f)).δ.app
        (ModuleCat.of (∀ a, Γ(U a, ⊤)) (∀ a, I a → Γ(U a, ⊤))) =
        ModuleCat.ofHom (duplicate U f I).toLinearMap := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul x z => rfl
      | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    have hm : (FaithfullyFlatCoalgebraDescent.descentComonad (coverRingMap U f)).map
        (ModuleCat.ofHom (transitionAlgebraMap U f I e H).toLinearMap) =
        ModuleCat.ofHom (extendTransition U f I e H).toLinearMap := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul x z => rfl
      | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    rw [hδ, hm]
    apply ModuleCat.hom_ext
    ext z
    exact tensorMap_coassoc U f I e H z

include e H in
/-- A finite flat-surjective affine permutation atlas has an actual descended
finite projective étale coefficient algebra and scalar-extension equivalence. -/
theorem exists_coefficientDescent [∀ a, Flat (f a)] [Surjective (Sigma.desc f)] :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra Γ(S, ⊤) E)
      (_ : Module.Finite Γ(S, ⊤) E) (_ : Module.Projective Γ(S, ⊤) E),
      Algebra.Etale Γ(S, ⊤) E ∧
        letI (a : α) := (f a).appTop.hom.toAlgebra
        letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
        Nonempty (((∀ a, Γ(U a, ⊤)) ⊗[Γ(S, ⊤)] E) ≃ₐ[∀ a, Γ(U a, ⊤)]
          (∀ a, I a → Γ(U a, ⊤))) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  letI := (FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).toAlgebra
  letI := ((FiniteProductCoefficients.scalarMap (fun a => Γ(U a, ⊤)) I).comp
    (coverRingMap U f)).toAlgebra
  let A := coaction U f I e H
  have hφ := coverRingMap_faithfullyFlat U f
  have hF := FiniteProductCoefficients.finite (fun a => Γ(U a, ⊤)) I
  have hE := FiniteProductCoefficients.etale (fun a => Γ(U a, ⊤)) I
  letI := A.finite_invariants hφ hF
  letI := A.projective_invariants hφ hF hE
  refine ⟨A.invariants, inferInstance, inferInstance, inferInstance, inferInstance,
    A.etale_invariants hφ hE, ?_⟩
  exact ⟨A.descentEquiv hφ⟩

end CoactionLaws
end Langlands.GroupScheme.FiniteAffinePermutationCoefficients
