import Langlands.AbelianScheme.PointedAbelianLawRepresentabilityStatement
import Langlands.AbelianScheme.PointedMorphismRigidityProof
import Langlands.AbelianScheme.GroupSchemeSubalgebraDescentProof

/-! # Pointed group laws on the pullbacks of a family -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory CategoryTheory.Functor
open scoped MonObj

namespace Langlands.AbelianScheme.PointedLaw

universe u

variable {S : Scheme.{u}}

/-- The group equations for multiplication, the prescribed unit, and inverse on a set of
    generalized points. Commutativity supplies the right unit and right inverse equations. -/
structure GroupEquations {A : Type*} (m : A → A → A) (e : A) (i : A → A) : Prop where
  assoc : ∀ x y z, m (m x y) z = m x (m y z)
  comm : ∀ x y, m x y = m y x
  leftUnit : ∀ x, m e x = x
  leftInv : ∀ x, m (i x) x = e

private theorem GroupEquations.of_injective {A B : Type*}
    {m : A → A → A} {e : A} {i : A → A} {m' : B → B → B} {e' : B} {i' : B → B}
    (f : A → B) (hf : Function.Injective f) (hm : ∀ x y, f (m x y) = m' (f x) (f y))
    (he : f e = e') (hi : ∀ x, f (i x) = i' (f x)) (h : GroupEquations m' e' i') :
    GroupEquations m e i where
  assoc x y z := hf (by simpa only [hm] using h.assoc (f x) (f y) (f z))
  comm x y := hf (by simpa only [hm] using h.comm (f x) (f y))
  leftUnit x := hf (by simpa only [hm, he] using h.leftUnit (f x))
  leftInv x := hf (by simpa only [hm, hi, he] using h.leftInv (f x))

/-- Candidate multiplication and inverse on the pullback of `X` to `T`, written as maps to
    `X` over `S` with a common parameter in `T`. -/
@[ext]
structure Law (X T : Over S) where
  mul : (X ⊗ X) ⊗ T ⟶ X
  inv : X ⊗ T ⟶ X

namespace Law

variable {X T U V : Over S}

/-- Multiplication of points with parameter `a`. -/
def mulAt (L : Law X T) (a : U ⟶ T) (x y : U ⟶ X) : U ⟶ X :=
  lift (lift x y) a ≫ L.mul

/-- Inversion of a point with parameter `a`. -/
def invAt (L : Law X T) (a : U ⟶ T) (x : U ⟶ X) : U ⟶ X :=
  lift x a ≫ L.inv

/-- Restrict the parameter of a candidate law. -/
def restrict (L : Law X T) (a : U ⟶ T) : Law X U :=
  ⟨((X ⊗ X) ◁ a) ≫ L.mul, (X ◁ a) ≫ L.inv⟩

@[simp]
theorem mulAt_restrict (L : Law X T) (a : U ⟶ T) (b : V ⟶ U) (x y : V ⟶ X) :
    (L.restrict a).mulAt b x y = L.mulAt (b ≫ a) x y := by
  simp [mulAt, restrict]

@[simp]
theorem invAt_restrict (L : Law X T) (a : U ⟶ T) (b : V ⟶ U) (x : V ⟶ X) :
    (L.restrict a).invAt b x = L.invAt (b ≫ a) x := by
  simp [invAt, restrict]

@[reassoc (attr := simp)]
theorem comp_mulAt (L : Law X T) (b : V ⟶ U) (a : U ⟶ T) (x y : U ⟶ X) :
    b ≫ L.mulAt a x y = L.mulAt (b ≫ a) (b ≫ x) (b ≫ y) := by
  simp only [mulAt, comp_lift_assoc, comp_lift]

@[reassoc (attr := simp)]
theorem comp_invAt (L : Law X T) (b : V ⟶ U) (a : U ⟶ T) (x : U ⟶ X) :
    b ≫ L.invAt a x = L.invAt (b ≫ a) (b ≫ x) := by
  simp only [invAt, comp_lift_assoc]

/-- The equations for every generalized point with a parameter in `T`. -/
def IsGroup (L : Law X T) (e : 𝟙_ (Over S) ⟶ X) : Prop :=
  ∀ ⦃U : Over S⦄ (a : U ⟶ T), GroupEquations (L.mulAt a) (toUnit U ≫ e) (L.invAt a)

end Law

section Fiber

variable (T : Over S)

/-- An object over `S` pulled back to the chosen test. -/
abbrev fiber (P : Over S) : Over T.left := (Over.pullback T.hom).obj P

private abbrev overBase (U : Over T.left) : Over S := (Over.map T.hom).obj U

private def parameter (U : Over T.left) : overBase T U ⟶ T := Over.homMk U.hom rfl

@[simp]
private theorem map_comp_parameter {U V : Over T.left} (b : U ⟶ V) :
    (Over.map T.hom).map b ≫ parameter T V = parameter T U :=
  Over.OverMorphism.ext (Over.w b)

private abbrev pointEquiv {U : Over T.left} {P : Over S} :
    (overBase T U ⟶ P) ≃ (U ⟶ fiber T P) := (Over.mapPullbackAdj T.hom).homEquiv U P

private abbrev forgetPoint {U : Over T.left} {P : Over S} (x : U ⟶ fiber T P) :
    overBase T U ⟶ P := (pointEquiv T).symm x

@[simp]
private theorem forgetPoint_left {U : Over T.left} {P : Over S} (x : U ⟶ fiber T P) :
    (forgetPoint T x).left = x.left ≫ pullback.fst P.hom T.hom := rfl

private def baseProductIso (P : Over S) : overBase T (fiber T P) ≅ P ⊗ T :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ (pullback.fst P.hom T.hom ≫ P.hom) = pullback.snd P.hom T.hom ≫ T.hom
    rw [Category.id_comp, pullback.condition])

private def operationEquiv {P X : Over S} :
    (P ⊗ T ⟶ X) ≃ (fiber T P ⟶ fiber T X) := by
  refine Equiv.trans ?_ (pointEquiv T)
  exact { toFun := fun f => (baseProductIso T P).hom ≫ f
          invFun := fun f => (baseProductIso T P).inv ≫ f
          left_inv := fun f => by simp
          right_inv := fun f => by simp }

private theorem forgetPoint_operation {P X : Over S} {U : Over T.left}
    (f : P ⊗ T ⟶ X) (x : U ⟶ fiber T P) :
    forgetPoint T (x ≫ operationEquiv T f) = lift (forgetPoint T x) (parameter T U) ≫ f := by
  change ((Over.mapPullbackAdj T.hom).homEquiv U X).symm
    (x ≫ (pointEquiv T) ((baseProductIso T P).hom ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply, ← Category.assoc]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;> apply Over.OverMorphism.ext
  · simp [baseProductIso]
  · simp [baseProductIso, parameter]
    exact Over.w x

private abbrev productComparison (P Q : Over S) :
    fiber T P ⊗ fiber T Q ≅ fiber T (P ⊗ Q) :=
  asIso (LaxMonoidal.μ (Over.pullback T.hom) P Q)

private theorem forgetPoint_pair {P Q : Over S} {U : Over T.left}
    (x : U ⟶ fiber T P) (y : U ⟶ fiber T Q) :
    forgetPoint T (lift x y ≫ (productComparison T P Q).hom) =
      lift (forgetPoint T x) (forgetPoint T y) := by
  let F := Over.pullback T.hom
  apply CartesianMonoidalCategory.hom_ext
  · change ((Over.mapPullbackAdj T.hom).homEquiv U (P ⊗ Q)).symm
        (lift x y ≫ LaxMonoidal.μ F P Q) ≫ fst P Q = _
    rw [← Adjunction.homEquiv_naturality_right_symm, Category.assoc, Monoidal.μ_fst,
      lift_fst, lift_fst]
  · change ((Over.mapPullbackAdj T.hom).homEquiv U (P ⊗ Q)).symm
        (lift x y ≫ LaxMonoidal.μ F P Q) ≫ snd P Q = _
    rw [← Adjunction.homEquiv_naturality_right_symm, Category.assoc, Monoidal.μ_snd,
      lift_snd, lift_snd]

variable {T} {X : Over S}

private def fiberMulEquiv : ((X ⊗ X) ⊗ T ⟶ X) ≃ (fiber T X ⊗ fiber T X ⟶ fiber T X) :=
  (operationEquiv T).trans
    { toFun := fun f => (productComparison T X X).hom ≫ f
      invFun := fun f => (productComparison T X X).inv ≫ f
      left_inv := fun f => by simp
      right_inv := fun f => by simp }

variable (e : 𝟙_ (Over S) ⟶ X)

/-- The prescribed identity section after base change to the test scheme. -/
def fiberUnit (T : Over S) : 𝟙_ (Over T.left) ⟶ fiber T X :=
  pointEquiv T (toUnit _ ≫ e)

private theorem fiberUnit_fst :
    (fiberUnit e T).left ≫ pullback.fst X.hom T.hom = T.hom ≫ e.left := by
  have h := forgetPoint_left T (fiberUnit e T)
  change ((pointEquiv T).symm ((pointEquiv T) (toUnit _ ≫ e))).left = _ at h
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

private theorem forgetPoint_fiberUnit {U : Over T.left} :
    forgetPoint T (toUnit U ≫ fiberUnit e T) = toUnit (overBase T U) ≫ e := by
  change ((Over.mapPullbackAdj T.hom).homEquiv U X).symm
    (toUnit U ≫ (pointEquiv T) (toUnit _ ≫ e)) = _
  rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply, ← Category.assoc,
    comp_toUnit]

namespace Law

variable (L : Law X T)

/-- Candidate multiplication, as an arrow in the slice over the test scheme. -/
def fiberMul : fiber T X ⊗ fiber T X ⟶ fiber T X := fiberMulEquiv L.mul

/-- Candidate inverse, as an arrow in the slice over the test scheme. -/
def fiberInv : fiber T X ⟶ fiber T X := operationEquiv T L.inv

private theorem forgetPoint_mul {U : Over T.left} (x y : U ⟶ fiber T X) :
    forgetPoint T (lift x y ≫ L.fiberMul) =
      L.mulAt (parameter T U) (forgetPoint T x) (forgetPoint T y) := by
  change forgetPoint T (lift x y ≫ (productComparison T X X).hom ≫ operationEquiv T L.mul) = _
  rw [← Category.assoc, forgetPoint_operation, forgetPoint_pair]
  rfl

private theorem forgetPoint_inv {U : Over T.left} (x : U ⟶ fiber T X) :
    forgetPoint T (x ≫ L.fiberInv) = L.invAt (parameter T U) (forgetPoint T x) :=
  forgetPoint_operation T L.inv x

private theorem eq_of_fiberOperations {L' : Law X T}
    (hm : L.fiberMul = L'.fiberMul) (hi : L.fiberInv = L'.fiberInv) : L = L' :=
  Law.ext (fiberMulEquiv.injective hm) ((operationEquiv T).injective hi)

private def ofFiberOperations (m : fiber T X ⊗ fiber T X ⟶ fiber T X)
    (i : fiber T X ⟶ fiber T X) : Law X T :=
  ⟨fiberMulEquiv.symm m, (operationEquiv T).symm i⟩

@[simp]
private theorem fiberMul_ofFiberOperations (m : fiber T X ⊗ fiber T X ⟶ fiber T X)
    (i : fiber T X ⟶ fiber T X) : (ofFiberOperations m i).fiberMul = m :=
  fiberMulEquiv.apply_symm_apply m

@[simp]
private theorem fiberInv_ofFiberOperations (m : fiber T X ⊗ fiber T X ⟶ fiber T X)
    (i : fiber T X ⟶ fiber T X) : (ofFiberOperations m i).fiberInv = i :=
  (operationEquiv T).apply_symm_apply i

private def FiberEquations : Prop :=
  ∀ (U : Over T.left), GroupEquations (fun (x y : U ⟶ fiber T X) => lift x y ≫ L.fiberMul)
    (toUnit U ≫ fiberUnit e T) (fun x => x ≫ L.fiberInv)

private theorem isGroup_iff_fiberEquations : L.IsGroup e ↔ L.FiberEquations e := by
  constructor
  · intro h U
    exact GroupEquations.of_injective (forgetPoint T) (pointEquiv T).symm.injective
      (L.forgetPoint_mul) (forgetPoint_fiberUnit e) (L.forgetPoint_inv) (h (parameter T U))
  · intro h U a
    let W : Over T.left := Over.mk a.left
    let j : overBase T W ≅ U := Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ U.hom = a.left ≫ T.hom
      rw [Category.id_comp, Over.w a])
    have hj : j.hom ≫ a = parameter T W := by
      apply Over.OverMorphism.ext
      change 𝟙 _ ≫ a.left = a.left
      exact Category.id_comp _
    let F : (U ⟶ X) → (W ⟶ fiber T X) := fun x => pointEquiv T (j.hom ≫ x)
    have hF : Function.Injective F := fun _ _ eq =>
      (cancel_epi j.hom).1 ((pointEquiv T).injective eq)
    refine GroupEquations.of_injective F hF ?_ ?_ ?_ (h W)
    · intro x y
      apply (pointEquiv T).symm.injective
      change forgetPoint T (F (L.mulAt a x y)) = forgetPoint T (lift (F x) (F y) ≫ L.fiberMul)
      rw [forgetPoint_mul]
      simp only [F, Equiv.symm_apply_apply, comp_mulAt, hj]
    · apply (pointEquiv T).symm.injective
      change forgetPoint T (F (toUnit U ≫ e)) = forgetPoint T (toUnit W ≫ fiberUnit e T)
      rw [forgetPoint_fiberUnit]
      simp only [F, Equiv.symm_apply_apply, ← Category.assoc, comp_toUnit]
    · intro x
      apply (pointEquiv T).symm.injective
      change forgetPoint T (F (L.invAt a x)) = forgetPoint T (F x ≫ L.fiberInv)
      rw [forgetPoint_inv]
      simp only [F, Equiv.symm_apply_apply, comp_invAt, hj]

@[instance_reducible]
private def grpObj (h : L.FiberEquations e) : GrpObj (fiber T X) where
  one := fiberUnit e T
  mul := L.fiberMul
  inv := L.fiberInv
  one_mul := by
    let Y := fiber T X
    have hleft : fiberUnit e T ▷ Y = lift (toUnit _ ≫ fiberUnit e T) (snd _ _) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [whiskerRight_fst, lift_fst, toUnit_unique (fst _ _) (toUnit _)]
      · rw [whiskerRight_snd, lift_snd]
    rw [hleft, leftUnitor_hom]
    exact (h _).leftUnit _
  mul_one := by
    let Y := fiber T X
    have hright : Y ◁ fiberUnit e T = lift (fst _ _) (toUnit _ ≫ fiberUnit e T) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [whiskerLeft_fst, lift_fst]
      · rw [whiskerLeft_snd, lift_snd, toUnit_unique (snd _ _) (toUnit _)]
    rw [hright, rightUnitor_hom]
    exact ((h _).comm _ _).trans ((h _).leftUnit _)
  mul_assoc := by
    let Y := fiber T X
    let m := L.fiberMul
    let x := fst (Y ⊗ Y) Y ≫ fst Y Y
    let y := fst (Y ⊗ Y) Y ≫ snd Y Y
    let z := snd (Y ⊗ Y) Y
    have hxyz : lift (lift x y) z = 𝟙 _ := by simp [x, y, z]
    change (m ▷ Y) ≫ m = (α_ Y Y Y).hom ≫ (Y ◁ m) ≫ m
    calc
      (m ▷ Y) ≫ m = lift (lift x y) z ≫ (m ▷ Y) ≫ m := by rw [hxyz, Category.id_comp]
      _ = lift (lift x y ≫ m) z ≫ m := lift_whiskerRight_assoc _ _ _ _
      _ = lift x (lift y z ≫ m) ≫ m := (h _).assoc x y z
      _ = lift (lift x y) z ≫ (α_ Y Y Y).hom ≫ (Y ◁ m) ≫ m := by
        rw [lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc]
      _ = _ := by rw [hxyz, Category.id_comp]
  left_inv := (h _).leftInv (𝟙 _)
  right_inv := ((h _).comm (𝟙 _) _).trans ((h _).leftInv (𝟙 _))

private theorem grpObj_comm (h : L.FiberEquations e) :
    letI := L.grpObj e h
    IsCommMonObj (fiber T X) := by
  let := L.grpObj e h
  constructor
  change (β_ _ _).hom ≫ L.fiberMul = L.fiberMul
  rw [← lift_snd_fst]
  simpa only [lift_fst_snd, Category.id_comp] using (h _).comm (snd _ _) (fst _ _)

private theorem isGroup_of_grpObj [GrpObj (fiber T X)] [IsCommMonObj (fiber T X)]
    (he : η[fiber T X] = fiberUnit e T) :
    (ofFiberOperations μ[fiber T X] ι[fiber T X]).IsGroup e := by
  apply (isGroup_iff_fiberEquations e _).2
  intro U
  simp only [fiberMul_ofFiberOperations, fiberInv_ofFiberOperations, ← he]
  exact ⟨fun x y z => mul_assoc x y z, fun x y => mul_comm x y,
    fun x => one_mul x, fun x => inv_mul_cancel x⟩

private def group (h : L.IsGroup e) : GroupScheme T.left where
  X := fiber T X
  grp := L.grpObj e ((L.isGroup_iff_fiberEquations e).1 h)

/-- On the pullback of a smooth proper geometrically connected family, the fixed unit
    determines the multiplication and inverse of a group law. -/
theorem unique [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    {L' : Law X T} (h : L.IsGroup e) (h' : L'.IsGroup e) : L = L' := by
  let G := L.group e h
  let H := L'.group e h'
  have hG : GroupScheme.IsAbelian G := by
    change Smooth (pullback.snd X.hom T.hom) ∧ IsProper (pullback.snd X.hom T.hom) ∧
      GeometricallyConnected (pullback.snd X.hom T.hom)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hf := pointedMorphismRigidity T.left G H hG
    (by change LocallyOfFinitePresentation (pullback.snd X.hom T.hom); infer_instance)
    (by change QuasiCompact (pullback.snd X.hom T.hom); infer_instance)
    (by change QuasiSeparated (pullback.snd X.hom T.hom); infer_instance)
    (𝟙 (fiber T X)) (by change fiberUnit e T ≫ 𝟙 _ = fiberUnit e T; simp)
  apply L.eq_of_fiberOperations
  · have hm := hf.mul_hom
    change L.fiberMul ≫ 𝟙 _ = (𝟙 (fiber T X) ⊗ₘ 𝟙 (fiber T X)) ≫ L'.fiberMul at hm
    simpa only [Category.comp_id, id_tensorHom_id, Category.id_comp] using hm
  · have hi := @GrpObj.inv_hom _ _ _ G.X H.X G.grp H.grp (𝟙 (fiber T X)) hf
    change L.fiberInv ≫ 𝟙 _ = 𝟙 _ ≫ L'.fiberInv at hi
    simpa only [Category.comp_id, Category.id_comp] using hi

end Law

end Fiber

/-- The candidate group equations are equivalent to the existence of the abelian scheme
    structure on the pullback with the prescribed unit and relative dimension. -/
theorem exists_law_iff {X T : Scheme.{u}} (p : X ⟶ S) (s : S ⟶ X) (hs : s ≫ p = 𝟙 S)
    (g : ℕ) [SmoothOfRelativeDimension g p] [IsProper p] [GeometricallyConnected p]
    (t : T ⟶ S) :
    (∃ L : Law (Over.mk p) (Over.mk t), L.IsGroup (Over.homMk s hs)) ↔
      HasPointedAbelianPullback p s g t := by
  let P := Over.mk p
  let B := Over.mk t
  let e : 𝟙_ (Over S) ⟶ P := Over.homMk s hs
  let Y := fiber B P
  let : SmoothOfRelativeDimension g Y.hom :=
    inferInstanceAs (SmoothOfRelativeDimension g (pullback.snd p t))
  let : Smooth Y.hom := SmoothOfRelativeDimension.smooth (n := g) Y.hom
  let : IsProper Y.hom := inferInstanceAs (IsProper (pullback.snd p t))
  let : GeometricallyConnected Y.hom := inferInstanceAs (GeometricallyConnected (pullback.snd p t))
  constructor
  · rintro ⟨L, hL⟩
    let A : AbelianScheme T :=
      { toGrp := L.group e hL
        comm := L.grpObj_comm e ((L.isGroup_iff_fiberEquations e).1 hL)
        smooth := ‹Smooth Y.hom›
        proper := ‹IsProper Y.hom›
        geometricallyConnected := ‹GeometricallyConnected Y.hom› }
    refine ⟨A, Iso.refl _, ‹SmoothOfRelativeDimension g Y.hom›, Category.id_comp _, ?_⟩
    change (fiberUnit e B).left ≫ 𝟙 _ ≫ pullback.fst p t = t ≫ s
    rw [Category.id_comp]
    exact fiberUnit_fst (T := B) e
  · rintro ⟨A, j, _, hj, he⟩
    let j' : A.X ≅ Y := Over.isoMk j hj
    let : GrpObj Y := GrpObj.ofIso j'
    have : IsMonHom j'.hom := isMonHom_ofIso j'
    let : IsCommMonObj Y := Langlands.GroupScheme.isCommMonObj_of_iso j'
    have hunit : η[Y] = fiberUnit e B := by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · change (η[A.X].left ≫ j.hom) ≫ pullback.fst p t =
          (fiberUnit e B).left ≫ pullback.fst p t
        rw [Category.assoc, he]
        exact (fiberUnit_fst (T := B) e).symm
      · exact (Over.w η[Y]).trans (Over.w (fiberUnit e B)).symm
    exact ⟨Law.ofFiberOperations μ[Y] ι[Y], Law.isGroup_of_grpObj e hunit⟩

end Langlands.AbelianScheme.PointedLaw
