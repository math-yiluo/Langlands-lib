import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.FreeSquareZero
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.FiniteBanachBounds

/-! # Bounded maps and base change of finite free square-zero algebras -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FreeSquareZero

open TrivSqZeroExt

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A B : PresentedAffinoidAlgebra K} {n : ℕ}
  {D : Type v} [NormedCommRing D] [NormedAlgebra K D]

private theorem coefficientMap_smul (g : BoundedAlgHom K B D) (b : Fin n → D)
    (r : B) (a : Fin n → B) : g.coefficientMap b (r • a) = g r * g.coefficientMap b a := by
  rw [BoundedAlgHom.coefficientMap_apply, BoundedAlgHom.coefficientMap_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.smul_apply, smul_eq_mul]
  rw [map_mul, mul_assoc]

private theorem coefficientMap_mul_eq_zero (g : BoundedAlgHom K B D) (b : Fin n → D)
    (hb : ∀ i j, b i * b j = 0) (a c : Fin n → B) :
    g.coefficientMap b a * g.coefficientMap b c = 0 := by
  rw [BoundedAlgHom.coefficientMap_apply, BoundedAlgHom.coefficientMap_apply, Finset.sum_mul_sum]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  calc
    _ = (g (a i) * g (c j)) * (b i * b j) := by ring
    _ = 0 := by rw [hb, mul_zero]

private def liftAlgHom (g : BoundedAlgHom K B D) (b : Fin n → D)
    (hb : ∀ i j, b i * b j = 0) : Coordinates B n →ₐ[K] D :=
  TrivSqZeroExt.lift g.toAlgHom (g.coefficientMap b).toLinearMap
    (coefficientMap_mul_eq_zero g b hb) (coefficientMap_smul g b)
    (fun r a => by
      change g.coefficientMap b (MulOpposite.op r • a) = g.coefficientMap b a * g r
      rw [op_smul_eq_smul, coefficientMap_smul, mul_comm])

/-- A bounded scalar map and a tuple with all pairwise products zero
extend to the square-zero algebra in coordinates. -/
def liftCoordinates (g : BoundedAlgHom K B D) (b : Fin n → D)
    (hb : ∀ i j, b i * b j = 0) : BoundedAlgHom K (Coordinates B n) D :=
  BoundedAlgHom.ofFiniteBanachTriangle (scalarMap K) (scalarMap_isFiniteBanach K) g
    (liftAlgHom g b hb) (AlgHom.ext fun a => by
      change liftAlgHom g b hb (inl a) = g a
      simp only [liftAlgHom, TrivSqZeroExt.lift_apply_inl])

@[simp] theorem liftCoordinates_inl (g : BoundedAlgHom K B D) (b : Fin n → D)
    (hb : ∀ i j, b i * b j = 0) (a : B) : liftCoordinates g b hb (inl a) = g a := by
  change liftAlgHom g b hb (inl a) = g a
  simp only [liftAlgHom, TrivSqZeroExt.lift_apply_inl]

@[simp] theorem liftCoordinates_basisElement (g : BoundedAlgHom K B D) (b : Fin n → D)
    (hb : ∀ i j, b i * b j = 0) (j : Fin n) : liftCoordinates g b hb (basisElement j) = b j := by
  have h : liftCoordinates g b hb (inr (Pi.single j 1)) = g.coefficientMap b (Pi.single j 1) :=
    by
      change liftAlgHom g b hb (inr (Pi.single j 1)) = g.coefficientMap b (Pi.single j 1)
      simp only [liftAlgHom, TrivSqZeroExt.lift_apply_inr]
      rfl
  rw [basisElement, h, BoundedAlgHom.coefficientMap_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Ne.symm hij]
  · simp

/-- Constant and degree-one coordinates determine every bounded map. -/
theorem coordinates_hom_ext (p q : BoundedAlgHom K (Coordinates B n) D)
    (hs : p.comp (scalarMap K) = q.comp (scalarMap K))
    (hb : ∀ j, p (basisElement j) = q (basisElement j)) : p = q := by
  apply BoundedAlgHom.ext
  intro x
  rw [← expansion K x, map_add, map_add, map_sum, map_sum]
  congr 1
  · exact congrArg (fun f : BoundedAlgHom K B D => f x.fst) hs
  · apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, map_mul]
    exact congrArg₂ (· * ·) (congrArg (fun f : BoundedAlgHom K B D => f (x.snd j)) hs) (hb j)

private def coordinateMapAlgHom (f : BoundedAlgHom K A B) : Coordinates A n →ₐ[K] Coordinates B n where
  toFun x := (f x.fst, fun i => f (x.snd i))
  map_one' := TrivSqZeroExt.ext (map_one f.toAlgHom) (funext fun _ => map_zero f.toAlgHom)
  map_zero' := TrivSqZeroExt.ext (map_zero f.toAlgHom) (funext fun _ => map_zero f.toAlgHom)
  map_add' x y := TrivSqZeroExt.ext (map_add f.toAlgHom _ _)
    (funext fun _ => map_add f.toAlgHom _ _)
  map_mul' x y := by
    apply TrivSqZeroExt.ext (map_mul f.toAlgHom _ _)
    ext i
    let X : Coordinates B n := (f x.fst, fun i => f (x.snd i))
    let Y : Coordinates B n := (f y.fst, fun i => f (y.snd i))
    change f.toAlgHom ((x * y).snd i) = (X * Y).snd i
    simp only [TrivSqZeroExt.snd_mul, op_smul_eq_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    change f.toAlgHom (x.fst * y.snd i + y.fst * x.snd i) =
      f.toAlgHom x.fst * f.toAlgHom (y.snd i) + f.toAlgHom y.fst * f.toAlgHom (x.snd i)
    rw [map_add, map_mul, map_mul]
  commutes' k := TrivSqZeroExt.ext (f.toAlgHom.commutes k) (funext fun _ => map_zero f.toAlgHom)

/-- Restrict each of the square-zero coordinates by the original bounded map. -/
def coordinateMap (f : BoundedAlgHom K A B) : BoundedAlgHom K (Coordinates A n) (Coordinates B n) :=
  BoundedAlgHom.ofFiniteBanachTriangle (scalarMap K) (scalarMap_isFiniteBanach K)
    ((scalarMap K).comp f) (coordinateMapAlgHom f) (AlgHom.ext fun _ =>
      TrivSqZeroExt.ext rfl (funext fun _ => map_zero f.toAlgHom))

@[simp] theorem coordinateMap_fst (f : BoundedAlgHom K A B) (x : Coordinates A n) :
    (coordinateMap f x).fst = f x.fst := rfl

@[simp] theorem coordinateMap_snd (f : BoundedAlgHom K A B) (x : Coordinates A n) (j : Fin n) :
    (coordinateMap f x).snd j = f (x.snd j) := rfl

@[simp] theorem coordinateMap_inl (f : BoundedAlgHom K A B) (a : A) :
    coordinateMap (n := n) f (inl a) = inl (f a) :=
  TrivSqZeroExt.ext rfl (funext fun _ => map_zero f.toAlgHom)

@[simp] theorem coordinateMap_inr (f : BoundedAlgHom K A B) (a : Fin n → A) :
    coordinateMap f (inr a) = inr (fun j => f (a j)) :=
  TrivSqZeroExt.ext (map_zero f.toAlgHom) rfl

@[simp] theorem coordinateMap_basisElement (f : BoundedAlgHom K A B) (j : Fin n) :
    coordinateMap f (basisElement j) = basisElement j := by
  rw [basisElement, basisElement, coordinateMap_inr]
  congr 1
  ext i
  by_cases hij : j = i
  · subst i
    simp
  · simp [Ne.symm hij]

variable [CompleteSpace K]

/-- The degree-one basis element in the actual affinoid presentation. -/
def generator (A : PresentedAffinoidAlgebra K) (j : Fin n) : algebra K A n :=
  (coordinateEquiv K A n).symm (basisElement j)

@[simp] theorem coordinateEquiv_generator (j : Fin n) :
    coordinateEquiv K A n (generator A j) = basisElement j :=
  (coordinateEquiv K A n).apply_symm_apply _

@[simp] theorem generator_mul_generator (i j : Fin n) : generator A i * generator A j = 0 := by
  apply (coordinateEquiv K A n).toAlgEquiv.injective
  rw [map_mul, map_zero]
  rw [coordinateEquiv_generator, coordinateEquiv_generator]
  exact inr_mul_inr A _ _

/-- Scalar restriction and the identity on the specified linear generators,
transported to the actual presentations. -/
def map (f : BoundedAlgHom K A B) (n : ℕ) : BoundedAlgHom K (algebra K A n) (algebra K B n) :=
  (coordinateEquiv K B n).symm.toBoundedAlgHom.comp
    ((coordinateMap f).comp (coordinateEquiv K A n).toBoundedAlgHom)

@[simp] theorem coordinateEquiv_map (f : BoundedAlgHom K A B) (x : algebra K A n) :
    coordinateEquiv K B n (map f n x) = coordinateMap f (coordinateEquiv K A n x) :=
  (coordinateEquiv K B n).apply_symm_apply _

@[simp] theorem map_baseMap (f : BoundedAlgHom K A B) :
    (map f n).comp (baseMap K A n) = (baseMap K B n).comp f := by
  apply BoundedAlgHom.ext
  intro a
  apply (coordinateEquiv K B n).toAlgEquiv.injective
  change coordinateEquiv K B n (map f n (baseMap K A n a)) = coordinateEquiv K B n (baseMap K B n (f a))
  rw [coordinateEquiv_map, coordinateEquiv_baseMap, coordinateEquiv_baseMap, coordinateMap_inl]

@[simp] theorem map_generator (f : BoundedAlgHom K A B) (j : Fin n) :
    map f n (generator A j) = generator B j := by
  apply (coordinateEquiv K B n).toAlgEquiv.injective
  rw [coordinateEquiv_map, coordinateEquiv_generator, coordinateEquiv_generator, coordinateMap_basisElement]


/-- The scalar map and the finite degree-one basis determine bounded maps
on the presented square-zero algebra. -/
theorem hom_ext (p q : BoundedAlgHom K (algebra K B n) D)
    (hs : p.comp (baseMap K B n) = q.comp (baseMap K B n))
    (hb : ∀ j : Fin n, p (generator B j) = q (generator B j)) : p = q := by
  let e := coordinateEquiv K B n
  have h : p.comp e.symm.toBoundedAlgHom = q.comp e.symm.toBoundedAlgHom :=
    coordinates_hom_ext _ _ hs hb
  apply BoundedAlgHom.ext
  intro x
  have hx := congrArg (fun f : BoundedAlgHom K (Coordinates B n) D => f (e x)) h
  simpa only [BoundedAlgHom.comp_apply, BoundedAlgEquiv.toBoundedAlgHom_apply,
    BoundedAlgEquiv.symm_apply_apply] using hx

@[simp] theorem map_comp {C : PresentedAffinoidAlgebra K}
    (g : BoundedAlgHom K B C) (f : BoundedAlgHom K A B) :
    (map g n).comp (map f n) = map (g.comp f) n := by
  apply hom_ext
  · rw [BoundedAlgHom.comp_assoc, map_baseMap f, ← BoundedAlgHom.comp_assoc,
      map_baseMap g, BoundedAlgHom.comp_assoc, map_baseMap (g.comp f)]
  · intro j
    simp only [BoundedAlgHom.comp_apply, map_generator]

private def liftPresentation (g : BoundedAlgHom K B D) (b : Fin n → D)
    (hb : ∀ i j, b i * b j = 0) : BoundedAlgHom K (algebra K B n) D :=
  (liftCoordinates g b hb).comp (coordinateEquiv K B n).toBoundedAlgHom

@[simp] private theorem liftPresentation_baseMap (g : BoundedAlgHom K B D) (b : Fin n → D)
    (hb : ∀ i j, b i * b j = 0) (a : B) : liftPresentation g b hb (baseMap K B n a) = g a := by
  change liftCoordinates g b hb (coordinateEquiv K B n (baseMap K B n a)) = g a
  rw [coordinateEquiv_baseMap, liftCoordinates_inl]

@[simp] private theorem liftPresentation_generator (g : BoundedAlgHom K B D) (b : Fin n → D)
    (hb : ∀ i j, b i * b j = 0) (j : Fin n) : liftPresentation g b hb (generator B j) = b j := by
  change liftCoordinates g b hb (coordinateEquiv K B n (generator B j)) = b j
  rw [coordinateEquiv_generator, liftCoordinates_basisElement]

variable (f : BoundedAlgHom K A B)

local notation "S" => algebra K A n
local notation "T" => algebra K B n
local notation "σ" => baseMap K A n
local notation "P" => AffinoidPushout.algebra σ f
local notation "ℓ" => AffinoidPushout.leftMap σ f
local notation "r" => AffinoidPushout.rightMap σ f

private def pushoutForward : BoundedAlgHom K P T :=
  AffinoidPushout.lift σ f T (map f n) (baseMap K B n) (map_baseMap f)

private theorem pushoutForward_left : (pushoutForward (n := n) f).comp ℓ = map f n :=
  AffinoidPushout.lift_comp_leftMap _ _ _ _ _ _

private theorem pushoutForward_right : (pushoutForward (n := n) f).comp r = baseMap K B n :=
  AffinoidPushout.lift_comp_rightMap _ _ _ _ _ _

private theorem pushoutGenerators_nil (i j : Fin n) :
    ℓ (generator A i) * ℓ (generator A j) = 0 := by
  rw [← map_mul, generator_mul_generator, map_zero]

private def pushoutInverse : BoundedAlgHom K T P :=
  liftPresentation r (fun j => ℓ (generator A j)) (pushoutGenerators_nil f)

private theorem pushoutInverse_comp_baseMap :
    (pushoutInverse (n := n) f).comp (baseMap K B n) = r :=
  BoundedAlgHom.ext fun a => liftPresentation_baseMap r _ (pushoutGenerators_nil f) a

private theorem pushoutInverse_comp_map : (pushoutInverse (n := n) f).comp (map f n) = ℓ := by
  apply hom_ext
  · rw [BoundedAlgHom.comp_assoc, map_baseMap, ← BoundedAlgHom.comp_assoc,
      AffinoidPushout.condition σ f]
    rw [pushoutInverse_comp_baseMap]
  · intro j
    change pushoutInverse f (map f n (generator A j)) = ℓ (generator A j)
    rw [map_generator]
    exact liftPresentation_generator r _ (pushoutGenerators_nil f) j

private theorem pushoutInverse_comp_forward :
    (pushoutInverse (n := n) f).comp (pushoutForward f) = BoundedAlgHom.id K P := by
  apply AffinoidPushout.hom_ext
  · rw [BoundedAlgHom.comp_assoc, pushoutForward_left, pushoutInverse_comp_map, BoundedAlgHom.id_comp]
  · rw [BoundedAlgHom.comp_assoc, pushoutForward_right,
      pushoutInverse_comp_baseMap, BoundedAlgHom.id_comp]

private theorem pushoutForward_comp_inverse :
    (pushoutForward (n := n) f).comp (pushoutInverse f) = BoundedAlgHom.id K T := by
  apply hom_ext
  · rw [BoundedAlgHom.comp_assoc, pushoutInverse_comp_baseMap, pushoutForward_right, BoundedAlgHom.id_comp]
  · intro j
    change pushoutForward f (pushoutInverse f (generator B j)) = generator B j
    calc
      _ = pushoutForward f (ℓ (generator A j)) :=
        congrArg (pushoutForward f) (liftPresentation_generator r _ (pushoutGenerators_nil f) j)
      _ = map f n (generator A j) := congrArg (fun h : BoundedAlgHom K S T => h (generator A j))
        (pushoutForward_left f)
      _ = _ := map_generator f j

/-- The actual affinoid pushout of the constant-coordinate inclusion is the
presented square-zero algebra over the new coefficient algebra. -/
def pushoutEquiv : BoundedAlgEquiv K P T :=
  BoundedAlgEquiv.ofHomInv (pushoutForward f) (pushoutInverse f)
    (fun x => congrArg (fun h : BoundedAlgHom K P P => h x) (pushoutInverse_comp_forward f))
    (fun x => congrArg (fun h : BoundedAlgHom K T T => h x) (pushoutForward_comp_inverse f))

@[simp] theorem pushoutEquiv_left :
    (pushoutEquiv (n := n) f).toBoundedAlgHom.comp ℓ = map f n :=
  pushoutForward_left f

@[simp] theorem pushoutEquiv_right :
    (pushoutEquiv (n := n) f).toBoundedAlgHom.comp r = baseMap K B n :=
  pushoutForward_right f

end Langlands.Analytic.PresentedAffinoidAlgebra.FreeSquareZero
