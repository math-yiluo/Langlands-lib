import Langlands.GroupScheme.Rational.IndependentWeightProductStatement
import Langlands.GroupScheme.Rational.ClosedImmersionPullbackProof
import Langlands.GroupScheme.MatrixRepresentation.VectorGroupPolynomial
import Langlands.GroupScheme.CorepresentedAffineComparison

/-! # Closed immersion of ordered products with independent torus weights -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IndependentWeightProduct

open PointedCoordinateWeights

local instance {k : Type u} [Field k] (n : ℕ) :
    IsAffineHom (VectorGroup.groupScheme (CommRingCat.of k) n).X.hom :=
  VectorGroup.isAffineHom_groupScheme _ n

/-! ### A diagonal torus action on standard affine space -/

section Diagonal

variable {R : CommRingCat.{u}} {n : ℕ} {S : CommGroupScheme (Spec R)}
  (u : Fin n → characterLattice S)

/-- Scale the `i`-th coordinate by the value of the `i`-th character. -/
def diagonalPointAction (T : Over (Spec R)) (s : T ⟶ S.X)
    (v : T ⟶ (VectorGroup.groupScheme R n).X) : T ⟶ (VectorGroup.groupScheme R n).X :=
  (VectorGroup.coordinates R n T).symm (Multiplicative.ofAdd fun i =>
    VectorGroup.charValue (u i) T s * (VectorGroup.coordinates R n T v).toAdd i)

theorem coordinates_diagonalPointAction (T : Over (Spec R)) (s : T ⟶ S.X)
    (v : T ⟶ (VectorGroup.groupScheme R n).X) :
    (VectorGroup.coordinates R n T (diagonalPointAction u T s v)).toAdd = fun i =>
      VectorGroup.charValue (u i) T s * (VectorGroup.coordinates R n T v).toAdd i := by
  rw [diagonalPointAction, MulEquiv.apply_symm_apply, toAdd_ofAdd]

theorem diagonalPointAction_comp {T T' : Over (Spec R)} (a : T' ⟶ T) (s : T ⟶ S.X)
    (v : T ⟶ (VectorGroup.groupScheme R n).X) :
    a ≫ diagonalPointAction u T s v = diagonalPointAction u T' (a ≫ s) (a ≫ v) :=
  VectorGroup.points_ext fun i => by
    simp only [VectorGroup.coordinates_comp, coordinates_diagonalPointAction,
      VectorGroup.charValue_comp, map_mul]

theorem diagonalPointAction_one (T : Over (Spec R)) (v : T ⟶ (VectorGroup.groupScheme R n).X) :
    diagonalPointAction u T 1 v = v :=
  VectorGroup.points_ext fun i => by
    simp only [coordinates_diagonalPointAction, VectorGroup.charValue_one, one_mul]

theorem diagonalPointAction_mul (T : Over (Spec R)) (s s' : T ⟶ S.X)
    (v : T ⟶ (VectorGroup.groupScheme R n).X) :
    diagonalPointAction u T (s * s') v =
      diagonalPointAction u T s (diagonalPointAction u T s' v) :=
  VectorGroup.points_ext fun i => by
    simp only [coordinates_diagonalPointAction, VectorGroup.charValue_mul, mul_assoc]

theorem diagonalPointAction_mul_right (T : Over (Spec R)) (s : T ⟶ S.X)
    (v v' : T ⟶ (VectorGroup.groupScheme R n).X) :
    diagonalPointAction u T s (v * v') =
      diagonalPointAction u T s v * diagonalPointAction u T s v' :=
  VectorGroup.points_ext fun i => by
    simp only [coordinates_diagonalPointAction, VectorGroup.coordinates_mul, Pi.add_apply,
      mul_add]

/-- The torus acts on standard affine space with the supplied character on each
coordinate. -/
def diagonalAction : AutomorphicAction S.toGrp (VectorGroup.groupScheme R n) :=
  AutomorphicAction.ofPoints (diagonalPointAction u) (diagonalPointAction_comp u)
    (diagonalPointAction_one u) (diagonalPointAction_mul u) (diagonalPointAction_mul_right u)

theorem diagonalAction_act {T : Over (Spec R)} (s : T ⟶ S.X)
    (v : T ⟶ (VectorGroup.groupScheme R n).X) :
    (diagonalAction u).act s v = diagonalPointAction u T s v :=
  AutomorphicAction.ofPoints_act _ (diagonalPointAction_comp u) (diagonalPointAction_one u)
    (diagonalPointAction_mul u) (diagonalPointAction_mul_right u) s v

/-- Affine parameters agree with the global-section coordinates. -/
theorem vectorCoordinates_affinePoint (A : CommAlgCat.{u} R) (t : Fin n → A) :
    (VectorGroup.coordinates R n ((algSpec R).obj (op A))
        (VectorGroup.affinePoint A t)).toAdd =
      fun j => (Scheme.ΓSpecIso (CommRingCat.of A)).inv (t j) := by
  change (Corepresented.pointsEquiv (VectorGroup.functor R n)
    (VectorGroup.corepresentableBy R n) _ _).toAdd = _
  rw [Corepresented.pointsEquiv_eq_affinePointsEquiv, VectorGroup.affinePointsEquiv_affinePoint]
  rfl

theorem affinePoint_injective (A : CommAlgCat.{u} R) :
    Function.Injective (VectorGroup.affinePoint (d := n) A) := by
  intro t t' h
  have h' := congrArg (Corepresented.affinePointsEquiv (VectorGroup.functor R n)
    (VectorGroup.corepresentableBy R n) A) h
  rw [VectorGroup.affinePointsEquiv_affinePoint, VectorGroup.affinePointsEquiv_affinePoint] at h'
  exact Multiplicative.ofAdd.injective h'

/-- On affine tests the diagonal action multiplies each affine parameter by the
corresponding character value. -/
theorem diagonalAction_affinePoint {A : Type u} [CommRing A] [Algebra R A]
    (s : Lie.AffinePoints S.toGrp A) (t : Fin n → A) :
    (diagonalAction u).act s (VectorGroup.affinePoint (CommAlgCat.of R A) t) =
      VectorGroup.affinePoint (CommAlgCat.of R A)
        (fun i => (Lie.characterValue (u i) s : A) * t i) := by
  rw [diagonalAction_act]
  apply VectorGroup.points_ext
  intro i
  rw [coordinates_diagonalPointAction, vectorCoordinates_affinePoint,
    vectorCoordinates_affinePoint]
  dsimp only
  have hc : VectorGroup.charValue (u i) ((algSpec R).obj (op (CommAlgCat.of R A))) s =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (Lie.characterValue (u i) s : A) := by
    change _ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv
      ((Scheme.ΓSpecIso (CommRingCat.of A)).hom
        (VectorGroup.charValue (u i) ((algSpec R).obj (op (CommAlgCat.of R A))) s))
    simp
  rw [hc]
  exact (map_mul _ _ _).symm

end Diagonal

/-! ### Actual coordinates of standard affine space -/

section Coordinates

variable {k : Type u} [Field k] {n : ℕ}

theorem pointsMap_affinePoint {A B : Type u} [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] (f : A →ₐ[k] B) (t : Fin n → A) :
    PointedCoordinateWeights.pointsMap (V := (VectorGroup.groupScheme (CommRingCat.of k) n).X) f
        (VectorGroup.affinePoint (CommAlgCat.of (CommRingCat.of k) A) t) =
      VectorGroup.affinePoint (CommAlgCat.of (CommRingCat.of k) B) (fun i => f (t i)) := by
  change (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op ≫
      (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (MvPolynomial.aeval t)).op = _
  rw [← Functor.map_comp, ← op_comp, ← CommAlgCat.ofHom_comp, MvPolynomial.comp_aeval]
  rfl

theorem pointsMap_universalPoint {V : Over (Spec (CommRingCat.of k))} [IsAffineHom V.hom]
    {A : Type u} [CommRing A] [Algebra k A] (v : Points V A) :
    PointedCoordinateWeights.pointsMap (pointCoordinates v) (universalPoint V) = v := by
  apply pointCoordinates.injective
  rw [pointCoordinates_naturality, coordinates_universalPoint, AlgHom.comp_id]

variable (k n) in
/-- The actual coordinate functions of standard affine space, read off from the
universal point in the chosen actual coordinates. -/
def coordinateFunctions : Fin n → Coord (VectorGroup.groupScheme (CommRingCat.of k) n).X :=
  (Corepresented.affinePointsEquiv (VectorGroup.functor (CommRingCat.of k) n)
    (VectorGroup.corepresentableBy (CommRingCat.of k) n)
    (CommAlgCat.of (CommRingCat.of k) (Coord (VectorGroup.groupScheme (CommRingCat.of k) n).X))
    (universalPoint (VectorGroup.groupScheme (CommRingCat.of k) n).X)).toAdd

theorem affinePoint_coordinateFunctions :
    VectorGroup.affinePoint (CommAlgCat.of (CommRingCat.of k)
        (Coord (VectorGroup.groupScheme (CommRingCat.of k) n).X)) (coordinateFunctions k n) =
      universalPoint (VectorGroup.groupScheme (CommRingCat.of k) n).X := by
  apply (Corepresented.affinePointsEquiv (VectorGroup.functor (CommRingCat.of k) n)
    (VectorGroup.corepresentableBy (CommRingCat.of k) n) _).injective
  rw [VectorGroup.affinePointsEquiv_affinePoint]
  rfl

/-- Evaluation of a coordinate function at an affine point is its parameter. -/
theorem pointCoordinates_affinePoint_coordinateFunctions {A : Type u} [CommRing A]
    [Algebra k A] (t : Fin n → A) (j : Fin n) :
    pointCoordinates (VectorGroup.affinePoint (CommAlgCat.of (CommRingCat.of k) A) t :
      Points (VectorGroup.groupScheme (CommRingCat.of k) n).X A)
        (coordinateFunctions k n j) = t j := by
  have hv := pointsMap_universalPoint
    (VectorGroup.affinePoint (CommAlgCat.of (CommRingCat.of k) A) t :
      Points (VectorGroup.groupScheme (CommRingCat.of k) n).X A)
  rw [← affinePoint_coordinateFunctions, pointsMap_affinePoint] at hv
  exact congrFun (affinePoint_injective _ hv) j

theorem pointCoordinates_affinePoint_aeval {A : Type u} [CommRing A] [Algebra k A]
    (t : Fin n → A) (P : MvPolynomial (Fin n) k) :
    pointCoordinates (VectorGroup.affinePoint (CommAlgCat.of (CommRingCat.of k) A) t :
      Points (VectorGroup.groupScheme (CommRingCat.of k) n).X A)
        (MvPolynomial.aeval (coordinateFunctions k n) P) = MvPolynomial.aeval t P := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  exact congrArg (fun f => MvPolynomial.aeval f P)
    (funext fun i => pointCoordinates_affinePoint_coordinateFunctions t i)

/-- The coordinate functions generate the actual coordinate algebra. -/
theorem aeval_coordinateFunctions_surjective :
    Function.Surjective (MvPolynomial.aeval (R := k) (coordinateFunctions k n)) := by
  intro z
  refine ⟨pointCoordinates (VectorGroup.affinePoint
    (CommAlgCat.of (CommRingCat.of k) (MvPolynomial (Fin n) k)) MvPolynomial.X :
      Points (VectorGroup.groupScheme (CommRingCat.of k) n).X (MvPolynomial (Fin n) k)) z, ?_⟩
  rw [← AlgHom.comp_apply, ← pointCoordinates_naturality, pointsMap_affinePoint]
  simp only [MvPolynomial.aeval_X]
  rw [affinePoint_coordinateFunctions, coordinates_universalPoint, AlgHom.id_apply]

end Coordinates

/-! ### Eigenfunctions of the diagonal action -/

section Weights

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}

theorem characterValue_add {A : Type u} [CommRing A] [Algebra k A]
    (χ ψ : characterLattice S) (s : Lie.AffinePoints S.toGrp A) :
    Lie.characterValue (χ + ψ) s = Lie.characterValue χ s * Lie.characterValue ψ s := by
  unfold Lie.characterValue
  rw [← map_mul]
  exact congrArg _ (comp_groupHom_add s χ ψ)

variable {V : Over (Spec (CommRingCat.of k))} [IsAffineHom V.hom] (a : PointedAction S V)

theorem characterValue_zero {A : Type u} [CommRing A] [Algebra k A]
    (s : Lie.AffinePoints S.toGrp A) : Lie.characterValue (0 : characterLattice S) s = 1 := by
  unfold Lie.characterValue
  rw [comp_groupHom_zero]
  exact map_one _

theorem one_mem_weightSpace : (1 : Coord V) ∈ PointedCoordinateWeights.weightSpace a 0 := by
  intro A _ _ s v
  rw [map_one, map_one, characterValue_zero, Units.val_one, one_mul]

theorem mul_mem_weightSpace {χ ψ : characterLattice S} {z z' : Coord V}
    (hz : z ∈ PointedCoordinateWeights.weightSpace a χ)
    (hz' : z' ∈ PointedCoordinateWeights.weightSpace a ψ) :
    z * z' ∈ PointedCoordinateWeights.weightSpace a (χ + ψ) := by
  intro A _ _ s v
  rw [map_mul, map_mul, hz A s v, hz' A s v, characterValue_add, Units.val_mul]
  ring

theorem pow_mem_weightSpace {χ : characterLattice S} {z : Coord V}
    (hz : z ∈ PointedCoordinateWeights.weightSpace a χ) (e : ℕ) :
    z ^ e ∈ PointedCoordinateWeights.weightSpace a (e • χ) := by
  induction e with
  | zero =>
    rw [pow_zero, zero_nsmul]
    exact one_mem_weightSpace a
  | succ e ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_weightSpace a ih hz

variable {n : ℕ} (u : Fin n → characterLattice S)

theorem coordinateFunctions_mem_weightSpace (i : Fin n) :
    coordinateFunctions k n i ∈
      PointedCoordinateWeights.weightSpace (PointedAction.ofGroup (diagonalAction u)) (u i) := by
  intro A _ _ s v
  obtain ⟨t, rfl⟩ := VectorGroup.affinePoint_surjective (CommAlgCat.of (CommRingCat.of k) A) v
  rw [PointedAction.ofGroup_act, diagonalAction_affinePoint,
    pointCoordinates_affinePoint_coordinateFunctions,
    pointCoordinates_affinePoint_coordinateFunctions]

/-- A monomial has the corresponding nonnegative combination of the characters as
its weight. -/
theorem aeval_monomial_mem_weightSpace (m : Fin n →₀ ℕ) :
    MvPolynomial.aeval (coordinateFunctions k n) (MvPolynomial.monomial m (1 : k)) ∈
      PointedCoordinateWeights.weightSpace (PointedAction.ofGroup (diagonalAction u))
        (Finsupp.linearCombination ℕ u m) := by
  induction m using Finsupp.induction_linear with
  | zero =>
    rw [← MvPolynomial.one_def, map_one, map_zero]
    exact one_mem_weightSpace _
  | add f g hf hg =>
    rw [show MvPolynomial.monomial (f + g) (1 : k) =
        MvPolynomial.monomial f 1 * MvPolynomial.monomial g 1 by
      rw [MvPolynomial.monomial_mul_monomial, one_mul], map_mul, map_add]
    exact mul_mem_weightSpace _ hf hg
  | single i e =>
    rw [← MvPolynomial.X_pow_eq_monomial, map_pow, MvPolynomial.aeval_X,
      Finsupp.linearCombination_single]
    exact pow_mem_weightSpace _ (coordinateFunctions_mem_weightSpace u i) e

end Weights

/-! ### Independent weights of linear coordinates -/

section Independence

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))} {r : ℕ}
  (w : Fin r → characterLattice S)

/-- For linearly independent weights, the only eigenfunctions of the weight of a
coordinate are the multiples of that coordinate. -/
theorem eq_smul_coordinateFunctions (hS : IsSplitTorus S.toGrp) (hw : LinearIndependent ℤ w)
    (j : Fin r) {F : Coord (VectorGroup.groupScheme (CommRingCat.of k) r).X}
    (hF : F ∈ PointedCoordinateWeights.weightSpace
      (PointedAction.ofGroup (diagonalAction w)) (w j)) :
    ∃ c : k, F = c • coordinateFunctions k r j := by
  classical
  have hind : iSupIndep (PointedCoordinateWeights.weightSpace
      (PointedAction.ofGroup (diagonalAction w))) :=
    (pointedCoordinateDecomposition k S hS _
      (PointedAction.ofGroup (diagonalAction w))).1.submodule_iSupIndep
  have hwN : LinearIndependent ℕ w := hw.restrict_scalars (by
    intro x y hxy
    simpa using hxy)
  obtain ⟨P, rfl⟩ := aeval_coordinateFunctions_surjective (k := k) (n := r) F
  refine ⟨P.coeff (Finsupp.single j 1), ?_⟩
  set c := P.coeff (Finsupp.single j 1) with hc
  set Q := P - MvPolynomial.monomial (Finsupp.single j 1) c with hQ
  have hmono : MvPolynomial.aeval (coordinateFunctions k r)
      (MvPolynomial.monomial (Finsupp.single j 1) c) = c • coordinateFunctions k r j := by
    rw [← MvPolynomial.C_mul_X_eq_monomial, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.aeval_X, Algebra.smul_def]
  have hQmem : MvPolynomial.aeval (coordinateFunctions k r) Q ∈
      PointedCoordinateWeights.weightSpace (PointedAction.ofGroup (diagonalAction w)) (w j) := by
    rw [hQ, map_sub, hmono]
    exact Submodule.sub_mem _ hF
      (Submodule.smul_mem _ c (coordinateFunctions_mem_weightSpace w j))
  have hQsup : MvPolynomial.aeval (coordinateFunctions k r) Q ∈
      ⨆ (χ) (_ : χ ≠ w j), PointedCoordinateWeights.weightSpace
        (PointedAction.ofGroup (diagonalAction w)) χ := by
    rw [Q.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    have hm' : m ≠ Finsupp.single j 1 := by
      rintro rfl
      apply MvPolynomial.mem_support_iff.mp hm
      simp only [hQ, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, ↓reduceIte, hc,
        sub_self]
    have hne : Finsupp.linearCombination ℕ w m ≠ w j := by
      intro h
      apply hm'
      apply hwN
      rw [h, Finsupp.linearCombination_single, one_smul]
    have hsmul : MvPolynomial.aeval (coordinateFunctions k r)
        (MvPolynomial.monomial m (Q.coeff m)) =
        Q.coeff m • MvPolynomial.aeval (coordinateFunctions k r)
          (MvPolynomial.monomial m (1 : k)) := by
      rw [← map_smul (MvPolynomial.aeval (coordinateFunctions k r)) (Q.coeff m)
        (MvPolynomial.monomial m (1 : k)), MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hsmul]
    exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem (Finsupp.linearCombination ℕ w m)
      (Submodule.mem_iSup_of_mem hne (aeval_monomial_mem_weightSpace w m)))
  have h0 : MvPolynomial.aeval (coordinateFunctions k r) Q = 0 :=
    Submodule.disjoint_def.mp (hind (w j)) _ hQmem hQsup
  have hPQ : P = Q + MvPolynomial.monomial (Finsupp.single j 1) c := by
    rw [hQ, sub_add_cancel]
  rw [hPQ, map_add, h0, zero_add, hmono]

end Independence

/-! ### Surjective coordinate pullback -/

section ClosedImmersion

variable {k : Type u} [Field k]

/-- Surjective actual coordinate pullback between affine schemes over a field
gives a closed immersion. -/
theorem isClosedImmersion_of_pullback_surjective {V W : Over (Spec (CommRingCat.of k))}
    [IsAffineHom V.hom] [IsAffineHom W.hom] (f : V ⟶ W)
    (hf : Function.Surjective (PointedCoordinateWeights.pullback f)) :
    IsClosedImmersion f.left := by
  have hleft := congrArg CommaMorphism.left (algSpec_map_pullback f)
  simp only [Over.comp_left, algSpec_map_left, Quiver.Hom.unop_op] at hleft
  set ψ := ((commAlgCatEquivUnder (CommRingCat.of k)).functor.map
    (CommAlgCat.ofHom (PointedCoordinateWeights.pullback f))).right
  have hs : Function.Surjective ψ := hf
  have : IsClosedImmersion (Spec.map ψ) := IsClosedImmersion.spec_of_surjective ψ hs
  have h1 : IsClosedImmersion ((coordinateIso V).hom.left ≫ f.left) := by
    rw [← hleft]
    infer_instance
  have hf' : f.left = inv (coordinateIso V).hom.left ≫ ((coordinateIso V).hom.left ≫ f.left) := by
    rw [IsIso.inv_hom_id_assoc]
  rw [hf']
  infer_instance

end ClosedImmersion

/-! ### The ordered product -/

section Product

/-- In a monoid, an ordered product whose factors are trivial away from one index
is that factor. -/
theorem list_prod_ofFn_eq_of_ne {M : Type*} [Monoid M] {r : ℕ} (f : Fin r → M) (j : Fin r)
    (hf : ∀ i, i ≠ j → f i = 1) : (List.ofFn f).prod = f j := by
  induction r with
  | zero => exact j.elim0
  | succ r ih =>
    rw [List.ofFn_succ, List.prod_cons]
    cases j using Fin.cases with
    | zero =>
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hf _ (Fin.succ_ne_zero i)
    | succ j =>
      rw [hf 0 (Fin.succ_ne_zero j).symm, one_mul]
      exact ih (fun i => f i.succ) j fun i hi => hf _ fun h => hi (Fin.succ_injective _ h)

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {S : CommGroupScheme (Spec (CommRingCat.of k))} (b : AutomorphicAction S.toGrp G) {r : ℕ}
  (y : Fin r → (VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G))
  (w : Fin r → characterLattice S)

theorem scalarPoint_zero (T : Over (Spec (CommRingCat.of k))) :
    VectorGroup.scalarPoint (CommRingCat.of k) T 0 = 1 :=
  VectorGroup.points_ext fun i => by
    rw [VectorGroup.coordinates_scalarPoint, map_one]
    rfl

/-- On an affine test, the scalar point is the affine point of its parameter. -/
theorem scalarPoint_affine (A : Type u) [CommRing A] [Algebra k A] (c : A) :
    VectorGroup.scalarPoint (CommRingCat.of k)
        ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) A)))
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c) =
      VectorGroup.affinePoint (CommAlgCat.of (CommRingCat.of k) A) (fun _ : Fin 1 => c) :=
  VectorGroup.points_ext fun i => by
    rw [VectorGroup.coordinates_scalarPoint, vectorCoordinates_affinePoint]

theorem point_single (j : Fin r) {T : Over (Spec (CommRingCat.of k))} (c : Γ(T.left, ⊤)) :
    point y T (Pi.single j c) = VectorGroup.scalarPoint (CommRingCat.of k) T c ≫ (y j).hom.hom := by
  rw [point, list_prod_ofFn_eq_of_ne _ j]
  · rw [Pi.single_eq_same]
  · intro i hi
    rw [Pi.single_eq_of_ne hi, scalarPoint_zero, MonObj.one_comp]

theorem point_zero {T : Over (Spec (CommRingCat.of k))} :
    point y T 0 = 1 := by
  rw [point, List.prod_eq_one]
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  rw [Pi.zero_apply, scalarPoint_zero, MonObj.one_comp]

variable {w}

/-- The supplied factor equivariance gives equivariance of the ordered formula. -/
theorem act_point
    (hy : ∀ (i : Fin r) (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X)
      (c : Γ(T.left, ⊤)),
      b.act s (VectorGroup.scalarPoint (CommRingCat.of k) T c ≫ (y i).hom.hom) =
        VectorGroup.scalarPoint (CommRingCat.of k) T
          (VectorGroup.charValue (w i) T s * c) ≫ (y i).hom.hom)
    {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S.X) (c : Fin r → Γ(T.left, ⊤)) :
    b.act s (point y T c) = point y T (fun i => VectorGroup.charValue (w i) T s * c i) := by
  change b.pointAut T s (point y T c) = _
  rw [point, map_list_prod, List.map_ofFn, point]
  exact congrArg List.prod (congrArg List.ofFn (funext fun i => hy i T s (c i)))

/-- The ordered product is equivariant for the diagonal action with the supplied
weights and preserves the identity. -/
theorem morphism_isPointedEquivariant
    (hy : ∀ (i : Fin r) (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X)
      (c : Γ(T.left, ⊤)),
      b.act s (VectorGroup.scalarPoint (CommRingCat.of k) T c ≫ (y i).hom.hom) =
        VectorGroup.scalarPoint (CommRingCat.of k) T
          (VectorGroup.charValue (w i) T s * c) ≫ (y i).hom.hom) :
    IsPointedEquivariant (PointedAction.ofGroup (diagonalAction w)) (PointedAction.ofGroup b)
      (morphism y) := by
  refine ⟨fun T s v => ?_, ?_⟩
  · rw [PointedAction.ofGroup_act, PointedAction.ofGroup_act, comp_morphism, comp_morphism,
      act_point b y hy, diagonalAction_act, coordinates_diagonalPointAction]
  · change η[(VectorGroup.groupScheme (CommRingCat.of k) r).X] ≫ morphism y = η[G.X]
    rw [MonObj.one_eq_one (VectorGroup.groupScheme (CommRingCat.of k) r).X,
      MonObj.one_eq_one G.X, comp_morphism, map_one]
    exact point_zero y

/-- Each supplied factor is equivariant for the action of its weight on the
additive group. -/
theorem factor_isPointedEquivariant
    (hy : ∀ (i : Fin r) (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X)
      (c : Γ(T.left, ⊤)),
      b.act s (VectorGroup.scalarPoint (CommRingCat.of k) T c ≫ (y i).hom.hom) =
        VectorGroup.scalarPoint (CommRingCat.of k) T
          (VectorGroup.charValue (w i) T s * c) ≫ (y i).hom.hom) (j : Fin r) :
    IsPointedEquivariant (PointedAction.ofGroup (diagonalAction fun _ : Fin 1 => w j))
      (PointedAction.ofGroup b) (y j).hom.hom := by
  refine ⟨fun T s v => ?_, IsMonHom.one_hom _⟩
  obtain ⟨c, rfl⟩ : ∃ c, v = VectorGroup.scalarPoint (CommRingCat.of k) T c :=
    ⟨(VectorGroup.coordinates (CommRingCat.of k) 1 T v).toAdd 0,
      VectorGroup.points_ext fun i => by
        rw [VectorGroup.coordinates_scalarPoint, Subsingleton.elim i 0]⟩
  rw [PointedAction.ofGroup_act, PointedAction.ofGroup_act, hy j T s c]
  congr 1
  apply VectorGroup.points_ext
  intro i
  rw [diagonalAction_act, coordinates_diagonalPointAction]
  beta_reduce
  rw [VectorGroup.coordinates_scalarPoint, VectorGroup.coordinates_scalarPoint]

end Product

/-! ### Assembly -/

section Assembly

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  (b : AutomorphicAction S.toGrp G) {r : ℕ}
  (y : Fin r → (VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G))
  {w : Fin r → characterLattice S}

/-- The coordinate of a closed factor of weight `w j` lifts to a function on the
group of the same weight. -/
theorem exists_lift (hS : IsSplitTorus S.toGrp) (hcl : ∀ i, IsClosedSubgroup (y i))
    (hy : ∀ (i : Fin r) (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X)
      (c : Γ(T.left, ⊤)),
      b.act s (VectorGroup.scalarPoint (CommRingCat.of k) T c ≫ (y i).hom.hom) =
        VectorGroup.scalarPoint (CommRingCat.of k) T
          (VectorGroup.charValue (w i) T s * c) ≫ (y i).hom.hom) (j : Fin r) :
    ∃ g ∈ PointedCoordinateWeights.weightSpace (PointedAction.ofGroup b) (w j),
      PointedCoordinateWeights.pullback (y j).hom.hom g = coordinateFunctions k 1 0 := by
  have h := (closedImmersionPullback k S hS (VectorGroup.groupScheme (CommRingCat.of k) 1).X
    G.X (PointedAction.ofGroup (diagonalAction fun _ : Fin 1 => w j))
    (PointedAction.ofGroup b) (y j).hom.hom (factor_isPointedEquivariant b y hy j)
    (hcl j)).2.2.1 (w j)
  have hmem : coordinateFunctions k 1 0 ∈ (PointedCoordinateWeights.weightSpace
      (PointedAction.ofGroup b) (w j)).map
        (PointedCoordinateWeights.pullback (y j).hom.hom).toLinearMap := by
    rw [h]
    exact coordinateFunctions_mem_weightSpace (fun _ : Fin 1 => w j) 0
  obtain ⟨g, hg, hgx⟩ := hmem
  exact ⟨g, hg, hgx⟩

omit [IsAffineHom G.X.hom] in
/-- The ordered product sends the `j`-th standard rational point to the image of
the unit parameter under the `j`-th factor. -/
theorem affinePoint_single_comp_morphism (j : Fin r) :
    VectorGroup.affinePoint (CommAlgCat.of (CommRingCat.of k) k) (Pi.single j (1 : k)) ≫
        morphism y =
      VectorGroup.affinePoint (CommAlgCat.of (CommRingCat.of k) k) (fun _ : Fin 1 => (1 : k)) ≫
        (y j).hom.hom := by
  rw [comp_morphism, ← scalarPoint_affine, ← point_single y j]
  congr 1
  funext i
  rw [vectorCoordinates_affinePoint]
  beta_reduce
  by_cases hi : i = j
  · subst hi
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, map_zero]

/-- The lifted coordinate pulls back to the corresponding coordinate of standard
affine space. -/
theorem pullback_lift_eq (hS : IsSplitTorus S.toGrp) (hw : LinearIndependent ℤ w)
    (hy : ∀ (i : Fin r) (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X)
      (c : Γ(T.left, ⊤)),
      b.act s (VectorGroup.scalarPoint (CommRingCat.of k) T c ≫ (y i).hom.hom) =
        VectorGroup.scalarPoint (CommRingCat.of k) T
          (VectorGroup.charValue (w i) T s * c) ≫ (y i).hom.hom) (j : Fin r)
    {g : Coord G.X} (hg : g ∈ PointedCoordinateWeights.weightSpace (PointedAction.ofGroup b) (w j))
    (hgx : PointedCoordinateWeights.pullback (y j).hom.hom g = coordinateFunctions k 1 0) :
    PointedCoordinateWeights.pullback (morphism y) g = coordinateFunctions k r j := by
  obtain ⟨c, hc⟩ := eq_smul_coordinateFunctions w hS hw j
    (pullback_mem_weightSpace _ _ (morphism y) (morphism_isPointedEquivariant b y hy) (w j) hg)
  have h1 : pointCoordinates (VectorGroup.affinePoint (CommAlgCat.of (CommRingCat.of k) k)
      (Pi.single j (1 : k)) : Points (VectorGroup.groupScheme (CommRingCat.of k) r).X k)
        (PointedCoordinateWeights.pullback (morphism y) g) = 1 := by
    rw [← AlgHom.comp_apply, ← coordinates_comp, affinePoint_single_comp_morphism,
      coordinates_comp, AlgHom.comp_apply, hgx, pointCoordinates_affinePoint_coordinateFunctions]
  have h2 : pointCoordinates (VectorGroup.affinePoint (CommAlgCat.of (CommRingCat.of k) k)
      (Pi.single j (1 : k)) : Points (VectorGroup.groupScheme (CommRingCat.of k) r).X k)
        (c • coordinateFunctions k r j) = c := by
    rw [map_smul, pointCoordinates_affinePoint_coordinateFunctions, Pi.single_eq_same,
      smul_eq_mul, mul_one]
  have hc1 : c = 1 := by
    rw [← h2, ← hc, h1]
  rw [hc, hc1, one_smul]

/-- An ordered product of closed additive embeddings of independent weights for
an actual split-torus action is a closed immersion of schemes. -/
theorem _root_.Langlands.GroupScheme.independentWeightProductImmersion :
    IndependentWeightProductImmersionStatement.{u} := by
  intro k _ G _ S hS b r y w hw hcl hy
  choose g hg hgx using exists_lift b y hS hcl hy
  have hφ : (PointedCoordinateWeights.pullback (morphism y)).comp (MvPolynomial.aeval g) =
      MvPolynomial.aeval (coordinateFunctions k r) :=
    MvPolynomial.algHom_ext fun j => by
      rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
        pullback_lift_eq b y hS hw hy j (hg j) (hgx j)]
  apply isClosedImmersion_of_pullback_surjective
  intro z
  obtain ⟨P, rfl⟩ := aeval_coordinateFunctions_surjective (k := k) (n := r) z
  exact ⟨MvPolynomial.aeval g P, by rw [← AlgHom.comp_apply, hφ]⟩

end Assembly

end Langlands.GroupScheme.IndependentWeightProduct
