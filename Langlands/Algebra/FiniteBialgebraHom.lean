import Langlands.TauCeti.RingTheory.WeilRestriction.Basic
import Mathlib.RingTheory.Bialgebra.TensorProduct
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.FiniteStability

/-! # Bialgebra maps into a finite free scalar extension

Let `A` and `P` be commutative `R`-bialgebras. For an `R`-algebra `C`, an algebra map
`f : A → C ⊗[R] P` is a *Hopf point* if it is compatible with comultiplication and counit.
These are exactly the `C`-bialgebra maps `C ⊗[R] A → C ⊗[R] P` (`bialgHomEquiv`). When `A` is
finitely presented and `P` is finite free, the Hopf points are represented by a finitely
presented `R`-algebra `HomAlgebra R A P`, a quotient of the Weil restriction of `P ⊗[R] A`
along `P`. -/

noncomputable section

universe u v w

open TensorProduct

namespace Langlands.FiniteBialgebraHom

variable (R : Type u) [CommRing R] {A P : Type u} [CommRing A] [CommRing P]
  [Bialgebra R A] [Bialgebra R P]

section Conditions

variable {C : Type v} [CommRing C] [Algebra R C]

/-- Comultiplication of `P` applied after `f`. -/
def comulLeft (f : A →ₐ[R] C ⊗[R] P) : A →ₐ[R] C ⊗[R] (P ⊗[R] P) :=
  (Algebra.TensorProduct.map (AlgHom.id R C) (Bialgebra.comulAlgHom R P)).comp f

/-- The first tensor-factor inclusion `C ⊗ P → C ⊗ (P ⊗ P)`. -/
abbrev inclFirst : C ⊗[R] P →ₐ[R] C ⊗[R] (P ⊗[R] P) :=
  Algebra.TensorProduct.map (AlgHom.id R C)
    (Algebra.TensorProduct.includeLeft : P →ₐ[R] P ⊗[R] P)

/-- The second tensor-factor inclusion `C ⊗ P → C ⊗ (P ⊗ P)`. -/
abbrev inclSecond : C ⊗[R] P →ₐ[R] C ⊗[R] (P ⊗[R] P) :=
  Algebra.TensorProduct.map (AlgHom.id R C) Algebra.TensorProduct.includeRight

/-- The product of the two factors of `f ⊗ f`, applied after comultiplication of `A`. -/
def comulRight (f : A →ₐ[R] C ⊗[R] P) : A →ₐ[R] C ⊗[R] (P ⊗[R] P) :=
  (Algebra.TensorProduct.lift ((inclFirst R).comp f) ((inclSecond R).comp f)
    (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom R A)

/-- The counit of `P` applied after `f`. -/
def counitMap (f : A →ₐ[R] C ⊗[R] P) : A →ₐ[R] C :=
  ((Algebra.TensorProduct.rid R R C).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id R C) (Bialgebra.counitAlgHom R P))).comp f

/-- An algebra map `A → C ⊗[R] P` compatible with comultiplication and counit. -/
def IsHopfPoint (f : A →ₐ[R] C ⊗[R] P) : Prop :=
  comulLeft R f = comulRight R f ∧
    counitMap R f = (Algebra.ofId R C).comp (Bialgebra.counitAlgHom R A)

variable {D : Type w} [CommRing D] [Algebra R D]

/-- Push a point along a coefficient algebra map. -/
abbrev pushPoint (g : C →ₐ[R] D) (f : A →ₐ[R] C ⊗[R] P) : A →ₐ[R] D ⊗[R] P :=
  (Algebra.TensorProduct.map g (AlgHom.id R P)).comp f

theorem pushPoint_pushPoint {E : Type*} [CommRing E] [Algebra R E] (h : D →ₐ[R] E)
    (g : C →ₐ[R] D) (f : A →ₐ[R] C ⊗[R] P) :
    pushPoint R h (pushPoint R g f) = pushPoint R (h.comp g) f := by
  rw [pushPoint, pushPoint, pushPoint, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    AlgHom.comp_id]

theorem pushPoint_id (f : A →ₐ[R] C ⊗[R] P) : pushPoint R (AlgHom.id R C) f = f := by
  rw [pushPoint, Algebra.TensorProduct.map_id, AlgHom.id_comp]

theorem comulLeft_pushPoint (g : C →ₐ[R] D) (f : A →ₐ[R] C ⊗[R] P) :
    comulLeft R (pushPoint R g f) =
      (Algebra.TensorProduct.map g (AlgHom.id R (P ⊗[R] P))).comp (comulLeft R f) := by
  rw [comulLeft, comulLeft, pushPoint, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc,
    ← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp]
  simp

@[simp]
theorem inclFirst_map (g : C →ₐ[R] D) (x : C ⊗[R] P) :
    inclFirst R (Algebra.TensorProduct.map g (AlgHom.id R P) x) =
      Algebra.TensorProduct.map g (AlgHom.id R (P ⊗[R] P)) (inclFirst R x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c q => simp
  | add x y hx hy => simp only [map_add, hx, hy]

@[simp]
theorem inclSecond_map (g : C →ₐ[R] D) (x : C ⊗[R] P) :
    inclSecond R (Algebra.TensorProduct.map g (AlgHom.id R P) x) =
      Algebra.TensorProduct.map g (AlgHom.id R (P ⊗[R] P)) (inclSecond R x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c q => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem comulRight_pushPoint (g : C →ₐ[R] D) (f : A →ₐ[R] C ⊗[R] P) :
    comulRight R (pushPoint R g f) =
      (Algebra.TensorProduct.map g (AlgHom.id R (P ⊗[R] P))).comp (comulRight R f) := by
  have key : Algebra.TensorProduct.lift ((inclFirst R).comp (pushPoint R g f))
      ((inclSecond R).comp (pushPoint R g f)) (fun _ _ => Commute.all _ _) =
      (Algebra.TensorProduct.map g (AlgHom.id R (P ⊗[R] P))).comp
        (Algebra.TensorProduct.lift ((inclFirst R).comp f) ((inclSecond R).comp f)
          (fun _ _ => Commute.all _ _)) :=
    Algebra.TensorProduct.ext' fun a b => by
      simp only [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, inclFirst_map,
        inclSecond_map, map_mul]
  rw [comulRight, comulRight, key, AlgHom.comp_assoc]

theorem counitMap_pushPoint (g : C →ₐ[R] D) (f : A →ₐ[R] C ⊗[R] P) :
    counitMap R (pushPoint R g f) = g.comp (counitMap R f) := by
  rw [counitMap, counitMap, pushPoint, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
  congr 1
  apply Algebra.TensorProduct.ext
  · ext c
    simp
  · ext p
    simp [Algebra.smul_def]

theorem IsHopfPoint.pushPoint {f : A →ₐ[R] C ⊗[R] P} (hf : IsHopfPoint R f)
    (g : C →ₐ[R] D) : IsHopfPoint R (pushPoint R g f) := by
  refine ⟨?_, ?_⟩
  · rw [comulLeft_pushPoint, comulRight_pushPoint, hf.1]
  · rw [counitMap_pushPoint, hf.2, ← AlgHom.comp_assoc]
    congr 1
    exact AlgHom.ext fun r => g.commutes r

end Conditions

section Coordinates

variable {C : Type v} [CommRing C] [Algebra R C] {D : Type w} [CommRing D] [Algebra R D]
  {Q : Type u} [CommRing Q] [Algebra R Q] {ι : Type*} (b : Module.Basis ι R Q)

/-- Coordinates of a scalar extension commute with a coefficient algebra map. -/
theorem basis_repr_map (g : C →ₐ[R] D) (x : C ⊗[R] Q) (i : ι) :
    (Algebra.TensorProduct.basis D b).repr (Algebra.TensorProduct.map g (AlgHom.id R Q) x) i =
      g ((Algebra.TensorProduct.basis C b).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul c q => simp
  | add x y hx hy => simp [hx, hy]

end Coordinates

section BaseChange

variable {C : Type v} [CommRing C] [Algebra R C]

variable (C P) in
/-- The comparison `(C ⊗[R] P) ⊗[C] (C ⊗[R] P) ≃ C ⊗[R] (P ⊗[R] P)`. -/
def tensorSquareEquiv : (C ⊗[R] P) ⊗[C] (C ⊗[R] P) ≃ₐ[C] C ⊗[R] (P ⊗[R] P) :=
  (Algebra.TensorProduct.cancelBaseChange R C C (C ⊗[R] P) P).trans
    (Algebra.TensorProduct.assoc R R C C P P)

theorem tensorSquareEquiv_tmul (x y : C ⊗[R] P) :
    tensorSquareEquiv R P C (x ⊗ₜ[C] y) = inclFirst R x * inclSecond R y := by
  induction x using TensorProduct.inductionOn with
  | tmul c p =>
    induction y using TensorProduct.inductionOn with
    | tmul c' p' =>
      simp only [tensorSquareEquiv, AlgEquiv.trans_apply,
        Algebra.TensorProduct.cancelBaseChange_tmul, inclFirst, inclSecond,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        one_mul]
      rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.assoc_tmul, mul_comm]
    | add y y' hy hy' => simp only [TensorProduct.tmul_add, map_add, mul_add, hy, hy']
  | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, add_mul, hx, hx']

theorem tensorSquareEquiv_comul (x : C ⊗[R] P) :
    tensorSquareEquiv R P C (Bialgebra.comulAlgHom C (C ⊗[R] P) x) =
      Algebra.TensorProduct.map (AlgHom.id R C) (Bialgebra.comulAlgHom R P) x := by
  induction x using TensorProduct.inductionOn with
  | tmul c p =>
    rw [Bialgebra.comulAlgHom_apply, TensorProduct.comul_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, Bialgebra.comulAlgHom_apply]
    generalize Coalgebra.comul (R := R) p = z
    induction z using TensorProduct.inductionOn with
    | tmul p₁ p₂ =>
      change tensorSquareEquiv R P C
        (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R C R C C C P P
          (((1 : C) ⊗ₜ[C] c) ⊗ₜ (p₁ ⊗ₜ p₂))) = _
      rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, tensorSquareEquiv_tmul]
      simp
    | add z z' hz hz' => simp only [TensorProduct.tmul_add, map_add, hz, hz']
  | add x x' hx hx' => simp only [map_add, hx, hx']

theorem counitAlgHom_scalarExtension (x : C ⊗[R] P) :
    Bialgebra.counitAlgHom C (C ⊗[R] P) x =
      (Algebra.TensorProduct.rid R R C)
        (Algebra.TensorProduct.map (AlgHom.id R C) (Bialgebra.counitAlgHom R P) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c p => simp [Algebra.smul_def, mul_comm]
  | add x x' hx hx' => simp only [map_add, hx, hx']

/-- The restriction to `A` of a `C`-algebra map out of `C ⊗[R] A`. -/
abbrev restrictPoint (φ : C ⊗[R] A →ₐ[C] C ⊗[R] P) : A →ₐ[R] C ⊗[R] P :=
  (AlgHom.liftEquiv R C A (C ⊗[R] P)).symm φ

theorem tensorSquareEquiv_map_comul (φ : C ⊗[R] A →ₐ[C] C ⊗[R] P) (a : A) :
    tensorSquareEquiv R P C (Algebra.TensorProduct.map φ φ
        (Bialgebra.comulAlgHom C (C ⊗[R] A) ((1 : C) ⊗ₜ a))) =
      comulRight R (restrictPoint R φ) a := by
  rw [Bialgebra.comulAlgHom_apply, TensorProduct.comul_tmul, comulRight, AlgHom.comp_apply,
    Bialgebra.comulAlgHom_apply]
  generalize Coalgebra.comul (R := R) a = z
  induction z using TensorProduct.inductionOn with
  | tmul a₁ a₂ =>
    change tensorSquareEquiv R P C (Algebra.TensorProduct.map φ φ
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R C R C C C A A
        (((1 : C) ⊗ₜ[C] (1 : C)) ⊗ₜ (a₁ ⊗ₜ a₂)))) = _
    rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
      Algebra.TensorProduct.map_tmul, tensorSquareEquiv_tmul, Algebra.TensorProduct.lift_tmul]
    rfl
  | add z z' hz hz' => simp only [TensorProduct.tmul_add, map_add, hz, hz']

theorem tensorSquareEquiv_comul_apply (φ : C ⊗[R] A →ₐ[C] C ⊗[R] P) (a : A) :
    tensorSquareEquiv R P C (Bialgebra.comulAlgHom C (C ⊗[R] P) (φ ((1 : C) ⊗ₜ a))) =
      comulLeft R (restrictPoint R φ) a :=
  tensorSquareEquiv_comul R _

theorem algebraTensorProductMap_eq_map (φ : C ⊗[R] A →ₐ[C] C ⊗[R] P)
    (z : (C ⊗[R] A) ⊗[C] (C ⊗[R] A)) :
    Algebra.TensorProduct.map φ φ z =
      TensorProduct.map (φ : C ⊗[R] A →ₗ[C] C ⊗[R] P) (φ : C ⊗[R] A →ₗ[C] C ⊗[R] P) z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

theorem isHopfPoint_restrictPoint (φ : C ⊗[R] A →ₐc[C] C ⊗[R] P) :
    IsHopfPoint R (restrictPoint R (φ : C ⊗[R] A →ₐ[C] C ⊗[R] P)) := by
  refine ⟨AlgHom.ext fun a => ?_, AlgHom.ext fun a => ?_⟩
  · rw [← tensorSquareEquiv_comul_apply, ← tensorSquareEquiv_map_comul,
      algebraTensorProductMap_eq_map, Bialgebra.comulAlgHom_apply, Bialgebra.comulAlgHom_apply]
    congr 1
    exact (CoalgHomClass.map_comp_comul_apply φ _).symm
  · have h := CoalgHomClass.counit_comp_apply φ ((1 : C) ⊗ₜ[R] a)
    rw [← Bialgebra.counitAlgHom_apply, counitAlgHom_scalarExtension] at h
    rw [counitMap, AlgHom.comp_apply, AlgHom.comp_apply]
    change (Algebra.TensorProduct.rid R R C)
      (Algebra.TensorProduct.map (AlgHom.id R C) (Bialgebra.counitAlgHom R P) (φ (1 ⊗ₜ a))) = _
    rw [h, TensorProduct.counit_tmul]
    simp [Algebra.smul_def]

/-- The `C`-algebra map out of `C ⊗[R] A` attached to a Hopf point is a bialgebra map. -/
def bialgHomOfHopfPoint (f : A →ₐ[R] C ⊗[R] P) (hf : IsHopfPoint R f) :
    C ⊗[R] A →ₐc[C] C ⊗[R] P :=
  BialgHom.ofAlgHom (AlgHom.liftEquiv R C A (C ⊗[R] P) f)
    (Algebra.TensorProduct.ext (Subsingleton.elim _ _) <| AlgHom.ext fun a => by
      have h := DFunLike.congr_fun hf.2 a
      simp only [counitMap, AlgHom.comp_apply] at h
      simp only [AlgHom.restrictScalars_apply, AlgHom.comp_apply,
        Algebra.TensorProduct.includeRight_apply, AlgHom.liftEquiv_tmul, one_smul,
        counitAlgHom_scalarExtension]
      rw [AlgEquiv.coe_toAlgHom] at h
      rw [h, Algebra.TensorProduct.map_tmul]
      simp [Algebra.smul_def])
    (Algebra.TensorProduct.ext (Subsingleton.elim _ _) <| AlgHom.ext fun a => by
      apply (tensorSquareEquiv R P C).injective
      have h1 := tensorSquareEquiv_map_comul R (AlgHom.liftEquiv R C A (C ⊗[R] P) f) a
      have h2 := tensorSquareEquiv_comul_apply R (AlgHom.liftEquiv R C A (C ⊗[R] P) f) a
      simp only [AlgHom.restrictScalars_apply, AlgHom.comp_apply,
        Algebra.TensorProduct.includeRight_apply]
      rw [h1, h2, restrictPoint, Equiv.symm_apply_apply, hf.1])

/-- Bialgebra maps `C ⊗[R] A → C ⊗[R] P` over `C` are exactly Hopf points `A → C ⊗[R] P`. -/
def bialgHomEquiv :
    (C ⊗[R] A →ₐc[C] C ⊗[R] P) ≃ {f : A →ₐ[R] C ⊗[R] P // IsHopfPoint R f} where
  toFun φ := ⟨restrictPoint R (φ : C ⊗[R] A →ₐ[C] C ⊗[R] P), isHopfPoint_restrictPoint R φ⟩
  invFun f := bialgHomOfHopfPoint R f.1 f.2
  left_inv φ := BialgHom.coe_toAlgHom_injective <|
    (AlgHom.liftEquiv R C A (C ⊗[R] P)).apply_symm_apply (φ : C ⊗[R] A →ₐ[C] C ⊗[R] P)
  right_inv f := Subtype.ext <| (AlgHom.liftEquiv R C A (C ⊗[R] P)).symm_apply_apply f.1

theorem bialgHomEquiv_apply_coe (φ : C ⊗[R] A →ₐc[C] C ⊗[R] P) (a : A) :
    (bialgHomEquiv R φ).1 a = φ ((1 : C) ⊗ₜ a) := rfl

end BaseChange

section Representing

variable (A P) [Module.Finite R P] [Module.Free R P] [Algebra.FinitePresentation R A]

/-- The Weil restriction of `P ⊗[R] A` along `P`: it represents algebra maps `A → C ⊗[R] P`. -/
abbrev Weil : Type u := TauCeti.Algebra.WeilRestriction R P (P ⊗[R] A)

/-- The universal algebra map `A → Weil ⊗[R] P`. -/
def weilPoint : A →ₐ[R] Weil R A P ⊗[R] P :=
  TauCeti.Algebra.WeilRestriction.tensorHomEquiv R P A _ (AlgHom.id R _)

variable {R A P} in
theorem tensorHomEquiv_eq {C : Type u} [CommRing C] [Algebra R C] (g : Weil R A P →ₐ[R] C) :
    TauCeti.Algebra.WeilRestriction.tensorHomEquiv R P A C g = pushPoint R g (weilPoint R A P) := by
  have h := TauCeti.Algebra.WeilRestriction.tensorHomEquiv_comp (AlgHom.id R (Weil R A P)) g
  rwa [AlgHom.comp_id] at h

/-- A chosen finite set of algebra generators of `A`. -/
def gens : Finset A := (Algebra.FiniteType.out (R := R) (A := A)).choose

theorem adjoin_gens : Algebra.adjoin R (gens R A : Set A) = ⊤ :=
  (Algebra.FiniteType.out (R := R) (A := A)).choose_spec

/-- The chosen basis of `P ⊗[R] P`. -/
abbrev basisPP := Module.Free.chooseBasis R (P ⊗[R] P)

/-- The coordinates, at the generators, of the comultiplication defect of the universal point. -/
def comulRelation (x : gens R A × Module.Free.ChooseBasisIndex R (P ⊗[R] P)) : Weil R A P :=
  (Algebra.TensorProduct.basis (Weil R A P) (basisPP R P)).repr
    (comulLeft R (weilPoint R A P) x.1 - comulRight R (weilPoint R A P) x.1) x.2

/-- The counit defect of the universal point at the generators. -/
def counitRelation (a : gens R A) : Weil R A P :=
  counitMap R (weilPoint R A P) a - algebraMap R _ (Bialgebra.counitAlgHom R A a)

/-- The ideal cutting out the Hopf points. -/
def relationIdeal : Ideal (Weil R A P) :=
  Ideal.span (Set.range (comulRelation R A P) ∪ Set.range (counitRelation R A P))

theorem relationIdeal_fg : (relationIdeal R A P).FG :=
  ⟨(Set.finite_range _ |>.union (Set.finite_range _)).toFinset, by
    rw [Set.Finite.coe_toFinset]; rfl⟩

variable {R A P} in
theorem isHopfPoint_pushPoint_iff {C : Type u} [CommRing C] [Algebra R C]
    (g : Weil R A P →ₐ[R] C) :
    IsHopfPoint R (pushPoint R g (weilPoint R A P)) ↔ relationIdeal R A P ≤ RingHom.ker g := by
  constructor
  · intro h
    rw [relationIdeal, Ideal.span_le]
    rintro _ (⟨x, rfl⟩ | ⟨a, rfl⟩)
    · have h1 := DFunLike.congr_fun (comulLeft_pushPoint R g (weilPoint R A P)) (x.1 : A)
      have h2 := DFunLike.congr_fun (comulRight_pushPoint R g (weilPoint R A P)) (x.1 : A)
      rw [AlgHom.comp_apply] at h1 h2
      rw [SetLike.mem_coe, RingHom.mem_ker, comulRelation, ← basis_repr_map, map_sub, ← h1, ← h2,
        h.1, sub_self, map_zero, Finsupp.coe_zero, Pi.zero_apply]
    · have h3 := DFunLike.congr_fun (counitMap_pushPoint R g (weilPoint R A P)) (a : A)
      rw [AlgHom.comp_apply] at h3
      rw [SetLike.mem_coe, RingHom.mem_ker, counitRelation, map_sub, AlgHom.commutes, ← h3, h.2,
        AlgHom.comp_apply, Algebra.ofId_apply, sub_self]
  · intro h
    have hJ : ∀ x ∈ relationIdeal R A P, g x = 0 := fun x hx => RingHom.mem_ker.mp (h hx)
    refine ⟨AlgHom.ext_of_adjoin_eq_top (adjoin_gens R A) fun a ha => ?_,
      AlgHom.ext_of_adjoin_eq_top (adjoin_gens R A) fun a ha => ?_⟩
    · rw [comulLeft_pushPoint, comulRight_pushPoint, ← sub_eq_zero, AlgHom.comp_apply,
        AlgHom.comp_apply, ← map_sub]
      apply (Algebra.TensorProduct.basis C (basisPP R P)).repr.injective
      ext i
      rw [basis_repr_map, map_zero, Finsupp.coe_zero, Pi.zero_apply]
      exact hJ _ (Ideal.subset_span (Or.inl ⟨(⟨a, ha⟩, i), rfl⟩))
    · rw [counitMap_pushPoint, AlgHom.comp_apply, AlgHom.comp_apply, ← sub_eq_zero]
      have := hJ _ (Ideal.subset_span (Or.inr ⟨⟨a, ha⟩, rfl⟩))
      rw [counitRelation, map_sub, AlgHom.commutes] at this
      rwa [Algebra.ofId_apply]

/-- The algebra representing Hopf points `A → C ⊗[R] P`. -/
abbrev HomAlgebra : Type u := Weil R A P ⧸ relationIdeal R A P

instance : Algebra.FinitePresentation R (HomAlgebra R A P) :=
  Algebra.FinitePresentation.quotient (relationIdeal_fg R A P)

/-- The universal Hopf point. -/
def universalPoint : A →ₐ[R] HomAlgebra R A P ⊗[R] P :=
  pushPoint R (Ideal.Quotient.mkₐ R _) (weilPoint R A P)

theorem isHopfPoint_universalPoint : IsHopfPoint R (universalPoint R A P) :=
  (isHopfPoint_pushPoint_iff _).2 fun x hx => by
    rw [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hx

/-- Algebra maps out of `HomAlgebra R A P` are exactly Hopf points. -/
def homEquiv (C : Type u) [CommRing C] [Algebra R C] :
    (HomAlgebra R A P →ₐ[R] C) ≃ {f : A →ₐ[R] C ⊗[R] P // IsHopfPoint R f} where
  toFun g := ⟨pushPoint R g (universalPoint R A P), (isHopfPoint_universalPoint R A P).pushPoint R g⟩
  invFun f := Ideal.Quotient.liftₐ _
    ((TauCeti.Algebra.WeilRestriction.tensorHomEquiv R P A C).symm f.1) (by
      have h := f.2
      rw [← Equiv.apply_symm_apply (TauCeti.Algebra.WeilRestriction.tensorHomEquiv R P A C) f.1,
        tensorHomEquiv_eq, isHopfPoint_pushPoint_iff] at h
      exact fun x hx => RingHom.mem_ker.mp (h hx))
  left_inv g := by
    apply Ideal.Quotient.algHom_ext
    dsimp only
    rw [Ideal.Quotient.liftₐ_comp, Equiv.symm_apply_eq, tensorHomEquiv_eq, universalPoint,
      pushPoint_pushPoint]
  right_inv f := by
    apply Subtype.ext
    dsimp only
    rw [universalPoint, pushPoint_pushPoint, Ideal.Quotient.liftₐ_comp, ← tensorHomEquiv_eq,
      Equiv.apply_symm_apply]

theorem homEquiv_apply {C : Type u} [CommRing C] [Algebra R C] (g : HomAlgebra R A P →ₐ[R] C) :
    (homEquiv R A P C g).1 = pushPoint R g (universalPoint R A P) := rfl

end Representing

end Langlands.FiniteBialgebraHom
