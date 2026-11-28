import Langlands.AlgebraicGeometry.AffineCechDeRham
import Mathlib.LinearAlgebra.Alternating.Curry

/-!
# Degree-two relative Čech–de Rham cohomology on an affine cover

This module extends `Langlands.AlgebraicGeometry.AffineCechDeRham` by one total degree.
It constructs the relative three-forms `⋀[A]^3 Ω[A⁄R]` of an algebra, their maps along
algebra homomorphisms, and the exterior differential `RelativeForms.dTwo` from two-forms
to three-forms, with `d(a db ∧ dc) = da ∧ db ∧ dc`, naturality, and `d ∘ d = 0` on one-forms.
On the ordered affine cover it adds the total term `C3`, the total differential `D2` with the
sign rule `∂ ⊕ (-1)^p d` already used for `D0` and `D1`, the identity `D2 ∘ D1 = 0`, and the
degree-two module `H2` of cocycles modulo boundaries. Overlap one-forms `ω` that form a Čech
cocycle and are relatively closed give the class `closedOverlapClass` of `(0, ω, 0)`.

The total differential follows Lan, *Arithmetic compactifications of PEL-type Shimura
varieties*, revised 14 March 2021, §2.1.6, pp. 129–130 and 132. The retained source is
`lan-2008-pel-thesis-revision-2021`, with SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.

The differential on two-forms is not obtained from an algebra-bilinear formula, since
`d(a x ∧ y)` involves `da`. Instead the alternating map
`(x, y) ↦ (x ∧ y, y ∧ dx - x ∧ dy)`, whose second component equals `dx ∧ y - x ∧ dy`, is
algebra-multilinear into pairs of two-forms and three-forms with the twisted action
`a • (ω, η) = (a ω, da ∧ ω + a η)`, and `dTwo` is the second component of its linear lift.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

namespace RelativeForms

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- Relative three-forms on an algebra are the third exterior power over that algebra. -/
abbrev Three (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :=
  ⋀[A]^3 Ω[A⁄R]

/-- The wedge product of three relative one-forms. -/
def wedgeThree (x y z : Ω[A⁄R]) : Three R A := exteriorPower.ιMulti A 3 ![x, y, z]

private lemma ιMulti_two_eq_wedge (v : Fin 2 → Ω[A⁄R]) :
    exteriorPower.ιMulti A 2 v = wedge (v 0) (v 1) := by
  rw [wedge]
  congr 1
  funext i
  fin_cases i <;> rfl

private lemma wedge_add_left' (x y z : Ω[A⁄R]) :
    wedge (x + y) z = wedge x z + wedge y z :=
  (exteriorPower.ιMulti A 2).map_vecCons_add ![z] x y

private lemma wedge_smul_left' (a : A) (x y : Ω[A⁄R]) :
    wedge (a • x) y = a • wedge x y :=
  (exteriorPower.ιMulti A 2).map_vecCons_smul ![y] a x

private lemma wedge_swap' (x y : Ω[A⁄R]) : wedge y x = -wedge x y := by
  have h : (![x, y] : Fin 2 → Ω[A⁄R]) ∘ Equiv.swap 0 1 = ![y, x] := by
    funext i
    fin_cases i <;> rfl
  simpa only [wedge, h] using
    (exteriorPower.ιMulti A 2).map_swap ![x, y] (by decide : (0 : Fin 2) ≠ 1)

private lemma wedge_add_right' (x y z : Ω[A⁄R]) :
    wedge x (y + z) = wedge x y + wedge x z := by
  rw [wedge_swap' (y + z) x, wedge_add_left', wedge_swap' x y, wedge_swap' x z,
    neg_add, neg_neg, neg_neg]

private lemma wedge_smul_right' (a : A) (x y : Ω[A⁄R]) :
    wedge x (a • y) = a • wedge x y := by
  rw [wedge_swap' (a • y) x, wedge_smul_left', wedge_swap' x y, smul_neg, neg_neg]

private lemma wedge_zero_right' (x : Ω[A⁄R]) : wedge x 0 = (0 : Two R A) := by
  simpa only [zero_smul] using wedge_smul_right' (0 : A) x x

private lemma wedge_self' (x : Ω[A⁄R]) : wedge x x = (0 : Two R A) :=
  (exteriorPower.ιMulti A 2).map_eq_zero_of_eq ![x, x] (i := 0) (j := 1) rfl (by decide)

/-- The exterior differential of an exact one-form vanishes. -/
@[simp]
lemma dOne_D (a : A) : dOne R A (KaehlerDifferential.D R A a) = 0 :=
  dOne_dZero a

/-- The Leibniz rule `d(a ω) = da ∧ ω + a dω` for the exterior differential on one-forms. -/
lemma dOne_smul (a : A) (ω : Ω[A⁄R]) :
    dOne R A (a • ω) = wedge (KaehlerDifferential.D R A a) ω + a • dOne R A ω := by
  obtain ⟨t, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective R A ω
  induction t using TensorProduct.inductionOn with
  | tmul b c =>
    rw [Derivation.tensorProductTo_tmul, smul_smul, dOne_smul_d, dOne_smul_d,
      (KaehlerDifferential.D R A).leibniz, wedge_add_left', wedge_smul_left', wedge_smul_left',
      wedge_smul_right']
    abel
  | add x y hx hy =>
    simp only [map_add, smul_add, hx, hy, wedge_add_right']
    abel

/-- The product `x ∧ ω` of a one-form and a two-form, bilinear over the algebra. -/
def wedgeOneTwo : Ω[A⁄R] →ₗ[A] Two R A →ₗ[A] Three R A :=
  (exteriorPower.alternatingMapLinearEquiv (R := A) (n := 2) (M := Ω[A⁄R])
    (N := Three R A)).toLinearMap ∘ₗ (exteriorPower.ιMulti A 3).curryLeft

@[simp]
lemma wedgeOneTwo_wedge (x y z : Ω[A⁄R]) :
    wedgeOneTwo x (wedge y z) = wedgeThree (R := R) x y z := by
  simp only [wedgeOneTwo, wedge, wedgeThree, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.curryLeft_apply_apply]

private lemma wedgeThree_swap01 (x y z : Ω[A⁄R]) :
    wedgeThree (R := R) y x z = -wedgeThree x y z := by
  have h : (![x, y, z] : Fin 3 → Ω[A⁄R]) ∘ Equiv.swap 0 1 = ![y, x, z] := by
    funext i
    fin_cases i <;> rfl
  simpa only [wedgeThree, h] using
    (exteriorPower.ιMulti A 3).map_swap ![x, y, z] (by decide : (0 : Fin 3) ≠ 1)

private lemma wedgeThree_swap12 (x y z : Ω[A⁄R]) :
    wedgeThree (R := R) x z y = -wedgeThree x y z := by
  have h : (![x, y, z] : Fin 3 → Ω[A⁄R]) ∘ Equiv.swap 1 2 = ![x, z, y] := by
    funext i
    fin_cases i <;> rfl
  simpa only [wedgeThree, h] using
    (exteriorPower.ιMulti A 3).map_swap ![x, y, z] (by decide : (1 : Fin 3) ≠ 2)

private lemma wedgeThree_cycle (x y z : Ω[A⁄R]) :
    wedgeThree (R := R) z x y = wedgeThree x y z := by
  rw [wedgeThree_swap01 x z y, wedgeThree_swap12 x y z, neg_neg]

/-! ### The twisted module of pairs -/

/-- Two-forms paired with three-forms; the algebra acts by `a • (ω, η) = (a ω, da ∧ ω + a η)`. -/
private def Jet (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] : Type u :=
  Two R A × Three R A

private instance : AddCommGroup (Jet R A) :=
  inferInstanceAs (AddCommGroup (Two R A × Three R A))

private def Jet.mk (ω : Two R A) (η : Three R A) : Jet R A := (ω, η)

private def Jet.form (p : Jet R A) : Two R A := (p : Two R A × Three R A).1

private def Jet.diff (p : Jet R A) : Three R A := (p : Two R A × Three R A).2

private lemma Jet.ext {p q : Jet R A} (h₁ : Jet.form p = Jet.form q)
    (h₂ : Jet.diff p = Jet.diff q) : p = q :=
  Prod.ext h₁ h₂

@[simp] private lemma Jet.form_mk (ω : Two R A) (η : Three R A) :
    Jet.form (Jet.mk ω η) = ω := rfl

@[simp] private lemma Jet.diff_mk (ω : Two R A) (η : Three R A) :
    Jet.diff (Jet.mk ω η) = η := rfl

@[simp] private lemma Jet.form_add (p q : Jet R A) :
    Jet.form (p + q) = Jet.form p + Jet.form q := rfl

@[simp] private lemma Jet.diff_add (p q : Jet R A) :
    Jet.diff (p + q) = Jet.diff p + Jet.diff q := rfl

@[simp] private lemma Jet.form_zero : Jet.form (0 : Jet R A) = 0 := rfl

@[simp] private lemma Jet.diff_zero : Jet.diff (0 : Jet R A) = 0 := rfl

private instance : SMul A (Jet R A) where
  smul a p := Jet.mk (a • Jet.form p)
    (wedgeOneTwo (KaehlerDifferential.D R A a) (Jet.form p) + a • Jet.diff p)

@[simp] private lemma Jet.form_smul (a : A) (p : Jet R A) :
    Jet.form (a • p) = a • Jet.form p := rfl

@[simp] private lemma Jet.diff_smul (a : A) (p : Jet R A) :
    Jet.diff (a • p) =
      wedgeOneTwo (KaehlerDifferential.D R A a) (Jet.form p) + a • Jet.diff p := rfl

private instance : Module A (Jet R A) where
  smul a p := a • p
  one_smul p := Jet.ext (by simp) (by simp)
  mul_smul a b p := Jet.ext (by simp [mul_smul]) (by
    simp only [Jet.diff_smul, Jet.form_smul, Derivation.leibniz, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, smul_add, mul_smul]
    abel)
  smul_zero a := Jet.ext (by simp) (by simp)
  smul_add a p q := Jet.ext (by simp) (by
    simp only [Jet.diff_smul, Jet.diff_add, Jet.form_add, map_add, smul_add]
    abel)
  add_smul a b p := Jet.ext (by simp [add_smul]) (by
    simp only [Jet.diff_smul, Jet.diff_add, map_add, LinearMap.add_apply, add_smul]
    abel)
  zero_smul p := Jet.ext (by simp) (by simp)

private def jetAlternating : Ω[A⁄R] [⋀^Fin 2]→ₗ[A] Jet R A where
  toFun v := Jet.mk (wedge (v 0) (v 1))
    (wedgeOneTwo (v 1) (dOne R A (v 0)) - wedgeOneTwo (v 0) (dOne R A (v 1)))
  map_update_add' := by
    intro _ v i x y
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · refine Jet.ext ?_ ?_
      · simp [wedge_add_left']
      · simp [map_add]
        abel
    · refine Jet.ext ?_ ?_
      · simp [wedge_add_right']
      · simp [map_add]
        abel
  map_update_smul' := by
    intro _ v i a x
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · refine Jet.ext ?_ ?_
      · simp [wedge_smul_left']
      · simp only [Jet.diff_mk, Jet.diff_smul, Jet.form_mk, Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 from one_ne_zero), dOne_smul, map_add,
          map_smul, LinearMap.smul_apply, wedgeOneTwo_wedge, smul_sub]
        rw [wedgeThree_cycle (KaehlerDifferential.D R A a) x (v 1)]
        abel
    · refine Jet.ext ?_ ?_
      · simp [wedge_smul_right']
      · simp only [Jet.diff_mk, Jet.diff_smul, Jet.form_mk, Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 from zero_ne_one), dOne_smul, map_add,
          map_smul, LinearMap.smul_apply, wedgeOneTwo_wedge, smul_sub]
        rw [wedgeThree_swap01 (v 0) (KaehlerDifferential.D R A a) x]
        abel
  map_eq_zero_of_eq' := by
    intro v i j hv hij
    have h : v 0 = v 1 := by
      fin_cases i <;> fin_cases j <;> simp_all
    refine Jet.ext ?_ ?_
    · simp [h, wedge_self']
    · simp [h]

private def jetMap : Two R A →ₗ[A] Jet R A :=
  exteriorPower.alternatingMapLinearEquiv jetAlternating

private lemma jetMap_wedge (x y : Ω[A⁄R]) :
    jetMap (wedge x y) =
      Jet.mk (wedge x y) (wedgeOneTwo y (dOne R A x) - wedgeOneTwo x (dOne R A y)) := by
  rw [wedge, jetMap, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

private def formHom : Jet R A →ₗ[A] Two R A where
  toFun := Jet.form
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma jetMap_form (ω : Two R A) : Jet.form (jetMap ω) = ω := by
  change (formHom ∘ₗ jetMap) ω = (LinearMap.id : Two R A →ₗ[A] Two R A) ω
  congr 1
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v => ?_)
  change Jet.form (jetMap (exteriorPower.ιMulti A 2 v)) = exteriorPower.ιMulti A 2 v
  rw [ιMulti_two_eq_wedge, jetMap_wedge, Jet.form_mk]

/-- The exterior differential on relative two-forms. It is the three-form component of the
algebra-linear map sending `x ∧ y` to `(x ∧ y, y ∧ dx - x ∧ dy)` in the pairs of two-forms
and three-forms with the twisted action `a • (ω, η) = (a ω, da ∧ ω + a η)`. -/
def dTwo (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] : Two R A →ₗ[R] Three R A where
  toFun ω := Jet.diff (jetMap ω)
  map_add' x y := by rw [map_add, Jet.diff_add]
  map_smul' r ω := by
    rw [RingHom.id_apply, ← IsScalarTower.algebraMap_smul A r ω, map_smul, Jet.diff_smul,
      (KaehlerDifferential.D R A).map_algebraMap, map_zero, LinearMap.zero_apply, zero_add,
      IsScalarTower.algebraMap_smul]

/-- The exterior differential of a wedge of one-forms: `d(x ∧ y) = y ∧ dx - x ∧ dy`,
that is `dx ∧ y - x ∧ dy`. -/
lemma dTwo_wedge (x y : Ω[A⁄R]) :
    dTwo R A (wedge x y) = wedgeOneTwo y (dOne R A x) - wedgeOneTwo x (dOne R A y) := by
  change Jet.diff (jetMap (wedge x y)) = _
  rw [jetMap_wedge, Jet.diff_mk]

/-- The Leibniz rule `d(a ω) = da ∧ ω + a dω` for the exterior differential on two-forms. -/
lemma dTwo_smul (a : A) (ω : Two R A) :
    dTwo R A (a • ω) = wedgeOneTwo (KaehlerDifferential.D R A a) ω + a • dTwo R A ω := by
  change Jet.diff (jetMap (a • ω)) = _ + a • Jet.diff (jetMap ω)
  rw [map_smul, Jet.diff_smul, jetMap_form]

/-- The exterior differential sends `a db ∧ dc` to `da ∧ db ∧ dc`. -/
lemma dTwo_smul_wedge_d (a b c : A) :
    dTwo R A (a • wedge (KaehlerDifferential.D R A b) (KaehlerDifferential.D R A c)) =
      wedgeThree (KaehlerDifferential.D R A a) (KaehlerDifferential.D R A b)
        (KaehlerDifferential.D R A c) := by
  rw [dTwo_smul, dTwo_wedge, dOne_D, dOne_D, map_zero, map_zero, sub_self, smul_zero, add_zero,
    wedgeOneTwo_wedge]

/-- The exterior differential vanishes on exact two-forms. -/
@[simp]
lemma dTwo_dOne (ω : Ω[A⁄R]) : dTwo R A (dOne R A ω) = 0 := by
  obtain ⟨t, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective R A ω
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Derivation.tensorProductTo_tmul, dOne_smul_d, dTwo_wedge, dOne_D, dOne_D, map_zero,
      map_zero, sub_self]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, add_zero]

lemma dTwo_comp_dOne : (dTwo R A).comp (dOne R A) = 0 :=
  LinearMap.ext dTwo_dOne

section Maps

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

private def alternatingThree (f : A →ₐ[R] B) :
    letI : Module A (Three R B) := Module.compHom (Three R B) f.toRingHom
    Ω[A⁄R] [⋀^Fin 3]→ₗ[A] Three R B := by
  letI : Module A (Three R B) := Module.compHom (Three R B) f.toRingHom
  exact
    { toFun := fun v => exteriorPower.ιMulti B 3 (mapOne f ∘ v)
      map_update_add' := by
        intro _ v i x y
        simp only [Function.comp_update, (mapOne f).map_add, AlternatingMap.map_update_add]
      map_update_smul' := by
        intro _ v i a x
        change exteriorPower.ιMulti B 3 (mapOne f ∘ Function.update v i (a • x)) =
          f a • exteriorPower.ιMulti B 3 (mapOne f ∘ Function.update v i x)
        rw [Function.comp_update, Function.comp_update, (mapOne f).map_smulₛₗ,
          AlternatingMap.map_update_smul]
        rfl
      map_eq_zero_of_eq' := fun v _ _ h hne =>
        (exteriorPower.ιMulti B 3).map_eq_zero_of_eq _ (congrArg (mapOne f) h) hne }

/-- The map on relative three-forms induced by a homomorphism of base algebras. -/
def mapThree (f : A →ₐ[R] B) : Three R A →ₛₗ[f.toRingHom] Three R B := by
  letI : Module A (Three R B) := Module.compHom (Three R B) f.toRingHom
  let F := exteriorPower.alternatingMapLinearEquiv (alternatingThree f)
  exact { F.toAddMonoidHom with map_smul' := F.map_smul }

@[simp]
lemma mapThree_ιMulti (f : A →ₐ[R] B) (v : Fin 3 → Ω[A⁄R]) :
    mapThree f (exteriorPower.ιMulti A 3 v) = exteriorPower.ιMulti B 3 (mapOne f ∘ v) := by
  let : Module A (Three R B) := Module.compHom (Three R B) f.toRingHom
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (alternatingThree f) v

@[simp]
lemma mapThree_wedgeThree (f : A →ₐ[R] B) (x y z : Ω[A⁄R]) :
    mapThree f (wedgeThree x y z) = wedgeThree (mapOne f x) (mapOne f y) (mapOne f z) := by
  rw [wedgeThree, mapThree_ιMulti, wedgeThree]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp]
lemma mapThree_id (ω : Three R A) : mapThree (AlgHom.id R A) ω = ω := by
  change mapThree (AlgHom.id R A) ω = (LinearMap.id : Three R A →ₗ[A] Three R A) ω
  refine LinearMap.eqOn_span (s := Set.range (exteriorPower.ιMulti A 3)) ?_ ?_
  · rintro _ ⟨v, rfl⟩
    change mapThree (AlgHom.id R A) (exteriorPower.ιMulti A 3 v) = exteriorPower.ιMulti A 3 v
    rw [mapThree_ιMulti]
    exact congrArg (exteriorPower.ιMulti A 3) (funext fun i => mapOne_id (v i))
  · rw [exteriorPower.ιMulti_span]
    trivial

@[simp]
lemma mapThree_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) (ω : Three R A) :
    mapThree (g.comp f) ω = mapThree g (mapThree f ω) := by
  let F : Three R A →ₛₗ[(g.comp f).toRingHom] Three R C := (mapThree g).comp (mapThree f)
  change mapThree (g.comp f) ω = F ω
  refine LinearMap.eqOn_span (s := Set.range (exteriorPower.ιMulti A 3)) ?_ ?_
  · rintro _ ⟨v, rfl⟩
    change mapThree (g.comp f) (exteriorPower.ιMulti A 3 v) =
      mapThree g (mapThree f (exteriorPower.ιMulti A 3 v))
    rw [mapThree_ιMulti, mapThree_ιMulti, mapThree_ιMulti]
    exact congrArg (exteriorPower.ιMulti C 3) (funext fun i => mapOne_comp f g (v i))
  · rw [exteriorPower.ιMulti_span]
    trivial

/-- The product of a one-form with a two-form commutes with the maps induced by an
algebra homomorphism. -/
lemma mapThree_wedgeOneTwo (f : A →ₐ[R] B) (x : Ω[A⁄R]) (ω : Two R A) :
    mapThree f (wedgeOneTwo x ω) = wedgeOneTwo (mapOne f x) (mapTwo f ω) := by
  let F : Two R A →ₛₗ[f.toRingHom] Three R B := (mapThree f).comp (wedgeOneTwo x)
  let G : Two R A →ₛₗ[f.toRingHom] Three R B := (wedgeOneTwo (mapOne f x)).comp (mapTwo f)
  change F ω = G ω
  refine LinearMap.eqOn_span (s := Set.range (exteriorPower.ιMulti A 2)) ?_ ?_
  · rintro _ ⟨v, rfl⟩
    change mapThree f (wedgeOneTwo x (exteriorPower.ιMulti A 2 v)) =
      wedgeOneTwo (mapOne f x) (mapTwo f (exteriorPower.ιMulti A 2 v))
    rw [ιMulti_two_eq_wedge, wedgeOneTwo_wedge, mapTwo_wedge, wedgeOneTwo_wedge,
      mapThree_wedgeThree]
  · rw [exteriorPower.ιMulti_span]
    trivial

/-- The exterior differential on two-forms commutes with the maps induced by an algebra
homomorphism. -/
lemma dTwo_natural (f : A →ₐ[R] B) (ω : Two R A) :
    dTwo R B (mapTwo f ω) = mapThree f (dTwo R A ω) := by
  have hω : ω ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A 2)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [ιMulti_two_eq_wedge, mapTwo_wedge, dTwo_wedge, dTwo_wedge, dOne_natural, dOne_natural,
      map_sub, mapThree_wedgeOneTwo, mapThree_wedgeOneTwo]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | smul a x _ hx =>
    rw [(mapTwo f).map_smulₛₗ, dTwo_smul, dTwo_smul, hx, map_add, (mapThree f).map_smulₛₗ,
      mapThree_wedgeOneTwo, mapOne_d]
    rfl

end Maps

end RelativeForms

section Coefficients

variable (R : Type u) [CommRing R]

private def threeFormModules : CommAlgCat.{u} R ⥤ ModuleCat.{u} R where
  obj A := ModuleCat.of R (RelativeForms.Three R A)
  map g := ModuleCat.ofHom (restrictBase R g.hom (RelativeForms.mapThree g.hom))
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun ω => RelativeForms.mapThree_id ω)
  map_comp g h :=
    ModuleCat.hom_ext (LinearMap.ext fun ω => RelativeForms.mapThree_comp g.hom h.hom ω)

end Coefficients

section Cech

open Langlands.Cohomology
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq (inter inter_le_comp)

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (U : Scheme.AffineOpenCover.{u} X)

/-- The relative third exterior powers of the Kähler differentials of the section rings. -/
abbrev threeForms := sectionAlgebras f ⋙ threeFormModules R

/-- Componentwise exterior differential of relative two-forms. -/
def exteriorD2 : twoForms f ⟶ threeForms f where
  app V := ModuleCat.ofHom (RelativeForms.dTwo R ((sectionAlgebras f).obj V))
  naturality {_ _} i := ModuleCat.hom_ext (LinearMap.ext fun ω =>
    RelativeForms.dTwo_natural ((sectionAlgebras f).map i).hom ω)

/-- The Čech functions, one-forms, two-forms and three-forms of total degree three. -/
abbrev C3 := Cochains U (functions f) 3 × Cochains U (oneForms f) 2 ×
  Cochains U (twoForms f) 1 × Cochains U (threeForms f) 0

/-- The total differential `(a,b,c) ↦ (∂a, ∂b + da, ∂c - db, dc)`. -/
def D2 : C2 f U →ₗ[R] C3 f U :=
  let a := LinearMap.fst R (Cochains U (functions f) 2)
    (Cochains U (oneForms f) 1 × Cochains U (twoForms f) 0)
  let bc := LinearMap.snd R (Cochains U (functions f) 2)
    (Cochains U (oneForms f) 1 × Cochains U (twoForms f) 0)
  let b := (LinearMap.fst R (Cochains U (oneForms f) 1) (Cochains U (twoForms f) 0)).comp bc
  let c := (LinearMap.snd R (Cochains U (oneForms f) 1) (Cochains U (twoForms f) 0)).comp bc
  ((cechD U (functions f) 2).comp a).prod
    (((cechD U (oneForms f) 1).comp b + (cochainMap U (exteriorD0 f) 2).comp a).prod
      (((cechD U (twoForms f) 0).comp c - (cochainMap U (exteriorD1 f) 1).comp b).prod
        ((cochainMap U (exteriorD2 f) 0).comp c)))

@[simp]
lemma D2_apply (x : C2 f U) :
    D2 f U x = (cechD U (functions f) 2 x.1,
      cechD U (oneForms f) 1 x.2.1 + cochainMap U (exteriorD0 f) 2 x.1,
      cechD U (twoForms f) 0 x.2.2 - cochainMap U (exteriorD1 f) 1 x.2.1,
      cochainMap U (exteriorD2 f) 0 x.2.2) := rfl

/-- The total differentials in degrees one and two compose to zero. -/
lemma D2_comp_D1 : (D2 f U).comp (D1 f U) = 0 := by
  refine LinearMap.ext fun x => ?_
  change D2 f U (D1 f U x) = 0
  have h10 : cochainMap U (exteriorD1 f) 1 (cochainMap U (exteriorD0 f) 1 x.1) = 0 :=
    funext fun σ => RelativeForms.dOne_dZero (R := R)
      (A := (sectionAlgebras f).obj (op (inter (coverOpens U) σ))) (x.1 σ)
  have h21 : cochainMap U (exteriorD2 f) 0 (cochainMap U (exteriorD1 f) 0 x.2) = 0 :=
    funext fun σ => RelativeForms.dTwo_dOne (R := R)
      (A := (sectionAlgebras f).obj (op (inter (coverOpens U) σ))) (x.2 σ)
  simp only [D1_apply, D2_apply, map_sub, cechD_cechD, cechD_cochainMap, h10, h21, zero_sub,
    neg_add_cancel, sub_sub_cancel]
  rfl

/-- Degree-two cocycles of the total complex. -/
abbrev cocyclesTwo : Submodule R (C2 f U) := (D2 f U).ker

/-- The degree-one total differential with codomain restricted to degree-two cocycles. -/
def boundaryMapTwo : C1 f U →ₗ[R] cocyclesTwo f U :=
  LinearMap.codRestrict (cocyclesTwo f U) (D1 f U) fun x =>
    LinearMap.mem_ker.mpr (LinearMap.congr_fun (D2_comp_D1 f U) x)

@[simp]
lemma boundaryMapTwo_apply (x : C1 f U) : (boundaryMapTwo f U x : C2 f U) = D1 f U x := rfl

/-- The degree-two boundaries as a submodule of the degree-two cocycles. -/
def boundariesTwo : Submodule R (cocyclesTwo f U) := (boundaryMapTwo f U).range

/-- Degree-two relative Čech–de Rham cohomology for the supplied affine cover. -/
abbrev H2 [Smooth f] [IsSeparated f] [Finite U.I₀] : Type u :=
  cocyclesTwo f U ⧸ boundariesTwo f U

/-- Componentwise, `(a, b, c)` is a cocycle when `∂a = 0`, `∂b + da = 0`, `∂c = db` and
`dc = 0`. -/
lemma mem_cocyclesTwo_iff (x : C2 f U) :
    x ∈ cocyclesTwo f U ↔ cechD U (functions f) 2 x.1 = 0 ∧
      cechD U (oneForms f) 1 x.2.1 + cochainMap U (exteriorD0 f) 2 x.1 = 0 ∧
      cechD U (twoForms f) 0 x.2.2 = cochainMap U (exteriorD1 f) 1 x.2.1 ∧
      cochainMap U (exteriorD2 f) 0 x.2.2 = 0 := by
  rw [LinearMap.mem_ker, D2_apply, Prod.mk_eq_zero, Prod.mk_eq_zero, Prod.mk_eq_zero, sub_eq_zero]

/-- A degree-two cocycle is a boundary exactly when it is the total differential of an element
of total degree one. -/
lemma mem_boundariesTwo_iff (x : cocyclesTwo f U) :
    x ∈ boundariesTwo f U ↔ (x : C2 f U) ∈ LinearMap.range (D1 f U) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩

/-- Overlap one-forms that form a Čech cocycle and are relatively closed on every double
overlap. -/
def closedOverlapForms : Submodule R (Cochains U (oneForms f) 1) :=
  (cechD U (oneForms f) 1).ker ⊓ (cochainMap U (exteriorD1 f) 1).ker

lemma mem_closedOverlapForms_iff (ω : Cochains U (oneForms f) 1) :
    ω ∈ closedOverlapForms f U ↔
      cechD U (oneForms f) 1 ω = 0 ∧ cochainMap U (exteriorD1 f) 1 ω = 0 :=
  Iff.rfl

/-- The element `(0, ω, 0)` is a degree-two cocycle exactly when the overlap one-forms `ω` form
a Čech cocycle and are relatively closed. -/
lemma zero_overlap_zero_mem_cocyclesTwo_iff (ω : Cochains U (oneForms f) 1) :
    ((0, ω, 0) : C2 f U) ∈ cocyclesTwo f U ↔ ω ∈ closedOverlapForms f U := by
  rw [mem_cocyclesTwo_iff, mem_closedOverlapForms_iff]
  simp only [map_zero, add_zero, true_and, and_true]
  exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩

/-- The degree-two cocycle `(0, ω, 0)` attached to closed overlap one-forms. -/
def closedOverlapCocycle : closedOverlapForms f U →ₗ[R] cocyclesTwo f U :=
  LinearMap.codRestrict (cocyclesTwo f U)
    ((0 : closedOverlapForms f U →ₗ[R] Cochains U (functions f) 2).prod
      ((closedOverlapForms f U).subtype.prod 0))
    fun ω => (zero_overlap_zero_mem_cocyclesTwo_iff f U ω.val).mpr ω.property

@[simp]
lemma closedOverlapCocycle_apply (ω : closedOverlapForms f U) :
    (closedOverlapCocycle f U ω : C2 f U) = (0, ω.val, 0) := rfl

/-- Two degree-two cocycles have the same class exactly when their difference is the total
differential of an element of total degree one. -/
lemma mk_eq_mk_iff (x y : cocyclesTwo f U) :
    (Submodule.Quotient.mk x : cocyclesTwo f U ⧸ boundariesTwo f U) = Submodule.Quotient.mk y ↔
      (x : C2 f U) - y ∈ LinearMap.range (D1 f U) := by
  rw [Submodule.Quotient.eq, mem_boundariesTwo_iff, Submodule.coe_sub]

variable [Smooth f] [IsSeparated f] [Finite U.I₀]

/-- Send closed overlap one-forms `ω` to the degree-two class of `(0, ω, 0)`. -/
def closedOverlapClass : closedOverlapForms f U →ₗ[R] H2 f U :=
  (boundariesTwo f U).mkQ.comp (closedOverlapCocycle f U)

lemma closedOverlapClass_apply (ω : closedOverlapForms f U) :
    closedOverlapClass f U ω = Submodule.Quotient.mk (closedOverlapCocycle f U ω) := rfl

/-- The class of any degree-two cocycle with components `(0, ω, 0)` is the closed-overlap class
of `ω`. -/
lemma mk_eq_closedOverlapClass (x : cocyclesTwo f U) (ω : closedOverlapForms f U)
    (hx : (x : C2 f U) = (0, ω.val, 0)) :
    (Submodule.Quotient.mk x : H2 f U) = closedOverlapClass f U ω := by
  rw [closedOverlapClass_apply]
  exact congrArg Submodule.Quotient.mk (Subtype.ext hx)

/-- The classes of `(0, ω, 0)` and `(0, ω', 0)` agree exactly when `(0, ω - ω', 0)` is a
total boundary. -/
lemma closedOverlapClass_eq_iff (ω ω' : closedOverlapForms f U) :
    closedOverlapClass f U ω = closedOverlapClass f U ω' ↔
      ((0, ω.val - ω'.val, 0) : C2 f U) ∈ LinearMap.range (D1 f U) := by
  rw [closedOverlapClass_apply, closedOverlapClass_apply, mk_eq_mk_iff,
    closedOverlapCocycle_apply, closedOverlapCocycle_apply, Prod.mk_sub_mk, Prod.mk_sub_mk,
    sub_zero, sub_zero]

/-- The class of `(0, ω, 0)` vanishes exactly when there are Čech functions `a` on double
overlaps and one-forms `b` on the charts with `∂a = 0`, `∂b - da = ω` and `db = 0`. -/
lemma closedOverlapClass_eq_zero_iff (ω : closedOverlapForms f U) :
    closedOverlapClass f U ω = 0 ↔ ∃ x : C1 f U, cechD U (functions f) 1 x.1 = 0 ∧
      cechD U (oneForms f) 0 x.2 - cochainMap U (exteriorD0 f) 1 x.1 = ω.val ∧
      cochainMap U (exteriorD1 f) 0 x.2 = 0 := by
  rw [closedOverlapClass_apply, Submodule.Quotient.mk_eq_zero, mem_boundariesTwo_iff,
    closedOverlapCocycle_apply]
  constructor
  · rintro ⟨x, hx⟩
    rw [D1_apply, Prod.mk.injEq, Prod.mk.injEq] at hx
    exact ⟨x, hx.1, hx.2.1, hx.2.2⟩
  · rintro ⟨x, h₁, h₂, h₃⟩
    exact ⟨x, by rw [D1_apply, h₁, h₂, h₃]⟩

end Cech

end Langlands.AlgebraicGeometry.AffineCechDeRham
