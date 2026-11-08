import Langlands.GroupScheme.Rational.RootDoubleCommutatorBilinear
import Langlands.GroupScheme.Rational.RootHeisenbergNormalForm

/-! # Rational points detect the commutator pairing of a multipliable relative root

A pairing of vector groups that is bilinear in natural vector coordinates is trivial as soon
as it is trivial on rational points, because the coordinate basis vectors are rational. For
the commutator pairing of a multipliable relative root group with a Heisenberg normal form,
this gives: if the rational points of the root group commute, then its points over every test
scheme commute. In field coordinates of the quotient and of the doubled root group, a root
group whose points do not all commute has a non-symmetric cocycle.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section Coordinates

variable {k : Type u} [Field k] {V W : GroupScheme (Spec (CommRingCat.of k))} {d m : ℕ}
    {e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤))}
    {e' : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ W.X) ≃* Multiplicative (Fin m → Γ(T.left, ⊤))}
    {P : V.X ⊗ V.X ⟶ W.X}

/-- In natural vector coordinates, each coordinate basis vector over a test scheme is the
pullback of the corresponding rational basis vector along the structure morphism. -/
theorem symm_single_eq_comp (he : IsNaturalVectorCoordinates e)
    (T : Over (Spec (CommRingCat.of k))) (l : Fin d) :
    (e T).symm (Multiplicative.ofAdd (Pi.single l 1)) =
      Over.homMk (V := Over.mk (𝟙 (Spec (CommRingCat.of k)))) T.hom ≫
        (e (Over.mk (𝟙 (Spec (CommRingCat.of k))))).symm
          (Multiplicative.ofAdd (Pi.single l 1)) := by
  apply (e T).injective
  apply Multiplicative.toAdd.injective
  rw [MulEquiv.apply_symm_apply, he, MulEquiv.apply_symm_apply]
  funext n
  simp only [toAdd_ofAdd]
  by_cases hn : n = l
  · subst hn
    simp
  · simp [hn]

/-- **Rational detection.** A pairing of vector groups that is bilinear in natural vector
coordinates and trivial on rational points is trivial on the points of every test scheme. -/
theorem lift_comp_eq_one_of_rationalPoints (he : IsNaturalVectorCoordinates e)
    (hP : IsBilinearVectorPairing e e' P)
    (h : ∀ x y : rationalPoints V, lift x y ≫ P = 1)
    (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ V.X) : lift x y ≫ P = 1 := by
  let f : (Fin d → Γ(T.left, ⊤)) → (Fin d → Γ(T.left, ⊤)) → (Fin m → Γ(T.left, ⊤)) :=
    fun u v => (e' T (lift ((e T).symm (Multiplicative.ofAdd u))
      ((e T).symm (Multiplicative.ofAdd v)) ≫ P)).toAdd
  have hadd_left : ∀ u u' v, f (u + u') v = f u v + f u' v := by
    intro u u' v
    have hp := (hP T ((e T).symm (Multiplicative.ofAdd u)) ((e T).symm (Multiplicative.ofAdd u'))
      ((e T).symm (Multiplicative.ofAdd v)) 1 1).1
    simp only [f]
    rw [← hp, ofAdd_add, map_mul]
  have hadd_right : ∀ u v v', f u (v + v') = f u v + f u v' := by
    intro u v v'
    have hp := (hP T ((e T).symm (Multiplicative.ofAdd u)) 1 ((e T).symm (Multiplicative.ofAdd v))
      ((e T).symm (Multiplicative.ofAdd v')) 1).2.1
    simp only [f]
    rw [← hp, ofAdd_add, map_mul]
  have hsmul_left : ∀ (r : Γ(T.left, ⊤)) u v, f (r • u) v = r • f u v := by
    intro r u v
    have hp := (hP T ((e T).symm (Multiplicative.ofAdd u)) 1 ((e T).symm (Multiplicative.ofAdd v))
      1 r).2.2.1
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd] at hp
    exact hp
  have hsmul_right : ∀ (r : Γ(T.left, ⊤)) u v, f u (r • v) = r • f u v := by
    intro r u v
    have hp := (hP T ((e T).symm (Multiplicative.ofAdd u)) 1 ((e T).symm (Multiplicative.ofAdd v))
      1 r).2.2.2
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd] at hp
    exact hp
  let B : (Fin d → Γ(T.left, ⊤)) →ₗ[Γ(T.left, ⊤)] (Fin d → Γ(T.left, ⊤)) →ₗ[Γ(T.left, ⊤)]
      (Fin m → Γ(T.left, ⊤)) :=
    LinearMap.mk₂ _ f hadd_left hsmul_left hadd_right hsmul_right
  have hB : B = 0 := by
    refine LinearMap.ext_basis (Pi.basisFun _ (Fin d)) (Pi.basisFun _ (Fin d)) fun l n => ?_
    simp only [Pi.basisFun_apply, LinearMap.zero_apply, B, LinearMap.mk₂_apply, f]
    rw [symm_single_eq_comp he T l, symm_single_eq_comp he T n, ← comp_lift, Category.assoc, h,
      MonObj.comp_one, map_one, toAdd_one]
  have hxy : (e' T (lift x y ≫ P)).toAdd = 0 := by
    have hc := LinearMap.congr_fun₂ hB (e T x).toAdd (e T y).toAdd
    simpa only [B, LinearMap.mk₂_apply, f, ofAdd_toAdd, MulEquiv.symm_apply_apply,
      LinearMap.zero_apply] using hc
  apply (e' T).injective
  rw [map_one]
  exact Multiplicative.toAdd.injective hxy

end Coordinates

section RootGroups

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G U U₂ : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} {a : characterLattice S}
    {j : U ⟶ G} {hj : (subgroup i a).IsRepresentedBy j}
    {j₂ : U₂ ⟶ G} {hj₂ : (subgroup i (2 • a)).IsRepresentedBy j₂}

/-- The points of a group scheme over `Spec k` commute over every test scheme. -/
def PointsCommute (H : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of k))) (g g' : T ⟶ H.X), Commute g g'

/-- Two points of the root group commute when the commutator pairing of their images in the
quotient is trivial. -/
theorem DoubleRootCommutatorPairing.commute_of_lift_pairing_eq_one
    (C : DoubleRootCommutatorPairing i a hj hj₂) {T : Over (Spec (CommRingCat.of k))}
    (g h : T ⟶ U.X) (hp : lift (g ≫ C.q.hom.hom) (h ≫ C.q.hom.hom) ≫ C.pairing = 1) :
    Commute g h := by
  let : Mono j.hom.hom := hj.1
  have hc := C.lift_pairing T g h
  rw [hp, MonObj.one_comp] at hc
  have h3 := hc.symm
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
  apply (cancel_mono j.hom.hom).1
  rw [MonObj.mul_comp, MonObj.mul_comp]
  exact h3

variable [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- If no `n • a` with `n ≥ 3` is a relative root, the commutator pairing is trivial as soon as
it is trivial on rational points. -/
theorem DoubleRootCommutatorPairing.lift_pairing_eq_one_of_rationalPoints
    (C : DoubleRootCommutatorPairing i a hj hj₂) (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)
    (h : ∀ x y : rationalPoints C.V, lift x y ≫ C.pairing = 1)
    (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ C.V.X) : lift x y ≫ C.pairing = 1 := by
  obtain ⟨d, m, e, e', he, -, hP⟩ := C.exists_bilinear_coordinates hS ha hhigh
  exact lift_comp_eq_one_of_rationalPoints he.1 hP h T x y

namespace HeisenbergNormalForm

variable {C : DoubleRootCommutatorPairing i a hj hj₂} (N : HeisenbergNormalForm C)

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] in
include N in
/-- With a Heisenberg normal form, the commutator pairing is trivial on rational points of
the quotient when the rational points of the root group commute. -/
theorem lift_pairing_eq_one_of_commute_rationalPoints
    (h : ∀ g g' : rationalPoints U, Commute g g') (x y : rationalPoints C.V) :
    lift x y ≫ C.pairing = 1 := by
  let : Mono j₂.hom.hom := hj₂.1
  have hq (z : rationalPoints C.V) : (z ≫ N.sec) ≫ C.q.hom.hom = z := by
    rw [Category.assoc, N.sec_comp, Category.comp_id]
  have hp := C.lift_pairing _ (x ≫ N.sec) (y ≫ N.sec)
  have hab : ((x ≫ N.sec) ≫ j.hom.hom) * ((y ≫ N.sec) ≫ j.hom.hom) =
      ((y ≫ N.sec) ≫ j.hom.hom) * ((x ≫ N.sec) ≫ j.hom.hom) := by
    rw [← MonObj.mul_comp (x ≫ N.sec) (y ≫ N.sec) j.hom.hom,
      ← MonObj.mul_comp (y ≫ N.sec) (x ≫ N.sec) j.hom.hom, (h (x ≫ N.sec) (y ≫ N.sec)).eq]
  rw [hq, hq, hab, mul_inv_cancel_right, mul_inv_cancel] at hp
  apply (cancel_mono j₂.hom.hom).1
  rw [hp, MonObj.one_comp]

include N in
/-- **Rational commutation.** If no `n • a` with `n ≥ 3` is a relative root and the rational
points of the root group commute, then the points of the root group over every test scheme
commute. -/
theorem commute_of_commute_rationalPoints
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)
    (h : ∀ g g' : rationalPoints U, Commute g g') : PointsCommute U := fun T g g' =>
  C.commute_of_lift_pairing_eq_one g g'
    (C.lift_pairing_eq_one_of_rationalPoints hS ha hhigh
      (N.lift_pairing_eq_one_of_commute_rationalPoints h) T _ _)

/-- **Non-symmetry of the cocycle.** Suppose no `n • a` with `n ≥ 3` is a relative root and
two points of the root group over some test scheme do not commute. Read the cocycle through
a surjective parametrization of the rational points of the quotient and an injective map on
the rational points of the doubled root group. Then the result is not symmetric. -/
theorem exists_ne_swap_of_not_commute
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)
    {E F : Type*} (first : E → rationalPoints C.V) (hfirst : Function.Surjective first)
    (second : rationalPoints U₂ → F) (hsecond : Function.Injective second)
    {T : Over (Spec (CommRingCat.of k))} (g g' : T ⟶ U.X) (hgg' : ¬ Commute g g') :
    ∃ x y : E, second (lift (first x) (first y) ≫ N.cocycle) ≠
      second (lift (first y) (first x) ≫ N.cocycle) := by
  by_contra hne
  simp only [not_exists, not_not] at hne
  apply hgg'
  refine C.commute_of_lift_pairing_eq_one g g'
    (C.lift_pairing_eq_one_of_rationalPoints hS ha hhigh ?_ T _ _)
  intro x y
  obtain ⟨x', rfl⟩ := hfirst x
  obtain ⟨y', rfl⟩ := hfirst y
  rw [N.pairing_eq, hsecond (hne x' y'), mul_inv_cancel]

/-- **Non-symmetry in field coordinates.** In the shape of the field data of a Heisenberg
normal form: coordinates `first` of the rational points of the quotient by an additive group
`E`, coordinates `second` of the rational points of the doubled root group by an additive
subgroup `W` of `E`, and the cocycle read as a function `form` on `E`. If two points of the
root group over some test scheme do not commute, `form` is not symmetric. -/
theorem exists_form_ne_swap
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)
    {E : Type*} [AddGroup E] {W : AddSubgroup E}
    (first : Multiplicative E ≃* rationalPoints C.V)
    (second : Multiplicative W ≃* rationalPoints U₂) (form : E → E → E)
    (cocycle_eq : ∀ x y : E,
      (Multiplicative.toAdd
        (second.symm (lift (first (Multiplicative.ofAdd x)) (first (Multiplicative.ofAdd y)) ≫
          N.cocycle))).1 = form x y)
    {T : Over (Spec (CommRingCat.of k))} (g g' : T ⟶ U.X) (hgg' : ¬ Commute g g') :
    ∃ x y : E, form x y ≠ form y x := by
  obtain ⟨x, y, hxy⟩ := N.exists_ne_swap_of_not_commute hS ha hhigh
    (fun x : E => first (Multiplicative.ofAdd x))
    (fun z => ⟨Multiplicative.toAdd (first.symm z), first.apply_symm_apply z⟩)
    (fun w => (Multiplicative.toAdd (second.symm w)).1)
    (fun w w' hw => second.symm.injective (Multiplicative.toAdd.injective (Subtype.ext hw)))
    g g' hgg'
  exact ⟨x, y, by rwa [← cocycle_eq, ← cocycle_eq]⟩

end HeisenbergNormalForm

end RootGroups

end Langlands.GroupScheme.RelativeRoot
