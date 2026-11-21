import Langlands.Geometry.FormalGroup.TangentCharacters

/-! # Central scalar actions on the same formal group law -/

noncomputable section

universe u v w c k

namespace Langlands.FormalGroup.ModuleLaw.OrderAction

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {A : Type w} [Ring A] [Algebra O A]
variable {C : Type c} [CommRing C] [Algebra C R] [Algebra C A]
variable {K : Type k} [CommRing K]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable (E : OrderAction A M) {E' : OrderAction A N}

/-- The action on the underlying commutative formal group. -/
def underlyingAction : A →+* CommLaw.Hom M.groupLaw M.groupLaw where
  toFun a := (E.action a).toHom
  map_zero' := congrArg ModuleLaw.Hom.toHom (map_zero E.action)
  map_add' a b := congrArg ModuleLaw.Hom.toHom (map_add E.action a b)
  map_one' := congrArg ModuleLaw.Hom.toHom (map_one E.action)
  map_mul' a b := congrArg ModuleLaw.Hom.toHom (map_mul E.action a b)

variable (h : ∀ (a : C) (x : σ → R),
  E.fiberTangent (RingHom.id R) (algebraMap C A a) x = algebraMap C R a • x)

include h in
/-- Restrict an order action to the central scalars when they act structurally on tangent. -/
def centralModule : ModuleLaw C R σ where
  groupLaw := M.groupLaw
  action := E.underlyingAction.comp (algebraMap C A)
  linear_natural a i j := by
    classical
    let : Fintype σ := Fintype.ofFinite σ
    have hi := congrFun (h a (Pi.single j 1)) i
    change (E.action (algebraMap C A a)).toHom.toCoordinateMap.linearCoeff i j =
      CoordinateMap.scalarLinearCoeff (algebraMap C R a) i j
    rw [CoordinateMap.scalarLinearCoeff, (eq_comm : j = i ↔ i = j)]
    simpa only [fiberTangent_apply_apply, RingHom.id_apply, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] using hi

/-- The original order acts on the central formal module by the same endomorphisms. -/
def centralOrder : OrderAction A (E.centralModule h) where
  action := {
    toFun a := {
      toHom := (E.action a).toHom
      commutes := fun b => by
        change E.underlyingAction a * E.underlyingAction (algebraMap C A b) =
          E.underlyingAction (algebraMap C A b) * E.underlyingAction a
        rw [← map_mul, ← map_mul, Algebra.commutes] }
    map_zero' := by apply ModuleLaw.Hom.ext; exact E.underlyingAction.map_zero
    map_add' a b := by apply ModuleLaw.Hom.ext; exact E.underlyingAction.map_add a b
    map_one' := by apply ModuleLaw.Hom.ext; exact E.underlyingAction.map_one
    map_mul' a b := by apply ModuleLaw.Hom.ext; exact E.underlyingAction.map_mul a b }
  extends_scalars _ := rfl

@[simp]
theorem centralOrder_fiberTangent (φ : R →+* K) (a : A) :
    (E.centralOrder h).fiberTangent φ a = E.fiberTangent φ a := rfl

variable {E h}
variable {h' : ∀ (a : C) (x : τ → R),
  E'.fiberTangent (RingHom.id R) (algebraMap C A a) x = algebraMap C R a • x}

/-- An order-linear formal map retains its coordinates over the new central scalars. -/
def Hom.centralScalars (f : Hom E E') : Hom (E.centralOrder h) (E'.centralOrder h') :=
  ⟨⟨f.val.toHom, fun a => congrArg ModuleLaw.Hom.toHom (f.commutes (algebraMap C A a))⟩,
    fun a => ModuleLaw.Hom.ext (congrArg (fun g : ModuleLaw.Hom M N => g.toHom) (f.commutes a))⟩

/-- Order-linear isomorphisms remain the same inverse maps over the central scalars. -/
def Iso.centralScalars (f : Iso E E') : Iso (E.centralOrder h) (E'.centralOrder h') where
  hom := f.hom.centralScalars
  inv := f.inv.centralScalars
  inv_hom := by
    apply Subtype.ext
    apply ModuleLaw.Hom.ext
    exact congrArg (fun g : Hom E E => g.val.toHom) f.inv_hom
  hom_inv := by
    apply Subtype.ext
    apply ModuleLaw.Hom.ext
    exact congrArg (fun g : Hom E' E' => g.val.toHom) f.hom_inv

end Langlands.FormalGroup.ModuleLaw.OrderAction
