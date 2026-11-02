import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Hausdorff

/-!
# Evaluation topology on affine points

The named carrier `AlgPoint R A S` is the actual set of `R`-algebra maps from `A` to `S`.
It carries the topology induced by evaluation into `S ^ A`. No topology is required on
the coordinate algebra `A`. For rings in a common universe, `SpecPoint` is the actual
set of morphisms `Spec S ⟶ Spec A` over `Spec R`; the standard affine equivalence
transports the evaluation topology to these scheme points.
-/

noncomputable section

universe u v w z

open CategoryTheory Topology

namespace Langlands.AlgebraicGeometry.PointTopology

/-- A named copy of the actual algebra-map point set, allowing an intrinsic topology
without installing a global topology on every `AlgHom` type. -/
def AlgPoint (R : Type u) (A : Type v) (S : Type w)
    [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S] :=
  A →ₐ[R] S

namespace AlgPoint

variable {R : Type u} {A : Type v} {S : Type w}
variable [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]

instance : CoeFun (AlgPoint R A S) (fun _ => A → S) :=
  ⟨fun p a => (show A →ₐ[R] S from p) a⟩

/-- Forget only the named carrier; the point is an actual algebra map. -/
def toAlgHom (p : AlgPoint R A S) : A →ₐ[R] S := p

/-- Regard an algebra map as a point. -/
def ofAlgHom (p : A →ₐ[R] S) : AlgPoint R A S := p

/-- The named point carrier is canonically equivalent to the algebra-map set. -/
def algHomEquiv : AlgPoint R A S ≃ (A →ₐ[R] S) := Equiv.refl _

@[simp] theorem toAlgHom_apply (p : AlgPoint R A S) (a : A) :
    p.toAlgHom a = p a := rfl

@[simp] theorem ofAlgHom_apply (p : A →ₐ[R] S) (a : A) :
    ofAlgHom p a = p a := rfl

@[ext] theorem ext {p q : AlgPoint R A S} (h : ∀ a, p a = q a) : p = q :=
  AlgHom.ext h

/-- The evaluation embedding into the full function space. -/
def evaluation (p : AlgPoint R A S) : A → S := p

theorem evaluation_injective :
    Function.Injective (evaluation : AlgPoint R A S → (A → S)) :=
  fun _ _ h => ext (congrFun h)

instance [TopologicalSpace S] : TopologicalSpace (AlgPoint R A S) :=
  TopologicalSpace.induced evaluation inferInstance

theorem isEmbedding_evaluation [TopologicalSpace S] :
    IsEmbedding (evaluation : AlgPoint R A S → (A → S)) :=
  evaluation_injective.isEmbedding_induced

theorem continuous_evaluation [TopologicalSpace S] :
    Continuous (evaluation : AlgPoint R A S → (A → S)) :=
  isEmbedding_evaluation.continuous

theorem continuous_eval [TopologicalSpace S] (a : A) :
    Continuous (fun p : AlgPoint R A S => p a) :=
  (continuous_apply a).comp continuous_evaluation

/-- The universal property of the evaluation topology. -/
theorem continuous_iff [TopologicalSpace S] {T : Type z} [TopologicalSpace T]
    (f : T → AlgPoint R A S) :
    Continuous f ↔ ∀ a : A, Continuous (fun t => f t a) := by
  rw [isEmbedding_evaluation.isInducing.continuous_iff, continuous_pi_iff]
  rfl

instance [TopologicalSpace S] [T2Space S] : T2Space (AlgPoint R A S) :=
  isEmbedding_evaluation.t2Space

section Maps

variable {B : Type z} [CommRing B] [Algebra R B]

/-- The map of point sets contravariant in the coordinate algebra. -/
def precomp (f : A →ₐ[R] B) (p : AlgPoint R B S) : AlgPoint R A S :=
  p.toAlgHom.comp f

@[simp] theorem precomp_apply (f : A →ₐ[R] B) (p : AlgPoint R B S) (a : A) :
    precomp f p a = p (f a) := rfl

theorem continuous_precomp [TopologicalSpace S] (f : A →ₐ[R] B) :
    Continuous (precomp (S := S) f) :=
  (continuous_iff _).mpr (fun a => continuous_eval (f a))

@[simp] theorem precomp_id (p : AlgPoint R A S) :
    precomp (AlgHom.id R A) p = p := by
  ext a
  rfl

theorem precomp_comp {C : Type*} [CommRing C] [Algebra R C]
    (f : A →ₐ[R] B) (g : B →ₐ[R] C) (p : AlgPoint R C S) :
    precomp (g.comp f) p = precomp f (precomp g p) := by
  ext a
  rfl

/-- Coordinate-algebra isomorphisms give actual homeomorphisms of point spaces. -/
def congr [TopologicalSpace S] (e : A ≃ₐ[R] B) :
    AlgPoint R A S ≃ₜ AlgPoint R B S where
  toFun := precomp e.symm.toAlgHom
  invFun := precomp e.toAlgHom
  left_inv p := by
    ext a
    simp
  right_inv p := by
    ext b
    simp
  continuous_toFun := continuous_precomp _
  continuous_invFun := continuous_precomp _

end Maps

section Coefficients

variable {T : Type z} [CommRing T] [Algebra R T]

/-- Change the value ring by composition with an actual algebra map. -/
def mapCoefficients (f : S →ₐ[R] T) (p : AlgPoint R A S) : AlgPoint R A T :=
  f.comp p.toAlgHom

@[simp] theorem mapCoefficients_apply (f : S →ₐ[R] T) (p : AlgPoint R A S) (a : A) :
    mapCoefficients f p a = f (p a) := rfl

theorem continuous_mapCoefficients [TopologicalSpace S] [TopologicalSpace T]
    (f : S →ₐ[R] T) (hf : Continuous f) :
    Continuous (mapCoefficients (A := A) f) :=
  (continuous_iff _).mpr (fun a => hf.comp (continuous_eval a))

theorem precomp_mapCoefficients {B : Type*} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (g : S →ₐ[R] T) (p : AlgPoint R B S) :
    precomp f (mapCoefficients g p) = mapCoefficients g (precomp f p) := by
  ext a
  rfl

end Coefficients

end AlgPoint

section SchemePoints

open _root_.AlgebraicGeometry

variable (R A S : Type u) [CommRing R] [CommRing A] [CommRing S]
variable [Algebra R A] [Algebra R S]

/-- The actual `S`-valued points of `Spec A` over `Spec R`. -/
def SpecPoint :=
  {f : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of A) //
    f ≫ Spec.algebraMap R A = Spec.algebraMap R S}

/-- The standard affine scheme/algebra point comparison, using Mathlib's fully faithful
`Spec` functor and the exact equation over the base. -/
def specPointEquiv : SpecPoint R A S ≃ AlgPoint R A S :=
  Spec.homEquivAlgHom

instance [TopologicalSpace S] : TopologicalSpace (SpecPoint R A S) :=
  TopologicalSpace.induced (specPointEquiv R A S) inferInstance

/-- The actual scheme point space, with the transported evaluation topology,
is homeomorphic to the actual algebra-map point space. -/
def specPointHomeomorph [TopologicalSpace S] :
    SpecPoint R A S ≃ₜ AlgPoint R A S :=
  (specPointEquiv R A S).toHomeomorphOfIsInducing ⟨rfl⟩

end SchemePoints

end Langlands.AlgebraicGeometry.PointTopology
