import Langlands.Algebra.LocalApproximationMap
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Actual cokernels of compatible local module maps -/

universe uI uA uB uE uF uR uS uM uN

namespace Langlands.Algebra

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
  {D : LocalAlgebraSystem.{uI, uA, uB} ι R S}
  {M : Type uM} {N : Type uN} [AddCommGroup M] [AddCommGroup N]
  [Module S M] [Module S N]

namespace LocalModuleSystem.CompatibleMap

variable {E : LocalModuleSystem.{uI, uA, uB, uE} D M}
  {F : LocalModuleSystem.{uI, uA, uB, uF} D N} {f : M →ₗ[S] N}
  (φ : CompatibleMap E F f)

/-- The semilinear transition induced on the actual component range quotients. -/
def cokernelMap (i j : ι) (h : i ≤ j) :
    (F.obj i ⧸ LinearMap.range (φ.component i)) →ₛₗ[D.algMap i j h]
      (F.obj j ⧸ LinearMap.range (φ.component j)) :=
  (LinearMap.range (φ.component i)).mapQ (LinearMap.range (φ.component j))
    (F.map i j h) (by
      rintro y ⟨m, rfl⟩
      exact ⟨E.map i j h m, φ.map_comm i j h m⟩)

/-- The induced transition sends a quotient representative along the given transition of `F`. -/
@[simp] theorem cokernelMap_mk (i j : ι) (h : i ≤ j) (n : F.obj i) :
    φ.cokernelMap i j h (Submodule.Quotient.mk n) =
      Submodule.Quotient.mk (F.map i j h n) := rfl

/-- The semilinear cocone induced on the actual component and target range quotients. -/
def cokernelιM (i : ι) :
    (F.obj i ⧸ LinearMap.range (φ.component i)) →ₛₗ[D.algι i]
      (N ⧸ LinearMap.range f) :=
  (LinearMap.range (φ.component i)).mapQ (LinearMap.range f) (F.ιM i) (by
    rintro y ⟨m, rfl⟩
    exact ⟨E.ιM i m, (φ.ιM_comm i m).symm⟩)

/-- The quotient cocone sends a representative along the given cocone of `F`. -/
@[simp] theorem cokernelιM_mk (i : ι) (n : F.obj i) :
    φ.cokernelιM i (Submodule.Quotient.mk n) =
      Submodule.Quotient.mk (F.ιM i n) := rfl

/-- The local module diagram of actual cokernels, over the same supplied local algebra diagram. -/
def cokernelSystem :
    LocalModuleSystem.{uI, uA, uB, uF, uR, uS, uN} D (N ⧸ LinearMap.range f) where
  obj i := F.obj i ⧸ LinearMap.range (φ.component i)
  map := φ.cokernelMap
  directed := {
    map_self := by
      intro i x
      induction x using Submodule.Quotient.induction_on with
      | _ n =>
        rw [cokernelMap_mk, DirectedSystem.map_self' F.map]
    map_map := by
      intro k j i hij hjk x
      induction x using Submodule.Quotient.induction_on with
      | _ n =>
        rw [cokernelMap_mk, cokernelMap_mk, cokernelMap_mk,
          DirectedSystem.map_map' F.map] }
  ιM := φ.cokernelιM
  ιM_compat := by
    intro i j h x
    induction x using Submodule.Quotient.induction_on with
    | _ n =>
      rw [cokernelMap_mk, cokernelιM_mk, cokernelιM_mk, F.ιM_compat]

/-- The system's transition has the canonical quotient-map formula. -/
@[simp] theorem cokernelSystem_map_mk (i j : ι) (h : i ≤ j) (n : F.obj i) :
    φ.cokernelSystem.map i j h (Submodule.Quotient.mk n) =
      Submodule.Quotient.mk (F.map i j h n) := rfl

/-- The system's cocone has the canonical target quotient-map formula. -/
@[simp] theorem cokernelSystem_ιM_mk (i : ι) (n : F.obj i) :
    φ.cokernelSystem.ιM i (Submodule.Quotient.mk n) =
      Submodule.Quotient.mk (F.ιM i n) := rfl

/-- The canonical component and target quotient maps form a compatible map to the cokernel system. -/
def cokernelQuotient : CompatibleMap F φ.cokernelSystem (LinearMap.range f).mkQ where
  component i := (LinearMap.range (φ.component i)).mkQ
  map_comm _ _ _ _ := rfl
  ιM_comm _ _ := rfl

/-- The canonical compatible quotient map is the actual component quotient map. -/
@[simp] theorem cokernelQuotient_component (i : ι) (n : F.obj i) :
    φ.cokernelQuotient.component i n = Submodule.Quotient.mk n := rfl

/-- The actual additive comparison evaluates a canonical quotient representative via `F.ιM`. -/
@[simp] theorem cokernelSystem_moduleColimitMap_of_mk (i : ι) (n : F.obj i) :
    letI := Classical.decEq ι
    φ.cokernelSystem.moduleColimitMap
      (AddCommGroup.DirectLimit.of φ.cokernelSystem.obj
        (fun i j h ↦ (φ.cokernelSystem.map i j h).toAddMonoidHom) i
        (Submodule.Quotient.mk n)) =
      Submodule.Quotient.mk (F.ιM i n) := by
  classical
  exact φ.cokernelSystem.moduleColimitMap_of i (Submodule.Quotient.mk n)

end LocalModuleSystem.CompatibleMap
end Langlands.Algebra
