import Langlands.GroupScheme.Descent.FiniteUnramifiedComponents
import Langlands.GroupScheme.Descent.SemilinearDatum

/-! # Actual Čech data over finite unramified integer extensions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.LocalGalois Langlands.LocalGalois.Separable
open scoped ValuativeRel

namespace Langlands.GroupScheme.Descent.FiniteUnramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

local instance : NontriviallyNormedField F := localNormedField F
local instance : IsUltrametricDist F := localNormedField_ultrametric F
local instance : CompleteSpace F := localNormedField_complete F

variable (E : IntermediateField F (SeparableClosure F))
    [FiniteDimensional F E] [IsGalois F E]

/-- The actual integer-base automorphism attached to a small Galois index. -/
abbrev integerBaseAut (i : Fin (Module.finrank F E)) :
    Spec (CommRingCat.of (extensionIntegers F E)) ⟶
      Spec (CommRingCat.of (extensionIntegers F E)) :=
  Spec.map (CommRingCat.ofHom (integerAut F E (galoisIndexEquiv F E i)).toRingHom)

instance integerBaseAut_isIso (i : Fin (Module.finrank F E)) :
    IsIso (integerBaseAut F E i) :=
  isIso_SpecMap_iff.mpr (integerAut F E (galoisIndexEquiv F E i)).bijective

/-- Multiplication transported to the small index type. -/
def integerIndexMul (i j : Fin (Module.finrank F E)) : Fin (Module.finrank F E) :=
  (galoisIndexEquiv F E).symm (galoisIndexEquiv F E i * galoisIndexEquiv F E j)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[simp]
theorem galoisIndexEquiv_integerIndexMul (i j : Fin (Module.finrank F E)) :
    galoisIndexEquiv F E (integerIndexMul F E i j) =
      galoisIndexEquiv F E i * galoisIndexEquiv F E j :=
  (galoisIndexEquiv F E).apply_symm_apply _

/-- Contravariance of Spec turns Galois multiplication into base-map composition. -/
theorem integerBaseAut_comp (i j : Fin (Module.finrank F E)) :
    integerBaseAut F E i ≫ integerBaseAut F E j =
      integerBaseAut F E (integerIndexMul F E i j) := by
  dsimp only [integerBaseAut]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro x
  apply Subtype.ext
  change (galoisIndexEquiv F E i) ((galoisIndexEquiv F E j) (x : E)) =
    galoisIndexEquiv F E (integerIndexMul F E i j) (x : E)
  rw [galoisIndexEquiv_integerIndexMul]
  rfl

instance integerComponent_fst_isIso (hE : ArithmeticUnramified F E)
    (i : Fin (Module.finrank F E)) :
    IsIso (integerComponent F E hE i ≫ fst (integerMap F E)) := by
  rw [integerComponent_fst]
  infer_instance

variable (hE : ArithmeticUnramified F E)
    (G : GroupScheme (Spec (CommRingCat.of (extensionIntegers F E))))
    (e : ∀ i, (baseChange (integerBaseAut F E i)).obj G ≅ G)
    (he : ∀ i j,
      pullbackComparison (integerBaseAut F E j) (integerBaseAut F E i)
          (integerBaseAut F E (integerIndexMul F E i j)) (integerBaseAut_comp F E i j) G
          ≪≫ e (integerIndexMul F E i j) =
        (baseChange (integerBaseAut F E i)).mapIso (e j) ≪≫ e i)

/-- Actual Čech descent data from coherent integral semilinear isomorphisms. -/
def integerDatum : Datum (integerMap F E) G :=
  SemilinearComponents.datumOfSemilinear (integerMap F E) (integerComponent F E hE)
    (integerBaseAut F E) (integerComponent_fst F E hE) (integerComponent_snd F E hE)
    (integerIndexMul F E) (integerBaseAut_comp F E) G e he

/-- The datum restricts to the supplied normalized semilinear components. -/
@[simp]
theorem pullIso_integerDatum (i : Fin (Module.finrank F E)) :
    pullIso (integerComponent F E hE i)
        (integerComponent_fst F E hE i) (integerComponent_snd F E hE i)
        (integerDatum F E hE G e he).overlap =
      semilinearComponent G (e i) :=
  SemilinearComponents.pullIso_datumOfSemilinear
    (integerMap F E) (integerComponent F E hE)
    (integerBaseAut F E) (integerComponent_fst F E hE) (integerComponent_snd F E hE)
    (integerIndexMul F E) (integerBaseAut_comp F E) G e he i

end Langlands.GroupScheme.Descent.FiniteUnramified
