import Langlands.LinearAlgebra.IntegralRationalRootBase
import Langlands.GroupScheme.Reductive.RootDatumWeylComparison
import Langlands.GroupScheme.Rational.RootReflectionAssembly

/-! # Rational simple bases from supplied actual integral root data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IsRootDatumOf

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
  {J : Type*} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  (hP : IsRootDatumOf i P)

/-- Identify all indices of the supplied datum with the actual relative roots. -/
def relativeRootEquiv : J ≃ relativeRoots i where
  toFun j := ⟨P.root j, by
    rw [relativeRoots_eq_roots, ← hP.2.1]
    exact Set.mem_range_self j⟩
  invFun := hP.relativeRootIndex
  left_inv j := P.root.injective (hP.root_relativeRootIndex _)
  right_inv α := Subtype.ext (hP.root_relativeRootIndex α)

omit [Mono i.hom.hom.left] in
theorem relativeRootEquiv_val (j : J) :
    (hP.relativeRootEquiv j).val = P.root j :=
  rfl

omit [Mono i.hom.hom.left] in
theorem relativeRootIndex_relativeRootEquiv (j : J) :
    hP.relativeRootIndex (hP.relativeRootEquiv j) = j :=
  hP.relativeRootEquiv.left_inv j

variable (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite)

local instance :
    (hP.relativeRootReflectionData.rootPairing hT hfinite).IsRootSystem :=
  hP.relativeRootReflectionData.rootPairing_isRootSystem hT hfinite

local instance :
    (hP.relativeRootReflectionData.rootPairing hT hfinite).IsCrystallographic :=
  hP.relativeRootReflectionData.rootPairing_isCrystallographic hT hfinite

include hP

/-- The assembled rational pairing is the original integral pairing on every
pair of full roots, after the canonical integer scalar inclusion. -/
theorem rationalRootPairing_pairing (a b : J) :
    (hP.relativeRootReflectionData.rootPairing hT hfinite).pairing
      (hP.relativeRootEquiv a) (hP.relativeRootEquiv b) =
        (P.pairing a b : ℚ) := by
  change RelativeRootSystem.corootFunctional i
    (P.coroot (hP.relativeRootIndex (hP.relativeRootEquiv b)))
    (RelativeRootSystem.rootVector i (hP.relativeRootEquiv a)) = _
  rw [hP.relativeRootIndex_relativeRootEquiv,
    RelativeRootSystem.corootFunctional_rootVector]
  change (latticePairing T (P.root a) (P.coroot b) : ℚ) = _
  rw [← hP.1]
  rfl

variable [P.IsReduced]

/-- Transfer an actual integral simple base to the full rational relative-root
pairing; the ambient rational character space allows central directions. -/
def rationalBase (b : P.Base) :
    (hP.relativeRootReflectionData.rootPairing hT hfinite).Base := by
  letI := hfinite.to_subtype
  exact Langlands.LinearAlgebra.IntegralRationalRootBase.base P
    (hP.relativeRootReflectionData.rootPairing hT hfinite) toRat
    (relativeRootSpan i).subtype hP.relativeRootEquiv
    hT.character_toRat_injective Subtype.val_injective (fun _ => rfl) b

theorem support_rationalBase (b : P.Base) :
    ((hP.rationalBase hT hfinite b).support : Set (relativeRoots i)) =
      hP.relativeRootEquiv '' (b.support : Set J) := by
  let := hfinite.to_subtype
  exact Langlands.LinearAlgebra.IntegralRationalRootBase.support_base P
    (hP.relativeRootReflectionData.rootPairing hT hfinite) toRat
    (relativeRootSpan i).subtype hP.relativeRootEquiv
    hT.character_toRat_injective Subtype.val_injective (fun _ => rfl) b

/-- The rational simple support is indexed by the supplied integral support. -/
def rationalBaseSupportEquiv (b : P.Base) :
    b.support ≃ (hP.rationalBase hT hfinite b).support := by
  letI := hfinite.to_subtype
  exact Langlands.LinearAlgebra.IntegralRationalRootBase.supportEquiv P
    (hP.relativeRootReflectionData.rootPairing hT hfinite) toRat
    (relativeRootSpan i).subtype hP.relativeRootEquiv
    hT.character_toRat_injective Subtype.val_injective (fun _ => rfl) b

theorem cartanMatrix_rationalBaseSupportEquiv (b : P.Base) (a c : b.support) :
    (hP.rationalBase hT hfinite b).cartanMatrix
      (hP.rationalBaseSupportEquiv hT hfinite b a)
      (hP.rationalBaseSupportEquiv hT hfinite b c) = b.cartanMatrix a c := by
  let := hfinite.to_subtype
  exact Langlands.LinearAlgebra.IntegralRationalRootBase.cartanMatrix_supportEquiv P
    (hP.relativeRootReflectionData.rootPairing hT hfinite) toRat
    (relativeRootSpan i).subtype hP.relativeRootEquiv
    hT.character_toRat_injective Subtype.val_injective (fun _ => rfl) b
    (hP.rationalRootPairing_pairing hT hfinite) a c

end Langlands.GroupScheme.IsRootDatumOf
