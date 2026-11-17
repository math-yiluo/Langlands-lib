import Langlands.GroupScheme.RelativeLevi.RootWeightAmbientComparison
import Langlands.GroupScheme.RelativeLevi.SplitParabolicFaceChart

/-! # Canonical face terms with a fixed torus and positive base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.LinearAlgebra.RootDatumFaceHeight

variable {J M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootDatum J M N}

/-- For one positive base, the integral face height depends only on which
simple roots have zero pairing, not the nonzero pairing values. -/
theorem faceHeight_eq_of_simple_zero_iff (b : P.Base) (cv cv' : N)
    (hzero : ∀ a ∈ b.support, P.root' a cv = 0 ↔ P.root' a cv' = 0) :
    faceHeight b cv = faceHeight b cv' := by
  apply b.toWeightBasisInt.ext
  intro a
  have ha : b.toWeightBasisInt a = P.rootSpanMem ℤ a := by
    ext
    simp
  rw [ha, faceHeight_simple b cv a a.property, faceHeight_simple b cv' a a.property]
  by_cases hz : P.root' a cv = 0
  · simp [hz, (hzero a a.property).mp hz]
  · have hz' : P.root' a cv' ≠ 0 := fun h => hz ((hzero a a.property).mpr h)
    simp [hz, hz']

end Langlands.LinearAlgebra.RootDatumFaceHeight

namespace Langlands.GroupScheme.SplitParabolicFaceChart

open LocalSplitCell RelativeUnipotent
open Langlands.LinearAlgebra.RootDatumFaceHeight

variable {R : Type u} [CommRing R]
  {I J : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {fam fam' : J → (Ga R ⟶ G)} {wt wt' : I → ℤ}
  (C : SplitParabolicFaceChart i P fam wt)
  (C' : SplitParabolicFaceChart i P fam' wt') (hb : C.base = C'.base)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- Relabel two charts through their actual common positive-root labels. -/
def sameBaseIndexEquiv : Fin C.chart.dimension ≃ Fin C'.chart.dimension :=
  C.index.trans ((Equiv.subtypeEquivRight (fun a => by rw [hb])).trans C'.index.symm)

@[simp]
theorem sameBaseIndexEquiv_root (k : Fin C.chart.dimension) :
    (C'.index (C.sameBaseIndexEquiv C' hb k) : J) = (C.index k : J) := by
  simp [sameBaseIndexEquiv]

variable (hzero : ∀ a : J,
  coPairing (P.root a) wt = 0 ↔ coPairing (P.root a) wt' = 0)

include hzero in
/-- With one base and the same zero-root face, corresponding unscaled face
weights agree even when the original nonzero cocharacter values differ. -/
theorem sameBase_weight_eq (k : Fin C.chart.dimension) :
    C.weights.weight k = C'.weights.weight (C.sameBaseIndexEquiv C' hb k) := by
  have hface : faceHeight C.base C.faceCoweight = faceHeight C'.base C'.faceCoweight := by
    calc
      faceHeight C.base C.faceCoweight = faceHeight C.base C'.faceCoweight := by
        apply faceHeight_eq_of_simple_zero_iff
        intro a _
        rw [C.coweight_eq, C'.coweight_eq]
        exact hzero a
      _ = _ := congrArg (fun b => faceHeight b C'.faceCoweight) hb
  have hcast : (C.weights.weight k : ℤ) =
      (C'.weights.weight (C.sameBaseIndexEquiv C' hb k) : ℤ) := by
    rw [C.weight_eq, C'.weight_eq, ← hface, C.sameBaseIndexEquiv_root]
  exact_mod_cast hcast

variable (hfam : ∀ a, IsRootParametrization i (P.root a) (fam a))
  (hfam' : ∀ a, IsRootParametrization i (P.root a) (fam' a))

include hfam hfam' in
/-- Actual root-parametrization certificates identify the corresponding
ambient root ranges, without a chosen scalar comparison. -/
theorem sameBase_root_range_eq (k : Fin C.chart.dimension) :
    SubgroupFunctor.range (C.chart.roots (ULift.up k) ≫
      Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)) =
    SubgroupFunctor.range (C'.chart.roots
      (ULift.up (C.sameBaseIndexEquiv C' hb k)) ≫
      Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C'.cocharacter)) := by
  rw [C.root_comp, C'.root_comp, C.sameBaseIndexEquiv_root]
  exact (hfam (C.index k)).represents.2.trans (hfam' (C.index k)).represents.2.symm

include hb hzero hfam hfam' in
/-- Every actual face-filtration ambient range is independent of the root
parametrizations, enumeration and auxiliary regular cocharacter for a fixed
torus, base and zero-root face, on all scheme tests. -/
theorem range_inclusion_comp_sameBase (d : ℕ) :
    SubgroupFunctor.range (C.weights.inclusion d ≫
      Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)) =
    SubgroupFunctor.range (C'.weights.inclusion d ≫
      Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C'.cocharacter)) := by
  apply C.weights.range_inclusion_comp_eq C'.weights _ _ (C.sameBaseIndexEquiv C' hb)
    (fun T k => congrArg (fun F => F.carrier T)
      (C.sameBase_root_range_eq C' hb hfam hfam' k))
    (C.sameBase_weight_eq C' hb hzero) d

/-- The actual filtration terms with fixed torus, base and zero-root face
are isomorphic by an isomorphism preserving their ambient inclusions. -/
def sameBaseTermIso (d : ℕ) : C.weights.groupScheme d ≅ C'.weights.groupScheme d := by
  let j := Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)
  let j' := Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C'.cocharacter)
  let : Mono j.hom.hom :=
    (Dynamic.Affine.isRepresentedBy_unipotentHom
      (AffineRegularBorel.cocharacter i C.cocharacter)).1
  let : Mono j'.hom.hom :=
    (Dynamic.Affine.isRepresentedBy_unipotentHom
      (AffineRegularBorel.cocharacter i C'.cocharacter)).1
  exact C.weights.ambientTermIso C'.weights j j' (C.sameBaseIndexEquiv C' hb)
    (fun T k => congrArg (fun F => F.carrier T)
      (C.sameBase_root_range_eq C' hb hfam hfam' k))
    (C.sameBase_weight_eq C' hb hzero) d

/-- The fixed-base comparison preserves the exact original ambient maps. -/
theorem sameBaseTermIso_hom_comp (d : ℕ) :
    (C.sameBaseTermIso C' hb hzero hfam hfam' d).hom ≫
      (C'.weights.inclusion d ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C'.cocharacter)) =
      C.weights.inclusion d ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter) := by
  let : Mono (Dynamic.Affine.unipotentHom
      (AffineRegularBorel.cocharacter i C.cocharacter)).hom.hom :=
    (Dynamic.Affine.isRepresentedBy_unipotentHom
      (AffineRegularBorel.cocharacter i C.cocharacter)).1
  let : Mono (Dynamic.Affine.unipotentHom
      (AffineRegularBorel.cocharacter i C'.cocharacter)).hom.hom :=
    (Dynamic.Affine.isRepresentedBy_unipotentHom
      (AffineRegularBorel.cocharacter i C'.cocharacter)).1
  exact C.weights.ambientTermIso_hom_comp C'.weights
    (Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter))
    (Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C'.cocharacter))
    (C.sameBaseIndexEquiv C' hb)
    (fun T k => congrArg (fun F => F.carrier T)
      (C.sameBase_root_range_eq C' hb hfam hfam' k))
    (C.sameBase_weight_eq C' hb hzero) d

end Langlands.GroupScheme.SplitParabolicFaceChart
